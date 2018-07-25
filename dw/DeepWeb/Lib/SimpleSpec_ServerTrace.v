Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.
From ExtLib Require Monad.

From Custom Require Import
     List.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Internal.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Require Import DeepWeb.Free.Monad.Spec.

From DeepWeb Require Import
     Lib.Util
     Lib.SimpleSpec_Server
     Lib.SimpleSpec_Traces
     Lib.SimpleSpec_Observer
     Lib.SimpleSpec_Descramble.

Instance Monad_G : Monad G :=
  { ret _ := returnGen;
    bind _ _ := bindGen;
  }.

Definition shuffle {A} (xs : list A) : G (list A) :=
  let n := length xs in
  (fix shuf n xs :=
    match n, xs with
    | S n, x :: xs' =>
      zys <- elements (x, xs) (picks xs);;
      let '(z, ys) := zys in
      zs <- shuf n ys;;
      ret (z :: zs)
    | _, _ => ret []
    end) n xs.


(* Here we traverse the [server'] tree to generate its traces. *)

(* We use the following effect to annotate a tree with traces. *)
Inductive note_traceE : Type -> Type :=
| NoteTrace : real_trace -> note_traceE unit.

(* We keep track of a counter to generate fresh connection IDs. *)
Definition network_state := nat.

Definition new_connection (st : network_state) :
  network_state * connection_id :=
  (S st, Connection (S st)).

Definition traceM :=
  M (failureE +' nondetE +' arbitraryE +' note_traceE).

(* We traverse the tree, accumulating a trace and outputing
   it every time a new event gets added. The traces that the
   output tree is annotated with are exactly the set of traces
   of the original tree. *)

(* Main body of [enum_traces_handler]. *)
Definition enum_traces_handler :
  forall X, network_state * real_trace ->
            (failureE +' nondetE +' serverE) X -> traceM (_ * X) :=
  fun X '(st, cur_trace) e =>
    match e with
    | (| e ) =>
      let new_event e x st :=
          let cur_trace := (e :: cur_trace) in
          ^ NoteTrace (rev cur_trace) ;;
          ret ((st, cur_trace), x) in
      match e in serverE X' return (X' -> X) -> _ with
      | Accept => fun id =>
        let '(st, c) := new_connection st in
        new_event (NewConnection c) (id c) st
      | RecvByte c => fun id =>
        b <- arb;;
        new_event (ToServer c b) (id b) st
      | SendByte c b => fun id =>
        new_event (FromServer c b) (id tt) st
      end (fun x => x)
    | (| _Or |) => x <- embed _Or;; ret ((st, cur_trace), x)
    | ( Fail reason ||) => fail reason
    end.

Definition enum_traces (t : ServerM unit) : traceM unit :=
  mapM snd (hom_state enum_traces_handler (0, []) t).

(**)

(* A small backtracking generator library. *)

(* There are a lot of dead ends in the above tree.
   We use backtracking to increase our chances of reaching
   more interesting traces. *)

(* Backtracking generator. We use fuel to control the execution
   time predictably. *)
Definition G' (A : Type) := (nat -> G (list A)) -> nat -> G (list A).

Definition runG' {A} (fuel : nat) (g : G' A) : G (list A) :=
  g (fun _ => ret []) fuel.

(* Append two generators. *)
Definition orG' {A} (g1 g2 : G' A) : G' A :=
  fun cont =>
    g1 (fun fuel => match fuel with
                    | O => ret []
                    | S fuel => g2 cont fuel
                    end).

(* Generate a constant element. *)
Definition retG' {A} (x : A) : G' A :=
  fun cont fuel =>
    xs <- cont fuel;;
    ret (x :: xs).

(* Empty generator. *)
Definition emptyG' {A} : G' A := fun cont fuel => cont fuel.

(* Run a parameterized generator [f] with each element
   in the list [xs] as an argument. *)
Fixpoint traverseG' {A B} (xs : list A)
         (f : A -> G' B) : G' B :=
  match xs with
  | [] => emptyG'
  | x :: xs => orG' (f x) (traverseG' xs f)
  end.

(**)

(* Generate random traces up to a given depth in the tree. *)
Fixpoint random_trace' (max_depth : nat) (t : traceM unit) :
  G' real_trace :=
  match max_depth with
  | O => emptyG'
  | S max_depth =>
    match t with
    | Tau t => random_trace' max_depth t
    | Ret tt => emptyG'
    | Vis _ (| e ) k =>
      match e in note_traceE X return (X -> _) -> _ with
      | NoteTrace tr => fun id =>
        orG' (retG' tr)
             (random_trace' max_depth (k (id tt)))
      end id
    | Vis _ (| _Arb |) k =>
      match _Arb in arbitraryE X return (X -> _) -> _ with
      | Arb _ _ _ _ _ => fun id cont fuel =>
        x <- arbitrary;;
        random_trace' max_depth (k (id x)) cont fuel
      end id
    | Vis _ (| _Or ||) k =>
      match _Or in nondetE X return (X -> _) -> G' _ with
      | Or => fun id cont fuel =>
        xs <- shuffle [false; true];;
        traverseG' xs (fun x =>
          random_trace' max_depth (k (id x))) cont fuel
      end id
    | Vis _ ( Fail reason |||) k => emptyG'
    end
  end.

Definition random_trace (max_depth : nat) (fuel : nat)
           (t : ServerM unit) :
  G (list real_trace) :=
  runG' fuel (random_trace' max_depth (enum_traces t)).

(**)

(* Plumbing to adapt the test function. *)

(* Failure carries counterexample. *)
Definition test_result cx := result unit cx.

Definition Checker' := (nat -> Checker) -> (nat -> Checker).

Definition run_checker' (fuel : nat) (c : Checker') : Checker :=
  c (fun _ => checker true) fuel.

Definition burn (cont : nat -> Checker) (fuel : nat) : Checker :=
  match fuel with
  | O => checker true
  | S fuel => cont fuel
  end.

Notation eta f := (fun x => f (id x)).

Definition or_ck (c1 c2 : Checker') : Checker' :=
  fun cont => c1 (burn (eta (c2 cont))).

Notation "a ||? b" := (fun x => or_ck a b (id x))
(at level 50).

Definition ok : Checker' := fun cont => cont.

Fixpoint traverse_qc {A} (xs : list A)
         (ck : A -> Checker') : Checker' :=
  match xs with
  | [] => ok
  | x :: xs => ck x ||? traverse_qc xs ck
  end.

Definition count_from_server (tr : hypo_trace) :=
  length (filter is_FromServer tr).

Fixpoint forall_traces (max_depth : nat)
         (check_trace : real_trace -> result hypo_trace unit)
         (t : traceM unit)
  : Checker' :=
  match max_depth with
  | O => ok
  | S max_depth =>
    match t with
    | Tau t => forall_traces max_depth check_trace t
    | Ret tt => ok
    | Vis _ e k =>
      match e with
      | (| _Note ) =>
        match _Note in note_traceE X return (X -> _) -> _ with
        | NoteTrace tr => fun id cont fuel =>
          match check_trace tr with
          | DONTKNOW => ok cont fuel
          | OK tr =>
            (* collect (count_from_server tr) *)
                    (forall_traces max_depth check_trace (k (id tt)) cont fuel)
          | FAIL _ => whenFail' (fun _ => show tr) false
          end
        end id
      | (| _Arb |) =>
        match _Arb in arbitraryE X return (X -> _) -> _ with
        | Arb _ _ _ _ _ => fun id cont fuel =>
          checker (
            x <- arbitrary;;
            ret (forall_traces max_depth check_trace (k (id x))
                               cont fuel))
        end id
      | (| _Or ||) =>
        match _Or in nondetE X return (X -> _) -> _ with
        | Or => fun id cont fuel =>
          let check x :=
              forall_traces max_depth check_trace (k (id x)) in
          checker (
            xs <- shuffle [false; true];;
            ret (traverse_qc xs check cont fuel))
        end id
      | ( Fail reason |||) => ok
      end
    end
  end.

Definition refines_mod_network_test_
           (max_depth : nat)
           (backtrack_fuel : nat)
           (descramble_fuel : nat)
           (observer : ObserverM unit)
           (server : ServerM unit) :=
  let check_trace := is_scrambled_trace_test_ descramble_fuel observer in
  run_checker' backtrack_fuel
               (forall_traces max_depth check_trace (enum_traces server)).

Definition refines_mod_network_test
           (observer : ObserverM unit)
           (server : ServerM unit) :=
  refines_mod_network_test_ _1000 _100 (5 * _1000) observer server.
