Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.
From ExtLib Require Monad.

Require Import Ascii.
Require Import String.
Require Import List.
Require Import PArith.
Require Fin.
Import ListNotations.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Import NonDeterminismBis.
Require Import DeepWeb.Free.Monad.Spec.

From DeepWeb Require Import
     Lib.Util
     Lib.SimpleSpec_NetworkInterface
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
(* TODO: put in [Free]? *)
Inductive note_traceE : Type -> Type :=
| NoteTrace : real_trace -> note_traceE unit.

(* We keep track of a counter to generate fresh connection IDs. *)
Definition network_state := nat.

Definition new_connection (st : network_state) :
  network_state * connection_id :=
  (S st, Connection (S st)).

Definition traceE := nondetE +' arbitraryE +' note_traceE.

(* Type of trees annotated with traces. *)
Definition itree_traces := M traceE unit.

(* We traverse the tree, accumulating a trace and outputing
   it every time a new event gets added. The traces that the
   output tree is annotated with are exactly the set of traces
   of the original tree. *)

(* Main body of [enum_traces_handler]. *)
Definition enum_traces_handler :
  forall X, network_state * real_trace ->
            serverE X -> M traceE (_ * X) :=
  fun X '(st, cur_trace) e =>
    match e with
    | (| e ) =>
      let new_event e x st :=
          let cur_trace := (e :: cur_trace) in
          ^ NoteTrace (rev cur_trace) ;;
          ret ((st, cur_trace), x) in
      match e in networkE X' return (X' -> X) -> _ with
      | Accept => fun id =>
        let '(st, c) := new_connection st in
        new_event (NewConnection c) (id c) st
      | RecvByte c => fun id =>
        b <- arb;;
        new_event (ToServer c b) (id b) st
      | SendByte c b => fun id =>
        new_event (FromServer c b) (id tt) st
      end (fun x => x)
    | ( _Or |) => x <- embed _Or;; ret ((st, cur_trace), x)
    end.

Definition enum_traces (t : itree_server) : itree_traces :=
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
Fixpoint random_trace' (max_depth : nat) (t : itree_traces) :
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
    | Vis _ ( _Or ||) k =>
      match _Or in nondetE X return (X -> _) -> G' _ with
      | Or _ _ => fun id cont fuel =>
        xs <- shuffle every_fin;;
        traverseG' xs (fun x =>
          random_trace' max_depth (k (id x))) cont fuel
      end id
    end
  end.

Definition random_trace (max_depth : nat) (fuel : nat)
           (t : itree_server) :
  G (list real_trace) :=
  runG' fuel (random_trace' max_depth (enum_traces t)).

(**)

(* Plumbing to adapt the test function. *)

(* Failure carries counterexample. *)
Inductive test_result cx := OK | GIVEUP | FAIL (x : cx).

Arguments OK {cx}.
Arguments GIVEUP {cx}.
Arguments FAIL {cx} x.

Definition Checker' := (nat -> Checker) -> (nat -> Checker).

Definition run_checker' (fuel : nat) (c : Checker') : Checker :=
  c (fun _ => checker true) fuel.

Definition burn (cont : nat -> Checker) (fuel : nat) : Checker :=
  match fuel with
  | O => checker true
  | S fuel => cont fuel
  end.

Definition or_ck (c1 c2 : Checker') : Checker' :=
  fun cont => c1 (burn (c2 cont)).

Notation "a ||? b" := (fun x => or_ck a b (id x))
(at level 50).

Definition ok : Checker' := fun cont => cont.

Fixpoint traverse_qc {A} (xs : list A)
         (ck : A -> Checker') : Checker' :=
  match xs with
  | [] => ok
  | x :: xs => ck x ||? traverse_qc xs ck
  end.

Fixpoint forall_traces (max_depth : nat)
         (check_trace : real_trace -> result) (t : itree_traces)
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
          | OutOfFuel => ok cont fuel
          | Found _ => forall_traces max_depth check_trace (k (id tt)) cont fuel
          | NotFound => whenFail' (fun _ => show tr) false
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
      | ( _Or ||) =>
        match _Or in nondetE X return (X -> _) -> _ with
        | Or _ n => fun id cont fuel =>
          let check x :=
              forall_traces max_depth check_trace (k (id x)) in
          checker (
            xs <- shuffle every_fin;;
            ret (traverse_qc xs check cont fuel))
        end id
      end
    end
  end.

Definition check_trace_incl
           (max_depth : nat)
           (backtrack_fuel : nat)
           (descramble_fuel : nat)
           (spec : itree_spec)
           (impl : itree_server) :=
  let check_trace := is_scrambled_trace_of descramble_fuel spec in
  run_checker' backtrack_fuel
               (forall_traces max_depth check_trace (enum_traces impl)).

Definition check_trace_incl_def
           (spec : itree_spec)
           (impl : itree_server) :=
  check_trace_incl 100 100 1000 spec impl.
