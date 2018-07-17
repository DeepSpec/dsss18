Generalizable Variable E.
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

Require Import DeepWeb.Util.ByteType.

Require Import DeepWeb.Lib.NetworkInterface.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(* The observations that can be made by the spec.
   This is parameterized by a type of "hints" that
   can be used to help generating test cases. *)
Inductive observerE' (hint_ : Type) : Type -> Type :=
  (* Observe the creation of a new connection *)
| ObsConnect : observerE' hint_ connection_id

  (* Observe a byte going into the server on a particular
     connection *)
| ObsToServer :
    connection_id ->
    hint_ ->
    observerE' hint_ byte

  (* Observe a byte going out of the server.
     This action can return [None] "holes" as a way to hypothesize
     that the server sent some message we haven't yet received,
     so we can keep testing the rest of the trace.
     We must be careful that, if a trace with holes is
     rejected, then it must also be for any substitution
     of actual values for those holes. *)
| ObsFromServer :
    connection_id -> observerE' hint_ (option byte)
.

Arguments ObsConnect {hint_}.
Arguments ObsToServer {hint_}.
Arguments ObsFromServer {hint_}.

(* Observations without any hints. *)
Notation pure_observerE := (observerE' unit).

Definition msg_hint : Type := G byte.

(* Observations with hints, given by a random generator. *)
Notation observerE := (observerE' msg_hint).

Inductive hint : Type :=
| HintConnect : hint
| HintToServer : connection_id -> G byte -> hint.

Definition unhint {X R : Type} (e : observerE X)
           (k : option hint ->
                pure_observerE X -> R) : R :=
  match e in observerE' _ X'
        return (_ -> pure_observerE X' -> _) -> _ with
  | ObsConnect => fun k => k (Some HintConnect) ObsConnect
  | ObsToServer c h => fun k =>
    k (Some (HintToServer c h)) (ObsToServer c tt)
  | ObsFromServer c => fun k => k None (ObsFromServer c)
  end k.

Definition strip_hint {X : Type} (e : observerE X) :
  pure_observerE X :=
  unhint e (fun _ e => e).

Definition get_hint {X : Type} (e : observerE X) : option hint :=
  unhint e (fun h _ => h).

(* Equality comparison, return a proof of equality of the
   indices (this could be generalized to a complete decision
   procedure). *)
Definition observer_eq {X Y : Type}
           (e1 : pure_observerE X) (e2 : pure_observerE Y) :
  option (X = Y) :=
  match e1, e2 with
  | ObsConnect, ObsConnect => Some eq_refl
  | ObsToServer c tt, ObsToServer c' tt
  | ObsFromServer c, ObsFromServer c' =>
    if c = c' ? then Some eq_refl else None
  | _, _ => None
  end.

Definition coerce {X Y : Type} (p : X = Y) (x : X) : Y :=
  match p in eq _ Y return Y with
  | eq_refl => x
  end.

Definition E0 := nondetE +' observerE.

(* Make an assertion on a value, if it exists. *)
Definition assert_on {A}
           (r : string) (oa : option A) (check : A -> bool) :
  M E0 unit :=
  match oa with
  | None => ret tt
  | Some a =>
    if check a then ret tt else fail ("assertion failed: " ++ r)
  end.

Definition BUFF_SZ := 3.

(* Helper for [obs_msg_to_server] *)
CoFixpoint obs_msg_to_server'
           (c : connection_id) (n : nat) (k : bytes -> M E0 bytes) :
  M E0 bytes :=
  match n with
  | O => k ""
  | S n =>
    b <- ^ ObsToServer c arbitrary;;
    obs_msg_to_server' c n (fun bs => k (String b bs))
  end.

(* Observe a complete message sent to the server. *)
Definition obs_msg_to_server
           (c : connection_id) : M E0 bytes :=
  obs_msg_to_server' c BUFF_SZ ret.

(* Observe a complete message received from the server. *)
CoFixpoint obs_msg_from_server
           (c : connection_id) (msg : bytes) :
  M E0 unit :=
  match msg with
  | "" => ret tt
  | String b0 msg =>
    ob <- ^ ObsFromServer c;;
    assert_on "bytes must match" ob (fun b1 => b1 = b0 ?);;
    obs_msg_from_server c msg
  end.

(* [conns]: open connections, used for generating test cases.
   [last_msg]: last message received.
 *)
CoFixpoint swap_spec_loop
            (conns : list connection_id)
            (last_msg : bytes) :
  M E0 void :=
  disj "swap_spec"
    ( (* Accept a new connection. *)
      c <- ^ ObsConnect;;
      swap_spec_loop (c :: conns) last_msg
    | (* Exchange one pair of messages on a connection. *)
      c <- choose "do swap" conns;;
      msg <- obs_msg_to_server c;;
      obs_msg_from_server c last_msg;;
      swap_spec_loop conns msg
    ).

Definition init_msg :=
  let fix repeat_str c n :=
      match n with
      | O => ""
      | S n => String c (repeat_str c n)
      end in repeat_str "0"%char BUFF_SZ.

Definition swap_spec := swap_spec_loop [] init_msg.

(* The spec can be viewed as a set of traces. *)

(* An [event] is an observer action together with its result. *)
Inductive event :=
| Event : forall X, pure_observerE X -> X -> event.

Arguments Event {X}.

Definition trace := list event.

Definition match_obs {X Y R : Type}
           (e0 : pure_observerE X)
           (e1 : pure_observerE Y)
           (cont : M E0 void -> R)
           (fail_ : R) :
  X -> (Y -> M E0 void) -> R :=
  match e0 in observerE' _ X, e1 in observerE' _ Y
        return X -> (Y -> _) -> _ with
  | ObsConnect, ObsConnect => fun x k => cont (k x)
  | ObsToServer c _, ObsToServer c' _ => fun x k =>
    if c = c' ? then
      cont (k x)
    else
      fail_
  | ObsFromServer c, ObsFromServer c' => fun x k =>
    if c = c' ? then
      cont (k x)
    else
      fail_
  | _, _ => fun _ _ => fail_
  end.

(* [exists x, k x = true] *)
Definition nondet_exists {X : Type}
           (e : nondetE X) (k : X -> bool) : bool :=
  match e in nondetE X' return (X' -> X) -> _ with
  | Or n _ =>
    (fix go n0 : (Fin.t n0 -> X) -> bool :=
       match n0 with
       | O => fun _ => false
       | S n0 => fun f => k (f Fin.F1) || go n0 (fun m => f (Fin.FS m))
       end) n
  end%bool (fun x => x).

(* Basically, a trace [t] belongs to a tree if there is a path
   through the tree (a list of [E0] effects) such that its
   restriction to [observerE] events is [t].
   Because trees are coinductive (in particular, they can contain
   arbitrary sequences of [Tau] or [Vis] with invisible effects),
   it is not possible to decide whether a trace matches the tree.
   Thus we add a [fuel] parameter assumed to be "big enough"
   for the result to be reliable. *)
Fixpoint is_trace_of (fuel : nat) (t : trace) (s : M E0 void) : bool :=
  match fuel with
  | O => false
  | S fuel =>
    match s, t with
    | Tau s, t => is_trace_of fuel t s
    | Ret v, t => match v : void with end
    | Vis _ (| e1 ) k, Event _ e0 x :: t =>
      match_obs e0 (strip_hint e1) (fun s => is_trace_of fuel t s)
                false x k
    | Vis _ (| e1 ) k, [] => true
    (* The trace belongs to the tree [s] *)
    | Vis _ ( _Or |) k, t =>
      nondet_exists _Or (fun b => is_trace_of fuel t (k b))
    end
  end.

Example trace_example :
  true = is_trace_of 100 [
    Event ObsConnect 0;
    Event ObsConnect 1;
    Event (ObsToServer 0 tt) "a";
    Event (ObsToServer 0 tt) "b";
    Event (ObsToServer 0 tt) "c";
    Event (ObsFromServer 0) (Some "0");
    Event (ObsFromServer 0) (Some "0");
    Event (ObsFromServer 0) (Some "0");
    Event (ObsToServer 1 tt) "d";
    Event (ObsToServer 1 tt) "e";
    Event (ObsToServer 1 tt) "f";
    Event (ObsFromServer 1) (Some "a");
    Event (ObsFromServer 1) (Some "b");
    Event (ObsFromServer 1) (Some "c")
  ]%char swap_spec.
Proof. reflexivity. Qed.

Example trace_example2 :
  false = is_trace_of 100 [
    Event ObsConnect 0;
    Event (ObsToServer 0 tt) "a";
    Event (ObsToServer 0 tt) "b";
    Event (ObsToServer 0 tt) "c";
    Event (ObsFromServer 0) (Some "1")
    (* error: Initial state is 000 *)
  ]%char swap_spec.
Proof. reflexivity. Qed.

(* The traces produced by the tree [swap_spec] are very structured,
   with sequences of bytes sent and received alternating tidily.
   However, in general:
   - the network may reorder some messages, so the traces
     we actually see during testing will not be directly
     checkable using [is_trace_of], they must be descrambled
     first;
   - a server implementation may also want to reorder responses
     differently for performance and other practical reasons;
     here we will consider a server correct if it cannot be
     distinguished over the network from a server that actually
     produces the same traces as the spec above.
 *)

(* The constraints on the network are:
   - a connection must be open before bytes can be exchanged on it;
   - two bytes going in the same direction on the same connection
     must arrive in-order;
   - if we get a byte [b1] from the server before we send some [b2]
     to it, then the server definitely sent [b1] before it
     can receive [b2]. ([FromServer,ToServer] cannot be descrambled
     to [ToServer,FromServer], regardless of the connections
     where the two events happen.)
 *)

(* Unary tree node carrying some event. *)
Inductive eventE : Type -> Type :=
| Happened : event -> eventE unit.

(* We enumerate descramblings in a tree structure, using
   [nondetE] to branch, so that each successful pat (i.e., not
   leading to failure) is a descrambling of a given trace. *)
Definition eventE' := nondetE +' eventE.

(* Helper for [pick_event]. *)
CoFixpoint pick_event' (t_prev t : trace) :
  M eventE' trace :=
  match t with
  | [] => fail "empty trace"
  | Event _ e _ as ev :: t =>
    let pick_this :=
        _ <- ^ Happened ev;;
       ret (List.rev t_prev ++ t)%list in
    disj "pick_event'"
      ( match e with
        | ObsConnect =>
          if forallb (fun ev =>
                match ev with
                | Event _ (ObsFromServer _) _ => false
                | _ => true
                end) t_prev then
            pick_this
          else
            fail "inaccessible ObsConnect"

        | ObsToServer c _ =>
          if forallb (fun ev =>
               match ev with
               | Event _ (ObsFromServer c') _ => false
               | Event _ ObsConnect c'
               | Event _ (ObsToServer c' _) _ => c <> c' ?
               end) t_prev then
            pick_this
          else
            fail "inaccessible ObsToServer"

        | ObsFromServer c =>
          if forallb (fun ev =>
               match ev with
               | Event _ (ObsToServer _ _) _ => true
               | Event _ ObsConnect c'
               | Event _ (ObsFromServer c') _ => c <> c' ?
               end) t_prev then
            pick_this
          else
            fail "inaccessible ObsFromServer"

        end
      | pick_event' (ev :: t_prev) t
      )
  end.

(* Given a scrambled trace, remove one event that could potentially
   be the next one in a descrambling.
 *)
Definition pick_event : trace -> M eventE' trace :=
  pick_event' [].

Definition is_ObsFromServer (ev : event) :=
  match ev with
  | Event _ (ObsFromServer _) _ => true
  | _ => false
  end.

(* Once the only things left are messages sent to the server,
   we drop them, since there is no response to compare them
   against. *)
CoFixpoint descramble (t : trace) : M eventE' unit :=
  match filter is_ObsFromServer t with
  | [] => ret tt
  | _ :: _ =>
    t' <- pick_event t;;
    descramble t'
  end.

(* Functions to list the descrambled traces *)
Section ListDescramble.

Fixpoint list_eventE' (fuel : nat) (s : M eventE' unit)
           (acc : list trace) (new : trace -> trace) :
  option (list trace) :=
  match fuel with
  | O => None
  | S fuel =>
    match s with
    | Tau s => list_eventE' fuel s acc new
    | Ret tt => Some (new [] :: acc)
    | Vis _ (| e ) k =>
      match e in eventE X return (X -> _) -> _ with
      | Happened ev => fun k =>
        list_eventE' fuel (k tt) acc (fun t => new (ev :: t))
      end k
    | Vis X ( _Or |) k =>
      match _Or in nondetE X' return (X' -> _) -> _ with
      | Or n _ =>
        (fix go n0 : (Fin.t n0 -> X) -> _ :=
           match n0 with
           | O => fun _ => Some acc
           | S n0 => fun f =>
             match list_eventE' fuel (k (f Fin.F1)) acc new with
             | None => None
             | Some acc => go n0 (fun m => f (Fin.FS m))
             end
           end) n
      end (fun x => x)
    end
  end.

(* [None] if not enough fuel. *)
Definition list_eventE (fuel : nat) (s : M eventE' unit) :
  option (list trace) :=
  list_eventE' fuel s [] (fun t => t).

(* Fuel of the order of [length t ^ 2] should suffice. *)
Definition list_descramblings (fuel : nat) (t : trace) :
  option (list trace) :=
  list_eventE fuel (descramble t).

(*
Compute list_descramblings 50 [
  Event ObsConnect 0;
  Event (ObsToServer 0 tt) "A";
  Event ObsConnect 1;
  Event (ObsToServer 0 tt) "B";
  Event (ObsFromServer 0) (Some "C")
]%char.
*)

End ListDescramble.

(* Those descramblings are still missing [ObsFromServer] events
   with holes (i.e., with [None] in the last field of [Event]).
   We will insert them as needed when comparing the tree of
   descramblings with the spec tree. *)

CoFixpoint select_event' {X}
           (e : pure_observerE X) (t_prev t : trace) :
  M (nondetE +' eventE) (X * trace) :=
  match t with
  | [] =>
    match e with
    | ObsFromServer _ as e =>
      (* If we're expecting a reply from the server, we
         can temporarily put a hole to see what should happen
         next. *)
      ^ Happened (Event e None);;
      ret (None, rev t_prev)
    | _ => fail "no event left to pick"
    end
  | Event X' e' x as ev :: t =>
    match observer_eq e' e with
    | Some p => (* e' = e *)
        ^ Happened ev;;
        ret (coerce p x, rev t_prev ++ t)%list
    | None => (* e' <> e *)
      let try_next := Tau (select_event' e (ev :: t_prev) t) in
      match e, e' with

      | ObsConnect as e, ObsToServer _ _
      | ObsToServer _ _ as e, (ObsConnect | ObsToServer _ _)
      | ObsFromServer _ as e, _ =>
        try_next

        (* We're looking for a [Connect/ToServer] event
           but there is still a [FromServer] event to explain. *)
      | (ObsConnect | ObsToServer _ _), ObsFromServer _ =>
        fail "inaccessible event"

      | ObsConnect, ObsConnect => fail "should not happen"
      end
    end
  end.

Definition select_event {X} (e : pure_observerE X) :
  trace -> M (nondetE +' eventE) (X * trace) := select_event' e [].

(* [s]: tree of acceptable traces (spec)
   [t]: scrambled trace

   The result tree has a [Ret] leaf iff there is a descrambled
   trace accepted by [s] ([is_trace_of]). The leaf is annotated
   with a potential hint to generate potential new messages from.
 *)
CoFixpoint intersect_trace
            (s : M (nondetE +' observerE) void)
            (t : trace) :
  M (nondetE +' eventE) (option hint) :=
  match s with
  | Tau s => Tau (intersect_trace s t)
  | Ret v => match v : void with end
  | Vis _ ( e |) k => Vis ( e |) (fun x => intersect_trace (k x) t)
  | Vis X (| e ) k =>
    match filter is_ObsFromServer t with
    | [] => ret (get_hint e)
    | _ :: _ =>
      xt <- select_event (strip_hint e) t;;
      let '(x, t) := xt in
      intersect_trace (k x) t
    end
  end.

Inductive noteE : Type -> Type :=
| Note : option hint -> noteE unit.

CoFixpoint find' (ts : list (M (nondetE +' eventE) (option hint))) :
  M noteE unit :=
  match ts with
  | [] => ret tt
  | t :: ts =>
    match t with
    | Tau t => Tau (find' (t :: ts))
    | Ret h => ^ Note h;; find' (t :: ts)
    | Vis X e k =>
      match e with
      | (| ev ) =>
        match ev in eventE X' return (X' -> X) -> _ with
        | Happened _ => fun id => Tau (find' (k (id tt) :: ts))
        end (fun x => x)
      | ( _Or |) =>
        match _Or in nondetE X' return (X' -> X) -> _ with
        | Or n _ => fun id =>
          Tau (find' (map (fun n => k (id n)) every_fin ++ ts)%list)
        end (fun x => x)
      end
    end
  end.

Inductive result := Found (hs : list hint) | NotFound | OutOfFuel.

Definition option_to_list {A} (o : option A) : list A :=
  match o with
  | None => []
  | Some a => [a]
  end.

Fixpoint take_note (fuel n_hints : nat) (m : M noteE unit) : result :=
  match fuel with
  | O => OutOfFuel
  | S fuel =>
    match m with
    | Ret tt => NotFound
    | Tau m => take_note fuel n_hints m
    | Vis X e k =>
      match e in noteE X' return (X' -> X) -> _ with
      | Note h => fun id =>
        match n_hints with
        | O => Found (option_to_list h)
        | S n_hints =>
          match take_note fuel n_hints (k (id tt)) with
          | Found hs => Found (option_to_list h ++ hs)%list
          | _ => Found (option_to_list h)
          end
        end
      end (fun x => x)
    end
  end.

Definition is_scrambled_trace_of (fuel n_hints : nat) s t : result :=
  take_note fuel n_hints (find' [intersect_trace s t]).

Example scrambled_trace_example : exists h,
  Found h = is_scrambled_trace_of 1000 0 swap_spec [
    Event ObsConnect 0;
    Event ObsConnect 1;
    Event (ObsToServer 0 tt) "a";
    Event (ObsToServer 0 tt) "b";
    Event (ObsToServer 0 tt) "c";
    Event (ObsFromServer 0) (Some "0");
    Event (ObsFromServer 0) (Some "0");
    Event (ObsFromServer 0) (Some "0");
    Event (ObsToServer 1 tt) "d";
    Event (ObsToServer 1 tt) "e";
    Event (ObsToServer 1 tt) "f";
    Event (ObsFromServer 1) (Some "a");
    Event (ObsFromServer 1) (Some "b");
    Event (ObsFromServer 1) (Some "c")
  ]%char.
Proof. eexists; reflexivity. Qed.

Example scrambled_trace_example_2 : exists h,
  Found h = is_scrambled_trace_of 1000 0 swap_spec [
    Event ObsConnect 0;
    Event ObsConnect 1;
    Event (ObsToServer 0 tt) "a";
    Event (ObsToServer 0 tt) "b";
    Event (ObsToServer 0 tt) "c";
    Event (ObsToServer 1 tt) "d";
    Event (ObsToServer 1 tt) "e";
    Event (ObsToServer 1 tt) "f";
    Event (ObsFromServer 1) (Some "a");
    Event (ObsFromServer 1) (Some "b");
    Event (ObsFromServer 1) (Some "c");
    Event (ObsFromServer 0) (Some "0");
    Event (ObsFromServer 0) (Some "0");
    Event (ObsFromServer 0) (Some "0")
  ]%char.
Proof. eexists; reflexivity. Qed.

Example scrambled_trace_example_3 : exists h,
  Found h = is_scrambled_trace_of 1000 0 swap_spec [
    Event ObsConnect 0;
    Event ObsConnect 1;
    Event (ObsToServer 0 tt) "a";
    Event (ObsToServer 0 tt) "b";
    Event (ObsToServer 0 tt) "c";
    Event (ObsToServer 1 tt) "d";
    Event (ObsToServer 1 tt) "e";
    Event (ObsToServer 1 tt) "f";
    Event (ObsFromServer 0) (Some "d");
    Event (ObsFromServer 0) (Some "e");
    Event (ObsFromServer 0) (Some "f")
  ]%char.
Proof. eexists; reflexivity. Qed.

Example bad_scrambled_trace_example :
  NotFound = is_scrambled_trace_of 1000 0 swap_spec [
    Event ObsConnect 0;
    Event ObsConnect 1;
    Event ObsConnect 2;
    Event (ObsToServer 0 tt) "a";
    Event (ObsToServer 0 tt) "b";
    Event (ObsToServer 0 tt) "c";
    Event (ObsToServer 1 tt) "d";
    Event (ObsToServer 1 tt) "e";
    Event (ObsToServer 1 tt) "f";
    Event (ObsToServer 2 tt) "g";
    Event (ObsToServer 2 tt) "h";
    Event (ObsToServer 2 tt) "i";
    Event (ObsFromServer 1) (Some "g");
    Event (ObsFromServer 1) (Some "h");
    Event (ObsFromServer 1) (Some "i");
    Event (ObsFromServer 2) (Some "d");
    Event (ObsFromServer 2) (Some "e");
    Event (ObsFromServer 2) (Some "f")
  ]%char.
Proof. reflexivity. Qed.
