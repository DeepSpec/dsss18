Generalizable Variable E.
Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.

Require Import Ascii.
Require Import String.
Require Import List.
Require Import PArith.
Require Fin.
Import ListNotations.

From Custom Require Import Show.

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
(* TODO: decide whether to restore hints. *)
Inductive observerE : Type -> Type :=
  (* Observe the creation of a new connection *)
| ObsConnect : observerE connection_id

  (* Observe a byte going into the server on a particular
     connection *)
| ObsToServer :
    connection_id ->
    observerE byte

  (* Observe a byte going out of the server.
     This action can return [None] "holes" as a way to hypothesize
     that the server sent some message we haven't yet received,
     so we can keep testing the rest of the trace.
     We must be careful that, if a trace with holes is
     rejected, then it must also be for any substitution
     of actual values for those holes. *)
| ObsFromServer :
    connection_id -> observerE (option byte)
.

Definition obs_connect {E} `{observerE -< E} : M E connection_id :=
  embed ObsConnect.

Definition obs_to_server {E} `{observerE -< E} :
  connection_id -> M E byte :=
  embed ObsToServer.

Definition obs_from_server {E} `{observerE -< E} :
  connection_id -> M E (option byte) :=
  embed ObsFromServer.

(* Equality comparison, return a proof of equality of the
   indices (this could be generalized to a complete decision
   procedure). *)
Definition observer_eq {X Y : Type}
           (e1 : observerE X) (e2 : observerE Y) :
  option (X = Y) :=
  match e1, e2 with
  | ObsConnect, ObsConnect => Some eq_refl
  | ObsToServer c, ObsToServer c'
  | ObsFromServer c, ObsFromServer c' =>
    if c = c' ? then Some eq_refl else None
  | _, _ => None
  end.

Definition coerce {X Y : Type} (p : X = Y) (x : X) : Y :=
  match p in eq _ Y return Y with
  | eq_refl => x
  end.

Definition specE := nondetE +' observerE.

Definition itree_spec := M specE unit.

(* Make an assertion on a value, if it exists. *)
Definition assert_on {A}
           (r : string) (oa : option A) (check : A -> bool) :
  M specE unit :=
  match oa with
  | None => ret tt
  | Some a =>
    if check a then ret tt else fail ("assertion failed: " ++ r)
  end.

(* Helper for [obs_msg_to_server] *)
CoFixpoint obs_msg_to_server'
           (c : connection_id) (n : nat) (k : bytes -> M specE bytes) :
  M specE bytes :=
  match n with
  | O => k ""
  | S n =>
    b <- ^ ObsToServer c;;
    obs_msg_to_server' c n (fun bs => k (String b bs))
  end.

(* Observe a complete message sent to the server. *)
Definition obs_msg_to_server (buffer_size : nat)
           (c : connection_id) : M specE bytes :=
  obs_msg_to_server' c buffer_size ret.

(* Observe a complete message received from the server. *)
CoFixpoint obs_msg_from_server
           (c : connection_id) (msg : bytes) :
  M specE unit :=
  match msg with
  | "" => ret tt
  | String b0 msg =>
    ob <- ^ ObsFromServer c;;
    assert_on "bytes must match" ob (fun b1 => b1 = b0 ?);;
    obs_msg_from_server c msg
  end.

(* The spec can be viewed as a set of traces. *)

(* An [event] is an observer action together with its result. *)
Inductive event :=
| Event : forall X, observerE X -> X -> event.

Arguments Event {X}.

Definition show_event (ev : event) :=
  match ev with
  | Event _ e x =>
    match e in observerE X return X -> _ with
    | ObsConnect => fun c => show c ++ " !"
    | ObsToServer c => fun b =>
      show c ++ " <-- """ ++ pretty_char b ++ """"
    | ObsFromServer c => fun ob =>
      show c ++ " --> " ++
        match ob with
        | None => "?"
        | Some b => """" ++ pretty_char b ++ """"
        end
    end x
  end.

Instance Show_event : Show event :=
  { show := show_event }.

Definition trace := list event.

Definition match_obs {X Y R S : Type}
           (e0 : observerE X)
           (e1 : observerE Y)
           (cont : S -> R)
           (fail_ : R) :
  X -> (Y -> S) -> R :=
  match e0 in observerE X, e1 in observerE Y
        return X -> (Y -> _) -> _ with
  | ObsConnect, ObsConnect => fun x k => cont (k x)
  | ObsToServer c, ObsToServer c' => fun x k =>
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
Fixpoint is_trace_of (fuel : nat) (s : itree_spec) (t : trace) : bool :=
  match fuel with
  | O => false
  | S fuel =>
    match s, t with
    | Tau s, t => is_trace_of fuel s t
    | Ret tt, [] => true
    | Ret tt, _ :: _ => false
    | Vis _ (| e1 ) k, Event _ e0 x :: t =>
      match_obs e0 e1 (fun s => is_trace_of fuel s t)
                false x k
    | Vis _ (| e1 ) k, [] => true
    (* The trace belongs to the tree [s] *)
    | Vis _ ( _Or |) k, t =>
      nondet_exists _Or (fun b => is_trace_of fuel (k b) t)
    end
  end.


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

        | ObsToServer c =>
          if forallb (fun ev =>
               match ev with
               | Event _ (ObsFromServer c') _ => false
               | Event _ ObsConnect c'
               | Event _ (ObsToServer c') _ => c <> c' ?
               end) t_prev then
            pick_this
          else
            fail "inaccessible ObsToServer"

        | ObsFromServer c =>
          if forallb (fun ev =>
               match ev with
               | Event _ (ObsToServer _) _ => true
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
           (e : observerE X) (t_prev t : trace) :
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

      | ObsConnect as e, ObsToServer _
      | ObsToServer _ as e, (ObsConnect | ObsToServer _)
      | ObsFromServer _ as e, _ =>
        try_next

        (* We're looking for a [Connect/ToServer] event
           but there is still a [FromServer] event to explain. *)
      | (ObsConnect | ObsToServer _), ObsFromServer _ =>
        fail "inaccessible event"

      | ObsConnect, ObsConnect => fail "should not happen"
      end
    end
  end.

Definition select_event {X} (e : observerE X) :
  trace -> M (nondetE +' eventE) (X * trace) := select_event' e [].

(* [s]: tree of acceptable traces (spec)
   [t]: scrambled trace

   The result tree has a [Ret] leaf iff there is a descrambled
   trace accepted by [s] ([is_trace_of]).
 *)
CoFixpoint intersect_trace
            (s : M (nondetE +' observerE) unit)
            (t : trace) :
  M (nondetE +' eventE) unit :=
  match s with
  | Tau s => Tau (intersect_trace s t)
  | Ret tt =>
    match filter is_ObsFromServer t with
    | [] => ret tt
    | _ :: _ => fail "unexplained events remain"
    end
  | Vis _ ( e |) k => Vis ( e |) (fun x => intersect_trace (k x) t)
  | Vis X (| e ) k =>
    match filter is_ObsFromServer t with
    | [] => ret tt
    | _ :: _ =>
      xt <- select_event e t;;
      let '(x, t) := xt in
      intersect_trace (k x) t
    end
  end.

CoFixpoint find' (ts : list (M (nondetE +' eventE) unit)) :
  M emptyE bool :=
  match ts with
  | [] => ret false
  | t :: ts =>
    match t with
    | Tau t => Tau (find' (t :: ts))
    | Ret tt => ret true
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

Inductive result := Found | NotFound | OutOfFuel.

Definition option_to_list {A} (o : option A) : list A :=
  match o with
  | None => []
  | Some a => [a]
  end.

Fixpoint to_result (fuel : nat) (m : M emptyE bool) : result :=
  match fuel with
  | O => OutOfFuel
  | S fuel =>
    match m with
    | Ret b => if b then Found else NotFound
    | Tau m => to_result fuel m
    | Vis X e k => match e in emptyE X' with end
    end
  end.

Definition is_scrambled_trace_of
           (fuel : nat) (s : itree_spec) (t : trace) : result :=
  to_result fuel (find' [intersect_trace s t]).

Module EventNotations.

Delimit Scope event_scope with event.

(* Connection [c] is open. *)
Notation "c !" := (Event ObsConnect c)
(at level 30) : event_scope.

(* Byte [b] goes to the server on connection [c]. *)
Notation "c <-- b" := (Event (ObsToServer c) b%char)
(at level 30) : event_scope.

(* Byte [b] goes out of the server on connection [c]. *)
Notation "c --> b" := (Event (ObsFromServer c) (Some b%char))
(at level 30) : event_scope.

(* Unknown byte goes out of the server on connection [c]. *)
Notation "c --> ?" := (Event (ObsFromServer c) None)
(at level 30) : event_scope.

Open Scope event_scope.

End EventNotations.
