(* Our specifications are itrees whose effects allow them to
   _observe_ events and make assertions to define what makes a
   valid interaction.
 *)

Generalizable Variable E.
Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.

Require Import List.
Require Import PArith.
Require Fin.
Import ListNotations.

From Custom Require Import Show String.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Import NonDeterminismBis.

Require Import DeepWeb.Lib.Util.

Require Import DeepWeb.Lib.SimpleSpec_Traces.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(** The type of observations that can be made by the spec. *)
(* The observations are parameterized by a type of "hints" that
   can be used to help generating test cases. *)
(* TODO: decide whether to restore hints. *)
(* SHOW *)
Inductive observerE : Type -> Type :=
| (* Observe the creation of a new connection *)
  ObsConnect : observerE connection_id

| (* Observe a byte going into the server on a particular
     connection *)
  ObsToServer : connection_id -> observerE byte

  (* Observe a byte going out of the server.  This action can return
     [None], indicating a "hole" as a way to hypothesize that the
     server sent some message we haven't yet received, so we can keep
     testing the rest of the trace.  (The spec writer must be careful
     that, if a trace with holes is rejected, then it must also be for
     any substitution of actual values for those holes.) *)
| ObsFromServer : connection_id -> observerE (option byte).

Definition obs_connect {E} `{observerE -< E} : M E connection_id :=
  embed ObsConnect.

Definition obs_to_server {E} `{observerE -< E} :
  connection_id -> M E byte :=
  embed ObsToServer.

Definition obs_from_server {E} `{observerE -< E} :
  connection_id -> M E (option byte) :=
  embed ObsFromServer.
(* /SHOW *)

(* Make an assertion on a value, if it exists. *)
Definition assert_on {E A} `{nondetE -< E}
           (r : string) (oa : option A) (check : A -> bool) :
  M E unit :=
  match oa with
  | None => ret tt
  | Some a =>
    if check a then ret tt else fail ("assertion failed: " ++ r)
  end.

(* Observe a message of length [n] sent to the server. *)
Fixpoint obs_msg_to_server `{observerE -< E}
         (n : nat) (c : connection_id) : M E bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- obs_to_server c;;
    bs <- obs_msg_to_server n c;;
    ret (b ::: bs)%string
  end.

(* Observe a message of length [n] received from the server. *)
Fixpoint obs_msg_from_server `{observerE -< E} `{nondetE -< E}
           (c : connection_id) (msg : bytes) :
  M E unit :=
  match msg with
  | "" => ret tt
  | String b0 msg =>
    ob <- obs_from_server c;;
    assert_on "bytes must match" ob (fun b1 => b1 = b0 ?);;
    obs_msg_from_server c msg
  end.

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

(* The spec can be viewed as a set of traces. *)

(* An [event] is an observer action together with its result. *)

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
           (e : nondetE X) (k : X -> simple_result) : simple_result :=
  match e in nondetE X' return (X' -> X) -> _ with
  | Or n _ =>
    (fix go n0 : (Fin.t n0 -> X) -> simple_result :=
       match n0 with
       | O => fun _ => FAIL tt
       | S n0 => fun f =>
                  match k (f Fin.F1) with
                  | OK tt => OK tt
                  | DONTKNOW
                  | FAIL tt => go n0 (fun m => f (Fin.FS m))
                  end
       end) n
  end%bool (fun x => x).

Definition event_to_observerE (e : hypo_event) :
  { X : Type & (observerE X * X)%type } :=
  match e with
  | NewConnection c => existT _ _ (ObsConnect, c)
  | ToServer c b => existT _ _ (ObsToServer c, b)
  | FromServer c ob => existT _ _ (ObsFromServer c, ob)
  end.

Instance EventType_observerE : EventType hypo_event observerE := {|
    from_event := event_to_observerE;
  |}.

Definition is_spec_trace : itree_spec -> hypo_trace -> Prop :=
  is_trace.

(* SHOW *)
(* Basically, a trace [t] belongs to a tree if there is a path
   through the tree (a list of [E0] effects) such that its
   restriction to [observerE] events is [t].
   Because trees are coinductive (in particular, they can contain
   arbitrary sequences of [Tau] or [Vis] with invisible effects),
   it is not possible to decide whether a trace matches the tree.
   Thus we add a [fuel] parameter assumed to be "big enough"
   for the result to be reliable. *)

Fixpoint is_spec_trace_test
         (max_depth : nat) (s : itree_spec) (t : hypo_trace) : simple_result :=
  match max_depth with
  | O => DONTKNOW
  | S max_depth =>
    match s, t with
    | Tau s, t => is_spec_trace_test max_depth s t
    | Ret tt, [] => OK tt
    | Ret tt, _ :: _ => FAIL tt
    | Vis _ (| e1 ) k, x :: t =>
      match event_to_observerE x with
      | existT T1 (e0, y) => 
        match_obs e0 e1 (fun s => is_spec_trace_test max_depth s t)
                  (FAIL tt) y k
      end
    | Vis _ (| e1 ) k, [] => OK tt
    (* The trace belongs to the tree [s] *)
    | Vis _ ( _Or |) k, t =>
      nondet_exists _Or (fun b => is_spec_trace_test max_depth (k b) t)
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
     produces the same traces as the spec above. *)

(* The network's behavior is defined in [Lib/SimpleSpec_Traces.v]
   and is accounted for in testing in [Lib/SimpleSpec_Descramble.v]. *)
(* /SHOW *)
