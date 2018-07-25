(* Traces and scramblings. *)

(* We define the notion of trace and a "scrambling"
   relation between the traces produced by a server and
   those that can be observed by a client on the other side
   of the network.

   The network is defined as a state machine with transitions
   visible either by the server or by the client;
   see [Lib.SimpleSpec_NetworkModel].
 *)

Require Import Relations.
Require Import RelationClasses.

From QuickChick Require Import QuickChick.
From Custom Require Import List Show String.
Import ListNotations.
From Custom Require Map.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.SimpleSpec_NetworkModel.

Set Bullet Behavior "Strict Subproofs".

(* An event can be observed to happen on the network,
   either from the server's or the client's point of view.
   It is paremeterized by the type to represent the server's
   output... *)
Inductive event (byte' : Type) :=
| NewConnection : connection_id -> event byte'
| ToServer : connection_id -> byte -> event byte'
| FromServer : connection_id -> byte' -> event byte'
.

(* ... In the real world, this output is a concrete byte.
   (the other event type is [hypo_event], down below). *)
Definition real_event := event byte.

Arguments NewConnection {byte'}.
Arguments ToServer {byte'}.
Arguments FromServer {byte'}.

(* A trace is a sequence of events. *)
Definition trace byte' := list (event byte').
Definition real_trace := list real_event.

Definition server_transition (ev : real_event) 
                           : network_state -> network_state -> Prop :=
  fun ns ns' =>
    match ev with
    | NewConnection c => server_accept c ns = Some (ns', tt)
    | ToServer c b => server_recv c ns = Some (ns', b)
    | FromServer c b => server_send c b ns = Some (ns', tt)
    end.

Definition client_transition (ev : real_event) :
  network_state -> network_state -> Prop :=
  fun ns ns' =>
    match ev with
    | NewConnection c => client_connect c ns = Some (ns', tt)
    | ToServer c b => client_send c b ns = Some (ns', tt)
    | FromServer c b => client_recv c ns = Some (ns', b)
    end.

(* The main "scrambling" relation. *)
(* Corresponding "server-side" and "client-side" traces. *)
Inductive network_scrambled_ 
                : network_state -> real_trace -> real_trace -> Prop :=
| ScrambleEmpty : forall ns, network_scrambled_ ns [] []
| ScrambleServer : forall ns ns' e tr_server tr_client,
    server_transition e ns ns' ->
    network_scrambled_ ns'       tr_server  tr_client ->
    network_scrambled_ ns  (e :: tr_server) tr_client
| ScrambleClient : forall ns ns' e tr_server tr_client,
    client_transition e ns ns' ->
    network_scrambled_ ns' tr_server       tr_client ->
    network_scrambled_ ns  tr_server (e :: tr_client)
.

Definition network_scrambled := network_scrambled_ initial_ns.

Definition event_connection {byte'} (ev : event byte') :
  connection_id :=
  match ev with
  | NewConnection c' => c'
  | ToServer c' _ => c'
  | FromServer c' _ => c'
  end.

(* Some notations to make traces readable. *)
Module EventNotations.
Delimit Scope event_scope with event.

(* Connection [c] is open. *)
Notation "c !" := (NewConnection (Connection c))
(at level 30) : real_scope.

(* Byte [b] goes to the server on connection [c]. *)
Notation "c <-- b" := (ToServer (Connection c) b%char)
(at level 30) : real_scope.

(* Byte [b] goes out of the server on connection [c]. *)
Notation "c --> b" := (FromServer (Connection c) b%char)
(at level 30) : real_scope.

Notation "c !" := (NewConnection (Connection c) : event (option byte))
(at level 30) : hypo_scope.

(* Byte [b] goes to the server on connection [c]. *)
Notation "c <-- b" :=
  (ToServer (Connection c) b%char : event (option byte))
(at level 30) : hypo_scope.

(* Byte [b] goes out of the server on connection [c]. *)
Notation "c --> b" :=
  (FromServer (Connection c) (Some b)%char : event (option byte))
(at level 30) : hypo_scope.

(* Unknown byte goes out of the server on connection [c]. *)
Notation "c --> ?" := (FromServer (Connection c) None : event (option byte))
(at level 30) : hypo_scope.

(* Open Scope real_scope. *)

Delimit Scope hypo_scope with hypo.
Delimit Scope real_scope with real.

End EventNotations.

(* With the [network_scrambled] relation we defined here, we
   can state the correctness property we generally want to test
   and verify about server itrees, in
   [Lib.SimpleSpec_Refinement]. It is specialized to the
   swap server in [Spec.TopLevelSpec]. *)




(*************** Internals ******************)

(* Basic predicates *)

Definition is_Connect {byte' : Type} (ev : event byte') :=
  match ev with
  | NewConnection _ => true
  | _ => false
  end.

Definition is_FromServer {byte' : Type} (ev : event byte') :=
  match ev with
  | FromServer _ _ => true
  | _ => false
  end.

Definition is_ToServer {byte' : Type} (ev : event byte') :=
  match ev with
  | ToServer _ _ => true
  | _ => false
  end.

(* Traces with holes. *)

(* It will also be useful for testing to insert hypothetical
   bytes of unknown values in a trace, representing values that the
   server may have output but which have not reached the client yet. *)
Definition hypo_event := event (option byte).
Definition hypo_trace := list hypo_event.

(* We can convert real things to hypothetical things. *)

Definition real_to_hypo_event : real_event -> hypo_event :=
  fun ev =>
    match ev with
    | NewConnection c => NewConnection c
    | ToServer c b => ToServer c b
    | FromServer c b => FromServer c (Some b)
    end.

Coercion real_to_hypo_event : real_event >-> hypo_event.

Definition real_to_hypo_trace : real_trace -> hypo_trace :=
  map real_to_hypo_event.

Coercion real_to_hypo_trace : real_trace >-> hypo_trace.

(* Events and effects *)

(* We relate events to effects as follows: an event is a pair of
   an effect (of type [eff X] for some [X]) and a result (of
   type [X]). *)
Class EventType (event : Type) (eff : Type -> Type) :=
  Build_EventType {
    from_event : event -> { X : Type & (eff X * X)%type };
  }.

Definition event_eff
           {event} {eff} `{EventType event eff} (ev : event) :
  eff (projT1 (from_event ev)) :=
  fst (projT2 (from_event ev)).

Definition event_res
           {event} {eff} `{EventType event eff} (ev : event) :
  projT1 (from_event ev) :=
  snd (projT2 (from_event ev)).

(* [E +' F] is a signature of _visible_ effects [F] and _invisible_
   effects [E]. The trace (of type [list event]) is a sequence of
   visible effects [F] with their results. *)
Inductive is_trace
          {event : Type} {E F : Type -> Type} {R : Type}
          `{EventType event F} :
  M (E +' F) R -> list event -> Prop :=
| ServerEmpty : forall s, is_trace s []
| ServerVis : forall ev k tr,
    is_trace (k (event_res ev)) tr ->
    is_trace (Vis (| event_eff ev) k) (ev :: tr)
| ServerInvis : forall X e k (x : X) tr,
    is_trace (k x) tr ->
    is_trace (Vis (e |) k) tr
.


(* Show instances *)

Definition show_real_event (ev : real_event) :=
  match ev with
  | NewConnection c => (show c ++ " !")%string
  | ToServer c b =>
    (show c ++ " <-- " ++ show b)%string
  | FromServer c b =>
    (show c ++ " --> " ++ show b)%string
  end.

Instance Show_real_event: Show real_event :=
  { show := show_real_event }.

Definition show_hypo_event (ev : hypo_event) :=
  match ev with
  | NewConnection c => (show c ++ " !")%string
  | ToServer c b =>
    (show c ++ " <-- " ++ show b)%string
  | FromServer c ob =>
    (show c ++ " --> " ++ match ob with
                          | Some b => show b
                          | None => "?"
                          end)%string
  end.

Instance Show_hypo_event: Show hypo_event :=
  { show := show_hypo_event }.
