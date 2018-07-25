Require Import List.
Import ListNotations.

From QuickChick Require Import QuickChick.
From Custom Require Import String Monad.
Import MonadNotations.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Export
     Lib.SimpleSpec_Server
     Lib.SimpleSpec_Observer
     Lib.SimpleSpec_Descramble
     Lib.SimpleSpec_Traces
     Lib.SimpleSpec_Refinement
     Lib.SimpleSpec_ServerTrace
     Lib.SimpleSpec_NetworkModel.

(** * Interfaces *)

(** ** Server *)

(* Types and operations for defining server implementation ITrees. *)
Module Type ServerIface.

(* A server is a program with internal nondeterminism and
   external network effects. *)
Inductive serverE : Type -> Type :=
  | (* Accept a new connection. *)
    Accept   : serverE connection_id
  | (* Receive one byte from a connection. *)
    RecvByte : connection_id -> serverE byte
  | (* Send one byte to a connection. *)
    SendByte : connection_id -> byte -> serverE unit.

(* The server monad to write implementations in.
   A server is a program with internal nondeterminism and
   external network effects. *)
Definition ServerM := M (failureE +' nondetE +' serverE).

(* We wrap these constructors into [ServerM] values for convenience. *)

Definition accept :
  ServerM connection_id := embed Accept.
Definition recv_byte :
  connection_id -> ServerM byte := embed RecvByte.
Definition send_byte :
  connection_id -> byte -> ServerM unit := embed SendByte.

(* A few more useful operations, written using those above. *)

(* Receive up to [n] bytes, nondeterministically. *)
Parameter recv : connection_id -> nat -> ServerM bytes.

(* Receive a bytestring of length (exactly) [n]. *)
Parameter recv_full : connection_id -> nat -> ServerM bytes.

(* Send all bytes in a bytestring. *)
Parameter send : connection_id -> bytes -> ServerM unit.

End ServerIface.
(* Implemented in [Lib.SimpleSpec_Server]. *)

(** ** Observer *)

(* Types and operations for defining specifications as "observer"
   ITrees. *)

Module Type ObserverIface.

(* The interface of observers is similar to servers; the difference is
   that observer ITrees only _consume_ bytes (the types of their
   events return bytes as outputs, rather than taking them as inputs),
   while servers can produce bytes with [send]. In particular, the
   [ObsToServer] effect observes a particular byte being sent to the
   server (by a test trace generator, intuitively). *)

Inductive observerE : Type -> Type :=
  | (* Observe the creation of a new connection *)
    ObsConnect : observerE connection_id
  | (* Observe a byte going into the server on a particular
       connection *)
    ObsToServer : connection_id -> observerE byte
    (* Observe a byte going out of the server. *)
  | ObsFromServer : connection_id -> observerE (option byte).

(* The [ObsFromServer] effect returns an [option], where [None] is a
   "hole" in the observed trace: it represents a message
   hypothetically sent by the server and that we haven't yet
   received. These holes allow us to keep exploring an observer even
   in the presence of partial outputs from the server. *)

(* The main "observer monad" for writing specifications: *)
Definition ObserverM := M (failureE +' nondetE +' observerE).

(* ITree wrappers for the constructors: *)
Definition obs_connect :
  ObserverM connection_id := embed ObsConnect.
Definition obs_to_server :
  connection_id -> ObserverM byte := embed ObsToServer.
Definition obs_from_server :
  connection_id -> ObserverM (option byte) := embed ObsFromServer.

(* Also some derived operations. *)

(* Make an assertion on a value, if it exists.  (If the value is 
   [Some x] and the test returns false on [x], the [assert_on] 
   ITree fails. *)
Parameter assert_on :
  forall {A}, string -> option A -> (A -> bool) -> ObserverM unit.

(* Observe a message of fixed length sent to the server. *)
Parameter obs_msg_to_server : nat -> connection_id -> ObserverM bytes.

(* Observe a message of fixed length received from the server and
   match it with an expected value, failing if they are not
   equal.  (This is implemented in terms of [obs_from_server] and
   [assert_on].  In particular, when [obs_from_server] returns [None],
   we want to assume that the hole stands for the next expected byte
   and continue past it.) *)
Parameter obs_msg_from_server : connection_id -> bytes -> ObserverM unit.

End ObserverIface.
(* Implemented in [Lib.SimpleSpec_Observer]. *)

(** ** Event traces *)

Module Type TracesIface.

(* The refinement relation between ITrees is stated in terms of _event
   traces_, which are simply lists of events.

   Events are parameterized by the type to represent the server's
   output. For specification purposes, an output is a plain
   [byte] ([real_event]). But for testing it will be useful to insert
   holes by instantiating [byte' := option byte]. *)

Inductive event (byte' : Type) :=
| NewConnection : connection_id -> event byte'
| ToServer : connection_id -> byte -> event byte'
| FromServer : connection_id -> byte' -> event byte'.

(* Traces are sequences of events. *)
Definition trace byte' := list (event byte').

(* In the real world, events carry concrete bytes. *)
Definition real_event := event byte.
Definition real_trace := list real_event.

(* For testing, it is useful to insert "hypothetical bytes" of unknown
   values in a trace, representing values that the server may have
   output but which have not reached the client yet. *)
Definition hypo_event := event (option byte).
Definition hypo_trace := list hypo_event.

(* Traces with holes are a superset of real traces. *)
Parameter real_to_hypo_trace : real_trace -> hypo_trace.
Coercion real_to_hypo_trace : real_trace >-> hypo_trace.

(* [is_server_trace server tr] holds if [tr] is a trace of the [server].  *)
Parameter is_server_trace : ServerM unit -> real_trace -> Prop.

(* [is_observer_trace observer tr] holds if [tr] is a trace of
   the [observer]; [tr] may contain holes. *)
Parameter is_observer_trace : ObserverM unit -> hypo_trace -> Prop.

(* [Lib.Util.result] (from which [Lib.Util.simple_result] and
   [descrambled_result] are derived) is a type with three
   constructors representing success, failure, or "don't know",
   possibly with a (counter)example. *)

(* QuickChick test for [is_observer_trace]. *)
Parameter is_observer_trace_test :
  ObserverM unit -> hypo_trace -> simple_result.

End TracesIface.
(* This is implemented in [Lib.SimpleSpec_Traces]. *)

(** Pause here and look at examples! *)

(* *)

(** ** Network Model *)

(* The above interfaces describe servers and observers that interact
   over a network, which we model as the following state machine... *)
Module Type NetworkModelIface.

(* The network state is a map from [connection_id] to connection
   states. *)

Section ConnectionState.

(* First, we define the type of a single connection
   state ([connection_state]).  Essentially, a connection can be seen
   as a pair of buffers that servers and clients push bytes to
   asynchronously.
      - Connections start in the [CLOSED] state.
      - When a client initiates a connection, the connection enters
        the [PENDING] state, and the client can immediately start
        sending messages over it.
      - The server must then accept the connection, which enters the
        [ACCEPTED] state, before receiving and sending messages over
        it. The client can now also receive messages. *)

Inductive connection_state_enum := CLOSED | PENDING | ACCEPTED.

Record connection_state :=
  Build_connection_state {

    (* The state of the connection (see above). *)
    connection_status : connection_state_enum;

    (* The buffer of bytes going into the server. *)
    connection_inbytes : list byte;

    (* The buffer of bytes going out from the server. *)
    connection_outbytes : list byte;
  }.

Definition initial_cs : connection_state := {|
    connection_status := CLOSED;
    connection_inbytes := [];
    connection_outbytes := [];
  |}.

End ConnectionState.

(* We can now define the complete state of the network
   as a map from [connection_id] to [connection_state]. *)
Definition network_state := Map.t connection_id connection_state.

(* Initial state: all connections are closed. *)
Definition initial_ns : network_state := fun _ => initial_cs.

(* State transitions.
   - The result is [None] when a transition is not defined.
   - Transitions may carry some output (in this case, a byte
     for [recv] transitions. *)
Definition transition (output : Type) : Type :=
  network_state -> option (network_state * output).

(* Each of the following possible transitions succeeds (returning a
   result and a next state) if the given transition is possible from
   the current network state. *)

(* Server-side transitions *)
Parameter server_accept : connection_id -> transition unit.
Parameter server_send : connection_id -> byte -> transition unit.
Parameter server_recv : connection_id -> transition byte.

(* Client-side transitions *)
Parameter client_connect : connection_id -> transition unit.
Parameter client_send : connection_id -> byte -> transition unit.
Parameter client_recv : connection_id -> transition byte.

End NetworkModelIface.
(* Implemented in [Lib.SimpleSpec_NetworkModel]. *)

Module Type DescramblingIface
       (Traces : TracesIface) (NetworkModel : NetworkModelIface).
Import Traces.
Import NetworkModel.

(* These events label transitions in the network state machine
   defined above in [NetworkModelIface]. *)

(* Server-side interpretation of an event. *)
Definition server_transition (ev : real_event)
                           : network_state -> network_state -> Prop :=
  fun ns ns' =>
    match ev with
    | NewConnection c => server_accept c ns = Some (ns', tt)
    | ToServer c b => server_recv c ns = Some (ns', b)
    | FromServer c b => server_send c b ns = Some (ns', tt)
    end.

(* Client-side interpretation of an event. *)
Definition client_transition (ev : real_event) :
  network_state -> network_state -> Prop :=
  fun ns ns' =>
    match ev with
    | NewConnection c => client_connect c ns = Some (ns', tt)
    | ToServer c b => client_send c b ns = Some (ns', tt)
    | FromServer c b => client_recv c ns = Some (ns', b)
    end.

(* The main "scrambling" relation. *)
(* [network_scrambled_ ns tr str] holds when, starting from
   the network state [ns], there is an execution of the
   network with server-side trace [tr_server] and client-side
   trace [tr_client].

   We say that [tr_client] is a scrambling of [tr_server],
   or that [tr_server] is a descrambling of [tr_client]. *)
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
    network_scrambled_ ns  tr_server (e :: tr_client).

(* At the top level, we consider traces starting from the initial state. *)
Definition network_scrambled := network_scrambled_ initial_ns.

(* A trace [str] is "consistent" with an [observer] if it can be
   descrambled to an [observer] trace. We say that [str] is a
   "scrambled trace" of [observer]. *)
Definition is_scrambled_trace : ObserverM unit -> real_trace -> Prop :=
  fun observer tr =>
    exists str,
      network_scrambled str tr /\
      is_observer_trace observer str.

(* The main property defining our notion of "correctness". *)

(* Refinement relation "modulo network scrambling".

   A server ([server : ServerM unit]) refines a "linear spec"
   (an [observer : ObserverM unit]) if, for every trace [tr] that the
   server can produce, and every scrambling [str] of [tr]
   (representing what we observe of [tr] from the other side of
   the network), [str] is a scrambled trace of the [observer].
   Some examples can be found in [Spec.Descramble_Examples]. *)
Definition refines_mod_network observer server : Prop :=
  forall tr : real_trace,
    is_server_trace server tr ->
    forall str : real_trace,
      network_scrambled tr str ->
      exists dstr : real_trace,
        network_scrambled dstr str /\
        is_observer_trace observer dstr.

(* Tests *)

(* Test result of descrambling: success is witnessed by a
   descrambled [hypo_trace]. *)
Definition descrambled_result := result hypo_trace unit.

(* A test for [is_scrambled_trace], which tries to
   descramble the given trace to a trace of the observer. *)
Parameter is_scrambled_trace_test :
  ObserverM unit -> real_trace -> descrambled_result.

(* QuickChick test for [refines_mod_network].  Checks that every trace
   of the server can be descrambled into a trace of the observer. *)
Parameter refines_mod_network_test :
  ObserverM unit -> ServerM unit -> Checker.

End DescramblingIface.
(* The implementation of this interface is split in a couple of modules.
   The most important parts:
   - the definition of descrambling is in [Lib.SimpleSpec_Traces];
   - the general property [refines_mod_network] is defined in
     [Lib.SimpleSpec_Refinement];
   - the descrambling function for a single trace,
     [is_scrambled_trace_test] is in [Lib.SimpleSpec_Descramble];
   - the test function for refinement, [refines_mod_network_test]
     is in [Lib.SimpleSpec_ServerTrace]. *)
