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

(* Types and operations for defining server implementation ITrees.
   For more details, see [Lib.SimpleSpec_Server]. *)
Module Type ServerIface.

(* A server is a program with internal nondeterminism and
   external network effects. *)
Inductive serverE : Type -> Type :=

(* Accept a new connection. *)
| Accept   : serverE connection_id

(* Receive one byte from a connection. *)
| RecvByte : connection_id -> serverE byte

(* Send one byte to a connection. *)
| SendByte : connection_id -> byte -> serverE unit
.

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

(* Here are a few more useful operations written using those
   above. *)

(* Receive up to [n] bytes, nondeterministically. *)
Parameter recv : connection_id -> nat -> ServerM bytes.

(* Receive a bytestring of length (exactly) [n]. *)
Parameter recv_full : connection_id -> nat -> ServerM bytes.

(* Send all bytes in a bytestring. *)
Parameter send : connection_id -> bytes -> ServerM unit.

End ServerIface.

(** ** Observer *)

(* Module to define specifications as "observer" ITrees.
   For more details, see [Lib.SimpleSpec_Observer]. *)
Module Type ObserverIface.

(** The type of observations that can be made. *)
(* The interface of observers is similar to servers;
   the difference is that observers only consume bytes,
   while servers can produce bytes with [send]. *)
Inductive observerE : Type -> Type :=
| (* Observe the creation of a new connection *)
  ObsConnect : observerE connection_id

| (* Observe a byte going into the server on a particular
     connection *)
  ObsToServer : connection_id -> observerE byte

  (* Observe a byte going out of the server. *)
| ObsFromServer : connection_id -> observerE (option byte).

(* The [ObsFromServer] effect returns an [option].
   [None] is a "hole" in the observed trace, it represents a
   message hypothetically sent by the server and that we haven't
   yet received. These holes allow us to keep exploring an
   observer even in the presence of partial outputs from the
   server. *)


(* The observer monad we write specifications in. *)
Definition ObserverM := M (failureE +' nondetE +' observerE).

(* As usual, we provide some itree wrappers for these constructors. *)

Definition obs_connect :
  ObserverM connection_id := embed ObsConnect.
Definition obs_to_server :
  connection_id -> ObserverM byte := embed ObsToServer.
Definition obs_from_server :
  connection_id -> ObserverM (option byte) := embed ObsFromServer.

(* Also some derived operations. *)

(* Make an assertion on a value, if it exists. *)
(* BCP: Think about how to explain this *)
Parameter assert_on :
  forall {A}, string -> option A -> (A -> bool) -> ObserverM unit.

(* Observe a message of fixed-length sent to the server. *)
Parameter obs_msg_to_server : nat -> connection_id -> ObserverM bytes.

(* Observe a message of fixed length received from the server
   and match it with an expected value, failing if they are not
   equal. *)
Parameter obs_msg_from_server : connection_id -> bytes -> ObserverM unit.

(* [obs_msg_from_server] is implemented in terms of [obs_from_server]
   and [assert_on].  In particular, when [obs_from_server] returns
   [None], we assume that the hole stands for the next expected
   byte. *)

End ObserverIface.

(** ** Event traces *)

Module Type TracesIface.

(* An event can be observed to happen on the network, either from the
   server's or the client's point of view.  It is paremeterized by the
   type to represent the server's output... *)
Inductive event (byte' : Type) :=
| NewConnection : connection_id -> event byte'
| ToServer : connection_id -> byte -> event byte'
| FromServer : connection_id -> byte' -> event byte'.

(* Traces are sequences of events. *)
Definition trace byte' := list (event byte').

(* ... In the real world, this output is a concrete byte. *)
Definition real_event := event byte.
Definition real_trace := list real_event.

(* ... but it is also useful for testing to insert hypothetical bytes
   of unknown values in a trace, representing values that the server
   may have output but which have not reached the client yet. *)
Definition hypo_event := event (option byte).
Definition hypo_trace := list hypo_event.

Parameter real_to_hypo : real_trace -> hypo_trace.

(* [is_server_trace server tr] holds if [tr] is a trace of
   the [server].  *)
Parameter is_server_trace : ServerM unit -> real_trace -> Prop.

(* [is_observer_trace observer tr] holds if [tr] is a trace of
   the [observer]. *)
Parameter is_observer_trace : ObserverM unit -> hypo_trace -> Prop.

(* Corresponding "server-side" and "client-side" traces. *)
Parameter network_scrambled : real_trace -> real_trace -> Prop.

(* Property that a real trace [tr] is a scrambled trace of some
   spec trace. *)
Definition is_scrambled_trace : ObserverM unit -> real_trace -> Prop :=
  fun observer tr =>
    exists str,
      network_scrambled str tr /\
      is_observer_trace observer (real_to_hypo str).

(* A server ([server : ServerM unit]) refines a "linear spec"
   ([observer : ObserverM unit]) if, for every trace [tr] that the
   server can produce, and every trace [str] that can be observed
   from it via the network, it can be explained by a "descrambled
   trace" [dstr] in the "linear spec".
   Some examples can be found in [Spec/Swap_ExampleServers.v].
 *)
Parameter refines_mod_network :
  ObserverM unit -> ServerM unit -> Prop.

(* Tests *)

(* See [Lib.Util.result] for the definition of the test result
   types below. *)

(* A test for [is_observer_trace]. *)
(* TODO: reuse comment above the definition of this thing? *)
Parameter is_observer_trace_test :
  nat -> ObserverM unit -> hypo_trace -> simple_result.

(* Test result of descrambling: if a descrambling is found,
   it gets returned. *)
Definition descrambled_result := result hypo_trace unit.

(* A test for [is_scrambled_trace]. *)
Parameter is_scrambled_trace_test :
  nat -> ObserverM unit -> real_trace -> descrambled_result.

(* A test for [refines_mod_network].
   Check that every trace of the server can be descrambled into
   a trace of the spec. *)
Parameter refines_mod_network_test :
  ObserverM unit -> ServerM unit -> Checker.

End TracesIface.
