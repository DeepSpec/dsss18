From QuickChick Require Import QuickChick.
From Custom Require Import String Monad.
Import MonadNotations.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import NonDeterminismBis SumNotations.

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

(** ** Network *)

(* Types and operations for defining server ITrees.  For more details,
   see [Lib.SimpleSpec_Server]. *)
Module Type ServerIface.

(* A server is a program with internal nondeterminism and
   external network effects. *)
Parameter serverE : Type -> Type.

(* Internal nondeterminism is implemented via [nondetE]. *)
Declare Instance nondet_server : nondetE -< serverE.

(* Accept a new connection. *)
Parameter accept : M serverE connection_id.

(* Receive one byte from a connection. *)
Parameter recv_byte : connection_id -> M serverE byte.

(* Send one byte to a connection. *)
Parameter send_byte : connection_id -> byte -> M serverE unit.

(* Receive up to [n] bytes, nondeterministically. *)
Parameter recv : connection_id -> nat -> M serverE bytes.

(* Receive a bytestring of length (exactly) [n]. *)
Parameter recv_full : connection_id -> nat -> M serverE bytes.

(* Send all bytes in a bytestring. *)
Parameter send : connection_id -> bytes -> M serverE unit.

End ServerIface.

(** ** Observer *)

(* Module to define specifications as "observers".
   For more details, see [Lib.SimpleSpec_Observer]. *)
Module Type ObserverIface.

(* The interface of observer is similar to servers;
   the difference is that observers only consume bytes,
   while servers can produce bytes with [send]. *)
Parameter specE : Type -> Type.

(* Internal nondeterminism is implemented via [nondetE]. *)
Declare Instance nondet_spec : nondetE -< specE.

(* Observe a new connection. *)
Parameter obs_connect : M specE connection_id.

(* Observe a byte sent to the server. *)
Parameter obs_to_server : connection_id -> M specE byte.

(* Observe a byte sent from the server. A [None] result is a
   "hypothetical" byte of unknown value (a hole in the observed
   trace). *)
(* BCP: We'll need some examples showing how the option is handled *)
Parameter obs_from_server : connection_id -> M specE (option byte).

(* Make an assertion on a value, if it exists. *)
Parameter assert_on :
  forall {A}, string -> option A -> (A -> bool) -> M specE unit.

(* Observe a message of fixed-length sent to the server. *)
Parameter obs_msg_to_server : nat -> connection_id -> M specE bytes.

(* Observe a message of fixed length received from the server
   and match it with an expected value, failing if they are not
   equal. *)
Parameter obs_msg_from_server : connection_id -> bytes -> M specE unit.

End ObserverIface.

(** ** Event traces *)

Module Type TracesIface.

(* An event can be observed to happen on the network,
   either from the server's or the client's point of view.
   It is paremeterized by the type to represent the server's
   output... *)
Inductive event (byte' : Type) :=
| NewConnection : connection_id -> event byte'
| ToServer : connection_id -> byte -> event byte'
| FromServer : connection_id -> byte' -> event byte'.

(* ... In the real world, this output is a concrete byte. *)
Definition real_event := event byte.

(* ... but it will also be useful for testing to insert hypothetical
   bytes of unknown values in a trace, representing values that the
   server may have output but which have not reached the client yet. *)
Definition hypo_event := event (option byte).

Definition real_trace := list real_event.
Definition hypo_trace := list hypo_event.

Parameter real_to_hypo : real_trace -> hypo_trace.

Parameter is_server_trace : itree_server -> real_trace -> Prop.
Parameter is_spec_trace : itree_spec -> hypo_trace -> Prop.

(* Corresponding "server-side" and "client-side" traces. *)
Parameter network_scrambled0 : real_trace -> real_trace -> Prop.

(* Property that a real trace [tr] is a scrambled trace of some
   spec trace. *)
Definition is_scrambled_trace : itree_spec -> real_trace -> Prop :=
  fun spec tr =>
    exists str,
      network_scrambled0 str tr /\
      is_spec_trace spec (real_to_hypo str).

(* Tests *)

(* A test for [is_spec_trace]. *)
Parameter is_spec_trace_test :
  nat -> itree_spec -> hypo_trace -> simple_result.

(* Test result of descrambling: if a descrambling is found,
   it gets returned. *)
Definition descrambled_result := result hypo_trace unit.

(* A test for [is_scrambled_trace]. *)
Parameter is_scrambled_trace_test :
  nat -> itree_spec -> real_trace -> descrambled_result.

(* Check that every trace of the server can be descrambled into
   a trace of the spec. *)
Parameter refines_mod_network_test :
  M specE unit -> M serverE unit -> Checker.

End TracesIface.

(** * Implementations *)

Module Observer <: ObserverIface.
Import Lib.SimpleSpec_Observer.
Definition specE := specE.
Instance nondet_spec : nondetE -< specE.
Proof. typeclasses eauto. Defined.
Definition obs_connect := @obs_connect specE _.
Definition obs_to_server := @obs_to_server specE _.
Definition obs_from_server := @obs_from_server specE _.
Definition assert_on A := @assert_on specE A _.
Definition obs_msg_to_server := @obs_msg_to_server specE _.
Definition obs_msg_from_server := @obs_msg_from_server specE _ _.
End Observer.

Module Network : ServerIface.
Definition serverE := Network.serverE.
Instance networkE_server : networkE -< serverE.
Proof. typeclasses eauto. Defined.
Instance nondet_server : nondetE -< serverE.
Proof. typeclasses eauto. Defined.
Definition accept := @Network.accept _ _.
Definition recv_byte := @Network.recv_byte _ _.
Definition send_byte := @Network.send_byte _ _.
Definition recv := @Network.recv _ _ _.
Definition recv_full := @Network.recv_full _ networkE_server.
Definition send := @Network.send _ networkE_server.
End Network.

Module Traces : TracesIface.

  Include SimpleSpec_Traces.
  
  Definition real_to_hypo := real_to_hypo_trace.
  Definition is_server_trace := Network.is_server_trace.
  Definition is_spec_trace := SimpleSpec_Observer.is_spec_trace.

  (* TODO: reuse comment above the definition of this thing? *)
  Definition is_spec_trace_test := SimpleSpec_Observer.is_spec_trace_test.
  
  (* Property that a real trace [tr] is a scrambled trace of some
   spec trace. *)
  Definition is_scrambled_trace : itree_spec -> real_trace -> Prop :=
    fun spec tr =>
      exists str,
        network_scrambled0 str tr /\
        is_spec_trace spec (real_to_hypo str).

  Definition descrambled_result := result hypo_trace unit.

  (* Parameter is_spec_trace_of : nat -> itree_spec -> hypo_trace -> result. *)

  Definition is_scrambled_trace_test :=
    SimpleSpec_Descramble.is_scrambled_trace_of.

  Definition refines_mod_network_test
    := SimpleSpec_ServerTrace.refines_mod_network_test.
  
End Traces.

  
