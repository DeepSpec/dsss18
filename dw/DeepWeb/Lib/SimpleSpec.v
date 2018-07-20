From QuickChick Require Import QuickChick.
From Custom Require Import String.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import NonDeterminismBis.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Export
     Lib.SimpleSpec_NetworkInterface
     Lib.SimpleSpec_Observer
     Lib.SimpleSpec_Descramble
     Lib.SimpleSpec_ServerTrace.

(* SimpleSpec Interface. *)

(* Module to define servers. *)
Module Type NetworkIface.

(* A server is a program with internal nondeterminism and
   external network effects. *)
Parameter serverE : Type -> Type.

(* Accept a new connection. *)
Parameter accept : M serverE connection_id.

(* Receive one byte from a connection. *)
Parameter recv_byte : connection_id -> connection_id -> M serverE byte.

(* Send one byte to a connection. *)
Parameter send_byte : connection_id -> byte -> M serverE unit.

(* Receive up to [n] bytes, nondeterministically. *)
Parameter recv : connection_id -> nat -> M serverE bytes.

(* Receive a bytestring of length [n] exactly. *)
Parameter recv_full : connection_id -> nat -> M serverE bytes.

(* Send all bytes in a bytestring. *)
Parameter send : connection_id -> bytes -> M serverE unit.

(* TODO: null terminated strings? *)

End NetworkIface.

(* Module to define specifications as observers. *)
Module Type ObserverIface.

Parameter specE : Type -> Type.

(* Observe a new connection. *)
Parameter obs_connect : M specE connection_id.

(* Observe a byte sent to the server. *)
Parameter obs_to_server : connection_id -> M specE byte.

(* Observe a byte sent from the server. A [None] result is a
   "hypothetical" byte of unknown value (a hole in the observed
   trace). *)
Parameter obs_from_server : connection_id -> M specE (option byte).

(* Make an assertion on a value, if it exists. *)
Parameter assert_on :
  forall {A}, string -> option A -> (A -> bool) -> M specE unit.

(* Observe a fixed-length message sent to the server. *)
Parameter obs_msg_to_server : nat -> connection_id -> M specE bytes.

(* Observe a complete message received from the server. *)
Parameter obs_msg_from_server :
  connection_id -> bytes -> M specE unit.

End ObserverIface.

(* Module to connect servers and observers. *)
Module Type TraceCheck.
Parameter check_trace_incl_def :
  M specE unit -> M serverE unit -> Checker.
End TraceCheck.

Module Observer : ObserverIface.
Import Lib.SimpleSpec_Observer.
Definition specE := specE.
Definition obs_connect := @obs_connect specE _.
Definition obs_to_server := @obs_to_server specE _.
Definition obs_from_server := @obs_from_server specE _.
Definition assert_on := @assert_on.
Definition obs_msg_to_server := @obs_msg_to_server.
Definition obs_msg_from_server := @obs_msg_from_server.
End Observer.
