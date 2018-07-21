(*! Section BaseTest *)
Generalizable Variable E.
Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.

Require Import Ascii.
Require Import String.
Require Import List.
Require Import PArith.
Require Fin.
Import ListNotations.

From Custom Require Import
     String.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Import NonDeterminismBis.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.NetworkInterface.
Require Import DeepWeb.Lib.SimpleSpec.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(** * Main specification of a "single-swap" server *)

(* SHOW *)
(* This is the main loop of the swap server.  [conns] maintains the
    list of open connections (this is used for generating test cases).
    [last_msg] holds the message received from the last client (which
    will be sent back to the next client).  The server first accepts a
    new connection, does a receive and then a send on that connection,
    and then loops back and does it again. *)
CoFixpoint swap_spec_loop
              (buffer_size : nat)
              (conns : list connection_id)
              (last_msg : bytes) 
            : itree_spec :=
  c <- obs_connect;;
  msg <- obs_msg_to_server buffer_size c;;
  obs_msg_from_server c last_msg;;
  swap_spec_loop buffer_size conns msg.

(* The server's initial state (which will be the message sent back to
    the first client). *)
Definition init_msg (buffer_size : nat) :=
  repeat_string "0"%char buffer_size.

Definition swap_spec_ buffer_size :=
  swap_spec_loop buffer_size [] (init_msg buffer_size).

(* Top-level spec *)
Definition swap_spec := swap_spec_ Util.TestDefault.buffer_size.
(* /SHOW *)
