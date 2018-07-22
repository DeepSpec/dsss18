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
Require Import DeepWeb.Lib.SimpleSpec.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(* [conns]: open connections
   [last_msg]: last message received.
 *)
CoFixpoint swap_spec_loop
           (buffer_size : nat)
           (conns : list connection_id)
           (last_msg : bytes) :
  itree_spec :=
  disj "swap_spec"
    ( (* Accept a new connection. *)
      c <- obs_connect;;
      swap_spec_loop buffer_size (c :: conns) last_msg
    | (* Exchange one pair of messages on a connection. *)
      c <- choose "do swap" conns;;
      msg <- obs_msg_to_server buffer_size c;;
      obs_msg_from_server c last_msg;;
      swap_spec_loop buffer_size conns msg
    ).

Definition swap_spec_
           (buffer_size : nat)
           (init_msg : bytes) : itree_spec :=
  swap_spec_loop buffer_size [] init_msg.

Module Def := Lib.Util.TestDefault.

Definition swap_spec_def : itree_spec :=
  swap_spec_ Def.buffer_size
             Def.init_message.
