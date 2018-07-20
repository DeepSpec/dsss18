Generalizable Variable E.

From DeepWeb.Free.Monad
     Require Import Free Common Verif.

From QuickChick Require Import Decidability.

From Custom Require Import List.
Import ListNotations.

Require Import DeepWeb.Spec.ServerDefs.
Require Import DeepWeb.Lib.Socket.
Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.SimpleSpec_NetworkInterface.

Require Import String.

Import SocketAPI.

From Custom Require Monad.
Import MonadNotations.

CoFixpoint server_
           (buffer_size : nat)
           (last_msg : bytes) : itree_server :=
  c <- accept;;
  msg <- recv_full c buffer_size;;
  send c last_msg;;
  server_ buffer_size msg.

Module Def := Lib.Util.TestDefault.

Definition server :=
  server_
    Def.buffer_size
    Def.init_message.
