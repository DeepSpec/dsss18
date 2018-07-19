Generalizable Variable E.

From DeepWeb.Free.Monad
     Require Import Free Common Verif.

From QuickChick Require Import Decidability.

From Custom Require Import List.
Import ListNotations.

Require Import DeepWeb.Spec.ServerDefs.
Require Import DeepWeb.Lib.Socket.
Require Import DeepWeb.Lib.TestDefaults.
Require Import DeepWeb.Util.ByteType.

Require Import String.

Import SocketAPI.

From Custom Require Monad.
Import MonadNotations.

CoFixpoint server_
           (endpoint : endpoint_id)
           (buffer_size : nat)
           (last_msg : bytes) : M _ unit :=
  c <- accept endpoint;;
  msg <- recv_full c buffer_size;;
  send c last_msg;;
  server_ endpoint buffer_size msg.

Definition server :=
  server_
    default_endpoint
    default_buffer_size
    default_init_message.
