Generalizable Variable E.
Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.

Require Import Ascii String List PArith.
Require Fin.
Import ListNotations.

From Custom Require Import String.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.

Require Import DeepWeb.Lib.Util DeepWeb.Lib.SimpleSpec.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(** * Main specification of a swap server *)

(** This is the main loop of the swap server.  The parameter [conns]
     maintains the list of open connections, while [last_msg] holds the message
     received from the last client (which will be sent back to the next
     client).  The server repeatedly chooses between accepting a new
     connection or doing a receive and then a send on some existing
     connection picked in the list [conns]. *)

CoFixpoint swap_observer_loop (buffer_size : nat)
                          (conns : list connection_id)
                          (last_msg : bytes) 
                        : ObserverM unit :=
  disj
    ( (* Accept a new connection. *)
      c <- obs_connect;;
      swap_observer_loop buffer_size (c :: conns) last_msg
    | (* Exchange a pair of messages on a connection. *)
      c <- choose conns;;
      msg <- obs_msg_to_server buffer_size c;;
      obs_msg_from_server c last_msg;;
      swap_observer_loop buffer_size conns msg
    )%nondet.

(* Top-level spec *)
Definition swap_observer_ (buffer_size : nat)
                      (init_msg : bytes) 
                    : ObserverM unit :=
  swap_observer_loop buffer_size [] init_msg.

Module Def := Lib.Util.TestDefault.

(* A variant for testing *)
Definition swap_observer_def : ObserverM unit :=
  swap_observer_ Def.buffer_size Def.init_message.
