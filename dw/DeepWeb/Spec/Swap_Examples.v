(*! Section SwapExamples *)

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
Import SumNotations.

Require Import DeepWeb.Lib.Util DeepWeb.Lib.SimpleSpec.

Require Import DeepWeb.Spec.Swap_SimpleSpec.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(* BCP: This whole file needs comments. Also, if these are supposed to
   be checkable properties, shouldn't we actually check them?? *)

(* BCP: Why the unit arguments?  For extraction?? *)

(* A simple echo server that receives up to 2 bytes. *)
CoFixpoint echo (tt : unit) : ServerM unit :=
  c <- accept ;;
  msg <- recv c 2 ;;
  send c msg ;;
  echo tt.

CoFixpoint echo_spec (tt : unit) : ObserverM unit :=
  c <- obs_connect ;;
  msg <- obs_msg_to_server 2 c;;
  obs_msg_from_server c msg ;;
  echo_spec tt.

(* A test *)

Definition test_echo := refines_mod_network_test (echo_spec tt) (echo tt).

(*! QuickChick test_echo. *)

(* Now on to the swap server *)

(* A swap server that trivially follows the specification. *)
CoFixpoint swap_server_loop (buffer_size : nat)
                          (conns : list connection_id)
                          (last_msg : bytes) 
                        : ServerM unit :=
  disj
    ( (* Accept a new connection. *)
      c <- accept;;
      swap_server_loop buffer_size (c :: conns) last_msg
    | (* Exchange a pair of messages on a connection. *)
      c <- choose conns;;
      msg <- recv c buffer_size;;
      send c last_msg;;
      swap_server_loop buffer_size conns msg
    )%nondet.

Definition swap_server_def : ServerM unit :=
  swap_server_loop Def.buffer_size [] Def.init_message.

Definition test_swap := refines_mod_network_test
                          swap_observer_def swap_server_def.

(*! QuickChick test_swap. *)

(* QuickChecking test_swap +++ Passed 10000 tests (0 discards) *)

(* A server that actually does no useful work *)
CoFixpoint eager_server (tt : unit) : ServerM unit :=
  c <- accept ;;
  eager_server tt.

Definition test_eager := refines_mod_network_test
                           swap_observer_def (eager_server tt).

(*! QuickChick test_eager. *)

(* QuickChecking test_eager ++ Passed 10000 tests (0 discards) *)


(* A server that's plainly wrong. *)

CoFixpoint const_server (buffer_size : nat) : ServerM unit :=
  c <- accept ;;
  msg <- recv c buffer_size ;;
  send c "0";;
  const_server buffer_size.

Definition test_const := expectFailure
  (refines_mod_network_test
     swap_observer_def (const_server Def.buffer_size)).

(*! QuickChick test_const. *)
(* QuickChecking test_const
[1 !; 1 <-- "C"; 1 <-- "\022"; 1 <-- "\003"; 1 --> 0"; 2 !; 2 <-- "P"; 2 <-- "o"; 2 <-- "n"; 2 --> 0"]
*** Failed after 1 tests and 0 shrinks. (0 discards) *)


(* A server that only accepts up to two connections, but still correct. *)

CoFixpoint bounded_server (buffer_size : nat) (conns : list connection_id)
           (last_msg : string)
  : ServerM unit :=
  disj
       ( if (length conns <= 2)? then
           c <- accept ;; bounded_server buffer_size (c :: conns) last_msg
         else
           ret tt ;; bounded_server buffer_size conns last_msg
       | c <- choose conns;;
         msg <- recv c buffer_size ;;
         send c last_msg ;;
         bounded_server buffer_size conns msg 
       )%nondet.

Definition test_bounded_server :=
  refines_mod_network_test
    swap_observer_def (bounded_server Def.buffer_size [] Def.init_message).

(*! QuickChick test_bounded_server. *)

(* A server that works for a while and then stops. *)

CoFixpoint terminating_server (buffer_size : nat) (conns : list connection_id)
           (last_msg : string) (num_sends : nat) : ServerM unit :=
  if num_sends < 3 ? then 
    disj
         ( c <- accept;;
           terminating_server buffer_size (c :: conns) last_msg num_sends
         | c <- choose conns;;
           msg <- recv c buffer_size;;
           send c last_msg;;
           terminating_server buffer_size conns msg (num_sends + 1)
         )%nondet
  else ret tt.

Definition test_terminating_server :=
  refines_mod_network_test
    swap_observer_def
    (terminating_server Def.buffer_size [] Def.init_message 0).

(*! QuickChick test_terminating_server. *)

(* A server that behaves properly at first, then malfunctions. *)
Definition malfunctioning_server (buffer_size : nat) (conns : list connection_id)
           (last_msg : string) (num_sends : nat) : ServerM unit :=
  terminating_server buffer_size conns last_msg num_sends ;;
  const_server buffer_size.
  
Definition test_malfunctioning_server := expectFailure
  (refines_mod_network_test
    swap_observer_def
    (malfunctioning_server Def.buffer_size [] Def.init_message 0)).

(*! QuickChick test_malfunctioning_server. *)

