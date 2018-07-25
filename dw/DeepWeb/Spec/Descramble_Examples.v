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

Import EventNotations.

(* Instantiate a server with default values [buffer_size] and
   [init_message]. *)
Definition def (f : nat -> bytes -> ServerM unit) : ServerM unit :=
  f Def.buffer_size Def.init_message.

(** * Example scrambled traces *)

(* "Scrambled traces" describe what the clients _across the network_
   can observe, given that the server is behaving according to the
   given sequential specification.

   The [is_scrambled_trace_test] function checks whether a given
   "observed trace" is a scrambled version of a trace belonging
   to a given specification.  If so, it returns that "descrambled
   trace" that explains the observed trace. *)

(* Every actual trace of the server is also a scrambled trace: *)
Example scrambled_trace_example_1 :
  is_scrambled_trace_test swap_observer_def [
    0 !;
    1 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "0";
    0 --> "0";
    0 --> "0";
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    1 --> "a";
    1 --> "b";
    1 --> "c"
  ]%real = OK [
    0 !;
    1 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c"; 
    0 --> "0";
    0 --> "0";
    0 --> "0";
    1 <-- "d"; 
    1 <-- "e";
    1 <-- "f";
    1 --> "a";
    1 --> "b"; 
    1 --> "c"
  ]%hypo.
Proof. cbn. reflexivity. Qed.

(* The "scrambling" of messages in the network can result in responses
   on different connections being received out of order.  The
   resulting "explanation" shows the order that they must have been
   sent by the server. *)
Example scrambled_trace_example_2 :
  is_scrambled_trace_test swap_observer_def [
    0 !;
    1 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    1 --> "a";
    1 --> "b";
    1 --> "c";
    0 --> "0";
    0 --> "0";
    0 --> "0"
  ]%real = OK [
    0 !;
    1 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "0";
    0 --> "0";
    0 --> "0";
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    1 --> "a";
    1 --> "b";
    1 --> "c"]%hypo.
Proof. reflexivity. Qed.

(* A bad trace, where the server sends back a response that was never
   sent to it by any client: *)
Example bad_scrambled_trace_example_1 :
  is_scrambled_trace_test swap_observer_def [
    0 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "X"
  ]%real = FAIL tt.
Proof. reflexivity. Qed.

(* A more interesting bad trace, where the server appears to send the
   requests from connection 1 as responses along connection 2 _and
   vice versa_. *)
Example bad_scrambled_trace_example_2 :
  is_scrambled_trace_test swap_observer_def [
    0 !;
    1 !;
    2 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    2 <-- "g";
    2 <-- "h";
    2 <-- "i";
    1 --> "g";
    1 --> "h";
    1 --> "i";
    2 --> "d";
    2 --> "e";
    2 --> "f"
  ]%real = FAIL tt.
Proof. reflexivity. Qed.

(* Finally, an example of a trace that might be observed if the
   responses on connection 1 are delayed by the network.  The
   explanation of this observation includes three "hypothetical
   events" on connection 1, marking places where a client is still
   expecting messages from the server. *)
Example scrambled_trace_example_3 :
  is_scrambled_trace_test swap_observer_def [
    0 !;
    1 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    0 --> "d";
    0 --> "e";
    0 --> "f"
  ]%real = OK [
    0 !;
    1 !;
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    1 --> ?;
    1 --> ?;
    1 --> ?;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "d";
    0 --> "e";
    0 --> "f"]%hypo.
Proof. reflexivity. Qed.

(* The reason for including these "hypothetical events" in
   explanations is that it enables us to reject observations like
   this, where three "missing" events are followed by one that is
   clearly impossible: *)
Example bad_scrambled_trace_example_3 :
  is_scrambled_trace_test swap_observer_def [
    0 !;
    1 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    0 --> "0";
    1 --> "X"
  ]%real = FAIL tt.
Proof. reflexivity. Qed.

(** * Refinement-modulo-descrambling examples *)

(** ** Straightforward swap server *)

(* A swap server that trivially follows the specification. *)

CoFixpoint swap_server_loop
           (conns : list connection_id)
           (buffer_size : nat)
           (last_msg : bytes)
         : ServerM unit :=
  disj
    ( (* Accept a new connection. *)
      c <- accept;;
      swap_server_loop (c :: conns) buffer_size last_msg
    | (* Exchange a pair of messages on a connection. *)
      c <- choose conns;;
      msg <- recv c buffer_size;;
      send c last_msg;;
      swap_server_loop conns buffer_size msg
    )%nondet.

Definition test_swap := refines_mod_network_test
                          swap_observer_def
                          (def (swap_server_loop [])).

(*! QuickChick test_swap. *)
(* ===>
     Checking Descramble_Examples.test_swap...
     +++ Passed 100 tests (0 discards) *)

(** ** Trivial server *)

(* A silly server that does no useful work at all (it accepts
   connections but never sends or receives on them) *)
CoFixpoint eager_server (tt : unit) : ServerM unit :=
  c <- accept ;;
  eager_server tt.

Definition test_eager := refines_mod_network_test
                           swap_observer_def
                           (eager_server tt).

(*! QuickChick test_eager. *)
(* ===>
     Checking Descramble_Examples.test_eager...
     +++ Passed 100 tests (0 discards) *)

(** ** Bad server *)

(* A server that's plainly wrong. *)

CoFixpoint const_server (buffer_size : nat) : ServerM unit :=
  c <- accept ;;
  msg <- recv c buffer_size ;;
  send c "0";;
  const_server buffer_size.

Definition test_const :=
  expectFailure
    (refines_mod_network_test
       swap_observer_def
       (const_server Def.buffer_size)).

(*! QuickChick test_const. *)
(* ===>
     Checking Descramble_Examples.test_const...
[[
     [1 !; 1 <-- "C"; 1 <-- "\022"; 1 <-- "\003"; 1 --> "0"; 
      2 !; 2 <-- "P"; 2 <-- "o"; 2 <-- "n"; 2 --> "0"]
]]
     *** Failed after 1 tests and 0 shrinks. (0 discards) *)

(** ** Bounded server *)

(* A (correct) server that only accepts up to two connections *)

CoFixpoint bounded_server (conns : list connection_id)
                          (buffer_size : nat)
                          (last_msg : string)
                        : ServerM unit :=
  disj
     ( if (length conns <= 2)? then
         c <- accept ;; bounded_server (c :: conns) buffer_size last_msg
       else
         ret tt ;; bounded_server conns buffer_size last_msg
     | c <- choose conns;;
       msg <- recv c buffer_size ;;
       send c last_msg ;;
       bounded_server conns buffer_size msg
     )%nondet.

Definition test_bounded_server :=
  refines_mod_network_test
    swap_observer_def
    (def (bounded_server [])).

(*! QuickChick test_bounded_server. *)

(* ===>
     Checking Descramble_Examples.test_bounded_server...
     +++ Passed 100 tests (0 discards) *)

(** ** Terminating server *)

(* A server that works for a while and then stops. *)

CoFixpoint terminating_server (conns : list connection_id)
                              (num_sends : nat)
                              (buffer_size : nat)
                              (last_msg : string)
                            : ServerM unit :=
  if num_sends < 3 ? then 
    disj
      ( c <- accept;;
        terminating_server (c :: conns) num_sends buffer_size last_msg
      | c <- choose conns;;
        msg <- recv c buffer_size;;
        send c last_msg;;
        terminating_server conns (num_sends + 1) buffer_size msg
      )%nondet
  else ret tt.

Definition test_terminating_server :=
  refines_mod_network_test
    swap_observer_def
    (def (terminating_server [] 0)).

(*! QuickChick test_terminating_server. *)

(** ** Eventually bad server *)

(* A server that behaves properly at first, then malfunctions. *)
Definition malfunctioning_server (conns : list connection_id)
                                 (num_sends : nat)
                                 (buffer_size : nat)
                                 (last_msg : string)
                               : ServerM unit :=
  terminating_server conns num_sends buffer_size last_msg ;;
  const_server buffer_size.
  
Definition test_malfunctioning_server :=
  expectFailure
    (refines_mod_network_test
      swap_observer_def
      (def (malfunctioning_server [] 0))).

(*! QuickChick test_malfunctioning_server. *)
(* ===>
     Checking Descramble_Examples.test_malfunctioning_server...
[[
     [1 !;
      1 <-- "i"; 1 <-- "Z"; 1 <-- "|";
      1 --> "0"; 1 --> "0"; 1 --> "0";
      2 !; 3 !; 4 !;
      2 <-- "\001"; 2 <-- "="; 2 <-- "`";
      2 --> "i"; 2 --> "Z"; 2 --> "|";
      4 <-- "]"; 4 <-- "l"; 4 <-- "}";
      4 --> "\001"; 4 --> "="; 4 --> "`";
      5 !;
      5 <-- "J"; 5 <-- "_"; 5 <-- "z";
      5 --> "0"]
]]
     +++ Failed (as expected) after 1 tests and 0 shrinks. (0 discards) *)

(** ** Echo server *)

(* Finally, just to show that we can specify things besides swap
   servers (;-), here is a simple echo server that repeatedly accepts
   a connection, receives up to 2 bytes, and sends them back along the
   same connection. *)

(* The [unit] argument is there for extraction to OCaml. *)
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

Definition test_echo := refines_mod_network_test
                          (echo_spec tt)
                          (echo tt).

(*! QuickChick test_echo. *)
(* ===>
     Checking Descramble_Examples.test_echo...
     +++ Passed 100 tests (0 discards) *)
