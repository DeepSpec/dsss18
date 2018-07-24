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
Import SumNotations NonDeterminismBis.

Require Import DeepWeb.Lib.Util DeepWeb.Lib.SimpleSpec.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(** * Main specification of a swap server *)

(** This is the main loop of the swap server.  The parameter [conns]
     maintains the list of open connections (this is used for
     generating test cases), while [last_msg] holds the message
     received from the last client (which will be sent back to the next
     client).  The server repeatedly chooses between accepting a new
     connection or doing a receive and then a send on some existing
     connection. *)
(* BCP: How is conns used for generating test cases?? *)

(* BCP: Should/could this be written using [forever]? *)
CoFixpoint swap_spec_loop (buffer_size : nat)
                          (conns : list connection_id)
                          (last_msg : bytes) 
                        : itree_spec :=
  disj "swap_spec"
    ( (* Accept a new connection. *)
      c <- obs_connect;;
      swap_spec_loop buffer_size (c :: conns) last_msg
    | (* Exchange a pair of messages on a connection. *)
      c <- choose "do swap" conns;;
      msg <- obs_msg_to_server buffer_size c;;
      obs_msg_from_server c last_msg;;
      swap_spec_loop buffer_size conns msg
    ).

Definition swap_spec_ (buffer_size : nat)
                      (init_msg : bytes) 
                    : itree_spec :=
  swap_spec_loop buffer_size [] init_msg.

Module Def := Lib.Util.TestDefault.

(* Top-level spec *)
Definition swap_spec_def : itree_spec :=
  swap_spec_ Def.buffer_size Def.init_message.

(** * Examples *)

Import EventNotations.

(** _Traces_ are lists of "observed events" of the following forms:
<<
       c !        Connection c is opened
       c <-- b    Server receives byte b on connection c
       c --> b    Server sends byte b on connection c
>>
*)

(** ** Example traces *)

(** The [is_trace_of] property checks that some trace of events
    belongs to some sequential specification [itree_spec]. *)

(* A simple example illustrated the behavior described by the spec: *)
Example trace_example :
  OK tt = is_spec_trace_test 100 swap_spec_def [
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
Proof. reflexivity. Qed.

(* An example of a behavior _not_ described by the spec (the first
   byte sent back should be ["0"], not ["1"]): *)
Example trace_example2 :
  FAIL tt = is_spec_trace_test 100 swap_spec_def [
    0 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "1"   (* error: Initial state is 000 *)
  ]%hypo.
Proof. reflexivity. Qed.

(** ** Example scrambled traces *)

(** "Scrambled traces" describe what the clients _across the network_
    can observe, given that the server is behaving according to the
    given sequential specification.

    The [is_scrambled_trace_of] function checks whether a given
    "observed trace" is a scrambled version of some "linear trace"
    belonging to a given specification.  If so, it returns the linear
    trace that explains the observed trace. *)

(* Every actual trace of the server is also a scrambled trace: *)
Example scrambled_trace_example_1 :
  is_scrambled_trace_of 1000 swap_spec_def [
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
Proof. reflexivity. Qed.

(* The "scrambling" of messages in the network can result in responses
   on different connections being received out of order.  The
   resulting "explanation" shows the order that they must have been
   sent by the server. *)
Example scrambled_trace_example_2 :
  is_scrambled_trace_of 1000 swap_spec_def [
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
  is_scrambled_trace_of 1000 swap_spec_def [
    0 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "X"
  ]%real = FAIL tt.
Proof. reflexivity. Qed.

(* A more interesting bad trace, where the server appears to send the
   requests from connection 1 as responses along connection 2 _and
   vice versa_.  (This one requires quite a bit of fuel to reject...) *)
Example bad_scrambled_trace_example_2 :
  is_scrambled_trace_of 2000 swap_spec_def [
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
  is_scrambled_trace_of 1000 swap_spec_def [
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
  is_scrambled_trace_of 1000 swap_spec_def [
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

