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

Require Import
        DeepWeb.Lib.Util
        DeepWeb.Lib.SimpleSpec
        DeepWeb.Spec.Swap_SimpleSpec.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(* The swap server spec (for easy reference):
[[
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
]]
*)

Import EventNotations.

(** * Example traces *)

(** _Traces_ are lists of "observed events" of the following forms
    (plus one more that we'll see below):
<<
       c !        Connection c is opened
       c <-- b    Server receives byte b on connection c
       c --> b    Server sends byte b on connection c
>>
*)

(** The [is_observer_trace_test] property checks that some trace
    of events belongs to some sequential specification [ObserverM]. *)

(* A simple example illustrated the behavior described by the spec: *)
Example trace_example :
  OK tt = is_observer_trace_test swap_observer_def [
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
  FAIL tt = is_observer_trace_test swap_observer_def [
    0 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "1"   (* error: Initial state is 000 *)
  ]%hypo.
Proof. reflexivity. Qed.

