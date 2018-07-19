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

Require Import DeepWeb.Util.ByteType.

Require Import DeepWeb.Lib.NetworkInterface.
Require Import DeepWeb.Lib.SimpleSpec.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

(* [conns]: open connections, used for generating test cases.
   [last_msg]: last message received.
 *)
CoFixpoint swap_spec_loop
           (buffer_size : nat)
           (conns : list connection_id)
           (last_msg : bytes) :
  itree_spec :=
  (* Accept a new connection. *)
  c <- ^ ObsConnect;;
  (* Exchange one pair of messages. *)
  msg <- obs_msg_to_server buffer_size c;;
  obs_msg_from_server c last_msg;;
  swap_spec_loop buffer_size conns msg.

Definition init_msg (buffer_size : nat) :=
  repeat_string "0"%char buffer_size.

Definition swap_spec_ buffer_size :=
  swap_spec_loop buffer_size [] (init_msg buffer_size).

Definition swap_spec_def := swap_spec_ 3.

Section ExampleTraces.

Import EventNotations.

Example trace_example :
  true = is_trace_of 100 swap_spec_def [
    0 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "0";
    0 --> "0";
    0 --> "0";
    1 !;
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    1 --> "a";
    1 --> "b";
    1 --> "c"
  ].
Proof. reflexivity. Qed.

Example trace_example2 :
  false = is_trace_of 100 swap_spec_def [
    0 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "1"
    (* error: Initial state is 000 *)
  ].
Proof. reflexivity. Qed.

Example scrambled_trace_example :
  Found = is_scrambled_trace_of 1000 swap_spec_def [
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
  ].
Proof. reflexivity. Qed.

Example scrambled_trace_example_2 :
  Found = is_scrambled_trace_of 1000 swap_spec_def [
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
  ].
Proof. reflexivity. Qed.

Example scrambled_trace_example_3 :
  NotFound = is_scrambled_trace_of 1000 swap_spec_def [
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
  ].
Proof. reflexivity. Qed.

Example bad_scrambled_trace_example :
  NotFound = is_scrambled_trace_of 1000 swap_spec_def [
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
  ].
Proof. reflexivity. Qed.

End ExampleTraces.
