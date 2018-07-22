Require Import Ascii.
Require Import List.
Import ListNotations.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.SimpleSpec.
Require Import DeepWeb.Spec.Swap_SimpleSpec.

Import EventNotations.

Example trace_example :
  true = is_trace_of 100 swap_spec_def [
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
  ] = Found [
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
  ] = Found [
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
    1 --> "c"].
Proof. reflexivity. Qed.

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
  ] = Found [
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
    0 --> "f"].
Proof. reflexivity. Qed.

(* This one requires quite a bit of fuel to reject... *)
Example bad_scrambled_trace_example :
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
  ] = NotFound.
Proof. reflexivity. Qed.
