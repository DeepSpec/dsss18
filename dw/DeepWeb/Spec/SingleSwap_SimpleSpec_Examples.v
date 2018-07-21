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
Require Import DeepWeb.Lib.NetworkInterface.
Require Import DeepWeb.Lib.SimpleSpec.
Require Import DeepWeb.Spec.SingleSwap_SimpleSpec.

(** * Examples of the SingleSwap spec *)

Import EventNotations.
(** Convenient notations for events:
<<
       c !        Connection c is open
       c <-- b    Server receives byte b on connection c
       c --> b    Server sends byte b on connection c
       c --> ?    Server sends unknown byte b on connection c
>>
*)
(* BCP: The notion of "unknown byte" will need to be explained, either
   here or pretty soon.  Maybe best to do it later and, here, to just
   say "see below". *)

(** ** Example traces *)

(** A simple example showing the expected behavior described by the spec: *)
Example trace_example :
  true = is_trace_of 100 swap_spec [
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

(** An example of a behavior _not_ described by the spec (the first
    byte sent back should be ["0"], not ["1"]): *)
Example trace_example2 :
  false = is_trace_of 100 swap_spec [
    0 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "1"  (* error: Initial state is 000 *)
  ].
Proof. reflexivity. Qed.

(** Another non-trace of the spec is one that accepts two connections
    in a row without doing the two communications on the first one: *)
Example trace_example_3 :
  false = is_trace_of 100 swap_spec [
    0 !;
    1 !
  ].
Proof. reflexivity. Qed.

(** ** Example scrambled traces *)

(** "Scrambled traces" describe what the clients across the network
    can observe, given that the server is behaving according to the
    given sequential specification. *)

(** Every actual trace of the server is also a scrambled trace: *)
Example scrambled_trace_example_trivial :
  Found = is_scrambled_trace_of 1000 swap_spec [
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

(** More interestingly, the server can appear (from across the
    network) to accept two connections at the beginning and then 
    exchange messages on them: *)
Example scrambled_trace_example_1 :
  Found = is_scrambled_trace_of 1000 swap_spec [
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

(** Or, with yet more scrambling by the network, the server can appear
    to accept both connections, then receive messages from both, and
    then send messages on the second connection before sending on the
    first: *)
Example scrambled_trace_example_2 :
  Found = is_scrambled_trace_of 1000 swap_spec [
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

(** With even more scrambling, the communications on the two
    connections can appear arbitrarily interleaved: *)
Example scrambled_trace_example_2a :
  Found = is_scrambled_trace_of 1000 swap_spec [
    0 !;
    1 !;
    0 <-- "a";
    1 <-- "d";
    0 <-- "b";
    0 <-- "c";
    1 <-- "e";
    1 <-- "f";
    0 --> "0";
    0 --> "0";
    1 --> "a";
    1 --> "b";
    1 --> "c";
    0 --> "0"
  ].
Proof. reflexivity. Qed.

(* BCP: Not sure I can explain exactly why the following examples come
   out the way they do... *)
Example scrambled_trace_example_3 :
  NotFound = is_scrambled_trace_of 1000 swap_spec [
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

Example scrambled_trace_example_3a :
  Found = is_scrambled_trace_of 1000 swap_spec [
    1 !;
    0 !;
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> "d";
    0 --> "e";
    0 --> "f"
  ].
Proof. reflexivity. Qed.

Example scrambled_trace_example_4 :
  NotFound = is_scrambled_trace_of 1000 swap_spec [
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

(* BCP: Let's also have some examples showing a descrambled trace with
   holes.  Here is one kind of random one, but I'm not sure what to
   say about it...  In particular, I am confused by the fact that a
   concrete value can be observed on a connection _after_ a hole is
   observed on the same connection. *)
Example scrambled_trace_example_with_holes_1 :
  Found = is_scrambled_trace_of 1000 swap_spec [
    0 !;
    0 <-- "a";
    0 <-- "b";
    0 <-- "c";
    0 --> ?;
    0 --> "0";
    0 --> "0";
    1 !;
    1 <-- "d";
    1 <-- "e";
    1 <-- "f";
    1 --> ?;
    1 --> "b";
    1 --> ?
  ].
Proof. reflexivity. Qed.

