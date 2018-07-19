(* Simulate a server, nondeterministically returning
   the new state of the network. *)

Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.
From ExtLib Require Monad.

Require Import Ascii.
Require Import String.
Require Import List.
Require Import PArith.
Require Fin.
Import ListNotations.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Import NonDeterminismBis.
Require Import DeepWeb.Free.Monad.Spec.

Require Import DeepWeb.Lib.TestDefaults.
Require Import DeepWeb.Util.ByteType.

From DeepWeb Require Import
     Lib.NetworkInterface
     Lib.SimpleSpec
     Lib.SimpleSpecTest.

From DeepWeb.Spec Require
     Swap_CLikeSpec
     Swap_SimpleSpec.

(* Enumerate the traces of the [server'] itree (swap server). *)
Definition random_trace_server :=
  random_trace 500 10 Swap_CLikeSpec.test_server.

(*
Sample random_trace_server.
*)

Definition test :=
  check_trace_incl_def
    Swap_SimpleSpec.swap_spec_def
    Swap_CLikeSpec.test_server.

(* Takes a few seconds *)
(*! QuickChick test. *)

Require Import DeepWeb.Spec.SingleSwap_SimpleSpec.
Require Import DeepWeb.Spec.SingleSwapSequential_Impl.

Module SingleSwap.

Definition spec := swap_spec_ default_buffer_size.
Definition impl := server.

Definition test :=
  check_trace_incl_def spec impl.

End SingleSwap.

(*! QuickChick SingleSwap.test. *)
