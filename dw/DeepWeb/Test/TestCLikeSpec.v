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

From DeepWeb Require Import
     Lib.SimpleSpec
     Lib.NetworkAdapter.

From DeepWeb.Spec Require
     Swap_CLikeSpec
     Swap_SimpleSpec.

Definition swap_server : itree_server :=
  simplify_network Swap_CLikeSpec.test_server.

(* Enumerate the traces of the [server'] itree (swap server). *)
Definition random_trace_server :=
  random_trace 500 10 swap_server.

(*
Sample random_trace_server.
*)

Definition test :=
  check_trace_incl_def
    Swap_SimpleSpec.swap_spec_def
    swap_server.

(* Takes a few seconds *)
(*! QuickChick test. *)

Require DeepWeb.Spec.SingleSwap_SimpleSpec.
Require DeepWeb.Spec.SingleSwapSequential_Impl.

Module SingleSwap.

Definition spec := SingleSwap_SimpleSpec.swap_spec.
Definition impl := SingleSwapSequential_Impl.server.

Definition test :=
  check_trace_incl_def spec impl.

End SingleSwap.

(*! QuickChick SingleSwap.test. *)
