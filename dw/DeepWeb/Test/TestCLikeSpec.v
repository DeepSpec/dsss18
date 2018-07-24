(*! Section CLikeTest *)(*! extends BaseTest *)

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
  refines_mod_network_test
    Swap_SimpleSpec.swap_spec_def
    swap_server.

(*! QuickChick test. *)
