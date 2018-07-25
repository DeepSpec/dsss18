(*! Section CLikeTest *)(*! extends BaseTest *)

(** * Top-level "internal" test *)

Typeclasses eauto := 6.

From QuickChick Require Import QuickChick.
From ExtLib Require Monad.

From DeepWeb Require Import
     Lib.SimpleSpec.

From DeepWeb.Spec Require
     Swap_CLikeSpec
     Swap_SimpleSpec.
(* begin hide *)

Definition swap_server : ServerM unit :=
  Swap_CLikeSpec.test_server.

Definition swap_observer : ObserverM unit :=
  Swap_SimpleSpec.swap_observer_def.

(* Enumerate the traces of the [server'] itree (swap server). *)
Definition random_trace_server :=
  random_trace 500 10 swap_server.

(* Sample random_trace_server. *)
(* end hide *)

Definition test :=
  refines_mod_network_test
    Swap_SimpleSpec.swap_observer_def
    Swap_CLikeSpec.test_server.

(*! QuickChick test. *)
