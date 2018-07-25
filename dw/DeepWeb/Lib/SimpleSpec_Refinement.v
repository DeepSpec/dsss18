Require Import Relations.
Require Import RelationClasses.

From QuickChick Require Import QuickChick.
From Custom Require Import List.
Import ListNotations.
From Custom Require Map.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Import
     Lib.SimpleSpec_NetworkModel
     Lib.SimpleSpec_Server
     Lib.SimpleSpec_Observer
     Lib.SimpleSpec_Scramble
     Lib.SimpleSpec_Traces.

Import SimpleSpec_Scramble.ScramblingFacts.

Set Bullet Behavior "Strict Subproofs".

(* The definition of "refinement" between an itree representing
   a server implementation, and an itree of "linear traces"
   as a specification. The [ScramblingFacts] that the
   theorems below depend on are defined and proved in
   [Lib.SimpleSpec_Scramble]. *)

(* A server ([server : ServerM unit]) refines a "linear spec"
   ([observer : ObserverM unit]) if, for every trace [tr] that the
   server can produce, and every trace [str] that can be observed
   from it via the network, it can be explained by a "descrambled
   trace" [dstr] in the "linear spec".
   Some examples can be found in [Spec.Descramble_Examples].
 *)
Definition refines_mod_network observer server : Prop :=
  forall tr : real_trace,
    is_server_trace server tr ->
    forall str : real_trace,
      network_scrambled tr str ->
      exists dstr : real_trace,
        network_scrambled dstr str /\
        is_observer_trace observer dstr.

(* It turns out that we can simplify this property
   (three quantifiers!) to remove an intermediate step.
   We can directly descramble only the traces of the server.
   [strong_sound] and [strong_complete] shown below establish
   the equivalence between these two properties. *)
Definition strong_refines_mod_network observer server : Prop :=
  forall tr : real_trace,
    wf_trace tr ->
    is_server_trace server tr ->
      exists dstr : real_trace,
        network_scrambled dstr tr /\
        is_observer_trace observer dstr.

(* [strong_sound] and [strong_complete] rely on two properties
   of the [network_scrambled] relation: it is reflexive
   ([scrambled_reflexive]) and transitive ([scrambled_transitive]).
   (These are shown in [Lib.SimpleSpec_Scramble].)
 *)

Definition strong_sound :
  forall server spec,
    strong_refines_mod_network server spec ->
    refines_mod_network server spec.
Proof.
  intros server spec Hstrong tr Htr_istrace str Hstr_scrambled.
  pose proof (scrambled_preserves_wf _ _ Hstr_scrambled) as Hwf.
  destruct (Hstrong tr (proj1 Hwf) Htr_istrace)
    as [dstr [Hdstr_scrambled Hdstr_istrace]].
  exists dstr.
  split; auto.
  etransitivity; eauto.
Qed.

Definition strong_complete :
  forall server spec,
    refines_mod_network server spec ->
    strong_refines_mod_network server spec.
Proof.
  intros server spec Hcorrect tr Htr_wf Htr_istrace.
  destruct (Hcorrect tr Htr_istrace tr)
    as [dstr [Hdstr_scrambled Hdstr_istrace]].
  { apply scrambled_reflexive; auto. }
  exists dstr.
  auto.
Qed.

(* [refines_mod_network] is part of the toplevel property
   about the swap server, stated in [Spec.TopLevelSpec]. *)
