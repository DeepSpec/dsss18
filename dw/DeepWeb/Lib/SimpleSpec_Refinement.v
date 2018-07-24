Require Import Relations.
Require Import RelationClasses.

From QuickChick Require Import QuickChick.
From Custom Require Import List.
Import ListNotations.
From Custom Require Map.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import NonDeterminismBis.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Import
     Lib.SimpleSpec_NetworkModel
     Lib.SimpleSpec_NetworkInterface
     Lib.SimpleSpec_Observer
     Lib.SimpleSpec_Scramble
     Lib.SimpleSpec_Traces.

Set Bullet Behavior "Strict Subproofs".

Module MkScramblingRefinement (ScramblingFacts : ScramblingTypes).

Import ScramblingFacts.

Definition refines_mod_network server spec : Prop :=
  forall tr : real_trace,
    wf_trace tr ->
    is_server_trace server tr ->
    forall str : real_trace,
      network_scrambled0 tr str ->
      exists dstr : real_trace,
        network_scrambled0 dstr str /\
        is_spec_trace spec dstr.

Definition strong_refines_mod_network server spec : Prop :=
  forall tr : real_trace,
    wf_trace tr ->
    is_server_trace server tr ->
      exists dstr : real_trace,
        network_scrambled0 dstr tr /\
        is_spec_trace spec dstr.

Definition strong_sound :
  forall server spec,
    strong_refines_mod_network server spec ->
    refines_mod_network server spec.
Proof.
  intros server spec Hstrong tr Htr_wf Htr_istrace str Hstr_scrambled.
  destruct (Hstrong tr Htr_wf Htr_istrace)
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
  destruct (Hcorrect tr Htr_wf Htr_istrace tr)
    as [dstr [Hdstr_scrambled Hdstr_istrace]].
  { apply scrambled_reflexive; auto. }
  exists dstr.
  auto.
Qed.

End MkScramblingRefinement.

Module Export ScramblingRefinement :=
  MkScramblingRefinement ScramblingFacts.
