Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import SimpleDS.NetSem.
Require Import SimpleDS.Fresh.

Import Fresh.
Include NetSem(Fresh).

(* trace-based spec *)

Definition out_of_event (e : client_event) : list nat :=
  match e with
  | client_in _ _ => []
  | client_out _ (Fresh n) => [n]
  end.

Definition outputs (trace : list client_event) : list nat :=
  List.flat_map out_of_event trace.

Definition outputs_fresh (w : world) : Prop :=
  NoDup (outputs (trace w)).


(* This is what we want to prove, but it's not inductive!

      forall w,
        reachable' ideal_step w ->
        outputs_fresh w

   What we do know is that the Servers's state is greater
   than any past output...
*)

(* since our system is single-node,
   we never need to reason about msg delivery *)
Lemma packet_bogus :
  forall P, packet -> P.
Proof.
  intros P [d m].
  destruct m.
Qed.

Ltac packet_bogus :=
  apply packet_bogus; assumption.

(* relate state and trace *)
Lemma fresh_outputs_lt_state :
  forall w,
    reachable' ideal_step w ->
    (forall n,
        In n (outputs (trace w)) ->
        n < (locals w Server)).
Proof.
  intros w Hreach.
  induction Hreach.
  - simpl. tauto.
  - invcs H; [| packet_bogus].
    destruct n; invcs H0.
    unfold update; simpl.
    intuition.
Qed.

(* easy consequence of above *)
Lemma state_not_in_outputs :
  forall w,
    reachable' ideal_step w ->
    ~ In (locals w Server) (outputs (trace w)).
Proof.
  unfold not; intros.
  eapply fresh_outputs_lt_state in H; eauto.
  omega.
Qed.

(* Now we can prove our spec! *)
Theorem fresh_correct :
  forall w,
    reachable' ideal_step w ->
    outputs_fresh w.
Proof.
  intros w Hreach.
  induction Hreach.
  - constructor.
  - invc H; [| packet_bogus].
    destruct n; invcs H0.
    unfold outputs_fresh; simpl.
    apply NoDup_cons; auto.
    apply state_not_in_outputs; auto.
Qed.
