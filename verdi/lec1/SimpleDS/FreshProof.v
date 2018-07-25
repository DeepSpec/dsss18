Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import NetSem.
Require Import Fresh.

(* Note that Fresh module we imported above actually contains
   *another* module named Fresh which is our actual system. We'll
   import that as well to get more convenient access to our
   definitions. *)
Import Fresh.

(* Now we apply the NetSem functor to the Fresh system and import the
   result to get semantics for the Fresh system. *)
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

(* first attempt at proof *)

Theorem fresh_correct :
  forall w,
    reachable' ideal_step w ->
    outputs_fresh w.
Proof.
  intros w Hreach.
  induction Hreach.
  - constructor.
  - invc H.
    + destruct n; invcs H0.
      unfold outputs_fresh; simpl.
      (* STUCK!

         We know all the outputs up to this point did not have
         duplicates.  Now we need to prove that if we tack on the
         current state of our node to the output, there are still no
         duplicates.

         However, we don't have any information relating the state of
         our node to those past outputs!

         The problem is that our specification is NOT INDUCTIVE.  That
         is, just because the spec holds for a given state, it doesn't
         guarantee that all possible next states will also satisfy the
         spec.

         We need to back out and prove a lemma that relates the trace
         and state.

       *)
Abort.


(* since our system is single-node,
   we never need to reason about msg delivery *)
Lemma packet_bogus :
  forall P, packet -> P.
Proof.
  intros P p.
  destruct p.
  destruct payload.
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