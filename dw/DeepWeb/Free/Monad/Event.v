Set Implicit Arguments.
Set Contextual Implicit.

Require Import List.
Import ListNotations.
Require Import Relations.

Require Import ProofIrrelevance.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Open Scope sum_scope.

Inductive event (E : Type -> Type) : Type :=
| Event : forall X, E X -> X -> event E.

Definition event_trace (E : Type -> Type) : Type := list (event E).

(* [RunTo p t q]: Program [p] executes with trace [t]
   until state [q].
   [F]: invisible events (e.g., nondeterminism)
   [E]: visible events *)
Inductive RunTo {E F X}
  : M (F +' E) X -> event_trace E -> M (F +' E) X -> Prop :=
| Stop : forall p, RunTo p [] p
| Step : forall Y (e : E Y) (y : Y) (k : Y -> M (F +' E) X) t q,
    RunTo (k y) t q ->
    RunTo (Vis (| e) k) (Event e y :: t) q
| Work : forall p t q, RunTo p t q -> RunTo (Tau p) t q
| Guess : forall Y (e : F Y) (y : Y) (k : Y -> M (F +' E) X) t q,
    RunTo (k y) t q ->
    RunTo (Vis (e |) k) t q.

(* Preorder (if we ignore the trace index). *)
Lemma RunTo_refl {E F X} : forall (p : M (F +' E) X), RunTo p [] p.
Proof. constructor. Qed.

Lemma RunTo_trans {E F X} : forall (p q r : M (F +' E) X) t u,
    RunTo p t q -> RunTo q u r -> RunTo p (t ++ u)%list r.
Proof.
  induction 1 as
      [
      | Y e y k t q RTq IH
      | p t q RTq IH
      | Y e y k t q RTq IH ].
  - auto.
  - intros. constructor. auto.
  - intros. constructor. auto.
  - intros. econstructor. eauto.
Qed.

Lemma RunTo_trans' {E F X} : forall (p q r : M (F +' E) X) t u tu,
    RunTo p t q -> RunTo q u r -> (t ++ u)%list = tu -> RunTo p tu r.
Proof.
  intros.
  subst.
  eapply RunTo_trans; eauto.
Qed.

CoInductive Simulate {E F X} : M (F +' E) X -> M (F +' E) X -> Prop :=
| SimRet : forall (x : X), Simulate (Ret x) (Ret x)
| SimTauL : forall p q, Simulate p q -> Simulate (Tau p) q
| SimVis : forall Y (e : E Y) kp q kq,
    RunTo q [] (Vis (| e) kq) ->
    (forall y, Simulate (kp y) (kq y)) ->
    Simulate (Vis (| e) kp) q
| SimInvis : forall Y (e : F Y) kp q,
    (forall y, Simulate (kp y) q) ->
    Simulate (Vis (e |) kp) q.

Definition TraceIncl {E F X} (p q : M (F +' E) X) : Prop :=
  forall t p', RunTo p t p' -> exists q', RunTo q t q'.

Require ProofIrrelevance.
Section Simulate_TraceIncl.
Import ProofIrrelevance.

Lemma Simulate_TraceIncl' {E F X} :
  forall (p0 : M (F +' E) X) t p',
    RunTo p0 t p' ->
    forall q0, Simulate p0 q0 -> exists q', RunTo q0 t q'.
Proof.
  induction 1 as
      [
      | Y e y k t q RTq IH
      | p t q RTq IH
      | Y e y k t q RTq IH ].
  - intros. exists q0. constructor.

  - intros q0 Sq0.
    inversion Sq0.
    repeat (match goal with
            | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H
            end).
    subst.
    match goal with
    | [H : forall _, Simulate _ (kq _) |- _] =>
      specialize H with y; apply IH in H; destruct H as [ q' RTq' ]
    end.
    exists q'.
    eapply RunTo_trans'.
    + eauto.
    + eapply RunTo_trans'.
      * constructor.
      * constructor. eauto.
      * eauto.
    + eauto.

  - intros q0 Sq0.
    apply IH.
    inversion Sq0; auto.
  - intros q0 Sq0.
    apply IH.
    inversion Sq0.
    repeat (match goal with
            | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H
            end).
    subst.
    auto.
Qed.

Lemma Simulate_TraceIncl {E F X} : forall (p0 q0 : M (F +' E) X),
  Simulate p0 q0 -> TraceIncl p0 q0.
Proof.
  intros p0 q0 Sq0 t p' Rtp'.
  eapply Simulate_TraceIncl'; eauto.
Qed.

End Simulate_TraceIncl.

(* p simulates q until r.
   p is a "uniform prefix" of q, with "residual" r. *)
CoInductive PreSimulate {E F X A B}
  : M (F +' E) X -> M (F +' E) A -> (B -> M (F +' E) A) -> Prop :=
| PreSimRet : forall (x : X) (b : B) (r : B -> M (F +' E) A),
    PreSimulate (Ret x) (r b) r
| PreSimTauL : forall p q r,
    PreSimulate p q r -> PreSimulate (Tau p) q r
| PreSimVis : forall Y (e : E Y) kp q kq r,
    RunTo q [] (Vis (| e) kq) ->
    (forall y, PreSimulate (kp y) (kq y) r) ->
    PreSimulate (Vis (| e) kp) q r
| PreSimInvis : forall Y (e : F Y) kp q r,
    (forall y, PreSimulate (kp y) q r) ->
    PreSimulate (Vis (e |) kp) q r.

Module Type Invariant.
  Parameter E : Type -> Type.

  (* Shared state (can be modified by both client and server) *)
  Parameter S : Type.

  (* Local state (the current tree can modify it) *)
  Parameter I : Type.

  (* Remote state (the current tree cannot modify it, but
     it can be modified between any two local actions) *)
  Parameter J : Type.

  (* Property that is maintained between the three states. *)
  Parameter inv : S -> I -> J -> Prop.

  (* The allowed operations for the current tree are
     determined by the local state. *)
  Parameter pre : forall X, E X -> I -> Prop.

  (* Step relation.
     [step e s i s' i' x]: The action [e : E X] takes the local and
     shared states [(s,i)] to [(s',i')] and produces a result [x]. *)
  Parameter step : forall X, E X -> S -> I -> S -> I -> X -> Prop.

  (* Lemma: the step relation preserves the invariant. *)
  Parameter step_inv : forall X (e : E X) s i j,
      pre e i ->
      inv s i j ->
      forall s' i' x,
        step e s i s' i' x ->
        inv s' i' j.

  (* Client side *)
  (* TODO: Solve duplicate. *)
  Parameter pre' : forall X, E X -> J -> Prop.
  Parameter step' : forall X, E X -> S -> J -> S -> J -> X -> Prop.

  (* Lemma: the step relation preserves the invariant. *)
  Parameter step_inv' : forall X (e : E X) s i j,
      pre' e j ->
      inv s i j ->
      forall s' j' x,
        step' e s j s' j' x ->
        inv s' i j'.

End Invariant.

Module Stable (Inv : Invariant).

CoInductive Stable {F A}
  : Inv.I -> M (F +' failureE +' Inv.E) A -> Prop :=
| StableRet : forall i (a : A), Stable i (Ret a)
| StableTau : forall i m, Stable i m -> Stable i (Tau m)
| StableInvis :
    forall i Y (e : F Y) (k : Y -> M _ A),
      (forall y, Stable i (k y)) ->
      Stable i (Vis (e||) k)
| StableVis :
    forall i Y (e : Inv.E Y) (k : Y -> M _ A),
      Inv.pre e i ->
      (forall s s' i' y, Inv.step e s i s' i' y -> Stable i' (k y)) ->
      Stable i (Vis (|e) k).

CoInductive Stable' {F A}
  : Inv.J -> M (F +' failureE +' Inv.E) A -> Prop :=
| Stable'Ret : forall j (a : A), Stable' j (Ret a)
| Stable'Tau : forall j m, Stable' j m -> Stable' j (Tau m)
| Stable'Invis :
    forall i Y (e : F Y) (k : Y -> M _ A),
      (forall y, Stable' i (k y)) ->
      Stable' i (Vis (e||) k)
| Stable'Vis :
    forall j Y (e : Inv.E Y) (k : Y -> M _ A),
      Inv.pre' e j ->
      (forall s s' j' y, Inv.step' e s j s' j' y -> Stable' j' (k y)) ->
      Stable' j (Vis (|e) k).

End Stable.

CoInductive GoodTrace {E : Type -> Type}
            (P : forall Y, E Y -> Prop)
  : M E unit -> Prop :=
| GoodTau : forall m, GoodTrace P m -> GoodTrace P (Tau m)
| GoodRet : GoodTrace P (Ret tt)
| GoodVis : forall Y (e : E Y) k,
    P Y e -> (forall y, GoodTrace P (k y)) ->
    GoodTrace P (Vis e k).
