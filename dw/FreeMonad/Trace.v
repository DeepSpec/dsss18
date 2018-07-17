Set Implicit Arguments.
Set Contextual Implicit.

Require Import List.
Import ListNotations.
Require Import Relations.

Require Import ProofIrrelevance.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.

Class Visibility (E : Type -> Type) :=
  {
    dec_visible : forall X, E X -> bool
  }.

Definition visible {E} `{Visibility E} {X} (e : E X) : Prop :=
  dec_visible _ e = true.

(* Label events with some results. *)
Inductive labeledE (E : Type -> Type) (Y : Type) : Type :=
| Label : E Y -> list Y -> labeledE E Y.

(* Traces with labeled events. *)
(* By making this inductive, we can easily print a prefix
   of a computation by [Compute]. *)
Inductive T (E : Type -> Type) (X : Type) : Type :=
| TRet : X -> T E X
| TVis : forall Y, E Y -> list (Y * T E X) -> T E X
| TEllipsis.

Notation "(...)" := TEllipsis.

Fixpoint MtoT {E X} (fuel : nat) (m : M (labeledE E) X) : T E X :=
  match fuel with
  | O => (...)
  | S fuel' =>
    match m with
    | Ret x => TRet x
    | Tau m' => MtoT fuel' m'
    | Vis (Label e ys) k =>
      TVis e (map (fun y => (y, MtoT fuel' (k y))) ys)
    end
  end.

CoInductive ImpM {E} {X} `{Visibility E} : relation (M E X) :=
| ImpRet : forall x, ImpM (Ret x) (Ret x)
| ImpVis : forall Y (e : E Y) k1 k2,
    visible e ->
    (forall y, ImpM (k1 y) (k2 y)) ->
    ImpM (Vis e k1) (Vis e k2)
| ImpInvisL : forall Y (e : E Y) k1 m2,
    ~(visible e) ->
    (forall y, ImpM (k1 y) m2) ->
    ImpM (Vis e k1) m2
| ImpInvisR : forall Y (e : E Y) (y : Y) m1 k2,
    ~(visible e) ->
    ImpM m1 (k2 y) ->
    ImpM m1 (Vis e k2)
| ImpTauL : forall m1 m2,
    ImpM m1 m2 -> ImpM (Tau m1) m2
| ImpTauR : forall m1 m2,
    ImpM m1 m2 -> ImpM m1 (Tau m2).

(* The above is almost a simulation relation. *)
(* Here we will define a relation that is actually a simulation. *)
(* TODO: Simulation says nothing about missing transitions... *)
Section Simulation.

(* After some number of invisible steps, [P] is satisfied *)
Inductive IStepM {E X} `{Visibility E}
  : relation (M E X) :=
| NoIStep : forall m, IStepM m m
| IStepInvis : forall Y (e : E Y) (y : Y) k m,
    ~(visible e) ->
    IStepM (k y) m ->
    IStepM (Vis e k) m
| IStepTau : forall m1 m2, IStepM m1 m2 -> IStepM (Tau m1) m2.

Definition StepM {E X} `{Visibility E} Y (e : E Y)
  : relation (M E X) :=
  fun m1 m2 => (exists k, m2 = Vis e k) /\ IStepM m1 m2.

CoInductive SimM {E} {X} `{Visibility E} : relation (M E X) :=
(* [Ret] terminates the program. *)
| SimRet : forall m x, IStepM m (Ret x) -> SimM (Ret x) m

(* This could refactor SimRet and SimVis but needs to say
   "takes at least one invisible step"
| SimInvisR : forall m1 m2,
    IStepM (fun m2' => m2' = m2) m2' ->
    SimM m1 m2 ->
    SimM m1 m2'
*)

(* A visible effect on the left must be matched on the right. *)
| SimVis : forall Y (e : E Y) k1 m2 k2,
    visible e ->
    IStepM m2 (Vis e k2) ->
    (forall y, SimM (k1 y) (k2 y)) ->
    SimM (Vis e k1) m2

| SimInvis : forall Y (e : E Y) k1 m2,
    ~(visible e) ->
    (forall y, SimM (k1 y) m2) ->
    SimM (Vis e k1) m2

| SimTau : forall m1 m2,
    SimM m1 m2 -> SimM (Tau m1) m2.

(* If [m1] and [m2] are related by [SimM], then every visible
   transition from [m1] to some [m1'] corresponds to a visible
   transition from [m2] to some [m2'] such that [m1'] and [m2']
   are related by [SimM]. *)
Lemma sim_simulation E X `{Visibility E} :
  forall (m1 m2 : M E X),
    SimM m1 m2 ->
    forall m1' Y (e : E Y) (y : Y),
      visible e ->
      StepM _ e m1 m1' ->
      exists m2', StepM _ e m2 m2' /\ SimM m1' m2'.
Proof.
  intros m1 m2 HSim m1' Y e y He HStep.
  generalize dependent m2.
  destruct HStep as [ [k Hm1'] HIStep ].
  induction HIStep; intros.

  (* Visible step *)
  - subst.
    inversion HSim.
    + apply inj_pair2 in H1.
      subst.
      eexists.
      split.
      * split; eauto.
      * econstructor 2.
        auto.
        constructor.
        apply inj_pair2 in H2.
        subst.
        auto.
    + apply inj_pair2 in H1.
      subst.
      contradiction.

  (* Invisible step *)
  - apply IHHIStep.
    { auto. }
    inversion HSim.
    + apply inj_pair2 in H2.
      subst.
      contradiction.
    + apply inj_pair2 in H4.
      subst.
      auto.

  (* Tau step *)
  - apply IHHIStep.
    { auto. }
    inversion HSim.
    auto.
Qed.

(* SimM is the greatest simulation over StepM. *)

Lemma simulation_sim E X `{Visibility E} :
  forall (m1 m2 : M E X),
      (forall x, IStepM m1 (Ret x) -> IStepM m2 (Ret x)) ->
      (forall Y (e : E Y) (k1' : Y -> M E X),
          visible e ->
          IStepM m1 (Vis e k1') ->
          exists k2', IStepM m2 (Vis e k2') /\
                      forall y, SimM (k1' y) (k2' y)) ->
    SimM m1 m2.
Proof.
  cofix.
  intros.
  destruct m1 eqn:Hm1.
  - constructor.
    apply H0.
    constructor.
  - destruct (dec_visible _ e) eqn:He.
    + assert (HIStep1 : IStepM (Vis e k) (Vis e k)).
      { constructor. }
      apply H1 in HIStep1.
      destruct HIStep1 as [ k2' [ HIStep2 HSim ]].
      econstructor.
      * auto.
      * eauto.
      * auto.
      * auto.
    + constructor.
      * unfold visible.
        rewrite He.
        auto.
      * intro.
        apply simulation_sim.
        -- intros.
           apply H0.
           econstructor.
           unfold visible. rewrite He. auto.
           eauto.
        -- intros.
           apply H1.
           ++ auto.
           ++ econstructor.
              unfold visible; rewrite He; auto.
              eauto.
  - constructor.
    apply simulation_sim.
    + intros.
      apply H0.
      constructor.
      auto.
    + intros.
      apply H1.
      auto.
      constructor.
      auto.
Qed.

Lemma sim_super E X `{Visibility E} :
  forall (R : relation (M E X)),
    (forall (m1 m2 : M E X),
        R m1 m2 ->
        (forall x, IStepM m1 (Ret x) -> IStepM m2 (Ret x)) /\
        (forall Y (e : E Y) (k1' : Y -> M E X),
            visible e ->
            IStepM m1 (Vis e k1') ->
            exists k2', IStepM m2 (Vis e k2') /\
                        forall y, SimM (k1' y) (k2' y))) ->
    forall (m1 m2 : M E X),
      R m1 m2 -> SimM m1 m2.
Proof.
  intros R HR.
  cofix.
  intros.
  apply HR in H0.
  destruct H0.
  apply simulation_sim; auto.
Qed.

End Simulation.
