Set Implicit Arguments.
Set Contextual Implicit.

Require Import Coq.Init.Specif.
Require Import Setoid.
Require Import ProofIrrelevance.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Internal.
Import MonadNotations.

Class Equiv (m : Type -> Type) : Type :=
  { equiv : forall X, relation (m X) }.

Notation "a ~ b" := (equiv _ a b)
(at level 80, no associativity).

Notation LeftId M :=
  (forall X Y x (k : X -> M Y), ret x >>= k ~ k x).

Notation RightId M :=
  (forall X (s : M X), s >>= ret ~ s).

Notation BindAssoc M :=
  (forall X Y Z (s : M X) (k : X -> M Y) (h : Y -> M Z),
      s >>= (fun x => k x >>= h) ~ (s >>= k) >>= h).

Section CoinductiveEq.

Variable E : Type -> Type.
Variable X : Type.

(** Leaving Taus as uninterpreted actions, we have a monad,
    only the bind is not too satisfactory. *)

CoInductive EqM : relation (M E X) :=
| EqRet : forall x, EqM (Ret x) (Ret x)
| EqVis : forall Y (e : E Y) k1 k2,
    (forall y, EqM (k1 y) (k2 y)) ->
    EqM (Vis e k1) (Vis e k2)
| EqTau : forall m1 m2,
    EqM m1 m2 -> EqM (Tau m1) (Tau m2).

Instance eq_Reflexive : Reflexive EqM.
Proof.
  cofix self.
  intros []; constructor; auto.
Qed.

Instance eq_Symmetric : Symmetric EqM.
Proof.
  cofix self.
  intros x y []; constructor; auto.
Qed.

Instance eq_Transitive : Transitive EqM.
Proof.
  cofix self.
  intros x y z [] Hyz; inversion Hyz.
  - constructor.
  - apply inj_pair2 in H2.
    apply inj_pair2 in H3.
    subst.
    constructor.
    intro y'.
    eapply self; auto.
  - constructor; eapply self; eauto.
Qed.

Global Instance eq_Equivalence : Equivalence EqM.
Proof.
  constructor; typeclasses eauto.
Qed.

(* Axiom EqM_eq : forall a b, EqM a b -> a = b. *)

End CoinductiveEq.

Arguments EqM {E} [X].

Module CoreLawful.
Section CoreLawful.

Variable E : Type -> Type.

Import Monad.Free.Core.

Local Instance Equiv_M : Equiv (M E) :=
  { equiv := EqM }.

Lemma cong_bind X Y :
  forall s (k k' : X -> M E Y),
    (forall x, EqM (k x) (k' x)) ->
    EqM (Core.bindM s k) (Core.bindM s k').
Proof.
  cofix self.
  intros.
  do 2 rewrite bind_def_core.
  destruct s; simpl.
  - auto.
  - constructor. auto.
  - constructor. auto.
Qed.

Section CoreMonad.

Existing Instance Core.Monad_M.

Lemma leftId : LeftId (M E).
Proof.
  intros X Y x k.
  simpl.
  rewrite (@matchM _ _ (bindM _ _)); simpl; rewrite <- matchM.
  apply Equivalence.equiv_reflexive.
  typeclasses eauto.
Qed.

Lemma rightId : RightId (M E).
Proof.
  cofix self.
  intros X s.
  rewrite (matchM (bind _ _)).
  destruct s; constructor; intros; apply self.
Qed.

Lemma bindAssoc : BindAssoc (M E).
Proof.
  simpl.
  cofix self.
  intros X Y Z s k h.
  simpl.
  do 2 (rewrite bind_def_core with (s := s)).
  destruct s; simpl.
  - apply Equivalence.equiv_reflexive.
    typeclasses eauto.
  - rewrite bind_def_core with (s := Vis _ _).
    constructor.
    intro y'.
    apply self.
  - rewrite bind_def_core with (s := Tau _).
    constructor.
    apply self.
Qed.

End CoreMonad.
End CoreLawful.
End CoreLawful.

Section Lawful.
Variable E : Type -> Type.

(** Equivalence up to tau. *)
Section UpToTau.

Variable X : Type.

Inductive UnTau : relation (M E X) :=
| OneTau : forall s t, UnTau s t -> UnTau (Tau s) t
| NoTau : forall s, UnTau s s.

CoInductive EquivUpToTau : relation (M E X) :=
(* Equality with spin is undecidable,
   but one can coinductively generate a proof with this. *)
| EquivTau : forall s t,
    EquivUpToTau s t ->
    EquivUpToTau (Tau s) (Tau t)
| EquivTauExhaust : forall s s' t t',
    UnTau s s' ->
    UnTau t t' ->
    EquivNoTau s' t' ->
    EquivUpToTau s t

with

EquivNoTau : relation (M E X) :=
| EquivRet : forall x, EquivNoTau (Ret x) (Ret x)
| EquivVis : forall Y (e : E Y) (k1 k2 : Y -> M E X),
    (forall y, EquivUpToTau (k1 y) (k2 y)) ->
    EquivNoTau (Vis e k1) (Vis e k2).

Lemma eutt_refl_EqM : forall (s s' : M E X),
    EqM s s' -> EquivUpToTau s s'.
Proof.
  cofix self.
  intros s s' [].
  + econstructor; constructor.
  + econstructor; constructor. auto.
  + constructor. auto.
Qed.


Lemma eutt_refl : forall (s : M E X), EquivUpToTau s s.
Proof.
  cofix self.
  intros [].
  + econstructor; constructor.
  + econstructor; constructor; intros; apply self.
  + constructor; apply self.
Qed.

(* NB: EquivNoTau is not reflexive for Taus. *)

Lemma eutt_sym :
  forall (s t : M E X),
    EquivUpToTau s t -> EquivUpToTau t s
with
eunt_sym :
  forall (s t : M E X),
    EquivNoTau s t -> EquivNoTau t s.
Proof.
  { intros s t []; econstructor; eauto. }
  { intros s t []; constructor; auto. }
Qed.

Lemma pop_tau :
  forall (s t : M E X),
    EquivUpToTau s (Tau t) -> EquivUpToTau s t.
Proof.
  cofix self.
  intros s t H.
  inversion H. destruct H2.
  - constructor. apply self. constructor. auto.
  - econstructor; [ constructor | | ]; eauto.
  - econstructor; eauto. destruct H2; inversion H1; auto.
Qed.

Lemma push_tau :
  forall (s t : M E X),
    EquivUpToTau s t -> EquivUpToTau s (Tau t).
Proof.
  cofix self.
  intros s t H.
  inversion H.
  - constructor. apply self. auto.
  - econstructor; eauto. constructor. auto.
Qed.

Lemma tau_notau :
  forall (s t t' u' : M E X),
    EquivUpToTau s t ->
    UnTau t t' ->
    EquivNoTau t' u' ->
    exists s', UnTau s s' /\ EquivNoTau s' t'.
Proof.
  intros s t t' u' Hst Htt' Ht'u'.
  induction Htt'.
  - apply IHHtt'; auto.
    apply pop_tau; auto.
  - destruct Hst; inversion Ht'u'; subst;
      exists s'; split; auto; inversion H0; subst; auto.
Qed.

Lemma eutt_untau : forall (s s' : M E X),
    UnTau s s' -> EquivUpToTau s s'.
Proof.
  intros s s' H.
  induction H.
  - apply eutt_sym.
    apply push_tau.
    apply eutt_sym.
    auto.
  - apply eutt_refl.
Qed.

Lemma untau_inj :
  forall (s s' s'' t' t'' : M E X),
    UnTau s s' ->
    UnTau s s'' ->
    EquivNoTau t' s' ->
    EquivNoTau s'' t'' ->
    s' = s''.
Proof.
  intros s s' s'' t' t'' H.
  induction H; intros H' Hts' Hst''; inversion H'; auto;
    (inversion Hst''; inversion Hts'; subst; discriminate).
Qed.

Lemma eutt_trans :
  forall (s t u : M E X),
    EquivUpToTau s t -> EquivUpToTau t u -> EquivUpToTau s u
with
eunt_trans :
  forall (s t u : M E X),
    EquivNoTau s t -> EquivNoTau t u -> EquivNoTau s u.
Proof.
  { intros s t u
           [ s1 t1 H1 | s1 s1' t1 t1' ]
           H2;
      inversion H2 as [ t2 u2 H2' | t2 t2' u2 u2' Ht2 Hu2 H2' ];
      subst.
    - (* Tau, Tau, Tau *) constructor; eapply eutt_trans; eauto.
    - (* Tau, Tau & _, _ *)
      apply push_tau in H1.
      pose (Hs1t1 := tau_notau H1 Ht2 H2').
      destruct Hs1t1 as [s' [Hs1 Hs't2']].
      econstructor.
      + constructor; eassumption.
      + eassumption.
      + eapply eunt_trans; eassumption.
    - (* _, _ & Tau, Tau *)
      apply eutt_sym in H2.
      apply eunt_sym in H1.
      pose (Ht1u := tau_notau H2 H0 H1).
      destruct Ht1u as [s' [Hu Hs't1']].
      econstructor.
      + eassumption.
      + eassumption.
      + eapply eunt_trans; apply eunt_sym; eassumption.
    - (* _, _, _ *)
      econstructor; try eassumption.
      eapply eunt_trans. eassumption.
      replace t2' with t1' in *.
      + auto.
      + eapply untau_inj; eauto.
  }
  { intros s t u Hst Htu.
    destruct Hst; inversion Htu; subst.
    - constructor; auto.
    - apply inj_pair2 in H2.
      apply inj_pair2 in H3.
      subst.
      constructor.
      intros.
      eapply eutt_trans; eauto.
  }
Qed.

Instance eutt_Reflexive : Reflexive EquivUpToTau.
Proof.
  auto using eutt_refl.
Qed.

Instance eutt_Symmetric : Symmetric EquivUpToTau.
Proof.
  auto using eutt_sym.
Qed.

Instance eunt_Symmetric : Symmetric EquivNoTau.
Proof.
  auto using eunt_sym.
Qed.

Instance eutt_Transitive : Transitive EquivUpToTau.
Proof.
  eauto using eutt_trans.
Qed.

Instance eunt_Transitive : Transitive EquivNoTau.
Proof.
  eauto using eunt_trans.
Qed.

Global Instance eutt_Equivalence : Equivalence EquivUpToTau.
Proof.
  constructor; typeclasses eauto.
Qed.

(*
Lemma untau_tau : forall s s',
    UnTau s (Tau s') -> exists s1, s = Tau s1 /\ UnTau s1 s'.
Proof.
  (* induction doesn't give me s = Tau s' in the NoTau case... *)
  fix IH 3.
  intros s s' H.
  inversion_clear H as [ s0 s0' H0 | ].
  - apply IH in H0.
    destruct H0 as [s1 [ e1 H1 ]].
    exists s0.
    split.
    + auto.
    + rewrite e1. constructor. auto.
  - exists s'.
    split; constructor.
Qed.
 *)

Lemma untau_tau : forall s s',
    UnTau s (Tau s') -> UnTau s s'.
Proof.
  fix IH 3.
  intros s s' H.
  inversion_clear H as [ s0 s0' H0 | ].
  - constructor. apply IH. assumption.
  - repeat constructor.
Qed.

Lemma untau_trans : forall s t u,
    UnTau s t -> UnTau t u -> UnTau s u.
Proof.
  fix IH 4.
  intros s t u Hst Htu.
  inversion_clear Hst as [ s0 s0' Hst0 | ].
  - constructor. eapply IH; eauto.
  - auto.
Qed.

Lemma untau_eutt : forall s s' t t',
    UnTau s s' ->
    UnTau t t' ->
    EquivUpToTau s' t' ->
    EquivUpToTau s t.
Proof.
  cofix self.
  intros s s' t t' Hs Ht Hst'.
  destruct Hst'.
  - inversion Hs; inversion Ht; subst.
    + constructor. eapply self; try eassumption.
      constructor. assumption.
    + constructor. eapply self.
      * apply untau_tau. eauto.
      * constructor.
      * auto.
    + constructor. eapply self.
      * constructor.
      * apply untau_tau. eauto.
      * auto.
    + constructor. auto.
  - econstructor.
    + eapply untau_trans; eauto.
    + eapply untau_trans; eauto.
    + auto.
Qed.

End UpToTau.

Arguments EquivUpToTau {X} s t.

Lemma untau_bind {X Y} :
  forall s s' (k : X -> M E Y),
    UnTau s s' -> UnTau (Core.bindM s k) (Core.bindM s' k).
Proof.
  fix IH 4.
  intros s x k H.
  inversion_clear H as [ s0 s0' H' | ].
  - rewrite bind_def_core. simpl.
    constructor. apply IH. auto.
  - rewrite bind_def_core. simpl.
    repeat constructor.
Qed.

Section Congruence.

(* We decompose the handling of [bindM] by
   first proving congruence of [Core.bindM]. *)

(** Everything should be a setoid. *)
Variables (X Y : Type).

Notation CONG_BIND bind :=
  (forall s s' (k k' : X -> M E Y),
      EquivUpToTau s s' ->
      (forall x, EquivUpToTau (k x) (k' x)) ->
      EquivUpToTau (bind s k) (bind s' k')).

(* FIXME: Give this a better name... *)
Ltac dispatch :=
  try (eapply untau_trans;
       [ eapply untau_bind; eauto
       | rewrite bind_def_core; do 2 constructor ]).

Lemma cong_bind_core : CONG_BIND Core.bindM.
Proof.
  simpl.
  cofix self. (* Recurse in the Tau case. *)
  intros s s' k k' Hss' Hkk'.
  destruct Hss'.
  - (* Tau *)
    do 2 rewrite bind_def_core.
    constructor.
    auto.
  - (* -> ~Tau *)
    destruct H1.
    + (* -> Ret *)
      eapply untau_eutt; dispatch.
      eauto.
    + (* -> Vis *)
      econstructor; dispatch.
      constructor. auto.
Qed.

Lemma cong_bind : CONG_BIND Free.bindM.
Proof.
  intros.
  unfold bindM.
  apply cong_bind_core.
  - auto.
  - intros. constructor. auto.
Qed.

End Congruence.

Section LawfulMonad.

Local Instance EquivUTT_M : Equiv (M E) :=
  { equiv := @EquivUpToTau }.

Lemma leftId : LeftId (M E).
Proof.
  intros.
  pose (lid := CoreLawful.leftId x k).
  simpl in *.
  rewrite bind_def. simpl.
  eapply eutt_trans.
  - apply eutt_untau.
    do 2 constructor.
  - apply eutt_refl.
Qed.

Lemma rightId : RightId (M E).
Proof.
  intros.
  eapply eutt_trans.
  - (* x <- s ;; Tau (Ret x)  ~  x <- s ;; Ret x *)
    eapply cong_bind_core.
    + apply eutt_refl.
    + intros. eapply eutt_trans.
      * apply eutt_untau.
        do 2 constructor.
      * econstructor.
        -- constructor.
        -- constructor 2.
        -- constructor.
  - (* x <- s ;; Ret x  ~  s *)
    apply eutt_refl_EqM.
    apply (@CoreLawful.rightId E).
Qed.

(* Associativity actually holds structurally. *)
Lemma bindAssoc_EqM X Y Z :
  forall (s : M E X) (k : X -> M E Y) (h : Y -> M E Z),
    EqM (s >>= (fun x => k x >>= h)) ((s >>= k) >>= h).
Proof.
  intros.
  simpl.
  unfold bindM.
  apply eq_Symmetric.
  eapply eq_Transitive.
  - apply eq_Symmetric.
    pose (ba := CoreLawful.bindAssoc
                  s (fun x => Tau (k x)) (fun y => Tau (h y))).
    simpl in ba.
    apply ba.
  - apply CoreLawful.cong_bind.
    intros.
    rewrite bind_def_core.
    simpl.
    apply eq_Reflexive.
Qed.

Lemma bindAssoc X Y Z :
  forall (s : M E X) (k : X -> M E Y) (h : Y -> M E Z),
    (s >>= (fun x => k x >>= h) ~ (s >>= k) >>= h).
Proof.
  intros.
  apply eutt_refl_EqM; auto.
  apply bindAssoc_EqM.
Qed.

End LawfulMonad.

End Lawful.

Lemma while_loop_unfold :
  forall {E T} (cond : T -> bool) (P : T -> M E T) (t : T),
    while cond P t = if (cond t) then
                       (r <- P t ;; while cond P r)
                     else ret t.
Proof.
  intros.
  rewrite (matchM (while _ _ _)).
  simpl.
  destruct (cond t);
    auto.
  match goal with
  | [|- ?LHS = ?RHS] =>
    replace LHS with (idM RHS);
      auto
  end.
  rewrite <- matchM.
  auto.
Qed.
