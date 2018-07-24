Require ProofIrrelevance.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Require Import DeepWeb.Free.Monad.Internal.
Import MonadNotations.

Section Sem.

Variable E : Type -> Type.
Variable S : Type.

Variable pre : forall X, E X -> S -> Prop.
Variable step : forall X, E X -> S -> S -> X -> Prop.

CoInductive Stable {X} (post : S -> X -> Prop) : S -> M E X -> Prop :=
| StableRet : forall s x, post s x -> Stable post s (Ret x)
| StableTau : forall s m, Stable post s m -> Stable post s (Tau m)
| StableVis : forall s Y (e : E Y) (k : Y -> M E X),
    pre _ e s ->
    (forall y s', step _ e s s' y ->
                  Stable post s' (k y)) ->
    Stable post s (Vis e k).

End Sem.

Lemma stable_bind E A B S
      (pre : forall X, E X -> S -> Prop)
      (step : forall X, E X -> S -> S -> X -> Prop)
      (postA : S -> A -> Prop)
      (postB : S -> B -> Prop) :
  forall (k : A -> M E B),
    (forall s' a,
        postA s' a -> Stable _ _ pre step postB s' (k a)) ->
    forall (s : S)
           (m : M E A),
      Stable _ _ pre step postA s m ->
      Stable _ _ pre step postB s (bindM m k).
Proof.
  intros k Hk.
  cofix self.
  intros s m Hm.
  inversion Hm.
  - rewrite bind_def; simpl.
    apply StableTau.
    apply Hk.
    auto.
  - rewrite bind_def; simpl.
    apply StableTau.
    apply self.
    auto.
  - rewrite bind_def; simpl.
    apply StableVis.
    { auto. }
    intros y s' Hs'.
    apply self.
    apply H0.
    auto.
Defined.

Section StableAssoc.

Import ProofIrrelevance.

Lemma stable_assoc E A B C :
  forall S (pre : forall X, E X -> S -> Prop)
         (step : forall X, E X -> S -> S -> X -> Prop)
         (post : S -> C -> Prop)
         (s : S)
         (m : M E A) (k : A -> M E B) (h : B -> M E C),
    Stable _ _ pre step post s (bindM m (fun a => bindM (k a) h)) ->
    Stable _ _ pre step post s (bindM (bindM m k) h).
Proof.
  intros S pre step post.
  cofix self.
  intros.
  destruct m.
  - rewrite matchM.
    rewrite matchM in H.
    simpl in *.
    assumption.
  - rewrite bind_def.
    rewrite bind_def in H.
    simpl in *.
    inversion H; subst.
    apply inj_pair2 in H1.
    apply inj_pair2 in H4.
    subst.
    apply StableVis.
    { assumption. }
    intros y s' Hs'.
    apply (self s' (k0 y) k h).
    apply H5.
    assumption.
  - rewrite bind_def.
    rewrite bind_def in H.
    simpl in *.
    inversion H; subst.
    apply StableTau.
    subst.
    apply (self s m k h).
    apply H2.
Defined.

Lemma stable_map_assoc E A B C :
  forall S (pre : forall X, E X -> S -> Prop)
         (step : forall X, E X -> S -> S -> X -> Prop)
         (post : S -> C -> Prop)
         (s : S)
         (m : M E A) (f : A -> B) (h : B -> M E C),
    Stable _ _ pre step post s (bindM m (fun a => h (f a))) ->
    Stable _ _ pre step post s (bindM (mapM f m) h).
Proof.
  intros S pre step post.
  cofix self.
  intros.
  destruct m.
  - rewrite matchM.
    rewrite matchM in H.
    simpl in *.
    assumption.
  - rewrite bind_def.
    rewrite bind_def in H.
    simpl in *.
    inversion H; subst.
    apply inj_pair2 in H1.
    apply inj_pair2 in H4.
    subst.
    apply StableVis.
    { assumption. }
    intros y s' Hs'.
    apply (self s' (k y) f h).
    apply H5.
    assumption.
  - rewrite bind_def.
    rewrite bind_def in H.
    simpl in *.
    inversion H; subst.
    apply StableTau.
    subst.
    apply (self s m f h).
    apply H2.
Defined.

End StableAssoc.

Lemma stable_mapM E A B :
  forall S (pre : forall X, E X -> S -> Prop)
         (step : forall X, E X -> S -> S -> X -> Prop)
         (postA : S -> A -> Prop)
         (postB : S -> B -> Prop)
         (f : A -> B),
    (forall s a, postA s a -> postB s (f a)) ->
    forall (s : S) (m : M E A),
      Stable _ _ pre step postA s m ->
      Stable _ _ pre step postB s (mapM f m).
Proof.
  intros S pre step postA postB f Hf.
  cofix self.
  intros.
  inversion H; rewrite matchM; simpl.
  - apply StableRet.
    apply Hf; assumption.
  - apply StableTau.
    apply self with (m := m0).
    assumption.
  - apply StableVis.
    assumption.
    intros.
    apply self with (m := k y).
    apply H1.
    assumption.
Defined.

Lemma hoist_def E F X Y (e : F Y) (k : Y -> M F X)
      (f : forall X, F X -> E X) :
  hoist f (Vis e k) = Vis (f _ e) (fun y => hoist f (k y)).
Proof.
  rewrite (matchM (hoist _ _)).
  simpl.
  auto.
Qed.

Lemma hom_def E F X Y (e : F Y) (k : Y -> M F X)
      (interpret : forall Y, F Y -> M E Y) :
  hom interpret (Vis e k)
  =
  interpret _ e >>= fun y =>
    hom interpret (k y).
Proof.
  rewrite (matchM (hom _ _)).
  rewrite (matchM (bind _ _)).
  simpl.
  auto.
Qed.

Lemma stable_run E F S_ S
      (pre_ : forall X, F X -> S_ -> Prop)
      (step_ : forall X, F X -> S_ -> S_ -> X -> Prop)
      (pre : forall X, E X -> S -> Prop)
      (step : forall X, E X -> S -> S -> X -> Prop)
      (refn : S_ -> S -> Prop)
      (interpret : forall X, F X -> M E X)
      X
      (post_ : S_ -> X -> Prop)
      (post : S -> X -> Prop) :
  (forall Y (e : F Y) s_ s,
    pre_ Y e s_ ->
    refn s_ s ->
    Stable E S pre step (fun s' y => exists s_',
                             step_ Y e s_ s_' y /\
                             refn s_' s')
           s
           (interpret _ e)) ->
  (forall s_' s' x, refn s_' s' -> post_ s_' x -> post s' x) ->
  forall (s_ : S_) (s : S) (m : M F X),
    refn s_ s ->
    Stable F S_ pre_ step_ post_ s_ m ->
    Stable E S pre step post s (run interpret (hoist (fun _ => inr) m)).
Proof.
  intros Hinterpret Hpost.
  cofix self.
  intros s_ s m Hss_ Hm.
  inversion Hm.
  - rewrite matchM; simpl; apply StableRet.
    eapply Hpost.
    eassumption.
    assumption.
  - rewrite matchM; simpl.
    apply StableTau.
    apply self with (s_ := s_).
    { assumption. }
    { assumption. }

  - rewrite hoist_def.
    unfold run.
    rewrite hom_def.
    apply stable_bind
    with
      (postA := fun s' y =>
         exists s_', step_ Y e s_ s_' y /\ refn s_' s').
    + intros s' a [s_' [Ha1 Ha2]].
      apply self
      with (s_ := s_').
      assumption.
      apply H0.
      assumption.
    + apply Hinterpret.
      assumption.
      assumption.
Defined.
