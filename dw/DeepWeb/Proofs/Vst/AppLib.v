Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit.

Require Import DeepWeb.Spec.ITreeSpec.

Open Scope list.
Open Scope logic.

Set Bullet Behavior "Strict Subproofs".

Section Basic_Extensions.
  Lemma filter_app: forall {A : Type} f (l1 l2 : list A),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof.
    induction l1; intros; trivial.
    simpl.
    destruct (f a); trivial.
    simpl.
    f_equal.
    apply IHl1.
  Qed.

  (*
Lemma In_preserved_by_map:
  forall {A B} (f : A -> B) (l1 l2 : list A),
    incl l1 l2 ->
    (forall y, In y (map f l1) -> In y (map f l2)).
Proof.
  intros A B f l1 l2 HIncl y HIn_map.
  apply list_in_map_inv in HIn_map.
  destruct HIn_map as [x [y_eq x_in]]; subst.
  apply in_map.
  unfold incl in HIncl; apply HIncl.
  assumption.
Qed.
   *)

  Lemma filter_incl:
    forall {A} (p : A -> bool) l, incl (filter p l) l.
  Proof.
    unfold incl.
    intros ? ? ? ? HIn.
    rewrite filter_In in HIn.
    destruct HIn; assumption.
  Qed.

  Lemma projected_filter_reflects_cond:
    forall {X Y} (f : X -> Y) (cond : X -> bool) (l : list X) (x : X) (y : Y),
      y = f x ->
      In x l -> 
      In y (map f (filter cond l)) ->
      NoDup (map f l) ->
      cond x = true.
  Proof.
    intros X Y f cond.
    induction l as [| a xs]; intros x y y_eq x_in y_in HNoDup;
      subst y; auto.
    destruct (cond x) eqn:Hcond; auto.
    exfalso.
    simpl in x_in.
    destruct x_in as [x_in_head | x_in_tail].
    - subst a.
      simpl in y_in.
      rewrite Hcond in y_in; simpl in y_in.
      pose proof (list_in_map_inv _ _ _ y_in) as H.
      destruct H as [x' [image_eq x'_in]].
      assert (In x' xs) as x'_in_tail by (eapply filter_incl; eassumption).
      simpl in HNoDup.
      rewrite NoDup_cons_iff in HNoDup.
      destruct HNoDup.
      apply in_map with (f0 := f) in x'_in_tail.
      rewrite image_eq in *.
      tauto.

    - simpl in HNoDup.
      rewrite NoDup_cons_iff in HNoDup.
      destruct HNoDup.
      assert (In (f x) (map f xs)) as fx_in_tail
          by (apply in_map; auto).

      simpl in y_in.
      destruct (cond a).
      + simpl in y_in.
        destruct y_in as [fa_fx | fx_in_filtered_tail];
          [rewrite fa_fx in *; tauto |].
        apply IHxs with (x := x) in fx_in_filtered_tail; auto.
        rewrite Hcond in *; discriminate.
      + apply IHxs with (x := x) in y_in; auto.
        rewrite Hcond in *; discriminate.
  Qed.

  Lemma same_key_preserves_NoDup:
    forall (T : Type) (g : T -> Z) (t t' : T) (prefix suffix : list T),
      g t = g t' ->
      NoDup (map g (prefix ++ t :: suffix)) ->
      NoDup (map g (prefix ++ t' :: suffix)).
  Proof.
    intros T g t t' prefix suffix Heq HNoDup.
    rewrite map_app in *.
    simpl in *.
    rewrite <- Heq.
    trivial.
  Qed.

End Basic_Extensions.


Section Interaction_Tree.
  
  Lemma replace_eq_given_discriminator
        {A : Type} (p1 p2: A -> bool) (g : A -> nat):
    forall (n : nat),
      (forall y, p1 y = true -> g y = n /\ p2 y = true) -> 
      forall (l : list A) (x : A),
        ~In n (map g (filter p2 l)) ->
        replace_when p1 x l = l.
  Proof.
    intros n Hdiscriminate.
    induction l as [| a l]; intros x n_not_in; auto.
    simpl.
    destruct (p1 _) eqn:p1_test; [| f_equal; apply IHl; try assumption].
    2 : {
      unfold not; intros Hcontra.
      simpl in n_not_in.
      destruct (p2 _); auto; simpl in n_not_in.
      destruct n_not_in; auto.
    }

    apply Hdiscriminate in p1_test.
    destruct p1_test as [g_a p2_test].
    revert n_not_in.
    simpl.
    rewrite p2_test.
    simpl.
    rewrite g_a.
    intros; tauto.
  Qed.        

  Lemma replace_when_NoDup {A : Type} (p1 p2: A -> bool) (g : A -> nat):
    forall (n : nat),
      (forall y, p1 y = true <-> g y = n /\ p2 y = true) ->
      forall (prefix suffix : list A) (x x' : A),
        g x = n /\ p2 x = true ->
        ~In (g x) (map g (filter p2 (prefix ++ suffix))) ->
        replace_when p1 x' (prefix ++ x :: suffix) = prefix ++ x' :: suffix.
  Proof.
    intros n tests_equal prefix suffix x x' [g_x p2_x]
           n_not_in.
    assert (forall y, p1 y = true -> g y = n /\ p2 y = true)
      as p1_p2.
    {
      intros; apply tests_equal; assumption.
    }

    assert (forall y, g y = n -> p2 y = true -> p1 y = true)
      as p2_p1.
    {
      intros; apply tests_equal; auto.
    }
    
    revert dependent prefix.
    induction prefix as [| a prefix]; intros n_not_in;
      rewrite g_x in *.
    { simpl.
      simpl in n_not_in.
      destruct (p1 _) eqn:p1_test.
      - f_equal.
        eapply replace_eq_given_discriminator; eauto.
      - pose proof (p2_p1 _ g_x p2_x).
        rewrite p1_test in *; discriminate.
    } 

    simpl.
    destruct (p1 _) eqn:p1_test.
    - destruct (p1_p2 _ p1_test) as [g_a p2_a].
      revert n_not_in.
      simpl.
      rewrite p2_a.
      simpl.
      intros; tauto.
    - f_equal.
      apply IHprefix.
      unfold not.
      intros Hcontra.
      
      assert (In n (map g (filter p2 [a]))
              \/ In n (map g (filter p2 (prefix ++ suffix))))
        as H by auto.
      apply in_or_app in H.
      rewrite <- map_app in H.
      rewrite <- filter_app in H.
      simpl app in H.
      tauto.
  Qed.

  Lemma conditional_id_iff {A : Type} (cond : A -> bool) (id : A -> nat):
    forall (x : A) (n : nat),
      (if cond x then (id x =? n)%nat else false) = true <->
      id x = n /\ cond x = true.
  Proof.
    intros.
    split. 
    - destruct (cond x); split; auto.
      + rewrite Nat.eqb_eq in H.
        assumption.
      + discriminate.
    - intros [id_n cond_x].
      rewrite cond_x.
      rewrite Nat.eqb_eq.
      assumption.
  Qed.

End Interaction_Tree.