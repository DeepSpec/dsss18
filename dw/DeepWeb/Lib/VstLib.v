From Custom Require Import List String.

Require Import VST.floyd.proofauto.

Open Scope logic.

Section Val_String.
  
  Definition val_of_ascii (a : Ascii.ascii) : val :=
    Vint (Int.repr (Z.of_nat (Ascii.nat_of_ascii a))).

  Fixpoint val_of_string (s : string) : list val :=
    match s with
    | EmptyString => []
    | String a str => 
      (val_of_ascii a) :: val_of_string str
    end.

  Lemma val_of_string_app:
    forall msg1 msg2,
      val_of_string (msg1 ++ msg2) =
      (val_of_string msg1 ++ val_of_string msg2)%list.
  Proof.
    intros.
    induction msg1; simpl; auto.
    rewrite IHmsg1.
    auto.
  Qed.

  Lemma Zlength_val_string_len:
    forall s : string, Zlength (val_of_string s) = Z.of_nat (String.length s).
  Proof.
    induction s; auto.
    simpl.
    rewrite Zpos_P_of_succ_nat.
    rewrite Zlength_cons.
    f_equal.
    auto.
  Qed.

  Definition rep_msg (msg : string) (bound : Z) : list val :=
    (val_of_string msg)
      ++ (list_repeat (Z.to_nat (bound - Zlength (val_of_string msg)))
                      Vundef).

  Definition rep_msg_len (msg : string) : val :=
    Vint (Int.repr (Zlength (val_of_string msg))).

  Lemma rep_empty_string: forall bound,
      rep_msg "" bound = list_repeat (Z.to_nat bound) Vundef.
  Proof.
    intros.
    unfold rep_msg.
    simpl val_of_string.
    rewrite app_nil_l.
    rewrite Zlength_nil.
    replace (bound - 0) with bound by omega.
    reflexivity.
  Qed.
  
  Lemma rep_msg_bound: forall s bound,
      Zlength (rep_msg s bound) <= bound -> Zlength (val_of_string s) <= bound.
  Proof.
    unfold rep_msg.
    intros s bound.
    rewrite Zlength_app.
    match goal with
    | [|- Zlength ?a + Zlength ?b <= _ -> _] =>
      pose proof (Zlength_nonneg a);
        pose proof (Zlength_nonneg b)
    end.
    omega.
  Qed.

  Lemma rep_msg_exact_length : forall s bound,
      Zlength (rep_msg s bound) <= bound -> Zlength (rep_msg s bound) = bound.
  Proof.
    intros s bound H.
    apply rep_msg_bound in H.
    unfold rep_msg.
    rewrite Zlength_app.
    autorewrite with sublist.
    omega.
  Qed.

  Lemma repeat_string_list_repeat:
    forall c n, 
      val_of_string (repeat_string c n) =
      list_repeat n (Vint (Int.repr (Z.of_nat (nat_of_ascii c)))).
  Proof.
    induction n; auto.
    simpl.
    f_equal.
    apply IHn.
  Qed.
  
End Val_String.

Section Sublist_Substring.
  Lemma sublist_of_nil {A: Type}:
    forall (n m : Z), sublist n m ([] : list A) = [].
  Proof.
    intros n m.
    revert n.
    apply Z_ind.
    - rewrite sublist_firstn.
      apply List.firstn_nil.
    - unfold sublist.
      intros p.
      rewrite skipn_nil.
      rewrite firstn_nil.
      reflexivity.
    - intros.
      unfold sublist.
      simpl.
      rewrite firstn_nil.
      reflexivity.
  Qed.

  Lemma sublist_inc1 {A: Type}:
    forall (l xs: list A) x (n m : nat),
      l = x :: xs ->
      sublist (Z.of_nat (S n)) (Z.of_nat (S m)) (x :: xs)
      = sublist (Z.of_nat n) (Z.of_nat m) xs.
  Proof.
    induction l; intros xs x n m Hl; inversion Hl.
    simpl.
    unfold sublist.
    repeat rewrite Zpos_P_of_succ_nat.
    replace (Z.succ (Z.of_nat m) - Z.succ (Z.of_nat n))
      with (Z.of_nat m - Z.of_nat n) by omega.
    repeat rewrite <- sublist_firstn.
    rewrite <- Nat2Z.inj_succ.
    repeat rewrite Nat2Z.id.
    
    replace (S n) with (n + 1)%nat by omega.
    rewrite <- skipn_drop.
    reflexivity.
  Qed.  

  Lemma sublist_inc2 {A : Type}:
    forall (l xs : list A) x n,
      l = x :: xs -> 
      sublist 0 (Z.of_nat (S n)) l = x :: (sublist 0 (Z.of_nat n) xs).
  Proof.
    induction l; intros xs x n Hl.
    - inversion Hl.
    - inversion Hl.
      repeat rewrite sublist_firstn.
      repeat rewrite Nat2Z.id.
      simpl.
      f_equal.
  Qed.

  Lemma substring_no_length:
    forall n (s : string), substring n 0 s = ""%string.
  Proof.
    induction n; intros s.
    + destruct s; auto.
    + destruct s; [reflexivity |].
      simpl.
      apply IHn.
  Qed.

  Lemma substring_firstn:
    forall s m,
      val_of_string (substring 0 m s) = sublist 0 (Z.of_nat m) (val_of_string s).
  Proof.
    induction s; intros m.
    - simpl.
      destruct m; rewrite sublist_of_nil; reflexivity.
    - simpl.
      destruct m.
      + rewrite sublist_nil_gen; try reflexivity.
      + simpl.
        rewrite Zpos_P_of_succ_nat;
          rewrite <- Nat2Z.inj_succ.
        erewrite sublist_inc2; [| reflexivity].
        rewrite IHs.
        reflexivity.
  Qed.

  Lemma substring_sublist:
    forall s n m, val_of_string (substring n m s)
             = sublist (Z.of_nat n) (Z.of_nat (n + m))
                       (val_of_string s).
  Proof.
    intros s n; revert s; induction n; intros s m.
    - simpl.
      apply substring_firstn.
    - simpl.
      destruct s.
      + simpl. rewrite sublist_of_nil. reflexivity.
      + rewrite Zpos_P_of_succ_nat;
          rewrite <- Nat2Z.inj_succ.
        rewrite Zpos_P_of_succ_nat;
          rewrite <- Nat2Z.inj_succ.
        simpl val_of_string.
        erewrite sublist_inc1; [| reflexivity].
        apply IHn.
  Qed.

End Sublist_Substring.

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
        {A Conn : Type} (p1 p2: A -> bool) (g : A -> Conn):
    forall (n : Conn),
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

  Lemma replace_when_NoDup {A Conn : Type} (p1 p2: A -> bool) (g : A -> Conn):
    forall (n : Conn),
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

  Lemma conditional_bool : forall (b : bool) c,
      (if b then c else false) = true <-> c = true /\ b = true.
  Proof.
    intros [] c; intuition.
  Qed.

  Lemma conditional_dec_true : forall (P : Prop) (b : {P} + {~P}),
      (if b then true else false) = true <-> P.
  Proof.
    intros P []; intuition.
  Qed.

End Interaction_Tree.
