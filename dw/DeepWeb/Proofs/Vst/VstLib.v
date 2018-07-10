Require Import String.

Require Import VST.floyd.proofauto.

Require Import DeepWeb.Proofs.Vst.VstInit.

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


Lemma split_data_app:
  forall (n1 n2 : Z) (prefix suffix : list val) (ptr : val)
    (sh : share),
    0 <= n1 <= n2 ->
    Zlength prefix = n1 ->
    Zlength suffix = n2 - n1 ->
    data_at sh (Tarray tuchar n2 noattr) (prefix ++ suffix) ptr =              
    data_at sh (Tarray tuchar n1 noattr)
            prefix ptr *
    data_at sh (Tarray tuchar (n2 - n1) noattr)
            suffix (field_address0 (Tarray tuchar n2 noattr)
                                   [ArraySubsc n1] ptr).
Proof.
  intros n1 n2 prefix suffix ptr sh [? ?] prefix_len suffix_len.
  remember (prefix ++ suffix) as buffer.
  assert (prefix = sublist 0 n1 buffer) as prefix_eq.
  {
    rewrite Heqbuffer.
    rewrite sublist_app1; [| omega..].
    rewrite <- prefix_len.
    rewrite sublist_same; auto.
  }
  assert (suffix = sublist n1 n2 buffer) as suffix_eq.
  {
    rewrite Heqbuffer.
    rewrite sublist_app2; [| omega].
    rewrite sublist_same; [auto | omega |].
    rewrite prefix_len.
    auto.
  }
  rewrite prefix_eq.
  rewrite suffix_eq.
  apply split2_data_at_Tarray_tuchar; [omega |].
  subst; rewrite Zlength_app; omega.
Qed.

Lemma data_at__Tarray_Vundef:
  forall n sh attr ptr,
    data_at sh (Tarray tuchar n attr)
            (list_repeat (Z.to_nat n) Vundef)
            ptr
    = data_at_ sh (Tarray tuchar n attr) ptr.
Proof.
  intros.
  unfold data_at_.
  unfold field_at_.
  unfold default_val.
  simpl.
  reflexivity.
Qed.

Lemma split_data_with_undefined_tail:
  forall (n1 n2 : Z) (prefix suffix : list val) (ptr : val) (sh : share),
    0 <= n1 <= n2 ->
    n1 = Zlength prefix ->
    suffix = list_repeat (Z.to_nat (n2 - n1)) Vundef ->
    data_at sh (Tarray tuchar n2 noattr) (prefix ++ suffix) ptr =              
    data_at sh (Tarray tuchar n1 noattr)
            prefix ptr *
    data_at_ sh (Tarray tuchar (n2 - n1) noattr)
             (field_address0 (Tarray tuchar n2 noattr)
                             [ArraySubsc n1] ptr).
Proof.
  intros.
  rewrite <- data_at__Tarray_Vundef.
  rewrite H1.
  pose proof split_data_app as Hsplit.
  unfold tarray in Hsplit.
  rewrite split_data_app with (n1 := n1); auto.
  rewrite Zlength_list_repeat; omega.
Qed.


Definition malloc_tokens (t : type) (ptrs : list val) :=
  fold_right (fun ptr a => sepcon a (malloc_token Tsh t ptr)) emp ptrs.

Lemma cons_malloc_tokens (t : type) (ptrs : list val) (ptr : val):
  malloc_tokens t ptrs * malloc_token Tsh t ptr
  = malloc_tokens t (ptr :: ptrs).
Proof.
  unfold malloc_tokens.
  rewrite fold_right_cons.
  reflexivity.
Qed.