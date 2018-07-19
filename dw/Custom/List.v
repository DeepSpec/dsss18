From Coq Require Export List.
Export ListNotations.

Definition replace_when {A : Type} (f : A -> bool) (new : A) (l : list A) :=
  List.fold_right
    (fun a tail => (if f a then new else a) :: tail)
    [] l.

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

Lemma filter_incl:
  forall {A} (p : A -> bool) l, incl (filter p l) l.
Proof.
  unfold incl.
  intros ? ? ? ? HIn.
  rewrite filter_In in HIn.
  destruct HIn; assumption.
Qed.

Lemma same_key_preserves_NoDup:
  forall (T U : Type) (g : T -> U) (t t' : T) (prefix suffix : list T),
    g t = g t' ->
    NoDup (map g (prefix ++ t :: suffix)) ->
    NoDup (map g (prefix ++ t' :: suffix)).
Proof.
  intros T U g t t' prefix suffix Heq HNoDup.
  rewrite map_app in *.
  simpl in *.
  rewrite <- Heq.
  trivial.
Qed.
