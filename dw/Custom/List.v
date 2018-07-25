From Coq Require Export List.
Export ListNotations.

Fixpoint take_while {A} (f : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs =>
    if f x then
      x :: take_while f xs
    else
      []
  end.

(* Helper for [picks]. *)
Fixpoint picks' {A} (xs1 xs2 : list A) : list (A * list A) :=
  match xs2 with
  | [] => []
  | x2 :: xs2' =>
    (x2, rev_append xs1 xs2') :: picks' (x2 :: xs1) xs2'
  end.

(* List of ways to pick an element out of a list. *)
Definition picks {A} (xs : list A) : list (A * list A) :=
  picks' [] xs.

Example picks_example : picks [1;2] = [(1,[2]); (2,[1])].
Proof. reflexivity. Qed.

Fixpoint filter_opt {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs =>
    match f x with
    | Some y => y :: filter_opt f xs
    | None => filter_opt f xs
    end
  end.

Fixpoint find_opt {A B} (f : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: xs =>
    match f x with
    | Some y => Some y
    | None => find_opt f xs
    end
  end.

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
