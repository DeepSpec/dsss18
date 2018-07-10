Require Export Ascii.
Require Export String.

From ExtLib Require Import
     Data.String
     Programming.Injection
     Structures.Monad.

Require Import ZArith.
Set Warnings "-extraction-opaque-accessed,-extraction,-notation-overridden,-parsing".

Require Import FMapList.
Require Import FMapFacts.
Require Export Coq.Structures.OrderedTypeEx.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation.

From Custom Require Import
     Decidability
     Show.

Require Import DeepWeb.Util.StringUtil.

Hint Resolve Dec_string : eq_dec.

(* ---------------------- *)
(* Stuff that probably belongs elsewhere... *)

Class MapEquiv (A : Type) := { map_equiv : A -> A -> Prop }.
Notation " s ≡ s' " := (map_equiv s s') (at level 60).

(* ---------------------- *)

(* TODO: Is this needed?  Or does QC provide it?  (BCP: QC does not
   provide it, but it probably should!  I've asked Leo...*)
Module String_as_OT <: UsualOrderedType.

  Definition t := string.

  Definition eq := @eq string.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Inductive lts : string -> string -> Prop :=
    | lts_empty : forall a s, lts EmptyString (String a s)
    | lts_tail : forall a s1 s2, lts s1 s2 -> lts (String a s1) (String a s2)
    | lts_head : forall (a b : ascii) s1 s2,
        lt (nat_of_ascii a) (nat_of_ascii b) ->
        lts (String a s1) (String b s2).

  Definition lt := lts.

  Lemma nat_of_ascii_inverse a b : nat_of_ascii a = nat_of_ascii b -> a = b.
  Proof.
    intro H.
    rewrite <- (ascii_nat_embedding a).
    rewrite <- (ascii_nat_embedding b).
    apply f_equal; auto.
  Qed.

  Lemma lts_tail_unique a s1 s2 : lt (String a s1) (String a s2) ->
    lt s1 s2.
  Proof.
    intro H; inversion H; subst; auto.
    remember (nat_of_ascii a) as x.
    apply NPeano.Nat.lt_irrefl in H1; inversion H1.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    induction x => y z H1 H2.
    - destruct y as [| b y']; first inversion H1.
      destruct z as [| c z']; first inversion H2.
      constructor.
    - destruct y as [| b y']; first inversion H1.
      destruct z as [| c z']; first inversion H2.
      destruct (Nat.compare (nat_of_ascii a) (nat_of_ascii b)) eqn:C1;
      destruct (Nat.compare (nat_of_ascii b) (nat_of_ascii c)) eqn:C2;
      repeat match goal with
        | [ H : _ = Datatypes.Eq |- _ ] =>
          apply NPeano.Nat.compare_eq in H;
          apply nat_of_ascii_inverse in H;
          subst; auto
        | [ H : lt (String ?X _) (String ?X _) |- _ ] =>
          apply lts_tail_unique in H
        | [ H : lt (String ?A _) (String ?B _),
            C : (nat_of_ascii ?A ?= nat_of_ascii ?B) = Gt |- _ ] =>
              inversion H; subst; clear H;
              apply nat_compare_gt in C;
              [ apply NPeano.Nat.lt_irrefl in C; exfalso; auto
              | apply NPeano.Nat.lt_asymm  in C; exfalso; auto ]
        end.
      + apply lts_tail; apply IHx with y'; auto.
      + apply lts_head; apply nat_compare_lt in C2; auto.
      + apply lts_head; apply nat_compare_lt; auto.
      + apply lts_head;
        apply nat_compare_lt in C1;
        apply nat_compare_lt in C2.
        eapply transitivity; eauto.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    induction x; intros y LT.
    - inversion LT; auto.
    - inversion LT; subst; intros EQ.
      * specialize (IHx s2 H2).
        inversion EQ; subst; auto.
        apply IHx; unfold eq; auto.
      * inversion EQ; subst; auto.
        apply NPeano.Nat.lt_irrefl in H2; auto.
  Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    generalize dependent y.
    induction x as [ | a s1]; destruct y as [ | b s2].
    - apply EQ; constructor.
    - apply LT; constructor.
    - apply GT; constructor.
    - destruct ((nat_of_ascii a) ?= (nat_of_ascii b)) eqn:ltb.
      + assert (a = b).
        {
          apply NPeano.Nat.compare_eq in ltb.
          assert (ascii_of_nat (nat_of_ascii a)
                  = ascii_of_nat (nat_of_ascii b)) by auto.
          repeat rewrite ascii_nat_embedding in H.
          auto.
        }
        subst.
        destruct (IHs1 s2).
        * apply LT; constructor; auto.
        * apply EQ. unfold eq in e. subst. constructor; auto.
        * apply GT; constructor; auto.
      + apply nat_compare_lt in ltb.
        apply LT; constructor; auto.
      + apply nat_compare_gt in ltb.
        apply GT; constructor; auto.
  Defined.

  Definition eq_dec (x y : string): {x = y} + { ~ (x = y)}.
  Proof. dec_eq. Defined.
End String_as_OT.

Module StringMap := FMapList.Make(String_as_OT).
Module StringMapProp := FMapFacts.Properties StringMap.
Module StringMapFacts := FMapFacts.Facts StringMap.

Example test_equality (m1 m2 : StringMap.t nat) :=
  StringMap.equal (fun (x y : nat) => (x = y)?) m1 m2.

Global Instance StringMap_Equiv_Dec {X}
                    (Eq : forall (x y : X), Dec (x = y))
                    (m1 m2 : StringMap.t X)
                  : Dec (StringMap.Equal m1 m2).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct (StringMap.equal (fun x y => (x = y)?) m1 m2) eqn:H.
  - left. apply StringMap.equal_2 in H.
    rewrite StringMapFacts.Equal_Equivb; eauto.
    intros x y; split.
    + intro H'; destruct dec; auto; congruence.
    + intro H'; destruct dec; auto.
  - right. intro H'.
    rewrite (@StringMapFacts.Equal_Equivb _ (fun (x y : X) => (x = y)?)) in H'; eauto.
    + apply StringMap.equal_1 in H'; congruence.
    + intros x y; destruct dec; split; auto.
      intro; congruence.
Defined.

Global Instance string_map_equiv X : MapEquiv (StringMap.t X) :=
  {| map_equiv := StringMap.Equal |}.

(* ----------------------------------------------------------------------- *)
(* A functor for generating "string synonyms" with different
   Arbitrary instances. *)

Module Type StringExamples.
  Parameter examples : list string.
  Parameter defaultGen : G string.
End StringExamples.

Module StringSynonym (Examples : StringExamples).

  Record t : Type := from_string { to_string : string }.

  Global Instance genT : Gen t :=
    {| arbitrary :=
         freq [ (1, liftGen from_string Examples.defaultGen)
              ; (9, liftGen from_string (elements "" Examples.examples))
              ]
    |}.

  Global Instance showT : Show t :=
    {| show := show ∘ to_string |}.

  Global Instance shrinkT : Shrink t :=
    {| shrink p := let '(from_string s) := p in map (fun s => from_string s) (shrink s) |}.

  (* Needed because UsualOrderedType defines a component t! *)
  Definition str := t.
  Module as_OT <: UsualOrderedType.
    Definition t := str.

    Definition eq := @eq str.
    Definition eq_refl := @eq_refl t.
    Definition eq_sym := @eq_sym t.
    Definition eq_trans := @eq_trans t.

    Inductive lts : str -> str -> Prop :=
      | lts_str : forall s1 s2, String_as_OT.lts s1 s2 -> lts (from_string s1) (from_string s2).

    Definition lt := lts.

    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof.
      unfold t. intros. inversion H. inversion H0. subst. inversion H5. subst.
      apply lts_str. eapply String_as_OT.lt_trans; eassumption. Qed.

    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof.
      unfold t. intros. inversion H. unfold not.
      intro C. inversion C. generalize H4.
      apply String_as_OT.lt_not_eq. assumption. Qed.

    Definition compare x y : Compare lt eq x y.
    Proof.
      destruct x as [s]. destruct y as [s0].
      destruct (String_as_OT.compare s s0).
      - apply LT. apply lts_str; assumption.
      - apply EQ. rewrite e. reflexivity.
      - apply GT. apply lts_str; assumption.
    Qed.

    Definition eq_dec : forall (x y : str), {x = y} + { ~ (x = y)}.
    Proof. intros; dec_eq. Defined.
  End as_OT.
  Hint Resolve as_OT.eq_dec : eq_dec.

  Global Instance t_Eq (x y : t) : Dec (x = y).
  Proof. dec_eq. Defined.

  Global Instance t_from_string_injection : Injection string t :=
    { inject := from_string }.
  Global Instance t_to_string_injection : Injection t string :=
    { inject := to_string }.

  Module Map := FMapList.Make(as_OT).
  Module MapProp := FMapFacts.Properties Map.
  Module MapFacts := FMapFacts.Facts Map.

  Global Instance Map_Equiv_Dec {X} (Eq : forall (x y : X), Dec (x = y)) (m1 m2 : Map.t X) : Dec (Map.Equal m1 m2).
  Proof.
    constructor. unfold ssrbool.decidable.
    destruct (Map.equal (fun x y => (x = y)?) m1 m2) eqn:H.
    - left. apply Map.equal_2 in H.
      rewrite MapFacts.Equal_Equivb; eauto.
      intros x y; split.
      + intro H'; destruct dec; auto; congruence.
      + intro H'; destruct dec; auto.
    - right. intro H'.
      rewrite (@MapFacts.Equal_Equivb _ (fun (x y : X) => (x = y)?)) in H'; eauto.
      + apply Map.equal_1 in H'; congruence.
      + intros x y; destruct dec; split; auto.
        intro; congruence.
  Defined.

  Definition t_eq (a b : t) : bool :=
    match a,b with
    | from_string sa, from_string sb => if string_dec sa sb then true else false
    end.

  Global Instance t_map_equiv X : MapEquiv (Map.t X) :=
    {| map_equiv := Map.Equal |}.

  Definition app (a b : t) : t :=
    from_string (to_string a ++ to_string b).

  Arguments Map.empty {elt}.

End StringSynonym.
