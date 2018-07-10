From Custom Require Import
     Decidability.

Require Import DeepWeb.Util.Common.

Inductive fresh_for: list nat -> nat -> Prop :=
| nil_fresh: forall n, fresh_for nil n
| cons_fresh: forall n n' l,
    fresh_for l n -> n <> n' -> fresh_for (n' :: l) n.
(* FIXME: The following derivation fails with new QuickChick. *)
(* Derive ArbitrarySizedSuchThat for (fun n => fresh_for l n). *)

Ltac destruct_eq a b H :=
  destruct (a =? b) eqn:H;
  first [apply beq_nat_true in H; subst | apply beq_nat_false in H].

Instance fresh_for_dec l n: Dec (fresh_for l n).
Proof.
  constructor. unfold ssrbool.decidable.
  induction l.
  - repeat constructor.
  - destruct IHl. destruct_eq a n Heq.
    + right. intro. inversion H. congruence.
    + left. constructor; auto.
  - right. intro. inversion H. contradiction.
Defined.

Lemma fresh_for_inv: forall a b l,
    fresh_for (a :: l) b -> fresh_for l b.
Proof.
  inversion 1; auto.
Qed.

Ltac fresh_tac :=
  match goal with
  | [H: fresh_for (?n :: _) ?n |- _] => inversion H; congruence
  | [H1: ?X -> False , H2: ?X |- _ ] => contradiction
  | [H1: ~ ?X , H2: ?X |- _ ] => contradiction
  end.
