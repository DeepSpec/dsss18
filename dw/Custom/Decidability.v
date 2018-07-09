(** Extracted from QuickChick *)
(* TODO: Why? *)

From mathcomp.ssreflect Require Import ssreflect ssrbool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

(* Class wrapper around "decidable" *)
(* begin decidable_class *)
Class Dec (P : Prop) : Type := { dec : decidable P }.
(* end decidable_class *)

Global Instance Dec_neg {P} {H : Dec P} : Dec (~ P).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D; auto.
Defined.

Global Instance Dec_conj {P Q} {H : Dec P} {I : Dec Q} : Dec (P /\ Q).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; auto;
      right; intro; destruct H; contradiction.
Defined.

Global Instance Dec_disj {P Q} {H : Dec P} {I : Dec Q} : Dec (P \/ Q).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; auto;
      right; intro; destruct H; contradiction.
Defined.

(* BCP: Not clear this is a good idea, but... *)
(* Leo: Should be ok with really low priority *)
Global Instance Dec_impl {P Q} {H : Dec P} {I : Dec Q} : Dec (P -> Q) | 100.
Proof.
  constructor. unfold decidable.
  destruct H as [D]. destruct D; destruct I as [D]; destruct D; auto.
  left. intros. contradiction. 
Defined.

Global Instance Dec_In {A} (Eq: forall (x y : A), Dec (x = y))
         (x : A) (l : list A) : Dec (In x l) := 
  {| dec := in_dec (fun x' y' => @dec _ (Eq x' y')) x l |}.

Theorem dec_if_dec_eq {A} (x y: A): Dec (x = y) -> {x = y} + {x <> y}.
Proof.
  intros. inversion H as [D].
  unfold decidable in D. assumption.
Defined.

Hint Resolve dec_if_dec_eq: eq_dec.

Ltac dec_eq :=
  repeat match goal with
         | [ |- _ ] => solve [auto with eq_dec]
         | [ |- Dec _ ] => constructor
         | [ |- context[decidable _] ] => unfold decidable

         | [ H: context[decidable _] |- _ ] => unfold decidable in H

         | [ |- {?x = ?y} + {?x <> ?y} ] =>
           multimatch goal with
             | [ H: forall x y, Dec _ |- _ ] => apply H
             | [ H: Eq _ |- _ ] => apply H
             | [ |- _ ] => decide equality
           end
         end.

(* Lifting common decidable instances *)
Global Instance Dec_eq_bool (x y : bool) : Dec (x = y).
Proof. dec_eq. Defined.

Global Instance Dec_eq_nat (m n : nat) : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_eq_opt (A : Type) (m n : option A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_eq_prod (A B : Type) (m n : A * B)
  `{_ : forall (x y : A), Dec (x = y)} 
  `{_ : forall (x y : B), Dec (x = y)} 
  : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_eq_list (A : Type) (m n : list A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.

Hint Resolve ascii_dec: eq_dec.
Hint Resolve string_dec: eq_dec.

Global Instance Dec_ascii (m n : Ascii.ascii) : Dec (m = n).
Proof. dec_eq. Defined.

Global Instance Dec_string (m n : string) : Dec (m = n).
Proof. dec_eq. Defined.

(* Everything that uses the Decidable Class *)
Require Import DecidableClass.

Instance dec_class_dec P (H : Decidable P): Dec P.
Proof.
  constructor; destruct H; destruct Decidable_witness.
  - left; auto.
    apply Decidable_spec; auto.
  - right => H; eauto.
    apply Decidable_spec in H.
    inversion H.
Defined.

(* Not sure about the level or binding, but good idea *)
Notation "P '?'" := (match (@dec P _) with 
                       | left _ => true
                       | right _ => false
                     end) (at level 100).

Hint Resolve Dec_eq_bool : eq_dec.
Hint Resolve Dec_eq_nat : eq_dec.
Hint Resolve Dec_eq_opt : eq_dec.
Hint Resolve Dec_eq_prod : eq_dec.
Hint Resolve Dec_eq_list : eq_dec.
Hint Resolve Dec_string : eq_dec.
