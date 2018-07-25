(** Combinators for Extensible Event Types *)

Generalizable Variables A B C D E.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Internal.

(* Union of two effect types. *)
Definition sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
  E1 X + E2 X.

(* Empty effect type. *)
Inductive emptyE : Type -> Type := .

(* Automatic application of commutativity and associativity for sums.

   TODO: This is still quite fragile and prone to infinite instance
   resolution loops. *)
(* BCP: This problem has been flagged for a while, and Gregory seems
   to be very interested in using this stuff in the new ITree
   repo... do we have ideas for how to make it more robust? *)

Class Convertible (A B : Type -> Type) :=
  { convert : forall {X}, A X -> B X }.

(* Don't try to guess. *)
Instance fluid_id A : Convertible A A | 0 :=
  { convert X a := a }.

(* Destructure sums. *)
Instance fluid_sum `{Convertible A C} `{Convertible B C}
  : Convertible (sum1 A B) C | 7 :=
  { convert X ab :=
      match ab with
      | inl a => convert a
      | inr b => convert b
      end }.

(* Lean left by default for no reason. *)
Instance fluid_left `{Convertible A B} C
  : Convertible A (sum1 B C) | 8 :=
  { convert X a := inl (convert a) }.

(* Very incoherent instances. *)
Instance fluid_right `{Convertible A C} B
  : Convertible A (sum1 B C) | 9 :=
  { convert X a := inr (convert a) }.

Instance fluid_empty A : Convertible emptyE A :=
  { convert X v := match v with end }.

Notation "E1 +' E2" := (sum1 E1 E2)
(at level 50, left associativity) : type_scope.

Notation "E ++' EE" := (List.fold_left sum1 EE E)
(at level 50, left associativity) : type_scope.

Notation "E -< F" := (Convertible E F)
(at level 90, left associativity) : type_scope.

Module Import SumNotations.

(* Is this readable? *)
(* Readable, yes.  Understandable (i.e., can I guess what it's
   for?), not really. *)

Delimit Scope sum_scope with sum.
Bind Scope sum_scope with sum1.

Notation "(| x )" := (inr x) : sum_scope.
Notation "( x |)" := (inl x) : sum_scope.
Notation "(| x |)" := (inl (inr x)) : sum_scope.
Notation "( x ||)" := (inl (inl x)) : sum_scope.
Notation "(| x ||)" := (inl (inl (inr x))) : sum_scope.
Notation "( x |||)" := (inl (inl (inl x))) : sum_scope.
Notation "(| x |||)" := (inl (inl (inl (inr x)))) : sum_scope.
Notation "( x ||||)" := (inl (inl (inl (inl x)))) : sum_scope.
Notation "(| x ||||)" :=
  (inl (inl (inl (inl (inr x))))) : sum_scope.
Notation "( x |||||)" :=
  (inl (inl (inl (inl (inl x))))) : sum_scope.
Notation "(| x |||||)" :=
  (inl (inl (inl (inl (inl (inr x)))))) : sum_scope.
Notation "( x ||||||)" :=
  (inl (inl (inl (inl (inl (inl x)))))) : sum_scope.
Notation "(| x ||||||)" :=
  (inl (inl (inl (inl (inl (inl (inr x))))))) : sum_scope.
Notation "( x |||||||)" :=
  (inl (inl (inl (inl (inl (inl (inl x))))))) : sum_scope.

End SumNotations.

Open Scope sum_scope.

Definition lift {E F X} `{Convertible E F} : M E X -> M F X :=
  hoist (@convert _ _ _).

Class Embed X Y :=
  { embed : X -> Y }.

Instance Embed_fun A X Y `{Embed X Y} : Embed (A -> X) (A -> Y) :=
  { embed := fun x a => embed (x a) }.

Instance Embed_eff E F X `{Convertible E F} : Embed (E X) (M F X) :=
  { embed := fun e => liftE (convert e) }.

Arguments embed {X Y _} e.

Notation "^ x" := (embed x) (at level 80).
