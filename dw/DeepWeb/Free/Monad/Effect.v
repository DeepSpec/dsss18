Generalizable Variables E.

Require Import List.
Import ListNotations.
Require Import String.
Require Fin.

From QuickChick Require Show.
From Custom Require Import List.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Internal.
Require Export DeepWeb.Free.Monad.OpenUnion.
Import MonadNotations SumNotations.

(* Effect types can be combined using the [+'] operator:
   [E +' F] is the disjoint union of effects [E] and [F].

   We have a typeclass [-<] ("convertible") such that
   there is an instance of [E -< S] if [S] is a sum
   constructed using [+'] and one of the operands is [E].
   For example, the following instances are available:

   [E -< E]
   [E -< (F +' E)]
   [E -< (E +' F)]
   [E -< (E +' F +' G)]

   If [E -< S], the function [convert] injects an effect [E]
   into the sum [S]:

   [convert : E X -> S X]

   The function [embed] further wraps an effect as a tree:

   [embed : E X -> M S X]

   [embed] can also transform unapplied or partially-applied
   constructors.

   [embed : (I -> E X) -> (I -> M S X)]
   [embed : (I -> J -> E X) -> (I -> J -> M S X)]

   Using [-<], we can write functions that are polymorphic
   over all sums containing containing some effects.
   For example, [fail] (defined just below) can be used in any
   tree that includes the [failureE] effect:

   [fail : forall E `{failureE -< E}, string -> M E S]

 *)


(** * Basic Effects *)

(** ** Failure *)
Module Failure.

  (* The [void] result type means this effect can never return.
     (It corresponds to an ITree with no children.) *)
  Inductive failureE : Type -> Type :=
  | Fail : string -> failureE void.

  (* An itree with no children can have any leaf type [X]. *)
  Definition fail `{failureE -< E} {X} (reason : string)
    : M E X :=
    Vis (convert (Fail reason)) (fun v : void => match v with end).

End Failure.

(** ** Nondeterminism *)
Module NonDeterminism.
Import Failure.

Inductive nondetE : Type -> Type :=
| Or : nondetE bool.

Definition or {E} `{nondetE -< E} {X} (k1 k2 : M E X)
  : M E X :=
  Vis (convert Or) (fun b : bool => if b then k1 else k2).

(* This can fail if the list is empty. *)
Definition choose {E} `{failureE -< E} `{nondetE -< E} {X}
  : list X -> M E X := fix choose' xs : M E X :=
  match xs with
  | [] => fail "choose: No choice left"
  | x :: xs =>
    or (Ret x) (choose' xs)
  end.

Global Notation "'disj' ( x | .. | y | z )" :=
  (or x .. (or y z) ..) : nondet_scope.

Delimit Scope nondet_scope with nondet.

End NonDeterminism.

(** ** Mutable state *)
Module State.
Section StateSection.

Variable (S : Type).

Inductive stateE : Type -> Type :=
| Get : stateE S
| Put : S -> stateE unit.

Definition get `{stateE -< E} : M E S := embed Get.
Definition put `{stateE -< E} : S -> M E unit := embed Put.
End StateSection.

Arguments Get {S}.
Arguments Put {S}.

End State.

(** ** Immutable State ([Reader]) *)

Module Reader.
Section ReaderSection.

(* Type of the global constant. *)
Variable (R : Type).

(* Access the constant. *)
Inductive readerE : Type -> Type :=
| Ask : readerE R.

Definition ask {E} `{readerE -< E} : M E R :=
  liftE (convert Ask).

(* Given a value [r] we can remove all [Ask] nodes, passing
   [r] to each continuation. *)
CoFixpoint run_reader {E A} (r : R) (m : M (E +' readerE) A)
  : M E A :=
  match m with
  | Ret a => Ret a
  | Vis (| e ) k =>
    match e in readerE T return (T -> _) -> _ with
    | Ask => fun k => Tau (run_reader r (k r))
    end k
  | Vis ( e |) k => Vis e (fun z => run_reader r (k z))
  | Tau m => Tau (run_reader r m)
  end.

End ReaderSection.

Arguments ask {R E _}.

End Reader.

(** ** Output ([Writer]) *)

Module Writer.
Section WriterSection.

(* Output type *)
Variable (W : Type).

Inductive writerE : Type -> Type :=
| Tell : W -> writerE unit.

Definition tell `{Convertible writerE E} (w : W) : M E unit :=
  liftE (convert (Tell w)).

End WriterSection.

Arguments tell {W E _} w.

End Writer.

(* Note that [stateE S] as a sum type is equivalent to
   [readerE S +' writerE S]. However they differ in the way
   they are interpreted: a [get] is assumed to get the value
   of the last [put], whereas [ask] is always going to return
   the same value. *)
