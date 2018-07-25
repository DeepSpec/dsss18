Generalizable Variables A B C D E F.

Require Import List.
Import ListNotations.
Require Import String.
Require Fin.

From QuickChick Require Show.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Internal.
Import MonadNotations.

Section Extensible.

(** * Combinators for Extensible Event Types *)

(* BCP: Move all the Convertible stuff to another file.  At the top of
   this file, but just an informal comment explaining +' and -< *)

(* Union of two effect types. *)
Definition sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
  E1 X + E2 X.

(* Empty effect type. *)
Inductive emptyE : Type -> Type := .

(* Automatic application of commutativity and associativity for sums.

   TODO: This is still quite fragile and prone to infinite instance
   resolution loops. *)

Class Convertible (A B : Type -> Type) :=
  { convert : forall {X}, A X -> B X }.

(* Don't try to guess. *)
Global Instance fluid_id A : Convertible A A | 0 :=
  { convert X a := a }.

(* Destructure sums. *)
Global Instance fluid_sum `{Convertible A C} `{Convertible B C}
  : Convertible (sum1 A B) C | 7 :=
  { convert X ab :=
      match ab with
      | inl a => convert a
      | inr b => convert b
      end }.

(* Lean left by default for no reason. *)
Global Instance fluid_left `{Convertible A B} C
  : Convertible A (sum1 B C) | 8 :=
  { convert X a := inl (convert a) }.

(* Very incoherent instances. *)
Global Instance fluid_right `{Convertible A C} B
  : Convertible A (sum1 B C) | 9 :=
  { convert X a := inr (convert a) }.

Global Instance fluid_empty A : Convertible emptyE A :=
  { convert X v := match v with end }.

End Extensible.

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

(** ** Nondeterminism *)

(* BCP: Needs some kind of introduction

   We show a minimized module signature for the sake of brevity.
   The implementation is at the end of this file. *)

Module Type NonDeterminismSig.

  (* A branching computation with [n] possible futures.
     The constructor can be annotated with a string to help
     debugging. *)

  Inductive nondetE : Type -> Type :=
  | Or : forall (n : nat), string -> nondetE (Fin.t n).
  (* BCP: What does the Fin.t do (why not just return nat)?  Where do
     we use it? (Answer: It simplifies some proofs.  Let's leave it
     and just explain what it means.) *)

  (* [Or] nodes can have no children ([n = 0]).  (We use only this
     version of [fail] in the swap server development -- the one above
     is just an example.) *)
  Parameter fail :
    forall {E A} `{nondetE -< E},
      string (* reason *) -> M E A.

  (* Disjunction between two ITrees *)
  Parameter or :
    forall {E A} `{nondetE -< E},
      M E A -> M E A -> M E A.

  (* Notation for disjunction between [n] ITrees, optionally annotated
     with an explanation string. *)
  Reserved Notation "'disj' reason ( f1 | .. | fn )"
  (at level 0, reason at next level).
  Reserved Notation "'disj' ( f1 | .. | fn )"
  (at level 0).

  (* ITree that nondeterministically chooses an element from a list
     and returns it. *)
  Parameter choose :
    forall {E A} `{nondetE -< E},
      string (* reason *) -> list A -> M E A.

  (* ITree that nondeterministically removes one element from a list
     and returns it with the rest of the list. *)
  Parameter pick_one :
    forall {E A} `{nondetE -< E},
      string -> list A -> M E (A * list A).

  (* BCP: The un-similarity of names between [choose] and [pick-one]
     is unfortunate!  (Rename pick_one to choose_) *)
End NonDeterminismSig.

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

(****************************** Internals ***************************)

(* Implementation of the nondeterminism signature. *)

Module NonDeterminism <: NonDeterminismSig.
  Import List.

  (* Nodes can be of any arity. They are annotated with
     a string to help debugging. *)
  Inductive nondetE : Type -> Type :=
  | Or : forall (n : nat), string -> nondetE (Fin.t n).

  Arguments Or n reason : clear implicits.

  (* [Or] nodes can have no children ([n = 0]), like [failureE]. *)
  Definition fail {E A} `{nondetE -< E}
             (reason : string) : M E A :=
    Vis (convert (Or 0 reason))
        (fun f => match f : Fin.t 0 with end).

  Fixpoint ix {A} (xs : list A) (i : Fin.t (List.length xs)) : A.
  Proof.
    destruct xs as [| x xs']; inversion i as [ | ? i' ].
    - apply x.
    - apply (ix _ xs' i').
  Defined.

  (* Choose one element in a list. *)
  Definition choose {E A} `{nondetE -< E}
             (reason : string) (xs : list A) : M E A :=
    Vis (convert (Or (length xs) reason)) (fun i => Ret (ix xs i)).

  Definition noFinZ {A} (m : Fin.t O) : A := match m with end.

  (* Extend a continuation indexed by [Fin.t] with a new case. *)
  Definition or_ {E A n} (f1 : M E A) (f2 : Fin.t n -> M E A)
             (m : Fin.t (S n)) : M E A :=
    match m in Fin.t n0 return
          match n0 with
          | O => False : Type
          | S n0 => (Fin.t n0 -> Fin.t n)
          end -> _ with
    | Fin.F1 => fun _ => f1
    | Fin.FS m => fun id => f2 (id m)
    end (fun x => x).

  Definition VisOr {E A n} `{nondetE -< E}
             (reason : string) (k : Fin.t n -> M E A) :
    M E A := Vis (convert (Or n reason)) k.

  Notation "'disj' reason ( f1 | .. | fn )" :=
    (VisOr reason (or_ f1 .. (or_ fn noFinZ) ..))
  (at level 0, reason at next level) : nondet_scope.

  Notation "'disj' ( f1 | .. | fn )" :=
    (VisOr "" (or_ f1 .. (or_ fn noFinZ) ..))
  (at level 0) : nondet_scope.

  Delimit Scope nondet_scope with nondet.
  Open Scope nondet_scope.

  Example ex_disj : M nondetE nat :=
    (disj "test" ( ret 0 | ret 1 | ret 2 )).

  Definition or {E A} `{nondetE -< E} (t1 t2 : M E A) : M E A :=
    disj ( t1 | t2 ).

  (* Remove an element from a list, also returning the remaining
     elements. *)

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

  (* [picks] embedded in a tree. *)
  Definition pick_one {E A} `{nondetE -< E}
             (reason : string) (xs : list A) : M E (A * list A) :=
    choose reason (picks xs).

  (* A few helpers for [Fin.t]. *)

  (* A list of [Fin.t]. *)
  Definition every_fin (m : nat) : list (Fin.t m) :=
    (fix every_fin m n :=
       match n return (Fin.t n -> Fin.t m) -> list (Fin.t m) with
       | O => fun _ => []
       | S n' => fun k =>
         k (@Fin.F1 n') :: every_fin m n' (fun i => k (Fin.FS i))
       end) m m (fun i => i).

  (* Convert a [nat] to a [Fin.t] without too much care. *)
  Fixpoint to_fin {n : nat} (m : nat) : option (Fin.t n) :=
    match n, m return option (Fin.t n) with
    | O, _ => None
    | S n, O => Some Fin.F1
    | S n, S m => option_map Fin.FS (to_fin m)
    end.

  (* Convert a [nat] to a [Fin.t] with even less care. *)
  Fixpoint to_fin' {n : nat} (m : nat) : Fin.t (S n) :=
    match n, m return Fin.t (S n) with
    | O, _ => Fin.F1
    | S n, O => Fin.F1
    | S n, S m => Fin.FS (to_fin' m)
    end.

End NonDeterminism.
