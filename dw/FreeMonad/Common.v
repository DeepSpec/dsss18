(** Common effects *)

(* TODO: make handlers obviously monad morphisms *)

Set Implicit Arguments.
Set Contextual Implicit.
Generalizable All Variables.

Require Import List.
Import ListNotations.
Require Import String.
Require Fin.

From QuickChick Require Show.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.

Section Extensible.

(** Sums for extensible event types. *)

Definition sum1 (E1 E2 : Type -> Type) (X : Type) : Type :=
  E1 X + E2 X.

Inductive emptyE : Type -> Type := .

Definition swap1 `(ab : sum1 A B X) : sum1 B A X :=
  match ab with
  | inl a => inr a
  | inr b => inl b
  end.

Definition bimap_sum1 `(f : A X -> C Y) `(g : B X -> D Y)
           (ab : sum1 A B X) : sum1 C D Y :=
  match ab with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.

(* Automatic application of commutativity and associativity for sums.
   TODO: This is still quite fragile and prone to
   infinite instance resolution loops.
 *)

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

Definition run {E F X} (run_ : forall Y, F Y -> M E Y)
  : M (E +' F) X -> M E X :=
  let run' Y (e : (E +' F) Y) :=
      match e with
      | (e' |) => liftE e'
      | (| f') => run_ _ f'
      end
  in hom run'.

Section Failure.

Inductive failureE : Type -> Type :=
| Fail : string -> failureE void.

Class HasFailure (E : Type -> Type) :=
  { Fail_ : string -> E void }.

Global Instance default_HasFailure `{Convertible failureE E}
  : HasFailure E :=
  { Fail_ reason := convert (Fail reason) }.

Definition fail `{HasFailure E} {X} (reason : string)
  : M E X :=
  Vis (Fail_ reason) (fun v : void => match v with end).

End Failure.

Section NonDeterminism.

Inductive nondetE : Type -> Type :=
| Or : nondetE bool.

Class HasNondet (E : Type -> Type) := { Or_ : E bool }.

Global Instance default_HasNondet `{Convertible nondetE E}
  : HasNondet E :=
  { Or_ := convert Or }.

Definition or `{HasNondet E} {X} (k1 k2 : M E X)
  : M E X :=
  Vis Or_ (fun b : bool => if b then k1 else k2).

(* This can fail if the list is empty. *)
Definition choose `{HasNondet E} `{HasFailure E} {X}
  : list X -> M E X := fix choose' xs : M E X :=
  match xs with
  | [] => fail "choose: No choice left"
  | x :: xs =>
    or (Ret x) (choose' xs)
  end.

(* TODO: how about a variant of [choose] that expects
   a nonempty list so it can't fail? *)

(* All ways of picking one element in a list apart
   from the others. *)
Definition select {X} : list X -> list (X * list X) :=
  let fix select' pre xs :=
      match xs with
      | [] => []
      | x :: xs' => (x, pre ++ xs') :: select' (pre ++ [x]) xs'
      end in
  select' [].

End NonDeterminism.

(* Another more flexible and informative variant of [nondetE]
   (that also incorporates something like [failureE]). *)
Module NonDeterminismBis.
  Import List.

  Inductive nondetE : Type -> Type :=
  | Or : forall (n : nat), string -> nondetE (Fin.t n).

  Arguments Or n reason : clear implicits.

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

  Delimit Scope nondet_scope with nondet.
  Open Scope nondet_scope.

  Example ex_disj : M nondetE nat :=
    (disj "test" ( ret 0 | ret 1 | ret 2 )).

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

End NonDeterminismBis.

Section Reader.

Variable (R : Type).

Inductive readerE : Type -> Type :=
| Ask : readerE R.

Definition ask {E} `{Convertible readerE E} : M E R :=
  liftE (convert Ask).

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

End Reader.

Arguments ask {R E _}.

Section State.

Variable (S : Type).

Inductive stateE : Type -> Type :=
| Get : stateE S
| Put : S -> stateE unit.

Class HasState (E : Type -> Type) :=
  { Get_ : E S;
    Put_ : S -> E unit;
  }.

Global Instance default_HasState `{Convertible stateE E}
  : HasState E :=
  { Get_ := convert Get;
    Put_ s := convert (Put s);
  }.

Definition get `{HasState E} : M E S := liftE Get_.
Definition put `{HasState E} (s : S) : M E unit :=
  liftE (Put_ s).

(** TODO: Refactorable if we can generalize
    [Free.hom] to arbitrary monads. *)
CoFixpoint run_state' {E A} (s : S) (m : M (E +' stateE) A)
  : M E (S * A) :=
  match m with
  | Ret x => Ret (s, x)
  | Tau n => Tau (run_state' s n)
  | Vis (| e4 ) k =>
    match e4 in stateE T return (T -> _) -> _ with
    | Get => fun k => Tau (run_state' s (k s))
    | Put s' => fun k => Tau (run_state' s' (k tt))
    end k
  | Vis ( e |) k => Vis e (fun z => run_state' s (k z))
  end.

Definition run_state `{Convertible E (F +' stateE)} {A}
           (s : S) (m : M E A) : M F (S * A) :=
  run_state' s (hoist (@convert _ _ _) m : M (F +' stateE) A).

Definition exec_state `{Convertible E (F +' stateE)} {A}
           (s : S) (m : M E A) : M F S :=
  mapM fst (run_state s m).

Definition eval_state `{Convertible E (F +' stateE)} {A}
           (s : S) (m : M E A) : M F A :=
  mapM snd (run_state s m).

End State.

Arguments get {S E _}.
Arguments put {S E _}.

Section Counter.

Class Countable (N : Type) := { zero : N; succ : N -> N }.

Global Instance Countable_nat : Countable nat | 0 :=
  { zero := O; succ := S }.

Inductive nat' {T} (tag : T) : Type :=
| Tagged : nat -> nat' tag.

Global Instance Countable_nat' T (tag : T)
  : Countable (nat' tag) :=
  { zero := Tagged O; succ := fun '(Tagged n) => Tagged (S n) }.

(* Parameterizing by the type of counters makes it easier
   to have more than one counter at once. *)
Inductive counterE (N : Type) : Type -> Type :=
| Incr : counterE N N.

Class HasCounter N (E : Type -> Type) :=
  { Incr_ : E N }.

Global Instance default_HasCounter `{Convertible (counterE N) E}
  : HasCounter N E :=
  { Incr_ := convert Incr }.

Definition incr `{HasCounter N E} : M E N := liftE Incr_.

CoFixpoint run_counter_from' `{Countable N} {E X} (c : N)
           (m : M (E +' counterE N) X)
  : M E X :=
  match m with
  | Ret x => Ret x
  | Tau n => Tau (run_counter_from' c n)
  | Vis (| e ) k =>
    match e in counterE _ T return (T -> _) -> _ with
    | Incr => fun k => Tau (run_counter_from' (succ c) (k c))
    end k
  | Vis ( e |) k =>
    Vis e (fun z => run_counter_from' c (k z))
  end.

Definition run_counter' `{Countable N} {E X}
  : M (E +' counterE N) X -> M E X :=
  run_counter_from' zero.

Definition run_counter_using
           `{Countable N} `{Convertible E (F +' counterE N)}
           `(m : M E X) : M F X :=
  run_counter' (hoist (@convert _ _ _) m).

Definition run_counter `{Convertible E (F +' counterE nat)} X
  : M E X -> M F X := run_counter_using.

Definition run_counter_for T (tag : T)
           `{Convertible E (F +' counterE (nat' tag))} X
  : M E X -> M F X := run_counter_using.

End Counter.

Arguments run_counter_using N {_ _ _ _ _} m.
Arguments run_counter_for {T} tag {_ _ _ _} m.

Section Writer.

Variable (W : Type).

Inductive writerE : Type -> Type :=
| Tell : W -> writerE unit.

Definition tell `{Convertible writerE E} (w : W) : M E unit :=
  liftE (convert (Tell w)).

End Writer.

Section Stop.
  (* "Return" as an effect. *)

  Inductive stopE (Y : Type) : Type -> Type :=
  | Stop : Y -> stopE Y void.

  Definition stop {Y X} `{stopE Y -< E} : Y -> M E X :=
    fun y =>
      Vis (convert (Stop y)) (fun v : void => match v with end).

End Stop.

Arguments stopE Y X.
Arguments stop {Y X E _} y.

Section Trace.

Inductive traceE : Type -> Type :=
| Trace : forall X `{Show.Show X}, X -> traceE unit.

Definition trace `{traceE -< E} : string -> M E unit :=
  embed (@Trace string _).

Definition trace' `{traceE -< E} `{Show.Show X} : X -> M E unit :=
  embed (@Trace X _).

CoFixpoint ignore_trace' {E X} (m : M (E +' traceE) X)
  : M E X :=
  match m with
  | Ret x => Ret x
  | Tau m => Tau (ignore_trace' m)
  | Vis (| e ) k =>
    match e in traceE T return (T -> _) -> _ with
    | Trace _ => fun k => Tau (ignore_trace' (k tt))
    end k
  | Vis ( e |) k => Vis e (fun z => ignore_trace' (k z))
  end.

Definition ignore_trace `{Convertible E (F +' traceE)} {X}
           (m : M E X) : M F X :=
  ignore_trace' (hoist (@convert _ _ _) m).

End Trace.

(** Zipping trees, combining some effects,
    leaving others untouched and arbitrarily
    interleaved. *)
Section Zip.

Variables (E F G : Type -> Type).
Variable (X Y : Type).
Variable zipE : forall U V, E U -> F V -> M G (U * V).

CoFixpoint zipM (mE : M (E +' G) X) (mF : M (F +' G) Y)
  : M G ((X * M (F +' G) Y) + (M (E +' G) X * Y)) :=
  match mE, mF with
  | Ret x, _ => Ret (inl (x, mF))
  | _, Ret y => Ret (inr (mE, y))
  | Vis (inr g) kE, _ =>
    Vis g (fun u => zipM (kE u) mF)
  | _, Vis (inr g) kF =>
    Vis g (fun v => zipM mE (kF v))
  | Vis (inl e) kE, Vis (inl f) kF =>
    uv <- @zipE _ _ e f;;
    let (u, v) := uv : _ * _ in
    zipM (kE u) (kF v)
  | Tau nE, _ => Tau (zipM nE mF)
  | _, Tau nF => Tau (zipM mE nF)
  end.

End Zip.

Section Instances.

Import Show.
Open Scope string.

Global Instance Show_sum1 {X} `{Show (A X)} `{Show (B X)}
: Show (sum1 A B X) := {
    show ab :=
      match ab with
      | inl a => show a
      | inr b => show b
      end }.

Global Instance Show_empty X : Show (emptyE X) :=
  { show e := match e with end }.

Global Instance Show_failure X : Show (failureE X) :=
  { show e :=
      let '(Fail r) := e in ("Fail " ++ show r)%string }.

Global Instance Show_nondetE X : Show (nondetE X) :=
  { show e := "Or" }.

Global Instance Show_counterE X : Show (counterE N X) :=
  { show e := "Incr" }.

Global Instance Show_stateE S X `{Show S} : Show (stateE S X) :=
  { show e :=
      match e with
      | Get => "Get"
      | Put s => "Put " ++ show s
      end }.

Global Instance Show_trace X : Show (traceE X) :=
  { show e := let '(Trace s) := e in ("Trace " ++ show s)%string }.

End Instances.
