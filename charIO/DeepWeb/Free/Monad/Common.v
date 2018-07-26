(** More common effects (see [Effect.v] first) *)

(* TODO: make handlers obviously monad morphisms *)

Set Implicit Arguments.
Set Contextual Implicit.
Generalizable All Variables.

Require Import String.
From Custom Require Import List.
Import ListNotations.

From QuickChick Require Show.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Internal.
Require Export DeepWeb.Free.Monad.Effect.
Import MonadNotations.
Import SumNotations.

Export Failure.
Export Reader.
Export Writer.
Export NonDeterminism.

Definition run {E F X} (run_ : forall Y, F Y -> M E Y)
  : M (E +' F) X -> M E X :=
  let run' Y (e : (E +' F) Y) :=
      match e with
      | (e' |) => liftE e'
      | (| f') => run_ _ f'
      end
  in hom run'.

Module Type FancyNonDeterminismSig.

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
End FancyNonDeterminismSig.

Module FancyNonDeterminism <: FancyNonDeterminismSig.
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
    Vis (convert (Or (List.length xs) reason))
        (fun i => Ret (ix xs i)).

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

  Definition upgrade_or {E A} `{nondetE -< E}
             (e : NonDeterminism.nondetE A) : M E A :=
    match e with
    | NonDeterminism.Or => or (ret true) (ret false)
    end.
End FancyNonDeterminism.

Module Export State.
Include Effect.State.

CoFixpoint run_state' {S E A} (s : S) (m : M (E +' stateE S) A)
  : M E (S * A) :=
  match m with
  | Ret x => Ret (s, x)
  | Tau n => Tau (run_state' s n)
  | Vis (| e4 ) k =>
    match e4 in stateE _ T return (T -> _) -> _ with
    | Get => fun k => Tau (run_state' s (k s))
    | Put s' => fun k => Tau (run_state' s' (k tt))
    end k
  | Vis ( e |) k => Vis e (fun z => run_state' s (k z))
  end.

Definition run_state {S} `{Convertible E (F +' stateE S)} {A}
           (s : S) (m : M E A) : M F (S * A) :=
  run_state' s (hoist (@convert _ _ _) m : M (F +' stateE S) A).

Definition exec_state {S} `{Convertible E (F +' stateE S)} {A}
           (s : S) (m : M E A) : M F S :=
  mapM fst (run_state s m).

Definition eval_state {S} `{Convertible E (F +' stateE S)} {A}
           (s : S) (m : M E A) : M F A :=
  mapM snd (run_state s m).

Arguments get {S E _}.
Arguments put {S E _}.

End State.

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

Definition incr `{counterE N -< E} : M E N := embed Incr.

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
