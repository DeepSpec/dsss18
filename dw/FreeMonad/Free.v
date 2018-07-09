(* The abstract Monad infrastructure  *)
(* TODO: Can we describe it a little more detail? *)

Set Implicit Arguments.
Set Contextual Implicit.

Require Import List.
Import ListNotations.

From Custom Require Export
     Monad.
Import MonadNotations.
Open Scope monad_scope.

(** An [M E X] is the denotation of a program as coinductive (possibly
    infinite) tree where the leaves are labeled with [X] and every node
    is either a [Tau] node with one child, or a branching node [Vis]
    with a visible event [E Y] that branches on the values of [Y]. *)
CoInductive M (Event : Type -> Type) X := 
| Ret (x:X)
| Vis {Y: Type} (e : Event Y) (k : Y -> M Event X)
| Tau (k: M Event X).

Definition liftE Event X (e : Event X) : M Event X :=
  Vis e (fun x => Ret x).

(** Note: One could imagine an alternative definition with an explicit
    Bind constructor (and a Prim constructor), but this might not be
    as nice / might not work at all -- this way makes productivity
    easier to deal with.  (Also, this one can be turned into a real
    monad.)  We should compare at some point. *)

(** [M] is known as the "Freer monad".

    "Freer Monads, More Extensible Effects",
    Oleg Kiselyov, Hiromi Ishii.

    The [Vis] constructor corresponds to a free functor construction
    also called Co-Yoneda or left Kan extension.
    Note that [Event] is meant to be an indexed type, and generally
    not a functor, but we have a monad in any case.

    Some relevant links to variations of this theme can be found in
    http://reddit6.com/r/haskell/comments/7q4sku/are_people_using_freer_monads_or_still_mostly/

    Another way to derive this is to consider "normal forms"
    resulting from rewriting [(m >>= k) >>= h] to [m >>= (k >=> h)].
    *)

(** The existence of [spin] makes this not quite free:
    amounts more or less to an additional [Event Void]
    constructor.

    - [go x = f x >>= go] when [f x] is "opaque".
      If [f x = Ret x], [go x = Ret x >>= go = go x] loops.
      We can check the absence of that case by inspecting [f].
    - A minor problem is if [f x = match x with ...]:
      even if there is a non-[Ret] constructor for all values of [x],
      this will fail [go]'s guardedness check; a CPS transformation
      ([CoDensity] in Haskell) fixes that.
    - A variant of the first point,
      [f x = if ... then Ret (g x) else (something with Vis)],
      where we may know that iterating [g] eventually breaks the
      condition... Not much to be done.
    - To interpret effects, we must replace them with [Tau]
      (same problem as [filter] for infinite streams).
  *)

(* Just another way to parameterize effects?
   - Inductive [M]?
   - Just use transformers over an abstract monad?

     Can't specify infinite computations
     There could be some
     [loop : (A -> M A) -> M' Void] function, but then
     we might as well be [M'].

     [M] as a coinductive type also computes: we can [simpl]
     and handle the effects one by one in a proof. *)

Module Core.

(** [M E] forms a [Monad] *)
Definition bind_body {E X Y}
           (s : M E X)
           (go : M E X -> M E Y)
           (t : X -> M E Y) : M E Y :=
  match s with
  | Ret x => t x
  | Vis e k => Vis e (fun y => go (k y))
  | Tau k => Tau (go k)
  end.

Definition bindM {E X Y} (s: M E X) (t: X -> M E Y) : M E Y :=
  (cofix go (s : M E X) :=
      bind_body s go t) s.

(* This is a Monad, but inserting [Tau] will be
   more convenient. *)
Definition Monad_M E : Monad (M E) :=
  Build_Monad (M E)
              (fun X x => Ret x)
              (@bindM E).

End Core.

(** We insert a Tau in the Ret case to make programs/specifications
    neater. This makes [M] no longer a monad structurally,
    but it remains one in a looser sense as long as Tau is
    interpreted as the identity. *)
Definition bindM {E X Y} (s: M E X) (t: X -> M E Y) : M E Y :=
  Core.bindM s (fun x => Tau (t x)).

Instance Monad_M E : Monad (M E) := { ret X x := Ret x; bind := @bindM E }.

Definition mapM {E X Y} (f: X -> Y) (s: M E X) : M E Y :=
let cofix go (s : M E X) := 
    match s with
    | Ret x => Ret (f x)
    | Vis e k => Vis e (fun y => go (k y))
    | Tau k => Tau (go k)
    end
in go s.

Fixpoint forM {M : Type -> Type} {MM : Monad M} {X Y}
         (xs : list X) (f : X -> M Y)
  : M (list Y) :=
  match xs with
  | [] => ret []
  | x :: xs => y <- f x;; ys <- forM xs f;; ret (y :: ys)
  end.

Definition ignore {E X} : M E X -> M E unit := mapM (fun _ => tt).

CoFixpoint spin {E} {X} : M E X := Tau spin.
Definition tick {E} : M E unit := Tau (Ret tt).

(** The void type is useful as a return type to [M] to enforce
    infinite programs *)
Inductive void : Type := .

CoFixpoint forever {E} {X} (x : M E X) : M E void :=
  x ;; forever x.

(** If we can interpret the events of one such monad as
    computations in another, we can extend that
    interpretation to the whole monad.
    (Like Haskell foldMap.  Could be extended with a tau in
    another monad M2...?)  Needed? Looks like so. *)
(** Generalizing [hom] with an arbitrary monad in the
    codomain has a problem with termination.
    Maybe [hom : M E1 X -> t (M E2) X] for a class of
    monad transformers?
    Or we could give up typing and define [hom] as a
    [Notation] (macro). *)
Section hom.
  Variable E1 E2 : Type -> Type.
  Variable f : forall {X}, E1 X -> M E2 X.

  CoFixpoint hom {X} (p : M E1 X) : M E2 X :=
  match p with
    | Ret x => Ret x
    | Vis e k => x <- f e;; hom (k x)
    | Tau k => Tau (hom k)
  end.
End hom.

CoFixpoint hoist {E F X}
           (f : forall Z, E Z -> F Z)
           (m : M E X)
  : M F X :=
  match m with
  | Ret x => Ret x
  | Vis e k => Vis (f _ e) (fun z => hoist f (k z))
  | Tau n => Tau (hoist f n)
  end.

Fixpoint collapse_root {E X} (fuel : nat) (m : M E X) : M E X :=
  match fuel with
  | O => m
  | S fuel' =>
    match m with
    | Tau m' => collapse_root fuel' m'
    | _ => m
    end
  end.

CoFixpoint collapse {E X} (refuel : nat) (m : M E X) : M E X :=
  match collapse_root refuel m with
  | Tau m' => Tau (collapse refuel m')
  | Vis e k => Vis e (fun z => collapse refuel (k z))
  | Ret x => Ret x
  end.

(* ------------------------------------------------------------- *)

Module MORE.

(** Some more interesting algebraic structure.  This is not
    immediately useful for zipping tests and programs because there
    are things in tests that we do not want to zip with anything in
    the program.  Might be useful later for something, though. *)

Inductive Pair1 (E1 E2: Type -> Type) : Type -> Type :=
 | pair1 {X} {Y} (e1 : E1 X) (e2 : E2 Y) : Pair1 E1 E2 (X * Y).

(** If we can interpret two infinite streams with different events as one
    where we line up the events in lockstep. *)
Definition lockstep {E1 E2 : Type -> Type} {X} : M E1 X -> M E2 X -> M (Pair1 E1 E2) X :=
  cofix go p1 p2 :=
    match p1, p2 with
      | Tau p1', _ => Tau (go p1' p2)
      | _, Tau p2' => Tau (go p1 p2')
      | Ret x,_ => Ret x
      | _, Ret x => Ret x
      | Vis e1 p1k, Vis e2 p2k =>
        Vis (pair1 e1 e2) (fun p => match p with (x, y) => go (p1k x) (p2k y) end)
    end.
(** There are a few variants depending on which return values we want
    to to force to be void. But this seems to be the most general
    one.*)

End MORE.

(** In order to unfold a cofixpoint we have to rewrite it with
    [matchM]. *)
Notation idM i :=
  match i with
  | Ret x => Ret x
  | @Vis _ _ Y e k => Vis e k
  | Tau k => Tau k
  end.

Lemma matchM : forall E X (i: M E X), i = idM i.
Proof. destruct i; auto. Qed.

Lemma bind_def_core : forall E X Y s (k : X -> M E Y),
    Core.bindM s k = Core.bind_body s (fun s => Core.bindM s k) k.
Proof.
  intros.
  rewrite matchM.
  destruct s; auto.
  simpl.
  rewrite (@matchM _ _ (k x)) at 2.
  auto.
Qed.

Lemma bind_def E X Y :
  forall s (k : X -> M E Y),
    bindM s k = Core.bind_body s (fun s' => bindM s' k) (fun x => Tau (k x)).
Proof.
  unfold bindM.
  intros s k.
  rewrite bind_def_core.
  auto.
Qed.


CoFixpoint loop {E void} (body : M E unit) : M E void :=
  body;; loop body.

Definition when {E} (b : bool) (body : M E unit)
  : M E unit :=
  if b then body else ret tt.

CoFixpoint for_each {E A} (bs : list A) (body : A -> M E unit)
  : M E unit :=
  match bs with
  | [] => ret tt
  | b :: bs' => body b;; for_each bs' body
  end.
