Set Implicit Arguments.
Set Contextual Implicit.

Require Import List.
Import ListNotations.

From Custom Require Export
     Monad.
Import MonadNotations.
Open Scope monad_scope.

(** * Interaction Trees. *)
(** ** Basic Definitions *)

(* The core definition of ITrees.  An [M E X] is the denotation of a
   program as coinductive (possibly infinite) tree where the leaves
   are [Ret] nodes labeled with return values from [X] and each
   internal nodes is either an "internal" [Tau] node with one child or
   else a "external" [Vis] node with a visible event of type [Event Y]
   plus a continuation [k] that receives a [Y] value from the event. *)

CoInductive M (Event : Type -> Type) X := 
| Ret (x:X)
| Vis {Y: Type} (e : Event Y) (k : Y -> M Event X)
| Tau (k: M Event X).

(* [M] is commonly known as the "Freer monad" -- see _Freer Monads,
   More Extensible Effects_, by Oleg Kiselyov and Hiromi Ishii. *)

(* begin hide *)
(* Abstract nonsense: The [Vis] constructor corresponds to a free
   functor construction also called Co-Yoneda or left Kan extension.
   Note that [Event] is meant to be an indexed type, and generally not
   a functor, but we have a monad in any case.

   Some relevant links to variations of this theme can be found in
   http://reddit6.com/r/haskell/comments/7q4sku/are_people_using_freer_monads_or_still_mostly/ 
*)

(*  Note: One could imagine an alternative definition with an explicit
    Bind constructor (and a Prim constructor), but this might not be
    as nice / might not work at all -- this way makes productivity
    easier to deal with.  (Also, this one can be turned into a real
    monad.)  We should compare at some point. *)

(*  Another way to derive this is to consider "normal forms" resulting
    from rewriting [(m >>= k) >>= h] to [m >>= (k >=> h)]. *)

(*  The existence of [spin] makes this not quite free:
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
(* end hide *)

(** ** Monad Structure *)

Module Core.

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

(* [M E] forms a [Monad] (for any type of events [E]). *)
Definition Monad_M E : Monad (M E) :=
  Build_Monad (M E)
              (fun X x => Ret x)
              (@bindM E).

End Core.

(* However, it is convenient to slightly change the bind operation to
   insert a [Tau] in the case where the right-hand argument to bind is
   just a [Ret], to make programs/specifications neater and easier to
   write.  With this variant of bind, [M] is no longer a monad
   strictly speaking, but it remains one in a looser sense where we
   ignore [Tau] such that [Tau t] is considered equivalent to [t]. *)
Definition bindM {E X Y} (s: M E X) (t: X -> M E Y) : M E Y :=
  Core.bindM s (fun x => Tau (t x)).

Instance Monad_M E : Monad (M E) := { ret X x := Ret x; bind := @bindM E }.

(* Lift a single event to an [M] action. *)
Definition liftE Event X (e : Event X) : M Event X :=
  Vis e (fun x => Ret x).

(** ** Handy Utilities *)

(* A number of useful ITrees and ITree combinators *)

(* An ITree representing an infinite loop *)
CoFixpoint spin {E} {X} : M E X := Tau spin.

(* An ITree that does one internal step and then returns. *)
Definition tick {E} : M E unit := Tau (Ret tt).

(* The void type is useful as a return type to [M], to enforce the
    constraint that a given computation should never terminate. *)
Inductive void : Type := .

(* An infinite loop with a given body. *)
CoFixpoint forever {E} {X} (x : M E X) : M E void :=
  x ;; forever x.

(* A one-sided conditional. *)
Definition when {E} (b : bool) (body : M E unit)
                : M E unit :=
  if b then body else ret tt.

(* An imperative "for each" loop over a list. *)
CoFixpoint for_each {E A} (bs : list A) (body : A -> M E unit)
                  : M E unit :=
  match bs with
  | [] => ret tt
  | b :: bs' => body b;; for_each bs' body
  end.

(* An imperative while-loop combinator. *)
CoFixpoint while {E : Type -> Type} {T : Type}
                 (cond : T -> bool)
                 (body : T -> M E T) 
               : T -> M E T :=
  fun t =>
    match cond t with
    | true =>
      r <- body t ;;
      while cond body r
    | false => ret t
    end.

(* Wrap a function around the results returned from an ITree *)
Definition mapM {E X Y} (f: X -> Y) (s: M E X) : M E Y :=
let cofix go (s : M E X) := 
    match s with
    | Ret x => Ret (f x)
    | Vis e k => Vis e (fun y => go (k y))
    | Tau k => Tau (go k)
    end
in go s.

(* Ignore the results from an ITree (changing it to have [unit] result type) *)
Definition ignore {E X} : M E X -> M E unit := mapM (fun _ => tt).

