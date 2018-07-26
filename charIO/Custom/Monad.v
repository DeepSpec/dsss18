(* Monad type class *)

(* We define our own instead of reusing ext-lib's because
   of a universe inconsistency when used with itrees and VST. *)

Class Monad (m : Type -> Type) : Type :=
  { ret : forall a, a -> m a;
    bind : forall a b, m a -> (a -> m b) -> m b
  }.

Arguments ret {m Monad a}.
Arguments bind {m Monad a b}.

Module MonadNotations.

Delimit Scope monad_scope with monad.

Notation "c >>= f" := (bind c f)
(at level 50, left associativity) : monad_scope.

Notation "f =<< c" := (bind c f)
(at level 51, right associativity) : monad_scope.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
(at level 100, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" := (bind c1 (fun pat => c2))
(at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
(at level 100, right associativity) : monad_scope.

End MonadNotations.

Require Import List.
Import ListNotations.
Import MonadNotations.

Fixpoint forM {M : Type -> Type} {MM : Monad M} {X Y}
              (xs : list X) (f : X -> M Y)
  : M (list Y) :=
  match xs with
  | [] => ret []
  | x :: xs => y <- f x;; ys <- forM xs f;; ret (y :: ys)
  end%monad.
