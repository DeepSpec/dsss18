Set Implicit Arguments.
Set Contextual Implicit.

Section StateT.

Variable S : Type.
Variable M : Type -> Type.
Variable MM : Monad M.

Definition stateT (X : Type) :=
  S -> M (S * X)%type.

Definition bind_stateT {X Y}
           (m : stateT X) (k : X -> stateT Y)
  : stateT Y := fun s =>
  sx <- m s;;
  let (s, x) := sx : S * X in
  k x s.

Definition ret_stateT {X} (x : X)
  : stateT X := fun s => ret (s, x).

Global Instance Monad_stateT : Monad stateT :=
  { ret := @ret_stateT;
    bind := @bind_stateT }.

End StateT.
