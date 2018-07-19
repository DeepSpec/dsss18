Require Import DeepWeb.Free.Monad.Free.

Inductive _M {E R} (n : nat) : M E R -> Prop :=
| MTau : forall t, _M (S n) t -> _M n (Tau t)
| MVis : forall X (e : E X) k x, _M (S n) (k x) -> _M n (Vis e k).

Ltac simpl_M := rewrite matchM; simpl; try rewrite <- matchM.
Ltac step_tau := repeat (apply MTau; simpl_M).
Ltac step y := apply MVis with (x := y); simpl_M; step_tau.
