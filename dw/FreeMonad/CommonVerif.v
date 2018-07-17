Set Implicit Arguments.
Set Contextual Implicit.
Generalizable All Variables.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Require Import DeepWeb.Free.Monad.Verif.
Import SumNotations.
Open Scope sum_scope.

Definition hom_assoc `(m : M (E +' (F +' G)) X)
  : M (F +' (E +' G)) X :=
  let transform Y (ev : (E +' (F +' G)) Y) : (F +' (E +' G)) Y :=
      match ev with
      | ( e |) => inj e
      | (| ( f |) ) => inj f
      | (| (| g ) ) => inj g
      end in
  hoist transform m.

Module Counter (E : EventType).

Module TauM := TauMonad E.
Definition E := TauM.E.

(* TODO: There's probably a more general theorem
   about effect handlers. *)
Lemma run_counter_comm :
  forall `(m : M (counterE nat +' (counterE nat +' E)) X)
         (a b : nat),
  TauM.EqM
    (run_counter_from' a (run_counter_from' b m))
    (run_counter_from' b (run_counter_from' a (hom_assoc m))).
Proof.
  cofix self.
  intros.
  match goal with
  | [ |- TauM.EqM ?v ?w ] =>
    rewrite (@matchM _ _ v); rewrite (@matchM _ _ w)
  end.
  destruct m; simpl.
  - constructor.
  - destruct e as [ c | [ c | ] ];
      [ destruct c | destruct c | ];
      constructor; intros; apply self.
  - constructor. apply self.
Qed.

End Counter.