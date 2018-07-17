Set Implicit Arguments.

Require Import String.
Require Import List.
Import ListNotations.

Require Export DeepWeb.Free.Monad.Free.
Require DeepWeb.Free.Monad.IO.
Import IO.IO.

Definition value := string.
Definition IO := @IO value.

(* ========================================================================== *)
(** Some little experiments with an alternate state-machine representation... *)

Definition ILabel : Type := value.
Definition OLabel : Type := value.

Record SM := {
  IState : Type; 
  OState : Type; 
  istep : IState -> ILabel -> (IState + OState);
  ostep : OState -> (option OLabel) * (IState + OState)
}.

Definition State (sm : SM) : Type := IState sm + OState sm.

Definition to_trace (sm : SM) : State sm -> IO void :=
  cofix go (s: State sm) :=
    match s with
    | inl is => bindM recv (fun v => go (istep sm is v))
    | inr os => match ostep sm os with
                | (None,   s') => Tau (go s')
                | (Some o, s') => bindM (send o) (fun _ => go s')
                end
    end.

Definition toState (t : IO void) :=
  match t with
  | Ret x => match x with end
  | Tau k => inr (None, k)
  | Vis Input k => inl k
  | Vis (Output v) k => inr (Some v, k tt)
  end.

Definition iosm : SM := {|
  IState := value -> IO void;
  OState := option value * IO void;
  istep := fun i v => toState (i v);
  ostep := fun o => match o with (vo, t) => (vo, toState t) end
|}.

(* TODO: Show that these form an iso up to trace equivalence.  Tricky
   because there's no generic definition of equality for state
   machines. *)
