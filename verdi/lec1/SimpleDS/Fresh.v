Require Import SysDef.

(* To start things off, we'll define a system with only
   one node -- basically just a stateful function. *)

Module FreshBase <: BaseSystemParams.

  Inductive input' :=
    GetFresh.

  Inductive output' :=
    Fresh: nat -> output'.
  
  Inductive node' :=
    Server.

  Definition state :=
    nat.

  (* single node system -- no messages *)
  Inductive msg' :=
    .

  (* Coq will not instantiate parameters with inductive types :( *)
  Definition input := input'.
  Definition output := output'.
  Definition node := node'.
  Definition msg := msg'.

  Definition node_eq_dec :
    forall x y : node, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Defined.

  Definition msg_eq_dec :
    forall x y : msg, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Defined.
End FreshBase.

Module Fresh <: SystemParams.
  Include (HandlerMonad FreshBase).

  Definition init_state : node -> state :=
    fun n => 0.

  Definition handle_input (n : node) (i : input) : handler :=
    do (
      n <- get ;;
      out (Fresh n) ;;
      set (S n)).

  Definition handle_msg (n : node) (m : msg) : handler :=
    (* remember, no messages *)
    match m with end.
End Fresh.

(* We'll discuss shims and the trusted computing base (TCB) for
   distributed systems later, but for now: how would you run a
   system like Fresh on a real network?

  Require Extraction.
  Extraction Fresh.
*)

