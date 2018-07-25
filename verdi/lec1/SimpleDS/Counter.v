Require Import SysDef.

Module CounterBase <: BaseSystemParams.

  Inductive input' :=
    BumpReq.

  Inductive output' :=
    BumpAck.
 
  Inductive node' :=
  | Primary
  | Backup.

  Definition state :=
    nat.

  Inductive msg' :=
  | Inc
  | Ack.

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
End CounterBase.

Module Counter <: SystemParams.
  Include (HandlerMonad CounterBase).

  Definition init_state : node -> state :=
    fun n => 0.

  Definition do_inc : handler_monad unit :=
    s <- get ;; set (s + 1).

  Definition handle_input (n : node) (i : input) : handler := do
    match n with
    | Primary => match i with
                 | BumpReq => do_inc ;;
                              send Backup Inc
                 end
    | _ => nop
    end.

  Definition handle_msg (n : node) (m : msg) : handler := do
    match n with
    | Backup => match m with
                | Inc => do_inc ;;
                         send Primary Ack
                | _ => nop
                end
    | Primary => match m with
                 | Ack => out BumpAck
                 | _ => nop
                 end
    end.
End Counter.

