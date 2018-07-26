Require Import Arith.
Require Import List.
Import ListNotations.
Require Import StructTact.Util.

Require Import SimpleDS.SysDef.

Module SeqNumBase (S : SystemParams) <: BaseSystemParams.

  (* keep same external I/O interface *)
  Definition input := S.input.
  Definition output := S.output.

  (* keep same set of nodes *)
  Definition node := S.node.

  (* giving up on serializability here *)
  Record state' :=
    mkstate {
        fresh : nat;
        seen : node -> nat -> bool;
        data : S.state
      }.

  (* single node system -- no messages *)
  Record msg' :=
    mkmsg {
        uid : nat;
        src : node;
        orig_msg : S.msg
      }.

  (* Coq will not instantiate parameters with inductive types :( *)
  Definition state := state'.
  Definition msg := msg'.
  
  Record packet : Set :=
    mkpacket {dest : node; payload : msg}.
  
  Definition node_eq_dec := S.node_eq_dec.

  Definition msg_eq_dec :
    forall x y : msg, {x = y} + {x <> y}.
  Proof.
    decide equality.
    - apply S.msg_eq_dec.
    - apply node_eq_dec.
    - decide equality.
  Defined.
End SeqNumBase.

Module SeqNum (S : SystemParams) <: SystemParams.
  Module SNB := SeqNumBase S.
  Module HM := HandlerMonad SNB.
  Include HM.

  Definition init_state : node -> state :=
    fun n => mkstate 0 (fun _ _ => false) (S.init_state n).

  Definition ship (self : node) (op : S.packet) : handler_monad unit :=
    s <- get ;;
    send (S.dest op) (mkmsg (fresh s) self (S.payload op)) ;;
    set (mkstate (S (fresh s)) (seen s) (data s)).

  Fixpoint ships self ops : handler_monad unit :=
    match ops with
    | [] => nop
    | op :: ops' => ship self op ;; ships self ops'
    end.
  
  Fixpoint outs (os : list output) : handler_monad unit :=
    match os with
    | [] => nop
    | o :: os' => out o ;; outs os'
    end.

  Definition handle_input (n : node) (i : input) : handler :=
    do (
      s <- get ;;
      let '(d', ps, os) := S.handle_input n i (data s) in
      set (mkstate (fresh s) (seen s) d') ;;
      ships n ps ;;
      outs os ).

  Definition mark seen src uid :=
    fun x y =>
      if node_eq_dec x src
      then if eq_nat_decide y uid
           then true
           else seen x y
      else seen x y.

  Definition handle_msg (n : node) (m : msg) : handler :=
    do (
      s <- get ;;
      if (seen s) (src m) (uid m) then
        nop
      else
        let '(d', ps, os) := S.handle_msg n (orig_msg m) (data s) in
        set (mkstate (fresh s) (mark (seen s) (src m) (uid m)) d') ;;
        ships n ps ;;
        outs os ).
End SeqNum.
