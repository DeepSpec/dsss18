Require Import String.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs MonadExports
     Representation AppLogic process_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib Connection SocketTactics.

Import SockAPIPred.
Import TracePred.

Open Scope list.
Open Scope logic.

Opaque bind.

Set Bullet Behavior "Strict Subproofs".

Lemma body_process:
  semax_body Vprog Gprog f_process (process_spec unit BUFFER_SIZE).
Proof.
  start_function.

  assert_PROP (field_compatible (Tstruct _connection noattr)
                                [] (conn_ptr))
    by entailer!.

  unfold rep_connection.
  rewrite connection_list_cell_eq; [| assumption].

  Intros.
  forward.

  forward_if.
  {
    unfold process_conn.
    match goal with
    | [H: Int.repr _ = Int.repr _ |- _] =>
      destruct (conn_state conn) eqn:cstate;
        try inversion H
    end.

    forward_call (k, st, conn, fd, last_msg, conn_ptr, msg_store_ptr).
    {
      unfold rep_connection.
      rewrite connection_list_cell_eq; [| assumption].
      rewrite cstate.
      cancel.
    }

    Intro vret.
    destruct vret as [[[conn' last_msg'] st'] ?].
    simpl.

    forward.
    
    Exists conn'.
    Exists last_msg'.
    Exists st'.
    Exists YES.
    
    entailer!.
    discriminate.
    
  }

  forward_if.
  {
    unfold process_conn.
    match goal with
    | [H: Int.repr _ = Int.repr _ |- _] =>
      destruct (conn_state conn) eqn:cstate;
        try inversion H
    end.

    rewrite trace_bind_assoc.
    
    forward_call ( (fun conn => b <- ret (conn, last_msg) ;; k b),
                   st, conn, fd, conn_ptr).
    {
      unfold rep_connection.
      rewrite connection_list_cell_eq; [| assumption].
      rewrite cstate.
      cancel.

      (* move to tactic *)
      match goal with
      | [|- context[ITREE ?tr1 * _ |-- ITREE ?tr2 * _]] =>
        replace tr1 with tr2 by reflexivity
      end.

      cancel.

    }

    Intro vret.
    destruct vret as [[conn' st'] ?].
    simpl.

    trace_bind_ret.

    forward.
    
    Exists conn'.
    Exists last_msg.
    Exists st'.
    Exists YES.
    entailer!.
    discriminate.
    
  }

  unfold process_conn.

  do 2 int_ineq_to_Z_ineq.

  assert (conn_state conn = DELETED \/ conn_state conn = DONE) as cases by
      (destruct (conn_state conn); try omega; auto).

  forward.
  
  Exists conn.
  Exists last_msg.
  Exists st.
  Exists YES.

  repeat apply andp_right; auto.
  - apply prop_right; repeat split; auto.
    + intros Hstate; destruct cases; rewrite Hstate in *; discriminate.
    + match goal with
      | [H: _ = SENDING |- _] =>
        rewrite H in *; destruct cases; discriminate
      end.
  - destruct cases as [Hstate | Hstate]; rewrite Hstate; 
      trace_bind_ret;
      unfold rep_connection;
      rewrite connection_list_cell_eq; auto;
        cancel.
    all: rewrite Hstate; cancel.

Qed.