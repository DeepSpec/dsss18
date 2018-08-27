Require Import String.

From DeepWeb.Spec.Vst
     Require Import MainInit SocketSpecs Gprog MonadExports
     Representation accept_connection_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib SocketTactics Connection.

Import SockAPIPred.
Import TracePred.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

Set Bullet Behavior "Strict Subproofs".

Open Scope list.
Open Scope logic.

Opaque bind.

Set Bullet Behavior "Strict Subproofs".

Lemma body_accept_connection:
  semax_body Vprog Gprog f_accept_connection (accept_connection_spec unit).
Proof.
  start_function.
  unfold accept_connection.
  forward_accept fd.
  { cancel. }

  Intro vret.
  destruct vret as
      [[accept_res st_post_accept] accept_ret].
  simpl.
  Intros.
  
  (* Get bounds on return value first *)
  assert (-1 <= accept_ret < Int.max_signed).
  {
    match goal with
    | [H: context[_ \/ accept_ret = NO] |- _] =>
      destruct H
        as [ [_ [accept_ret_geq accept_ret_lt] ] | accept_ret_eq]
    end; unfold NO in *; rep_omega.
  }     
  
  forward_if.
  {
    match goal with
    | [H: context[_ \/ accept_ret = NO] |- _] =>
      destruct H
        as [ [_ [accept_ret_geq accept_ret_lt] ] | accept_ret_eq];
        [rep_omega | ]
    end.
    
    match goal with
    | [H1: accept_ret = NO, H2: accept_ret = NO -> _ |- _] =>
      destruct (H2 H1) as [accept_res_eq st_post_accept_eq]
    end.

    rewrite accept_res_eq.

    take_branch2 0. 
    forward.

    rewrite (trace_bind_ret (None : option connection)).
    Exists (None : option (connection * sockfd * val)).
    Exists st.
    Exists NO.
    unfold NO.

    repeat apply andp_right; auto.
    - apply prop_right; repeat split; auto.
      intros; omega.
    - cancel.
  }

  assert (accept_ret <> NO) by (unfold NO in *; omega).
    
  match goal with
  | [H1: accept_ret <> NO, H2: accept_ret <> NO -> _ |- _] =>
    destruct (H2 H1)
      as [client_conn
            [client_fd
               [accept_res_eq
                  [accept_ret_eq
                     [lookup_client_fd
                        st_post_accept_eq]]]]]
  end.
  
  rewrite accept_res_eq.

  forward_if.
  {
    take_branch2 0.
    rewrite trace_bind_assoc.
    
    forward_shutdown client_fd.
    { subst accept_ret; apply prop_right; repeat split; auto. }
    { subst. repeat split; [assumption | | apply trace_incl_refl].
      apply lookup_update_socket_eq; reflexivity.
    }

    Intro vret.
    destruct vret as [st_post_shutdown shutdown_ret].
    simpl.
    Intros.

    (* close *)
    forward_call ((' b <- Ret None;; k b), st_post_shutdown, client_fd).
    { apply prop_right; simpl; subst; reflexivity. }
    
    Intro vret.
    destruct vret as [st_post_close close_ret].
    simpl.

    Intros.
    to_equal.
    forward.
    from_equal.
    
    Exists (None : option (connection * sockfd * val)).
    Exists st_post_close.
    Exists NO.
    unfold NO.

    assert (st_post_close = st).
    { prove_socket_map_eq st client_fd. }

    rewrite (trace_bind_ret (None : option connection)).
    entailer!.
  } 
    
  (* alloc connection *)
  forward_call tt.

  Intro vret.
  destruct vret
    as [conn_opt alloc_ret].
  simpl.

  Intros.
  forward_if.
  { (* precondition *)
    apply denote_tc_test_eq_split; [| apply valid_pointer_zero].
    match goal with
    | [H1: isptr alloc_ret \/ _,
       H2: isptr alloc_ret -> _,
       H3: alloc_ret = nullval -> _  |- _] =>
      destruct H1 as [alloc_ret_ptr | alloc_ret_null];
        [rewrite (H2 alloc_ret_ptr) | rewrite (H3 alloc_ret_null)]
    end.

    - entailer!.
    - entailer!.
  } 
  
  { (* if *)
    match goal with
    | [H1: alloc_ret = nullval,
       H2: alloc_ret = nullval -> _ |- _] =>
      rewrite (H2 H1)
    end.
    
    take_branch2 1.
    rewrite trace_bind_assoc.
    forward_shutdown client_fd.
    { subst accept_ret; apply prop_right; reflexivity. }
    { repeat split;
        [assumption | | apply trace_incl_refl ];
        subst; apply lookup_update_socket_eq;
        reflexivity. }

    Intro vret.
    destruct vret as [st_post_shutdown shutdown_ret].
    simpl.
    Intros.

    (* close *)
    forward_call ((' b <- Ret None;; k b), st_post_shutdown, client_fd).
    { apply prop_right; simpl; subst; reflexivity. }

    Intro vret.
    destruct vret as [st_post_close close_ret].
    simpl.
    Intros.

    trace_bind_ret.

    assert (st_post_close = st).
    { prove_socket_map_eq st client_fd. }

    to_equal.
    forward.
    from_equal.
    
    Exists (None : option (connection * sockfd * val)).
    Exists st_post_close.
    Exists NO.
    unfold NO.

    repeat apply andp_right; auto.
    - apply prop_right; repeat split; auto.
      intros Hcontra; omega.
    - subst.
      cancel.
  }

  match goal with
  | [H1: isptr alloc_ret \/ _,
     H2: isptr alloc_ret -> _,
     H3: alloc_ret = nullval -> _  |- _] =>
    destruct H1 as [alloc_ret_ptr | alloc_ret_null];
      [pose proof (H2 alloc_ret_ptr) as conn_opt_eq; rewrite conn_opt_eq
      | tauto];
      clear H1 H2 H3
  end.

  Intros tail.
  
  match goal with
  | [H: conn_opt = Some ?cn |- _] =>
    remember cn as conn0
  end.

  take_branch1 5.
  trace_bind_ret.

  assert_PROP (field_compatible (Tstruct _connection noattr) [] alloc_ret)
    by entailer!.
  
  forward_call (conn0, 
                {| descriptor := 0; is_descriptor := zero_is_fd |},
                client_fd,
                alloc_ret).
  { subst; apply prop_right; repeat split; auto. }

  forward.
  forward.
  forward.

  to_equal.
  forward.
  from_equal.
  
  set (conn := {| conn_id := client_conn;
                  conn_request := "";
                  conn_response := "";
                  conn_response_bytes_sent := 0;
                  conn_state := RECVING
               |}).
  
  Exists (Some (conn, client_fd, alloc_ret)).
  Exists st_post_accept.
  Exists YES.
  unfold YES, NO.

  repeat apply andp_right; auto.
  { 
    apply prop_right; repeat split; [omega | | omega | omega | assumption].
    intros _.
    exists client_conn; exists client_fd; exists alloc_ret.
    repeat split; auto.
    unfold FD_SETSIZE.
    rewrite <- accept_ret_eq.
    trivial.
  }

  cancel.

  unfold rep_connection.
  autounfold with updates; simpl.
  Exists curr_head.
  entailer!.
  
Qed.