Require Import String.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs MonadExports
     AppLogic Representation conn_write_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib SocketTactics Connection.

Import SockAPIPred.
Import TracePred.

Open Scope list.
Open Scope logic.

Opaque bind.

Set Bullet Behavior "Strict Subproofs".


Lemma body_conn_write:
  semax_body Vprog Gprog f_conn_write (conn_write_spec unit BUFFER_SIZE).
Proof.
  start_function.

  assert_PROP (field_compatible (Tstruct _connection noattr)
                                [] (conn_ptr))
    by entailer!.

  assert_PROP (field_compatible (Tstruct _connection noattr)
                                [StructField _response_buffer] conn_ptr)
    by entailer!.

  match goal with
  | [H: consistent_state _ _ _ |- _] =>
    inversion H; subst; try discriminate
  end.
  
  match goal with
  | [H: consistent_state _ _ (?c, _) |- _] =>
    set (conn := c)
  end.

  unfold rep_connection.
  rewrite connection_list_cell_eq; [| auto].
  
  Intros.
  do 5 forward.

  match goal with
  | [|- context[ITREE _]] =>
  match goal with
  | [|- context[SOCKAPI _]] =>
  match goal with
  | [|- context[field_at _ _ [StructField _response_buffer] _ _]] =>
    freeze [2; 3; 4; 5; 7; 8] FR1; simpl
  end
  end
  end.

  focus_SEP 3.
  rewrite field_at_data_at; simpl.
  saturate_rep_msg_bounds.
  unfold rep_msg.
  split_data_at. (* first split from undefined tail *)
  Intros.

  freeze [1; 2] FR2; simpl.
  focus_SEP 1.
  
  (* then split from what's been sent *)
  split_data_at (conn_response_bytes_sent conn).
  2: {
    subst conn; auto.
  } 
  Intros.
  freeze [0; 2] FR3; simpl.

  focus_SEP 1.
  rem_ptr buf_ptr.
  unfold conn_write.
  
  forward_send fd buf_ptr.
  { apply prop_right; repeat split; auto.
    - (* Unifying pointers *)
      simpl.
      rewrite sem_add_pi_ptr_special.
      2 : {
        apply isptr_offset_val'.
        auto.
      }
      subst; simpl.
      rewrite field_address0_offset; simpl.
      2 : {
        prove_field_compatible0_array_field_addr.
        simpl in Hcompat.
        prove_field_compatible_smaller_array.
        unfold tarray in Hcompat.
        - rewrite field_address_offset; auto.
        - unfold BUFFER_SIZE in *.
          simpl in *|-.
          auto.
      } 
      rewrite field_address_offset; auto.
    - (* Unifying string length from ITree with Zlength in VST *)
      simpl.
      repeat f_equal.
      repeat autorewrite_sublist; omega.
  }
  { cancel.
    autorewrite_sublist;
      [| autorewrite_sublist; subst; simpl; omega..].
    cancel.
  } 

  Intro vret.
  destruct vret as [[send_res st_post_send] send_ret].
  simpl fst; simpl snd.

  (* Rejoin buffer *)
  Intros.
  thaw FR3; thaw FR2; simpl.
  rem_trace tr.
  gather_SEP 2 3 4.
  Intros.
  subst buf_ptr.
  gather_SEP 1 0.
  autorewrite_sublist;
    [| autorewrite_sublist; subst; simpl; omega..].
  
  Intros.
  gather_SEP 0 1.
  coalesce.
  { autorewrite_sublist; omega. }
  simpl.
  rewrite sublist_firstn.
  rewrite firstn_skipn.

  gather_SEP 0 1.
  coalesce.
  fold_rep_msg.

  (* Restore all fields *)
  data_at_to_field_at.
  field_at_rebase_ptr.
  
  thaw FR1; simpl.

  assert (-1 <= send_ret < Int.max_signed).
  {
    match goal with
    | [H: _ \/ send_ret = _ |- _] =>
      unfold NO in H;
        destruct H as [[send_ret_lb send_ret_ub] | ?];
        try rep_omega
    end.
    subst; simpl in send_ret_ub. 
    autorewrite_sublist in send_ret_ub;
      [| autorewrite_sublist; omega..].
    rep_omega.
  } 

  forward_if.
  { (* send fails *)

    subst tr.
    assert (send_ret = NO) by (unfold NO; omega).
    match goal with
    | [H1: send_ret = NO, H2 : send_ret = NO -> _ |- _] =>
      destruct (H2 H1) as [send_res_eq st_post_send_cases]
    end.

    subst send_res.
    take_branch2 2.
    trace_bind_ret.

    forward.

    forward.

    Exists (upd_conn_state conn DELETED).
    Exists st_post_send.
    Exists YES.
    repeat apply andp_right; auto.
    - apply prop_right; repeat split; auto.
      subst.
      apply Conn_SENDING_Fail; auto.
    - unfold rep_connection.
      rewrite connection_list_cell_eq; [| assumption].
      cancel.
  }

  forward.
  
  forward_if.
  { (* send incomplete *)

    subst tr.
    assert (send_ret <> NO) by (unfold NO; omega).
    match goal with
    | [H1: send_ret <> NO, H2 : send_ret <> NO -> _ |- _] =>
      destruct (H2 H1) as [send_res_eq st_post_send_eq]
    end.

    subst send_res.
    assert ((String.length response <? Z.to_nat send_ret)%nat = false)
      as dead_cond.
    {
      rewrite Nat.ltb_ge.
      autorewrite_sublist.
      omega.
    }
    
    rewrite dead_cond.

    autorewrite_sublist.
    assert (num_bytes_sent + send_ret
            =? Zlength (val_of_string response) = false)
      as incomplete_cond.
    { rewrite Z.eqb_neq.
      unfold not; intros.
      omega.
    } 
    rewrite incomplete_cond.

    trace_bind_ret.

    forward.

    Exists ({| conn_id := client_id;
               conn_request := request;
               conn_response := response;
               conn_response_bytes_sent := num_bytes_sent + send_ret;
               conn_state := SENDING |}).
    Exists st.
    Exists YES.
    unfold rep_connection.
    rewrite connection_list_cell_eq; [| assumption].
    simpl.
    entailer!.
    
    apply Conn_SENDING_SENDING with (num_bytes_sent := send_ret);
      simpl; auto; omega.

    
  }

  subst tr.
  assert (send_ret <> NO) by (unfold NO; omega).
  match goal with
  | [H1: send_ret <> NO, H2 : send_ret <> NO -> _ |- _] =>
    destruct (H2 H1) as [send_res_eq st_post_send_eq]
  end.

  subst send_res.

  match goal with
  | [H: _ \/ send_ret = NO |- _] =>
    destruct H as [[send_ret_lb send_ret_ub] | ?]; try rep_omega
  end.

  autorewrite_sublist in send_ret_ub;
    [| autorewrite_sublist; omega ..].
  
  assert ((String.length response <? Z.to_nat send_ret)%nat = false)
    as dead_cond.
  {
    rewrite Nat.ltb_ge.
    autorewrite_sublist.
    subst conn; simpl in send_ret_ub.
    omega.
  }

  rewrite dead_cond.

  autorewrite_sublist.
  assert (num_bytes_sent + send_ret
          =? Zlength (val_of_string response) = true)
    as complete_cond.
  { rewrite Z.eqb_eq.
    subst conn; simpl in send_ret_ub.
    omega.
  } 

  rewrite complete_cond.
  trace_bind_ret.

  gather_SEP 3 4 5 6 0.
  Intros.
  gather_SEP 0 1 2 3 4 7 8.
  repeat rewrite <- sepcon_assoc.
  rewrite <- connection_list_cell_eq by assumption.
  
  set (conn_pre_reset :=
         {| conn_id := client_id;
            conn_request := request;
            conn_response := response;
            conn_response_bytes_sent := num_bytes_sent + send_ret;
            conn_state := SENDING
         |}
      ).

  fold_rep_connection conn_pre_reset fd.
  { go_lower. unfold rep_connection.
    subst conn_pre_reset.
    simpl.
    rewrite add_repr.
    cancel.
  }

  forward_call (conn_pre_reset, fd, fd, conn_ptr).
  subst st_post_send.
  
  forward.

  Exists ({| conn_id := client_id;
             conn_request := "";
             conn_response := "";
             conn_response_bytes_sent := 0;
             conn_state := RECVING |}).
  Exists st.
  Exists YES.
  entailer!.
  - apply Conn_SENDING_RECVING
      with (num_bytes_sent :=
              Zlength (val_of_string response) - num_bytes_sent);
      [auto | | reflexivity | auto].
    simpl.
    omega.
  - autounfold with updates.
    simpl.
    cancel.
    
Qed.