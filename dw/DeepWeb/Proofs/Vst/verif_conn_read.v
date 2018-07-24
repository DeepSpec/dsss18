Require Import String.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs MonadExports
     Representation AppLogic conn_read_spec.

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

Lemma body_conn_read:
  semax_body Vprog Gprog f_conn_read (conn_read_spec unit BUFFER_SIZE).
Proof.
  start_function.

  assert_PROP (field_compatible (Tstruct _connection noattr)
                                [] (conn_ptr))
    by entailer!.
  
  assert_PROP
    (field_compatible (Tstruct _connection noattr)
                      [StructField _request_buffer] (conn_ptr))
    by entailer!.

  match goal with
  | [H: context[consistent_state] |- _] =>
    inversion H; subst; try discriminate
  end.

  match goal with
  | [H: consistent_state _ _ (?c, _) |- _] =>
    set (conn := c)
  end.

  unfold rep_connection.
  rewrite connection_list_cell_eq; [| assumption].                                        
  Intros.

  do 4 forward.
  
  freeze [2; 3; 5; 6; 7; 8; 9] FR1.
  simpl.

  (* recv *)
  
  (* Split at current end of msg to recv there *)
  focus_SEP 3.
  rewrite field_at_data_at.
  simpl.
  saturate_rep_msg_bounds.
  
  split_data_at (Zlength (val_of_string (conn_request conn))).
  2 : { simpl; omega. }
  Intros.
  
  freeze [0] FR2.
  focus_SEP 1.
  rem_ptr buf_ptr.
    
  unfold conn_read.

  replace (BUFFER_SIZE - Z.of_nat (String.length (conn_request conn)))
    with (1024 - Zlength (val_of_string (conn_request conn))).
  2 : {
    unfold BUFFER_SIZE.
    autorewrite_sublist.
    reflexivity.
  }
  
  forward_recv fd buf_ptr
  (1024 - Zlength (val_of_string (conn_request conn))).
  { (* buffer pointer equality *)
    apply prop_right; repeat split; auto.
    subst; simpl.
    unfold rep_msg_len.
    rewrite sem_add_pi_ptr_special.
    2 : {
      apply isptr_offset_val'.
      auto.
    }
    rewrite field_address0_offset.
    2 : {
      prove_field_compatible0_array_field_addr.
      rewrite field_address_offset; auto.
    }

    simpl.
    rewrite field_address_offset; auto.
  } 
  { (* trace *) subst; cancel. }

  Intro vret.
  destruct vret as [[[recv_res st_post_recv] recv_ret] contents].

  simpl fst; simpl snd.
  Intros.

  (* Derive basic bounds on return value *)
  assert (-1 <= recv_ret < Int.max_signed).
  { match goal with
    | [H: _ \/ recv_ret = NO |- _] =>
      unfold NO in H; destruct H; try rep_omega
    end.
  } 

  (* Coalesce buffer first *)
  thaw FR2.
  gather_SEP 3 2.
  subst buf_ptr.
  coalesce.
  
  forward_if.
  {

    match goal with
    | [H1 : recv_ret < 0, H2 : recv_ret < 0 -> _ |- _] =>
      destruct (H2 H1)
        as [recv_res_eq [contents_eq st_post_recv_eq]]
    end.

    subst recv_res.

    take_branch2 2.
    trace_bind_ret.
    subst contents.
    fold_rep_msg.

    thaw FR1; simpl.
    Intros.

    to_equal.
    forward.
    from_equal.
    
    Exists conn.
    Exists last_msg.
    Exists st.
    Exists YES.

    repeat apply andp_right; auto.
    { apply prop_right; repeat split; auto.
      apply Conn_RECVING_Id.
    } 

    unfold rep_connection.
    rewrite connection_list_cell_eq; [| assumption].
    unfold BUFFER_SIZE.
    cancel.
    rewrite field_at_data_at; simpl; subst; cancel.

  }

  forward_if.
  { (* EOF *)
    

    match goal with
    | [H1 : recv_ret = 0, H2 : recv_ret = 0 -> _ |- _] =>
      destruct (H2 H1)
        as [recv_res_eq [contents_eq st_post_recv_eq]]
    end.
    subst recv_res.
    trace_bind_ret.
    
    subst contents.
    fold_rep_msg.
    
    thaw FR1.
    simpl.
    Intros.

    forward.
    
    to_equal.
    forward.
    from_equal.

    Exists (upd_conn_state conn DELETED).
    Exists last_msg.
    Exists (update_socket_state st fd OpenedSocket).
    Exists YES.
    
    repeat apply andp_right; auto.
    { apply prop_right; repeat split; auto.
      - apply Conn_RECVING_EOF; subst; auto.
      - subst; assumption.
    }       

    unfold rep_connection.
    rewrite connection_list_cell_eq; [| assumption].
    unfold BUFFER_SIZE.
    rewrite field_at_data_at; simpl; cancel.
    autounfold with updates.
    rewrite field_at_data_at.
    subst.
    cancel.
    
    
  } 

  assert (recv_ret > 0) by omega.
  match goal with
  | [H1 : recv_ret > 0, H2 : recv_ret > 0 -> _ |- _] =>
    destruct (H2 H1)
      as [[msg [recv_res_eq
                  [msg_len_eq
                     [contents_prefix contents_suffix]]]] st_post_recv_eq]
  end.
  subst recv_res.

  match goal with
  | [H: _ \/ recv_ret = NO |- _] =>
    destruct H as [recv_ret_bounds | recv_ret_eq];
      [| unfold NO in recv_ret_eq; subst recv_ret; omega ]
  end.

  (* Coalesce with new msg *)
  match goal with
  | [H1: sublist 0 _ _ = ?prefix, H2: sublist recv_ret _ _ = ?suffix |- _] =>
    assert (contents = (prefix ++ suffix))
  end.
  { 
    rewrite <- contents_prefix.
    rewrite <- contents_suffix.
    rewrite <- sublist_split; [ | omega | split; omega].
    rewrite sublist_same; auto.
  }
  
  subst contents.
  rewrite List.app_assoc.
  rewrite <- val_of_string_app.
  subst recv_ret.
  fold_rep_msg.
  2: { simpl in *|- ; omega. }

  match goal with
  | [|- context[data_at _ _ (rep_msg _ ?bound) _]] =>
    replace bound with 1024
  end.
  2 : {
    rewrite <- Z.sub_add_distr.
    autorewrite_sublist.
    reflexivity.
  } 
  
  (* End Coalesce *)
  
  thaw FR1.
  simpl.

  forward.
  forward.

  (* is_complete *)

  freeze [1; 2; 3; 4; 5; 6; 7; 8] FR1.
  simpl.
  
  (* Split again for check *)
  focus_SEP 1.
  saturate_rep_msg_bounds.
  unfold rep_msg.

  split_data_at.
  Intros.

  forward_call ((conn_request conn ++ msg)%string,
                field_address (Tstruct _connection noattr)
                              [StructField _request_buffer] conn_ptr,
                Zlength (val_of_string (conn_request conn ++ msg)),
                Tsh).
  { entailer!.
    autorewrite_sublist.
    split; auto.
    rewrite field_address_offset by assumption.
    auto.
  }

  {
    split; auto.
    subst conn; simpl.
    rep_omega.
  } 

  Intro is_complete_ret.
  Intros.

  (* Coalesce again *)
  gather_SEP 0 1.
  coalesce.
  fold_rep_msg.
  thaw FR1.
  simpl.

  (*
  replace (Zlength _ >? _) with false.

  2 : {
    unfold BUFFER_SIZE in *.
    
    symmetry.
    rewrite <- not_true_iff_false.
    unfold not.
    intros Hcontra.
    rewrite <- Zgt_is_gt_bool in Hcontra.

    match goal with
    | [H: Zlength (val_of_string _) <= _ |- _] =>
      revert H
    end.
    
    rewrite val_of_string_app.
    rewrite Zlength_app.
    intros.
    omega.

  } 
  *)
  
  forward_if.
  {
    (* Have more to receive *)
    
    match goal with
    | [H1: is_complete_ret = 0, H2: is_complete_ret = 0 -> _ |- _] =>
      simpl conn_request in H2; rewrite (H2 H1)
    end.

    set (conn' := {| conn_id := conn_id conn;
                     conn_request := conn_request conn ++ msg;
                     conn_response := conn_response conn;
                     conn_response_bytes_sent := conn_response_bytes_sent conn;
                     conn_state := RECVING
                  |}).
    trace_bind_ret.

    to_equal.
    forward.
    from_equal.

    Exists conn'.
    Exists last_msg.
    Exists st_post_recv.
    Exists YES.

    subst conn' st_post_recv.
    
    repeat apply andp_right; auto.
    { apply prop_right; repeat split; auto.
      eapply Conn_RECVING_RECVING; subst; simpl; auto.
    } 

    unfold rep_connection.
    rewrite connection_list_cell_eq; [| assumption].
    simpl.
    repeat rewrite field_at_data_at; simpl.
    cancel.
    autorewrite_sublist.
    cancel.
  }

  match goal with
  | [H: is_complete_ret = _ \/ _ |- _] =>
    destruct H; [| tauto ]
  end.
  
  match goal with
    | [H1: is_complete_ret = 1, H2: is_complete_ret = 1 -> _ |- _] =>
      simpl in H2; rewrite (H2 H1)
  end.
  
  forward.

  (* populate response *)
  data_at_to_field_at.

  field_at_rebase_ptr.
  
  gather_SEP 3 4 0 5 6 7 8.
  repeat rewrite <- sepcon_assoc.
  rewrite <- connection_list_cell_eq; [| assumption].

  set (conn_before_populate :=
         {| conn_id := conn_id conn;
            conn_request := conn_request conn ++ msg;
            conn_response := conn_response conn;
            conn_response_bytes_sent := conn_response_bytes_sent conn;
            conn_state := conn_state conn
         |}).            
  
  fold_rep_connection conn_before_populate fd.
  {
    go_lower.
    rewrite add_repr.
    subst conn_before_populate;
    unfold rep_connection, BUFFER_SIZE;
    simpl.
    unfold rep_msg_len.
    autorewrite_sublist.
    cancel.
  } 

  forward_call (conn_before_populate,
                fd,
                last_msg,
                conn_ptr,
                msg_store_ptr).
  
  Intro vret.
  destruct vret as [[populate_ret conn_post_populate] last_msg'].
  simpl fst; simpl snd.
  Intros.
  
  forward_if.
  { (* impossible branch *)
    omega.
  } 
  
  unfold rep_connection.
  rewrite connection_list_cell_eq; [| assumption].

  Intros.
  forward.

  gather_SEP 0 1 2 3 4 5 6 7 8.
  repeat rewrite <- sepcon_assoc.
  rewrite <- connection_list_cell_eq; [| assumption].
  
  trace_bind_ret.
  
  to_equal.
  forward.
  from_equal.

  Exists (upd_conn_state conn_post_populate SENDING).
  Exists last_msg'.
  Exists st_post_recv.
  Exists YES.

  subst conn_post_populate conn_before_populate st_post_recv last_msg'.
  repeat apply andp_right; auto.
  - apply prop_right; repeat split; auto.
    apply Conn_RECVING_SENDING; subst; simpl; auto.
  - autounfold with updates.
    simpl.
    unfold rep_connection, rep_connection_state.
    simpl.
    cancel.
      
Qed.