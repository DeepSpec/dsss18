Require Import String.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog Representation
     populate_response_spec SocketSpecs LibrarySpecs.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib Connection Store.

Open Scope list.
Open Scope logic.

Set Bullet Behavior "Strict Subproofs".

Lemma body_populate_response:
  semax_body Vprog Gprog f_populate_response populate_response_spec.
Proof.
  start_function.
  
  (* Saturate [field_compatible] for list cell and all accessed buffers *)
  assert_PROP (field_compatible (Tstruct _connection noattr) [] conn_ptr)
    by entailer!.
  assert_PROP (field_compatible (Tstruct _connection noattr)
                                [StructField _response_buffer] conn_ptr)
    by entailer!.
  assert_PROP (field_compatible (Tstruct _store noattr)
                                [StructField _stored_msg] last_msg_store_ptr)
    by entailer!.
  assert_PROP (field_compatible (Tstruct _connection noattr)
                                [StructField _request_buffer] conn_ptr)
    by entailer!.
  
  unfold rep_connection.
  rewrite connection_list_cell_eq; [| assumption].

  focus_SEP 1.
  Intros.
  unfold_field_at 1%nat.
  
  forward.
  forward.
  forward.
  forward.
  forward.
  simpl.

  freeze [0; 2; 3; 4; 5; 7; 8] FR1; simpl.

  focus_SEP 1.
  rewrite field_at_data_at; simpl; unfold tarray; saturate_rep_msg_bounds.
  split_data_at (Zlength (val_of_string last_msg)).

  focus_SEP 2.
  rewrite field_at_data_at; simpl; unfold tarray; saturate_rep_msg_bounds.
  split_data_at (Zlength (val_of_string last_msg)).

  Intros.

  rem_ptr dst_ptr.
  focus_SEP 2.
  rem_ptr src_ptr.

  forward_memcpy dst_ptr src_ptr (Zlength (val_of_string last_msg)).
  { apply prop_right; subst;
      repeat (rewrite field_address_offset; [| assumption]);
      split; simpl; auto.
  }
  { rep_omega. }

  unfold tarray, BUFFER_SIZE in *.

  (* Coalesce: erase tail, coalesce *)
  focus_SEP 2.
  erase_data.
  gather_SEP 1 0.
  coalesce.
  fold_rep_msg.

  focus_SEP 2.
  erase_data.
  gather_SEP 2 0.
  coalesce.
  fold_rep_msg.

  subst dst_ptr src_ptr.
  focus_SEP 1.
  data_at_to_field_at.

  thaw FR1.
  simpl.

  forward.
  forward.
  forward.

  freeze [0; 2; 3; 4; 6; 7; 8] FR1; simpl.
  
  (* Split *)
  focus_SEP 2.
  rewrite field_at_data_at; simpl; saturate_rep_msg_bounds.
  split_data_at (Zlength (val_of_string (conn_request conn))).

  focus_SEP 2.
  split_data_at (Zlength (val_of_string (conn_request conn))).

  Intros.
  
  (* memcpy: no need to explicitly erase destination *)
  rem_ptr dst_ptr.
  focus_SEP 2.
  rem_ptr src_ptr.

  forward_memcpy dst_ptr src_ptr (Zlength (val_of_string (conn_request conn))).
  { apply prop_right; subst;
      repeat (rewrite field_address_offset; [| assumption]);
      split; simpl; auto.
  }
  { rep_omega. }

  (* Coalesce *)
  
  focus_SEP 2.
  erase_data.
  gather_SEP 1 0.
  coalesce.
  fold_rep_msg.
  
  focus_SEP 2.
  erase_data.
  gather_SEP 2 0.
  coalesce.
  fold_rep_msg.

  subst dst_ptr src_ptr.

  (* Conclude *)
  forward.
  Exists 1.
  set (conn' :=
         upd_conn_response_bytes_sent
           (upd_conn_response conn last_msg) 0).
  Exists conn' (conn_request conn).
  thaw FR1; simpl.

  erewrite field_at_rep_store_eq; [| reflexivity].
  unfold rep_connection.
  rewrite connection_list_cell_eq; [| assumption].

  simpl.
  repeat apply andp_right; auto.
  - apply prop_right; repeat split; auto; omega.
  - repeat rewrite field_at_data_at.
    cancel.
    rewrite field_address_offset.
    
    2: {
      rewrite field_address_offset by assumption.
      pose proof (field_compatible_nested_field
                    (Tstruct _connection noattr)
                    [StructField _response_buffer] conn_ptr).
      auto.
    }
    rewrite isptr_offset_val_zero.
    cancel.
    apply field_address_isptr; assumption.
    
Qed.