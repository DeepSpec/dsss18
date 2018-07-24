Require Import String.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog Representation reset_connection_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib Connection.

Set Bullet Behavior "Strict Subproofs".

Lemma body_reset_connection:
  semax_body Vprog Gprog f_reset_connection reset_connection_spec.
Proof.
  start_function.

  assert_PROP
    (field_compatible (Tstruct _connection noattr) [] conn_ptr)
    by entailer!.

  assert_PROP
    (field_compatible (Tstruct _connection noattr)
                      [StructField _request_buffer] conn_ptr)
    by entailer!.

  assert_PROP
    (field_compatible (Tstruct _connection noattr)
                      [StructField _response_buffer] conn_ptr)
    by entailer!.
  
  unfold rep_connection.
  rewrite connection_list_cell_eq; [| assumption].

  Intros.

  do 7 forward.

  simpl offset_val.

  freeze [0; 1; 3; 4; 5; 6] FR1.
  simpl.

  focus_SEP 1.
  rewrite field_at_data_at.
  simpl.
  rem_ptr ptr.
  forward_call (ptr, 0, BUFFER_SIZE).
  { subst; apply prop_right; repeat split;
      rewrite field_address_offset; simpl; auto. }
  { unfold BUFFER_SIZE; rep_omega. }
  
  subst ptr.  
  remember (Z.to_nat BUFFER_SIZE) as size.
  unfold BUFFER_SIZE.
  simpl.
  erase_data.
  subst size.

  thaw FR1; simpl.

  freeze [0; 1; 2; 3; 5; 6] FR1.
  simpl.

  focus_SEP 1.
  rewrite field_at_data_at.
  simpl.
  rem_ptr ptr.
  forward_call (ptr, 0, BUFFER_SIZE).
  { subst; apply prop_right; repeat split;
      rewrite field_address_offset; simpl; auto. }
  { unfold BUFFER_SIZE; rep_omega. }

  subst ptr.  
  remember (Z.to_nat BUFFER_SIZE) as size.
  unfold BUFFER_SIZE.
  simpl.
  erase_data.
  subst size.

  thaw FR1; simpl.

  forward.
  unfold rep_connection.
  autounfold with updates.
  unfold BUFFER_SIZE.
  simpl.
  rewrite connection_list_cell_eq; [| assumption].
  repeat (rewrite field_at_data_at).
  cancel.
  rewrite rep_empty_string.

  cancel.
  
Qed.