From Custom Require Import String.

Require Import DeepWeb.Spec.ServerDefs.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog Representation init_store_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib Store.

Set Bullet Behavior "Strict Subproofs".

Lemma body_init_store:
  semax_body Vprog Gprog f_init_store init_store_spec.
Proof.
  start_function.

  forward.
  forward.

  unfold_field_at 1%nat.
  focus_SEP 1.

  assert_PROP (field_compatible (Tstruct _store noattr)
                                [StructField _stored_msg_len] ptr)
    by entailer!.
  
  assert_PROP (field_compatible (Tstruct _store noattr)
                                [StructField _stored_msg] ptr)
    by entailer!.

  forward_call (field_address (Tstruct _store noattr)
                              [StructField _stored_msg] ptr,
                48, (* '0' *)
                1024).
  { 
    entailer!.
    rewrite field_address_offset by assumption.
    simpl.
    reflexivity.
  } 
  
  { replace (1024 >? 0) with true
      by (symmetry; rewrite <- Zgt_is_gt_bool; omega).
    repeat rewrite field_at_data_at.
    cancel.
  }
  { rep_omega. }

  replace (1024 >? 0) with true
    by (symmetry; rewrite <- Zgt_is_gt_bool; omega).

  replace (list_repeat _ _) with (rep_msg INIT_MSG BUFFER_SIZE).
  2 : {
    unfold rep_msg.
    assert (Zlength (val_of_string INIT_MSG) = BUFFER_SIZE) as Hmsg.
    { unfold INIT_MSG.
      rewrite Zlength_val_string_len.
      rewrite repeat_string_length.
      autorewrite_sublist; auto.
      unfold BUFFER_SIZE; omega.
    } 
    rewrite Hmsg.
    replace (BUFFER_SIZE - BUFFER_SIZE) with 0 by omega.
    simpl list_repeat at 1.
    rewrite app_nil_r.
    unfold INIT_MSG.
    rewrite repeat_string_list_repeat.
    unfold BUFFER_SIZE.
    f_equal.
  }

  data_at_to_field_at.
  field_at_rebase_ptr.
  focus_SEP 1.
  data_at_to_field_at.
  field_at_rebase_ptr.
  { cancel. }
  simpl.

  gather_SEP 0 1.
  erewrite <- field_at_rep_store_eq by reflexivity.

  forward.
  
Qed.