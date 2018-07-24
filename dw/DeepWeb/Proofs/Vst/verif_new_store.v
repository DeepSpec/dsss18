Require Import String.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog
     Representation new_store_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib Store.

Set Bullet Behavior "Strict Subproofs".

Lemma body_new_store:
  semax_body Vprog Gprog f_new_store new_store_spec.
Proof.
  start_function.
  
  forward_call (Tstruct _store noattr).
  { repeat split; simpl; auto; rep_omega. }

  Intro new_ptr.
  
  forward_if.
  { destruct new_ptr; try tauto.
    - simpl in PNnew_ptr.
      subst.
      entailer.
    - simpl.
      entailer.
  }
  { subst.

    destruct (eq_dec nullval nullval);
      forward.

    Exists (None : option store).
    Exists nullval.
    entailer!.
  }

  destruct (eq_dec new_ptr nullval); [ tauto |].
  
  assert_PROP (field_compatible (Tstruct _store noattr) [] new_ptr)
    by entailer!.
  assert_PROP (field_compatible (Tstruct _store noattr)
                                [StructField _stored_msg] new_ptr)
    by entailer!.

  Intros.
  focus_SEP 1.

  (* Promote to field first *)
  data_at_to_field_at_default.
  
  match goal with
  | [|- context[default_val ?v]] =>
    remember (default_val v) as protected
  end.

  do 2 forward.
  simpl.
  erewrite field_at_rep_store_eq by (subst; reflexivity).
  Intros.
  focus_SEP 1.
  rewrite field_at_data_at.
  rewrite <- Heqprotected.
  erase_data.

  forward_call (offset_val 4 new_ptr, 0, 1024). 
  { replace (1024 >? 0) with true
      by (symmetry; rewrite <- Zgt_is_gt_bool; omega).
    rewrite field_address_offset by assumption.
    simpl.
    cancel.
  }
  { rep_omega. }

  replace (1024 >? 0) with true
    by (symmetry; rewrite <- Zgt_is_gt_bool; omega).

  match goal with
  | [|- context[list_repeat ?n ?v]] =>
    remember (list_repeat n v) as protected'
  end.

  forward.

  Exists (Some {| stored_msg := "" |}) new_ptr.
  unfold rep_store.
  erewrite field_at_rep_store_eq; [| reflexivity].
  rewrite rep_empty_string.
  unfold BUFFER_SIZE.
  repeat rewrite field_at_data_at.

  entailer!.
  rewrite field_address_offset by assumption.
  cancel.

Qed.