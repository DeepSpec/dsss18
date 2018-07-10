Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib VerifHelpers ServerSpecs
     Store new_store_spec.

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

  (* Decompose into separate fields *)
  erewrite field_at_rep_store_eq; [| subst; reflexivity].
  subst protected.
  Intros.

  match goal with
  | [|- context[list_repeat ?n ?v]] =>
    remember (list_repeat n v) as protected
  end.

  forward.
  forward.

  (* memset *)
  focus_SEP 1.
  rewrite field_at_data_at.
  erase_data. (* not necessary, but faster *)
  subst protected.
  simpl.

  forward_call
    (field_address (Tstruct _store noattr) [StructField _stored_msg] new_ptr,
     0, 1024); [| simpl; cancel |].
  { apply prop_right; repeat split; simpl; auto.
    rewrite field_address_offset; [| assumption].
    auto.
  }

  match goal with
  | [|- context[list_repeat ?n ?v]] =>
    remember (list_repeat n v) as protected;
      to_equal
  end.
  simpl.

  forward.
  from_equal.

  Exists (Some {| stored_msg := "" |}).
  Exists new_ptr.
  unfold rep_store.
  erewrite field_at_rep_store_eq; [| reflexivity].
  rewrite rep_empty_string.
  unfold BUFFER_SIZE.
  repeat rewrite field_at_data_at.

  subst.
  repeat apply andp_right; auto.
  - apply prop_right; repeat split; auto.
    intros; tauto.
  - cancel.
Qed.