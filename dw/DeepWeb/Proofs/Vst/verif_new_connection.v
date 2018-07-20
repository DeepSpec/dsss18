Require Import String.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs Representation
     new_connection_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs
     Require Import VerifLib Connection.

Set Bullet Behavior "Strict Subproofs".

Lemma body_new_connection:
  semax_body Vprog Gprog f_new_connection new_connection_spec.
Proof.
  start_function.
  forward_call (Tstruct _connection noattr).
  { repeat split; simpl; auto; rep_omega. }

  Intro conn_ptr.

  forward_if.
  { destruct conn_ptr; try tauto.
    - simpl in PNconn_ptr.
      subst.
      entailer.
    - simpl.
      entailer.
  }
  { subst.
    simpl.
    forward.
    Exists (None : option connection).
    Exists nullval.
    entailer!.
  }

  match goal with
    | [|- context[if ?cond then _ else _]] =>
      destruct cond; [tauto | ]
  end.

  Intros.

  focus_SEP 1.
  data_at_to_field_at_default.

  do 6 forward.

  set (new_conn := {| conn_id := Connection 0%nat;
                      conn_request := "";
                      conn_response := "";
                      conn_response_bytes_sent := 0;
                      conn_state := RECVING
                   |}).

  set (new_fd := {| descriptor := 0; is_descriptor := zero_is_fd |}).

  match goal with
  | [|- context[field_at _ _ _ ?rep _]] =>
    assert
      (rep = 
       (Vint (Int.repr (descriptor new_fd)),
        (rep_msg_len (conn_request new_conn),
         (rep_msg (conn_request new_conn) BUFFER_SIZE,
          (rep_msg_len (conn_response new_conn),
           (rep_msg (conn_response new_conn) BUFFER_SIZE,
            (Vint (Int.repr (conn_response_bytes_sent new_conn)),
             (rep_connection_state (conn_state new_conn),
              Vint (Int.repr 0))))))))) as Hrep by reflexivity;
      rewrite Hrep;
      clear Hrep
  end.

  unfold_field_at 1%nat.

  gather_SEP 0 1 2 3 4 5 6.
  repeat rewrite <- sepcon_assoc.
  assert_PROP (field_compatible (Tstruct _connection noattr) [] conn_ptr)
    by entailer!.
  rewrite <- connection_list_cell_eq; [| assumption].
  
  fold_rep_connection new_conn new_fd.
  { go_lower; subst new_conn; unfold rep_connection; simpl; cancel. }

  forward.
  Exists (Some new_conn).
  Exists conn_ptr.
  Exists nullval.

  repeat apply andp_right; auto.
  - apply prop_right; repeat split; auto. intros; tauto. 
  - cancel.
    apply andp_right; [entailer | cancel].
    subst new_fd.
    entailer.
    
Qed.
