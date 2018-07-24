Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit 
     Vst.Representation Swap_CLikeSpec.

From DeepWeb.Lib
     Require Import VstLib Socket.

From DeepWeb.Proofs.Vst
     Require Import VerifLib.

Import SocketAPI.

Open Scope logic.
Open Scope list.

Set Bullet Behavior "Strict Subproofs".

Section Lseg_Lemmas.

  Context {list_structid list_link : ident}.

  Lemma lseg_valid_pointer:
  forall (ls : listspec list_structid list_link list_token) sh contents p q R,
    sepalg.nonidentity sh ->
    field_offset cenv_cs list_link
                 list_fields + sizeof (field_type list_link list_fields)
    = field_offset_next cenv_cs list_link
                        list_fields (co_sizeof (get_co list_structid)) ->
    R |-- valid_pointer q ->
    R * lseg ls sh sh contents p q |-- valid_pointer p.
  Proof.
    intros ? ? ? ? ? ? NON_ID ? ?.
    destruct contents as [| [ptr rep] rest].
    { rewrite lseg_nil_eq. entailer. }
    rewrite lseg_unfold.
    Intros tail.
    apply sepcon_valid_pointer2.
    apply sepcon_valid_pointer1.
    rewrite sepcon_assoc.
    apply sepcon_valid_pointer2.
    eapply derives_trans; [| eapply LsegSpecial.list_cell_valid_pointer; eauto].
    cancel.
    apply derives_refl.
  Qed.

End Lseg_Lemmas.

(************************* Representation and Lemmas **************************)

Lemma connection_list_cell_eq:
  forall (sh : share) (fd_rep : val)
    (request_len_rep : val) (request_rep : list val)
    (response_len_rep : val) (response_rep : list val)
    (response_bytes_sent_rep : val)
    (state_rep : val) (ptr : val),
    field_compatible (Tstruct _connection noattr) [] ptr ->
    list_cell LS sh
              (fd_rep,
               (request_len_rep,
                (request_rep,
                 (response_len_rep,
                  (response_rep,
                   (response_bytes_sent_rep, state_rep))))))
              ptr =
    field_at sh (Tstruct _connection noattr) (DOT _fd)
             fd_rep ptr *
    field_at sh (Tstruct _connection noattr) (DOT _request_len)
             request_len_rep ptr *
    field_at sh (Tstruct _connection noattr) (DOT _request_buffer)
             request_rep ptr *
    field_at sh (Tstruct _connection noattr) (DOT _response_len)
             response_len_rep ptr *
    field_at sh (Tstruct _connection noattr) (DOT _response_buffer)
             response_rep ptr *
    field_at sh (Tstruct _connection noattr) (DOT _num_bytes_sent)
             response_bytes_sent_rep ptr *    
    field_at sh (Tstruct _connection noattr) (DOT _st)
             state_rep ptr.
Proof.
  intros.
  unfold field_at.
  rewrite !prop_true_andp by (auto with field_compatible).
  simpl.
  unfold list_cell, withspacer.
  simpl.
  rewrite prop_true_andp by (auto with field_compatible).
  repeat (rewrite sepcon_assoc).
  auto.
Qed.

Lemma filter_proj_commutes {X Y : Type} (proj: X -> Y)
      (p1 : X -> bool) (p2 : Y -> bool) :
  (forall x, p1 x = true <-> p2 (proj x) = true) ->
  forall (l : list X),
    map proj (filter p1 l) = filter p2 (map proj l).
Proof.
  induction l.
  { simpl; reflexivity. }
  simpl.
  destruct (p1 a) eqn:p1_a.
  - apply H in p1_a.
    rewrite p1_a.
    simpl.
    rewrite IHl by assumption.
    reflexivity.
  - destruct (p2 (proj a)) eqn:p2_a.
    + rewrite <- H in p2_a; rewrite p1_a in p2_a; discriminate.
    + apply IHl; assumption.
Qed.

Lemma has_conn_state_proj:
  forall (c : connection * sockfd * val) (st : connection_state),
    has_conn_state st c = true <-> has_conn_state st (proj_conn c) = true.
Proof.
  intros [[c ?] ?].
  simpl.
  split;
    intros H; auto.
Qed.

Tactic Notation "fold_rep_connection" constr(conn) constr(fd) :=
  match goal with
  | [|- context[SEPx (list_cell ?ls ?sh ?rep ?ptr :: _)]] =>
    replace_SEP
      0
      (list_cell ls sh (rep_connection conn fd) ptr)
  end.

Ltac prove_lseg_ptr_null_test :=
  let tac sh ptr :=
      apply denote_tc_test_eq_split; [| apply valid_pointer_null];
      repeat rewrite sepcon_assoc;
      apply sepcon_valid_pointer1;
      eapply derives_trans;
      [| apply (lseg_valid_pointer _ sh); auto];
      [ first [rewrite emp_sepcon; apply derives_refl
              | idtac "cannot unify"]
      | try apply valid_pointer_null]
  in 
  match goal with
  | [|- derives
         ?LHS
         (* ! tc_expr _ (ptr_name != (tptr void) (0)) *)
         (tc_expr _
                  (Eunop Onotbool
                         (Ebinop One (_ ?ptr_name _) ?casted_null _) tint))] =>
    match LHS with
    | context[temp ptr_name ?ptr] =>
      match goal with
      | [|- context[SEPx (lseg _ ?sh ?sh _ ptr _ :: _)]] =>
        go_lower;
        tac sh ptr
      end
    end
  | [|- derives ?LHS (denote_tc_test_eq ?ptr _)] =>
    match LHS with 
    | context[lseg _ ?sh ?sh _ ?ptr _] =>
      tac sh ptr
    end
  end.

Ltac fold_conn_cell_into_prefix :=
  match goal with
  | [|- context[SEPx (?cell_pred :: _)]] =>
    match cell_pred with
    | list_cell ?LS ?sh ?cell_rep ?curr_ptr
      * (field_at ?sh _ [StructField _] ?tail ?curr_ptr
         * (lseg _ ?sh ?sh ?prefix_rep ?head ?curr_ptr
            * lseg _ _ _ ?suffix_rep ?tail nullval)) =>
      replace_SEP
        0
        (lseg LS sh sh (prefix_rep ++ [(curr_ptr, cell_rep)]) head tail
         * lseg LS sh sh suffix_rep tail nullval);
      [ go_lower;
        pose proof (@lseg_cons_right_list) as lem;
        eapply derives_trans; [| apply lem]; auto;
        unfold rep_connection;
        simpl;
        cancel
      | ]
    end
  end.
