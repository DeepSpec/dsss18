Require Import String.

From DeepWeb.Spec
     Require Import Swap_CLikeSpec
     Vst.SocketSpecs Vst.MainInit Vst.MonadExports.

From DeepWeb.Lib 
     Require Import VstLib.

Import TracePred.
Import SockAPIPred.

Open Scope logic.
Open Scope list.

Definition malloc_tokens (t : type) (ptrs : list val) :=
  fold_right (fun ptr a => sepcon a (malloc_token Tsh t ptr)) emp ptrs.

Lemma cons_malloc_tokens (t : type) (ptrs : list val) (ptr : val):
  malloc_tokens t ptrs * malloc_token Tsh t ptr
  = malloc_tokens t (ptr :: ptrs).
Proof.
  unfold malloc_tokens.
  rewrite fold_right_cons.
  reflexivity.
Qed.

Lemma split_data_app:
  forall (n1 n2 : Z) (prefix suffix : list val) (ptr : val)
    (sh : share),
    0 <= n1 <= n2 ->
    Zlength prefix = n1 ->
    Zlength suffix = n2 - n1 ->
    data_at sh (Tarray tuchar n2 noattr) (prefix ++ suffix) ptr =              
    data_at sh (Tarray tuchar n1 noattr)
            prefix ptr *
    data_at sh (Tarray tuchar (n2 - n1) noattr)
            suffix (field_address0 (Tarray tuchar n2 noattr)
                                   [ArraySubsc n1] ptr).
Proof.
  intros n1 n2 prefix suffix ptr sh [? ?] prefix_len suffix_len.
  remember (prefix ++ suffix) as buffer.
  assert (prefix = sublist 0 n1 buffer) as prefix_eq.
  {
    rewrite Heqbuffer.
    rewrite sublist_app1; [| omega..].
    rewrite <- prefix_len.
    rewrite sublist_same; auto.
  }
  assert (suffix = sublist n1 n2 buffer) as suffix_eq.
  {
    rewrite Heqbuffer.
    rewrite sublist_app2; [| omega].
    rewrite sublist_same; [auto | omega |].
    rewrite prefix_len.
    auto.
  }
  rewrite prefix_eq.
  rewrite suffix_eq.
  apply split2_data_at_Tarray_tuchar; [omega |].
  subst; rewrite Zlength_app; omega.
Qed.

Lemma data_at__Tarray_Vundef:
  forall n sh attr ptr,
    data_at sh (Tarray tuchar n attr)
            (list_repeat (Z.to_nat n) Vundef)
            ptr
    = data_at_ sh (Tarray tuchar n attr) ptr.
Proof.
  intros.
  unfold data_at_.
  unfold field_at_.
  unfold default_val.
  simpl.
  reflexivity.
Qed.

Lemma split_data_with_undefined_tail:
  forall (n1 n2 : Z) (prefix suffix : list val) (ptr : val) (sh : share),
    0 <= n1 <= n2 ->
    n1 = Zlength prefix ->
    suffix = list_repeat (Z.to_nat (n2 - n1)) Vundef ->
    data_at sh (Tarray tuchar n2 noattr) (prefix ++ suffix) ptr =              
    data_at sh (Tarray tuchar n1 noattr)
            prefix ptr *
    data_at_ sh (Tarray tuchar (n2 - n1) noattr)
             (field_address0 (Tarray tuchar n2 noattr)
                             [ArraySubsc n1] ptr).
Proof.
  intros.
  rewrite <- data_at__Tarray_Vundef.
  rewrite H1.
  pose proof split_data_app as Hsplit.
  unfold tarray in Hsplit.
  rewrite split_data_app with (n1 := n1); auto.
  rewrite Zlength_list_repeat; omega.
Qed.

Module Auto_DB.

  Hint Rewrite <- val_of_string_app : sublist_supp.
  Hint Rewrite <- Zlength_app : sublist_supp.

  (* Conversion from Nat to Z *)
  Hint Rewrite Z2Nat.id using (subst; simpl; try omega) : sublist_supp.
  Hint Rewrite Nat2Z.id : sublist_supp.
  Hint Rewrite Nat2Z.inj_le using (subst; simpl; try omega) : sublist_supp.

  (* String *)
  Hint Rewrite <- Zlength_val_string_len : sublist_supp.
  Hint Rewrite substring_sublist : sublist_supp.
  (* Warning: May be over-aggressive; assumes that everything is within 
     bounds *)
  Hint Rewrite (@sublist_skip val)
       using (subst; simpl; try omega) : sublist_supp.
  Hint Rewrite (@Zlength_skipn val) : sublist_supp.
  Hint Rewrite Zmax0r using (subst; simpl; try omega) : sublist_supp.

  Lemma rejoin_size1: forall n m : Z, n + (m - n) = m.
  Proof. intros; omega. Qed.

  Lemma rejoin_size2 : forall (n m : nat), (n <= m)%nat -> (n + (m - n))%nat = m.
  Proof. intros; omega. Qed.

  Hint Rewrite rejoin_size1: sublist_supp.
  Hint Rewrite rejoin_size2
       using (apply Nat2Z.inj_le; subst; simpl; try omega) : sublist_supp.
  
  Tactic Notation "autorewrite_sublist" :=
    autorewrite with sublist;
    autorewrite with sublist_supp.

  Tactic Notation "autorewrite_sublist" "in" ident(H) :=
    autorewrite with sublist in H;
    autorewrite with sublist_supp in H.
  
  Hint Rewrite add_repr : vst_repr.

  Hint Unfold upd_conn_request : updates.
  Hint Unfold upd_conn_response : updates.
  Hint Unfold upd_conn_response_bytes_sent : updates.
  Hint Unfold upd_conn_state : updates.

  Hint Resolve trace_incl_respects_bind_assoc.
  Hint Resolve trace_or_incl_bind1.
  Hint Resolve trace_incl_refl.

End Auto_DB.

Module Protection.
  Inductive equal {A : Type} (x : A): A -> Prop :=
  | equal_refl: equal x x.

  Lemma equal_iff : forall (A : Type) (x y : A), x = y <-> equal x y.
  Proof. intros. split; intros; inversion H; try constructor; auto. Qed.

  Ltac to_equal :=
    repeat match goal with
           | [H : _ = _ |- _] =>
             apply equal_iff in H
           end.

  Ltac from_equal :=
    repeat match goal with
           | [H : equal _ _ |- _] =>
             apply equal_iff in H
           end.
End Protection.

Module Int_Repr.
        
  Ltac int_repr_inversion :=
    match goal with
    | [|- ?x = ?y] =>
      match goal with
      | [H: Int.repr x = Int.repr y |- _] =>
        apply repr_inj_signed in H;
        unfold repable_signed;
        try rep_omega
      end
    | [|- ?x <> ?y] =>
      match goal with
      | [H: Int.repr x <> Int.repr y |- _] =>
        apply repr_inj_signed' in H;
        unfold repable_signed;
        try rep_omega
      end    
    end.

  Ltac int_ineq_to_Z_ineq :=
    match goal with
    | [H : context[Int.signed (Int.repr ?r)] |- context[?r] ] =>
      rewrite Int.signed_repr in H;
      try rep_omega
    | [H: Int.repr _ <> Int.repr _ |- _] =>
      apply repr_neq_e in H
    end.
  
End Int_Repr.

Module Trace_Tactics.
  (* Introduces hypothesis that left branch of "Or" in current Itree is 
   included in the current Itree
   *)
  Ltac intro_trace_or_incl HTrace left_trace :=
    match goal with
    | [|- context[ITREE ?t]] =>
      match t with
      | (r <- ?or_trace ;; ?k) =>
        match or_trace with
        | or ?t1 ?t2 =>
          remember t1 as left_trace;
          assert (trace_incl (r <- t1 ;; k) t)
            as HTrace
              by (apply trace_or_incl_bind1)
        end
      | or ?t1 ?t2 =>
        remember t1 as left_trace;
        assert (trace_incl t1 t) as HTrace
            by (apply trace_or_incl)
      end
    end.

  (* Introduces hypothesis that current Itree is included in itself *)
  Ltac intro_trace_refl_incl HTrace :=
    match goal with
    | [|- context[ITREE ?t]] =>
      assert (trace_incl t t) as HTrace
          by (apply trace_incl_refl)
    end.

  Ltac simpl_trace_incl HTrace :=
    try apply trace_incl_respects_bind_assoc in HTrace.

  (* Chooses either first or second branch of "Or" *)
  Ltac take_branch1 idx := 
    match goal with
    | [|- context[ITREE (bind (or ?branch1 ?branch2) ?k)]] =>
      replace_SEP idx (ITREE (r <- branch1 ;; k r));
      [go_lower; apply internal_nondet1 | ]
    end.

  Ltac take_branch2 idx := 
    match goal with
    | [|- context[ITREE (bind (or ?branch1 ?branch2) ?k)]] =>
      replace_SEP idx (ITREE (r <- branch2 ;; k r));
      [go_lower; apply internal_nondet2 | ]
    end.

  Ltac trace_bind_ret :=
    match goal with
    | [|- context[ITREE (bind (ret ?a) ?k)]] =>
      rewrite (trace_bind_ret a)
    | [|- context[ITREE (bind (Ret ?a) ?k)]] =>
      rewrite (trace_bind_ret a)
    end.

  Ltac rem_trace_tail cont :=
  match goal with
  | [ |- context[ITREE (bind _ ?k)]] =>
    remember k as cont
  end.

  Ltac rem_trace cont :=
    match goal with
    | [ |- context[ITREE ?k]] =>
      remember k as cont
    end.

  Ltac rem_trace_or cont1 cont2 cont3 :=
    match goal with
    | [|- context[ITREE (bind (or ?k1 ?k2) ?k3)]] =>
      remember k1 as cont1;
      remember k2 as cont2;
      remember k3 as cont3
    end.

  Ltac unify_trace :=
    match goal with
    | [|- derives ?LHS ?RHS] =>
      match LHS with
      | context[ITREE ?tr1] =>
        match RHS with
        | context[ITREE ?tr2] =>
          replace tr1 with tr2 by reflexivity
        end
      end
    end.
  
End Trace_Tactics.

Module Field_At_Data_At.

  Ltac rem_ptr p :=
    match goal with
    | [|- context[SEPx (?data_pred :: _)]] =>
      match data_pred with
      | data_at _ _ _ ?ptr =>
        remember ptr as p 
      | data_at_ _ _ ?ptr =>
        remember ptr as p
      | field_at _ _ _ _ ?ptr =>
        remember ptr as p
      | field_at_ _ _ _ ?ptr =>
        remember ptr as p
      end
    end.

  (* Changes first sep conjunct containing data_at to field_at_ *)
  Ltac data_at_to_field_at :=
    match goal with
    | [|- context[SEPx (?data_pred :: ?SP)]] =>
      match data_pred with
      | data_at ?sh ?reptype ?rep ?ptr =>
        replace_SEP 0 (field_at sh reptype [] rep ptr) by entailer!
      end
    end.

  (* Changes first sep conjunct containing data_at to field_at with defaults *)
  Ltac data_at_to_field_at_default :=
    let to_data_at__ sh reptype ptr :=
        (replace_SEP
           0
           (data_at_ sh reptype ptr) by entailer!) in
    let to_field_at_default sh reptype ptr :=
        (replace_SEP
           0
           (field_at sh reptype [] (default_val reptype) ptr)
          by entailer!) in
    match goal with
    | [|- context[SEPx (?data_pred :: ?SP)]] =>
      match data_pred with
      | data_at ?sh ?reptype ?rep ?ptr =>
        to_data_at__ sh reptype ptr;
        to_field_at_default sh reptype ptr
      | data_at_ ?sh ?reptype ?ptr =>
        to_field_at_default sh reptype ptr
      end
    end.

  (* At first sep conjunct containing a [field_at] with a [field_address] ptr, 
   rebase it to the head of the structure.
   *)
  Ltac field_at_rebase_ptr :=
    match goal with
    | [|- context[SEPx (?field_at_pred :: _)]] =>
      match field_at_pred with
      | field_at ?sh ?inner_type ?nested_path ?rep
                 (field_address ?base_type ?path ?ptr) =>
        replace_SEP
          0
          (field_at sh base_type (path ++ nested_path) rep ptr);
        [go_lower;
         rewrite field_address_offset; auto;
         unfold field_at, at_offset;
         simpl;
         unfold tarray;
         try rewrite isptr_offset_val_zero; auto;
         try entailer! |] 
      end
    end.

  Ltac erase_data :=
    match goal with
    | [|- context[SEPx (data_at ?sh ?reptype ?rep ?ptr :: _)]] =>
      replace_SEP
        0
        (data_at_ sh reptype ptr) by entailer!
    end.

  Ltac prove_field_compatible0_array_field_addr :=
  match goal with
  | [|- field_compatible0 _ [ArraySubsc _]
                         (field_address ?reptype ?path ?ptr)] =>
    eapply field_compatible0_cons_Tarray; [reflexivity | | auto; try omega];
    let Hcompat := fresh "Hcompat" in
    pose proof (field_compatible_nested_field reptype path ptr) as Hcompat;
    try apply Hcompat
  end.

  Ltac prove_field_compatible_smaller_array :=
    unfold tarray;
    match goal with
    | [|- field_compatible (Tarray _ _ _) ?path ?ptr] =>
      eapply field_compatible_array_smaller0
    end.
  
End Field_At_Data_At.

Module Buffer_Bounds.
  
  (* Introduces bound on representation of contents derived from 
   a data_at/field_at; assumes such a predicate in first position *)
  Ltac intro_rep_in_buffer_bound :=
    unfold tarray;
    match goal with
    | [|- context[SEPx (data_at ?sh ?reptype ?rep ?ptr :: _)]] =>
      match reptype with
      | Tarray _ ?size _ =>
        replace_SEP 0 (!! (Zlength rep <= size) && data_at sh reptype rep ptr)
      end
    | [|- context[SEPx (field_at ?sh ?reptype ?path ?rep ?ptr :: _)]] =>
      match reptype with
      | Tarray _ ?size _ =>
        replace_SEP 0 (!! (Zlength rep <= size) &&
                          field_at sh reptype path rep ptr)
      end
    end;
    [ (* go_lower; try derive_buffer_bound *) entailer! | ].

  (* Given [data_at _ _ (rep_msg msg bound) _] in the first position, 
   saturate context with bounds and equalities that are useful for splitting.
   *)
  Ltac saturate_rep_msg_bounds :=
    match goal with
    | [|- context[SEPx
                   (data_at ?sh ?reptype (rep_msg ?msg ?bound) ?ptr :: _)]] =>
      intro_rep_in_buffer_bound;
      Intros;
      match goal with
      | [H1: Zlength (rep_msg msg _) <= _ |- _] =>
        pose proof (rep_msg_bound _ _ H1);
        pose proof (rep_msg_exact_length _ _ H1)
      end;
      pose proof (Zlength_nonneg (val_of_string msg))
    end.
  
End Buffer_Bounds.

Module Buffer_Splitting.

  Import Auto_DB.
  
  Tactic Notation "split_data_at" :=
    match goal with
    | [|- context[SEPx (data_at _ _ (_ ++ _) ?ptr :: _)]] =>
      first [ unfold tarray;
              erewrite split_data_app;
              [ | | reflexivity | autorewrite_sublist; auto];
              try omega
            | idtac "Try obtaining bounds for buffer contents"]
    end.

  Tactic Notation "split_data_at" constr(offset_term) :=
    match goal with
    | [|- context[SEPx (data_at _ _ _ ?ptr :: _)]] =>
      first [ let offset := fresh "offset" in
              remember offset_term as offset;
              rewrite split2_data_at_Tarray_tuchar with (n1 := offset);
              auto; try omega;
              subst offset
            | idtac "Try obtaining bounds for buffer contents"]
    end.
  
End Buffer_Splitting.

Module Buffer_Coalescing.
  Import Auto_DB.

  (* 
     Finds terms of the form [... ++ list_repeat ... Vundef] and tries to 
     turn it into [rep_msg str] for some str.
   *)
  Ltac fold_rep_msg :=
    let replace_tac rep msg bound :=
        (replace rep with (rep_msg msg bound);
         [| unfold BUFFER_SIZE; unfold rep_msg;
            autorewrite_sublist; auto])
    in
    match goal with
    | [|- context[sublist ?m ?n (rep_msg ?msg ?bound)
                         ++ list_repeat ?c Vundef]] =>
      replace_tac (sublist m n (rep_msg msg bound) ++ list_repeat c Vundef)
                  msg bound
    (* | [|- context [val_of_string ?msg1 ++ val_of_string ?msg2
                                ++ list_repeat ?undef_len Vundef]] =>
      replace_tac (val_of_string msg1 ++ val_of_string msg2
                                 ++ list_repeat undef_len Vundef)
                  (msg1 ++ msg2)%string
                  (Zlength (val_of_string ((msg1 ++ msg2)%string))
                   + Z.of_nat undef_len) *)
    | [|- context [val_of_string ?msg ++ list_repeat ?undef_len Vundef]] =>
      replace_tac (val_of_string msg ++ list_repeat undef_len Vundef)
                  msg (Zlength (val_of_string msg) + Z.of_nat undef_len)
    end;
    autorewrite_sublist.

  (* Assumes a first sep conjunct of the forms :
     - [data_at ... * data_at ...]
     - [data_at ... * data_at_ ...]
     Rejoins into a single [data_at ...].
  *)
  Ltac coalesce :=
    let pre := (unfold tarray; unfold rep_msg) in
    (* let post := (autorewrite_sublist; try fold_rep_msg) in *)
    match goal with
    | [|- context[SEPx (?data_pred :: _)]] =>
      match data_pred with
      | data_at _ _ _ ?ptr * data_at _ _ _ (field_address0 _ _ ?ptr) =>
        let new_data_pred := fresh "new_data" in
        pre;
        evar (new_data_pred : mpred);
        replace_SEP 0 new_data_pred;
        [ go_lower; rewrite <- split_data_app;
          (* simplify before unification + simplify to solve constraints *)
          autorewrite_sublist; 
          [ subst new_data_pred; apply derives_refl
          | auto; try omega..]
        |
        ]; subst new_data_pred 
      | data_at _ _ _ ?ptr * data_at_ _ _ (field_address0 _ _ ?ptr) =>
        let new_data_pred := fresh "new_data" in        
        pre;
        evar (new_data_pred : mpred);
        replace_SEP 0 new_data_pred;
        [ go_lower;
          erewrite <- split_data_with_undefined_tail;
          autorewrite_sublist;
          [ | | | reflexivity];
          [subst new_data_pred; apply derives_refl
          | auto; try omega ..]
        |
        ]; subst new_data_pred
      end
    end.
  
End Buffer_Coalescing.

Section Deprecated.

  Import Protection.
  Import Trace_Tactics.

  Ltac forward_if_with conjunct := 
    match goal with
    | [|- semax _
               (PROPx ?Props
                      (LOCALx ?Locals
                              (SEPx ?SP))) _ _] =>
      forward_if (PROPx (conjunct :: Props)
                        (LOCALx Locals
                                (SEPx SP)))
    end.
      
  Ltac bool_ineq_to_prop :=
    match goal with
    | [|- ~(?LHS > ?RHS)] =>
      match goal with
      | [H: LHS >? RHS = false |- _] =>
        unfold not; intros Hnot;
        rewrite Zgt_is_gt_bool in Hnot;
        rewrite Hnot in H; inversion H
      end
    | [|- ?LHS > ?RHS] =>
      match goal with
      | [H : LHS >? RHS = true |- _] =>
        rewrite Zgt_is_gt_bool; auto
      end
    | [|- ?LHS <= ?RHS] =>
      match goal with
      | [H : LHS <=? RHS = true |- _] =>
        rewrite Zle_is_le_bool; auto
      end
    | [|- ~(?LHS <= ?RHS)] =>
      match goal with
      | [H: LHS <=? RHS = false |- _] =>
        unfold not; intros Hnot;
        rewrite Zle_is_le_bool in Hnot;
        rewrite Hnot in H; inversion H
      end
    end.

  Tactic Notation "seal_entailer" :=
    let cont := fresh "cont" in
    (try rem_trace cont; to_equal; entailer!; from_equal; try subst cont).

  Tactic Notation "seal_forward" tactic(tac) :=
    let cont := fresh "cont" in  
    (try rem_trace cont; to_equal; tac; from_equal; try subst cont).


  Ltac cases_on_ret return_val :=
    let yes_no_disj_tac H :=
        let ret_ineq := fresh "ret_ineq" in
        destruct H;
        try assert (return_val >= 0) as ret_ineq
            by omega;
        try assert (return_val < 0) as ret_ineq
            by omega
    in
    match goal with
    | [H: ?lhs \/ ?rhs |- _] =>
      match lhs with
      | context[return_val] =>
        unfold YES, NO in *;
        yes_no_disj_tac H;
        match goal with
        | [H1: return_val >= 0, 
           H2: return_val >= 0 -> _,
           H3: return_val < 0 -> _ |- _] =>
          pose proof (H2 H1); clear H1 H2 H3
        | [H1: return_val < 0, 
           H2: return_val < 0 -> _,
           H3: return_val >= 0 -> _ |- _] =>
          pose proof (H2 H1); clear H1 H2 H3
        | [H1: return_val <> 0, 
           H2: return_val <> 0 -> _,
           H3: return_val = 0 -> _ |- _] =>
          pose proof (H2 H1); clear H1 H2 H3 
        | [H1: return_val = 0, 
           H2: return_val = 0 -> _,
           H3: return_val <> 0 -> _ |- _] =>
          pose proof (H2 H1); clear H1 H2 H3
        end
      end
    end.

  
  Ltac apply_data_array_at_local_facts :=
    match goal with
    | [|- context[data_at ?sh (Tarray tuchar ?size ?attr)
                         ?contents ?ptr]] =>
      (* 
    Alternatives:
    let Hderives := fresh "Hderives" in
    pose proof data_array_at_local_facts as Hderives;

    match goal with
    | [H: _ |-- !! ?RHS |- _] =>
      assert_PROP RHS; [apply Hderives |]
    end.
    
    eapply assert_PROP'; [apply Hderives |].
       *)
      sep_apply (data_array_at_local_facts tuchar size attr sh contents ptr)
    end.

  (* Solves a constraint of the form introduced by [intro_rep_in_buffer_bound] 
   *)
  Ltac derive_buffer_bound :=
    intros;
    apply andp_right; [| cancel];  
    try rewrite field_at_data_at;
    try rewrite field_address_offset;
    auto;
    simpl;
    unfold tarray;
    try apply_data_array_at_local_facts; 
    unfold unfold_reptype;
    simpl;
    try entailer.

End Deprecated.

Export Auto_DB.
Export Protection.
Export Int_Repr.
Export Trace_Tactics.
Export Field_At_Data_At.
Export Buffer_Bounds.
Export Buffer_Splitting.
Export Buffer_Coalescing.