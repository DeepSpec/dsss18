Require Import String.

From Custom Require Import List.

Require Import DeepWeb.Free.Monad.Verif.
Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs MonadExports
     Representation AppLogic select_loop_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib SocketTactics 
     Connection Store AppLib.

Import SockAPIPred.
Import TracePred.
Import FDSetPred.

Open Scope list.
Open Scope logic.

Opaque bind.

Set Bullet Behavior "Strict Subproofs".

Definition timeval_rep
  : reptype (nested_field_type (Tstruct _timeval noattr) []) :=
  (Vint (Int.repr 0), Vint (Int.repr 0)).
  (* 64-bit: 
     (Vlong (Int64.repr (Int.signed (Int.repr 0))),
        Vlong (Int64.repr (Int.signed (Int.repr 0)))) *)

Definition main_loop_invar
           (k : SocketM unit)
           (server_addr : endpoint_id)
           (server_fd : sockfd)
           (v_head : val)
           (v_timeout : val)
           (v_maxsock : val)
           (v_rs : val)
           (v_ws : val)
           (v_es : val)
           (msg_store_ptr : val) : environ -> mpred :=
  EX connections: list (connection * sockfd * val),
  EX last_msg : string,                  
  EX st : SocketMap,
  EX read_set : FD_Set,
  EX write_set : FD_Set,
  EX exception_set : FD_Set,
  EX head_ptr : val,
  PROP ( consistent_world st;
         lookup_socket st server_fd = ListeningSocket server_addr;
         Forall (fun '(conn, fd, ptr) =>
                   consistent_state BUFFER_SIZE st (conn, fd))
                connections;
         NoDup (map descriptor (map proj_fd connections));
         NoDup (map conn_id
                    (map proj_conn
                         (filter
                            (fun c => (has_conn_state RECVING c)
                                   || (has_conn_state SENDING c))%bool
                            connections)))
       )
  LOCAL (
    temp _server_socket (Vint (Int.repr (descriptor server_fd)));
    lvar _head (tptr (Tstruct _connection noattr)) v_head;
    lvar _timeout (Tstruct _timeval noattr) v_timeout;
    lvar _maxsock tint v_maxsock;
    lvar _rs (Tstruct _fd_set noattr) v_rs;
    lvar _ws (Tstruct _fd_set noattr) v_ws;
    lvar _es (Tstruct _fd_set noattr) v_es;
    temp _last_msg_store msg_store_ptr
  )
  SEP ( SOCKAPI st ;
        FD_SET Tsh read_set v_rs;
        FD_SET Tsh write_set v_ws;
        FD_SET Tsh exception_set v_es;
        field_at Tsh (Tstruct _timeval noattr) [] timeval_rep v_timeout;
        data_at_ Tsh tint v_maxsock;
        field_at Tsh (tptr (Tstruct _connection noattr)) [] head_ptr v_head;
        lseg LS Tsh Tsh
             (map rep_full_conn connections)
             head_ptr nullval;
        malloc_tokens (Tstruct _connection noattr) (map proj_ptr connections);
        ITREE (r <- select_loop server_addr BUFFER_SIZE
                 (true, (map proj_conn connections, last_msg))
               ;; k);
        field_at Tsh (Tstruct _store noattr) [] (rep_store last_msg)
                 msg_store_ptr
      ).

Lemma body_select_loop:
  semax_body Vprog Gprog f_select_loop (select_loop_spec).
Proof.
  start_function.

  assert_PROP (field_compatible (Tstruct _store noattr) [] msg_store_ptr)
    by entailer!.

  assert_PROP (field_compatible (tptr (Tstruct _connection noattr)) [] v_head)
    by entailer!.

  assert_PROP (field_compatible (Tstruct _timeval noattr) [] v_timeout)
    by entailer!.

  assert_PROP (field_compatible tint [] v_maxsock) by entailer!.
  
  do 5 forward.

  init_fd_set es v_es 3%nat.
  init_fd_set ws v_ws 4%nat.
  init_fd_set rs v_rs 5%nat.

  set (main_loop_inv :=
         main_loop_invar k server_addr server_fd
                         v_head v_timeout v_maxsock
                         v_rs v_ws v_es msg_store_ptr).

  unfold Swhile.
  
  forward_loop main_loop_inv break:(PROP(False) LOCAL() SEP ()).
  
  { (* precondition *)

    unfold main_loop_invar.
    Exists ([] : list (connection * sockfd * val)).
    Exists initial_msg st rs ws es (Vint (Int.repr 0)).

    entailer!.
    split; constructor.
    
  }

  { (* while loop *)

    unfold main_loop_inv, main_loop_invar.
    Intro connections.
    Intro last_msg.
    Intro st0.
    Intro read_set.
    Intro write_set.
    Intro exception_set.
    Intro head_ptr.

    forward_if.
    
    forward_fd_zero_macro read_set.
    forward_fd_zero_macro write_set.
    forward_fd_zero_macro exception_set.

    forward.
    
    forward_call (server_fd, ([]: FD_Set), v_rs, v_maxsock, -1).
    { unfold FD_SETSIZE; omega. }
    
    Intro vret.
    destruct vret as [[read_set1 max_fd] add_to_fd_set_ret].

    simpl fst; simpl snd.
    Intros.
    
    assert (-1 <= max_fd < FD_SETSIZE /\ fd_subset read_set1 [server_fd])
      as H_add_fd.
    { match goal with
      | [H: add_to_fd_set_ret = _ \/ _ |- _] =>
        unfold YES, NO in H; destruct H;
          [ assert (add_to_fd_set_ret >= 0) as ret_nonneg by omega
          | assert (add_to_fd_set_ret < 0) as ret_neg by omega];
          match goal with
          | [H1: add_to_fd_set_ret >= 0 -> _,
             H2: add_to_fd_set_ret < 0 -> _ |- _] =>
            try (destruct (H1 ret_nonneg) as [? [? ?]]);
              try (destruct (H2 ret_neg) as [? ?])
          end
      end;
        split; try omega;
          subst; simpl. 

      - apply incl_refl.
      - unfold incl; intros ? Hcontra; inversion Hcontra.

    }

    clear dependent add_to_fd_set_ret.
    destruct H_add_fd as [max_fd_bounds read_set1_subset].

    forward.
    
    forward_call (connections,
                  read_set1,
                  ([] : FD_Set),
                  max_fd,
                  head_ptr,
                  v_rs,
                  v_ws,
                  v_maxsock,
                  Tsh).

    Intro vret.
    destruct vret as [[read_set2 write_set2] max_fd2].

    simpl.

    Intros.

    match goal with
    | [|- context[lseg _ _ _ (map ?func connections) head_ptr nullval]] =>
      change func with rep_full_conn
    end.

    (* Select *)
    forward.

    unfold FD_SETSIZE in *. 
    forward_call (st0,
                  max_fd2 + 1,
                  read_set2, write_set2, ([] : FD_Set),
                  v_rs, v_ws, v_es, v_timeout,
                  Tsh, Tsh, Tsh).
    
    { 
      repeat split; auto.
      rep_omega.
    } 

    Intro vret.
    destruct vret as [[[[st1 read_set3] write_set3] exception_set3] select_ret].
    simpl.

    Intros.

    assert (st1 = st0
            /\ fd_subset read_set3 read_set2
            /\ fd_subset write_set3 write_set2
            /\ exception_set3 = []) as post_select.
    {
      destruct (select_ret <? 0) eqn:Hselect_ret;
        [ assert (select_ret < 0) as select_ret_ineq
            by (rewrite Z.ltb_lt in Hselect_ret; omega)
        | assert (select_ret >= 0) as select_ret_ineq
            by (rewrite Z.ltb_nlt in Hselect_ret; omega)
        ];
        match goal with
        | [H1 : select_ret < 0 -> _,
           H2 : select_ret >= 0 -> _ |- _] =>
          try destruct (H1 select_ret_ineq)
            as [Hread_set3 [Hwrite_set3 [Hexception_set3 st1_eq]]];
            try destruct (H2 select_ret_ineq)
            as [Hread_set3
                  [Hwrite_set3
                     [Hexception_set3
                        [select_ret_eq [all_fds_bounded st1_eq]]]]]
        end; repeat split; subst; auto.

      revert Hexception_set3.
      unfold fd_subset; simpl; destruct exception_set3 as [| x ?]; simpl;
        auto.
      unfold incl.
      intros Hcontra; exfalso; apply (Hcontra (descriptor x)).
      simpl; auto.
      
    }

    destruct post_select
      as [st1_eq [read_set3_subset [write_set3_subset exception_set3_eq]]].

    subst st1.

    match goal with
    | [H1: context[select_ret >= 0],
       H2: context[select_ret < 0],
       H3: context[select_ret] (* don't need bound either *) |- _] =>
      clear H1 H2 H3
    end.

    forward_if.
    {
      apply semax_seq with FF;
        [eapply semax_pre; [| apply semax_continue] | apply semax_ff].

      unfold POSTCONDITION, abbreviate.
      simpl overridePost.
      simpl RA_continue.
      unfold main_loop_inv, main_loop_invar.
      
      Exists connections.
      Exists last_msg.
      Exists st0.
      Exists read_set3.
      Exists write_set3.
      Exists ([] : FD_Set).
      Exists head_ptr.

      entailer!.
      rewrite field_at_data_at.
      rewrite field_address_offset; auto.
      simpl.
      entailer!.

    }       

    abbreviate_semax.

    (*

    assert (Forall (fun fd => descriptor fd < max_fd2 + 1) read_set3)
      as all_fds_bounded.
    {
      assert (select_ret >= 0) by omega.
      match goal with
      | [H1 : select_ret >= 0, H2 : select_ret >= 0 -> _ |- _] =>
        destruct (H2 H1)
          as [? [? [? [? [all_fds_bounded ?]]]]]
      end; auto.
    }
    
    *)    
    
    forward_call (server_fd, read_set3, v_rs, Tsh).
    
    Intro isset_server_fd_ret.
    Intros.
    
    (* if (socket_ready) *)
    match goal with
    | [|- context[SOCKAPI _]] =>
      match goal with 
      | [|- context[field_at _ _ _ head_ptr _]] =>
        match goal with
        | [|- context[lseg _ _ _ _ head_ptr _]] =>
          match goal with
          | [|- context[ITREE _]] =>
            freeze [0; 2; 3; 5; 6; 10] FR1; simpl
          end
        end
      end
    end.

    Ltac post_accept connections st head_ptr v_head loop_on := 
    match goal with
    | [|- context[LOCALx (?Locs) (SEPx (_ :: ?Frame)) ]] =>
      forward_if
        (EX conn_opt : option (connection * sockfd * val),
         EX connections' : list (connection * sockfd * val),
         EX st' : SocketMap,
         EX head_ptr' : val,
         PROP ( 
             match conn_opt with
             | Some (conn, conn_fd, new_head) =>
               exists client_conn,
               conn = {| conn_id := client_conn ;
                         conn_request := "";
                         conn_response := "";
                         conn_response_bytes_sent := 0; 
                         conn_state := RECVING
                      |} /\
               descriptor conn_fd < FD_SETSIZE /\
               lookup_socket st conn_fd = ClosedSocket /\
               connections' = (conn, conn_fd, new_head) :: connections /\
               st' = update_socket_state
                       st conn_fd (ConnectedSocket client_conn) /\
               head_ptr' = new_head
             | None => 
               connections' = connections /\ st' = st /\ head_ptr' = head_ptr
             end;
             consistent_world st'
           )
         (LOCALx ( Locs )
         (SEPx (
              SOCKAPI st' ::
              lseg LS Tsh Tsh (map rep_full_conn connections')
              head_ptr' nullval ::
              (field_at Tsh (tptr (Tstruct _connection noattr)) [] head_ptr'
                        v_head) ::
              (malloc_tokens (Tstruct _connection noattr)
                             (map proj_ptr connections')) :: 
              ITREE (loop_on connections') ::
              Frame
            )
         ))
        )
    end.

    rem_trace tr.
    gather_SEP 1 2 3 4 5.
    post_accept connections st0 head_ptr v_head
                (fun connections' =>
                   select_loop server_addr BUFFER_SIZE
                               (true, (map proj_conn connections', last_msg))
                               ;; k).

    { (* accept new connection *)

      Intros.
      subst tr.

      unfold select_loop.
      rewrite while_loop_unfold.
      simpl.
      rewrite trace_bind_assoc.
      take_branch1 4.
      rewrite trace_bind_assoc.

      rem_trace_tail k_accept.

      forward_call (k_accept, server_addr, st0, server_fd,
                    map rep_full_conn connections,
                    v_head, head_ptr).

      { (* precondition *)
        unify_trace.
        cancel.
      } 

      Intro vret.
      destruct vret as [[result_opt st'] accept_conn_ret].
      simpl fst; simpl snd; Intros.
      
      match goal with
      | [H: accept_conn_ret = _ \/ _ |- _] =>
        destruct H;
          unfold YES, NO in *;
          [ assert (accept_conn_ret >= 0) as accept_conn_ret_ineq by omega
          | assert (accept_conn_ret < 0) as accept_conn_ret_ineq by omega];
          match goal with
          | [H1: accept_conn_ret >= 0 -> _, H2: accept_conn_ret < 0 -> _ |- _] =>
            try destruct (H1 accept_conn_ret_ineq)
              as [client_conn
                    [client_fd
                       [new_head
                          [result_opt_eq
                             [client_fd_bound
                                [lookup_client st'_eq]]]]]];
              try destruct (H2 accept_conn_ret_ineq)
              as [result_opt_eq st'_eq]
          end
      end; subst result_opt.

      { (* if accept succeeded *)
        
        remember
          {| conn_id := client_conn;
             conn_request := "";
             conn_response := "";
             conn_response_bytes_sent := 0;
             conn_state := RECVING |} as new_conn.
        
        Exists (Some (new_conn, client_fd, new_head)).
        Exists ((new_conn, client_fd, new_head) :: connections).
        Exists st'.
        Exists new_head.

        subst k_accept.
        trace_bind_ret.
        unfold select_loop.
        
        go_lower.
        repeat apply andp_right; auto.
        - apply prop_right; repeat split; auto.
          exists client_conn; repeat split; auto.
        - apply prop_right; repeat split; auto.
        - cancel.
      }

      { (* accept failed *)

        Exists (None : option (connection * sockfd * val)).
        Exists connections.
        Exists st'.
        Exists head_ptr.

        subst k_accept.
        trace_bind_ret.

        unfold select_loop.

        go_lower.
        repeat apply andp_right; auto.
        - apply prop_right; repeat split; auto.
        - apply prop_right; repeat split; auto.
        - unify_trace; cancel.
      }
    } 

    {
      forward.

      Exists (None : option (connection * sockfd * val)).
      Exists connections.
      Exists st0.
      Exists head_ptr.

      subst tr.
      unify_trace.

      entailer!.

    } 

    (* after connection accepted *)
    
    Intro conn_opt.
    Intro connections1.
    Intro st1.
    Intro head_ptr1.

    Intros.

    (* Push invariants *)

    Ltac elim_some_conn_opt :=
      match goal with
      | [H: exists client_conn, _ |- _] =>
        destruct H
          as [client_conn
                [conn_eq
                   [conn_fd_bound
                      [lookup_conn_fd
                         [connections1_eq
                            [st1_eq head_ptr1_eq]]]]]]
      end.
          
    Ltac elim_none_conn_opt connections1 :=
      match goal with
        | [H: connections1 = _ /\ _ /\ _ |- _] =>
          destruct H as [connections1_eq [st1_eq head_ptr1_eq]]
      end.

    assert (NoDup (map descriptor (map proj_fd connections1)))
      as NoDup_fds_connections1.
    { 
      destruct conn_opt as [[[conn conn_fd] new_head] | ].
      2 : {
        elim_none_conn_opt connections1.
        subst; auto.
      } 

      elim_some_conn_opt.
      subst.
      simpl.
      rewrite NoDup_cons_iff.
      split; auto.
      eapply new_descriptor_is_distinct; eauto.
      
    }

    assert
    (Forall (fun '(conn, fd, _) =>
               consistent_state BUFFER_SIZE st1 (conn, fd)) connections1)
      as consistent_at_st1.
    {
      destruct conn_opt as [[[conn conn_fd] new_head] | ].      
      2 : {
        elim_none_conn_opt connections1.
        subst; auto.
      }       

      elim_some_conn_opt.
      subst.
      apply Forall_cons.
      econstructor; eauto.
      + apply lookup_update_socket_eq; reflexivity.
      + eapply update_preserves_frame_consistency; eauto.
        eapply new_descriptor_is_distinct; eauto.
        
    } 
    
    assert
    (NoDup
       (map conn_id
            (map proj_conn
                 (filter
                    (fun c => (has_conn_state RECVING c
                            || has_conn_state SENDING c)%bool) connections1))))
      as NoDup_ids_connection1.
    {
      destruct conn_opt as [[[conn conn_fd] new_head] | ].
      2 : {
        elim_none_conn_opt connections1.
        subst; auto.
      } 

      elim_some_conn_opt.
      subst.
      simpl.
      rewrite NoDup_cons_iff; split; [| assumption].
      
      unfold not.
      intros client_conn_in.
      rename client_conn into client_conn_id.

      destruct (list_in_map_inv _ _ _ client_conn_in)
        as [conn [same_id conn_in]].

      destruct (list_in_map_inv _ _ _ conn_in)
        as [[[conn' conn'_fd] conn'_ptr] [same_conn conn'_in_filtered]].
      simpl in same_conn.
      subst conn.

      assert (In (conn', conn'_fd, conn'_ptr) connections) as conn'_in
        by (apply (filter_incl _ _ _ conn'_in_filtered)).

      assert (conn'_fd <> conn_fd).
      { 
        simpl in NoDup_fds_connections1.
        apply in_map with (f := proj_fd) in conn'_in.
        apply in_map with (f := descriptor) in conn'_in.
        rewrite NoDup_cons_iff in NoDup_fds_connections1.
        destruct NoDup_fds_connections1 as [conn_not_in ?].
        simpl proj_fd in conn'_in.
        unfold not; intros; subst conn'_fd.
        tauto.
      }
      assert (conn_state conn' = RECVING \/ conn_state conn' = SENDING).
      {
        rewrite filter_In in conn'_in_filtered.
        destruct conn'_in_filtered as [? cond].
        apply orb_true_elim in cond.
        destruct cond as [e | e].
        - left.
          unfold has_conn_state in e.
          destruct (QuickChick.Decidability.dec); auto; discriminate.
        - right.
          unfold has_conn_state in e.
          destruct (QuickChick.Decidability.dec); auto; discriminate.
      }

      remember (update_socket_state _ _ _) as st1.
      assert (lookup_socket st1 conn'_fd = ConnectedSocket (conn_id conn'))
        as lookup_conn'_fd_st1.
      {
        (* true for RECVING and SENDING *)
        apply (consistent_RECVING_SENDING_connected BUFFER_SIZE);
          try assumption.
        rewrite Forall_forall in consistent_at_st1.
        specialize (consistent_at_st1 (conn', conn'_fd, conn'_ptr)).
        apply consistent_at_st1.
        simpl.
        subst; auto.
      }

      assert (lookup_socket st1 conn_fd = ConnectedSocket (client_conn_id))
        as lookup_conn_fd_st1.
      { 
        subst.
        simpl.
        destruct (_ =? _) eqn:Heq ; auto.
        rewrite Z.eqb_neq in Heq.
        tauto.
      }

      match goal with
      | [H: consistent_world st1 |- _] =>
        apply (H _ _ _ _ lookup_conn_fd_st1 lookup_conn'_fd_st1);
          auto
      end.
      
    }
    
    assert (lookup_socket st1 server_fd = ListeningSocket server_addr)
      as lookup_server_st1.
    { 
      destruct conn_opt as [[[conn conn_fd] new_head] | ].
      2 : {
        elim_none_conn_opt connections1.
        subst; auto.
      }

      elim_some_conn_opt.
      subst.
      rewrite lookup_update_socket_neq; auto.

      unfold not; intros Hcontra.
      apply lookup_descriptor with (api_st := st0) in Hcontra.
      rewrite Hcontra in lookup_conn_fd.
      match goal with
      | [H: lookup_socket st0 server_fd = ListeningSocket server_addr |- _] =>
        rewrite lookup_conn_fd in H
      end.
      discriminate.
    }
    
    assert (fd_subset
              read_set3
              (server_fd :: map proj_fd
                         (filter (has_conn_state RECVING) connections1))).
    {
      eapply fd_subset_trans; eauto.
      eapply fd_subset_trans; eauto.
      unfold fd_subset in *.
      rewrite map_app.
      simpl.
      match goal with
      | [|- incl _ (?a :: ?x)] =>
        change (a :: x) with ([a] ++ x)
      end.
      eapply incl_app.
      - apply incl_appl; assumption.
      - apply incl_appr.
        destruct conn_opt as [[[conn conn_fd] new_head] | ].
        2 : {
          elim_none_conn_opt connections1.
          subst; apply incl_refl.
        }

        elim_some_conn_opt.
        subst.
        simpl.
        match goal with
        | [|- incl _ (?a :: ?x)] =>
          change (a :: x) with ([a] ++ x)
        end.      
        apply incl_appr.
        apply incl_refl.
    }

    assert (fd_subset
              write_set3
              (map proj_fd (filter (has_conn_state SENDING) connections1))).
    {
      eapply fd_subset_trans; eauto.
      destruct conn_opt as [[[conn conn_fd] new_head] | ].
      2 : {
        elim_none_conn_opt connections1.
        subst; auto.
      }
      elim_some_conn_opt.
      subst.
      simpl.
      assumption.
    }       

    repeat match goal with
           | [H1: context[write_set2] |- _] =>
             clear H1
           | [H1: context[read_set2] |- _] =>
             clear H1             
           | [H1: context[read_set1] |- _] =>
             clear H1
           end.
    
    forward.
    
    thaw FR1; simpl.

    forward_call (k, st1, server_addr, server_fd, connections1,
                  read_set3, write_set3, last_msg, head_ptr1,
                  v_rs, v_ws, msg_store_ptr).
    { repeat split; assumption. }
      
    Intro vret.
    destruct vret as [[connections2 last_msg1] st2].
    simpl fst; simpl snd.
    Intros.

    unfold main_loop_inv, main_loop_invar.
    Exists connections2.
    Exists last_msg1.
    Exists st2.
    Exists read_set3.
    Exists write_set3.
    Exists exception_set3.
    Exists head_ptr1.
    
    entailer!.

    - (* NoDup *)
      replace (map proj_fd connections2) with (map proj_fd connections1)
        by assumption.
      assumption.
    - replace (map proj_ptr connections1)
        with (map proj_ptr connections2) by assumption.
      cancel.
      rewrite field_at_data_at.
      simpl.
      rewrite field_address_offset; auto.
      entailer!.
    - (* break *)
      forward.
      pose proof Int.one_not_zero.
      tauto.

  } (* end while *)
  
Qed.
