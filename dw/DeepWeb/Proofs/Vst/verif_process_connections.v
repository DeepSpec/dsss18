Require Import String.

Require Import DeepWeb.Free.Monad.Verif.
Require Import DeepWeb.Spec.Swap_CLikeSpec.

From Custom Require Import List.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs MonadExports
     Representation AppLogic process_connections_spec.

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

Set Bullet Behavior "Strict Subproofs".

Opaque bind.

Lemma proj_RECVING_SENDING: forall (c : connection * sockfd * val),
    (has_conn_state RECVING c || has_conn_state SENDING c)%bool = true <->
    (has_conn_state RECVING (proj_conn c)
     || has_conn_state SENDING (proj_conn c))%bool = true.
Proof.
  intros [[c ?] ?].
  simpl.
  split;
    intros H; apply orb_true_elim in H;
      apply orb_true_intro;
      destruct H; auto.
Qed.        

Definition process_loop_prop_invar
           (connections : list (connection * sockfd * val))
           (server_addr : endpoint_id)
           (server_fd : sockfd)
           (prefix suffix : list (connection * sockfd * val))
           (st : SocketMap) :=
  [consistent_world st;
     Forall (fun '(conn, fd, ptr) =>
               consistent_state BUFFER_SIZE st (conn, fd)) prefix;
     Forall (fun '(conn, fd, ptr) =>
               consistent_state BUFFER_SIZE st (conn, fd)) suffix;
     exists old_prefix,
     (connections = old_prefix ++ suffix /\
      map proj_fd old_prefix = map proj_fd prefix /\
      map conn_id
          (map proj_conn old_prefix) = map conn_id (map proj_conn prefix) /\
      map proj_ptr old_prefix = map proj_ptr prefix
     );
     
     NoDup
       (map conn_id
            (map proj_conn
                 (filter
                    (fun c => (has_conn_state RECVING c
                            || has_conn_state SENDING c)%bool)
                    (prefix ++ suffix))));
     
     lookup_socket st server_fd = ListeningSocket server_addr].

Definition process_loop_sep_invar
           (k : SocketM unit)
           (server_addr : endpoint_id)
           (read_set : FD_Set)
           (write_set : FD_Set)
           (head_ptr : val)
           (read_set_ptr : val)
           (write_set_ptr : val)
           (msg_store_ptr : val)
           (prefix suffix: list (connection * sockfd * val))
           (st : SocketMap)
           (last_msg : string)
           (curr_ptr : val)
  :=
    [SOCKAPI st ;
     ITREE ( (select_loop
                server_addr
                BUFFER_SIZE
                (true, (map proj_conn (prefix ++ suffix), last_msg)))
               ;; k );
     FD_SET Tsh read_set read_set_ptr;
     FD_SET Tsh write_set write_set_ptr;
     lseg LS Tsh Tsh (map rep_full_conn prefix) head_ptr curr_ptr;
     lseg LS Tsh Tsh (map rep_full_conn suffix) curr_ptr nullval;
     field_at Tsh (Tstruct _store noattr) [] (rep_store last_msg)
              msg_store_ptr].

Definition process_loop_invar
           (k : SocketM unit)
           (server_addr : endpoint_id)
           (server_fd : sockfd)
           (read_set : FD_Set)
           (write_set : FD_Set)
           (connections: list (connection * sockfd * val))
           (head_ptr : val)
           (read_set_ptr : val)
           (write_set_ptr : val)
           (msg_store_ptr : val)
  : environ -> mpred :=
  EX prefix : list (connection * sockfd * val),
  EX suffix : list (connection * sockfd * val),
  EX st : SocketMap,
  EX last_msg : string,
  EX curr_ptr : val,
  PROPx (process_loop_prop_invar
          connections server_addr server_fd prefix suffix st)
  (LOCAL (
      temp _head head_ptr;
      temp _curr curr_ptr;
      temp _rs read_set_ptr;
      temp _ws write_set_ptr;
      temp _last_msg_store msg_store_ptr
     )
  (SEPx (process_loop_sep_invar
           k server_addr read_set write_set
           head_ptr read_set_ptr write_set_ptr
           msg_store_ptr prefix suffix st last_msg curr_ptr
  ))).

Definition process_loop_postcond
           (k : SocketM unit)
           (server_addr : endpoint_id)
           (server_fd : sockfd)
           (read_set : FD_Set)
           (write_set : FD_Set)
           (connections: list (connection * sockfd * val))
           (head_ptr : val)
           (read_set_ptr : val)
           (write_set_ptr : val)
           (msg_store_ptr : val)
  : environ -> mpred :=
  EX prefix : list (connection * sockfd * val),
  EX suffix : list (connection * sockfd * val),
  EX st : SocketMap,
  EX last_msg : string,
  EX curr_ptr : val,
  PROPx ((curr_ptr = nullval)
           ::  (process_loop_prop_invar
                  connections server_addr server_fd prefix suffix st))
  (LOCAL (
      temp _head head_ptr;
      temp _curr curr_ptr;
      temp _rs read_set_ptr;
      temp _ws write_set_ptr;
      temp _last_msg_store msg_store_ptr
     )
  (SEPx (process_loop_sep_invar
           k server_addr read_set write_set
           head_ptr read_set_ptr write_set_ptr
           msg_store_ptr prefix suffix st last_msg curr_ptr
  ))).           


Lemma body_process_connections:
  semax_body Vprog Gprog f_process_connections
             (process_connections_spec BUFFER_SIZE).
Proof.
  start_function.
  
  forward.

  assert (forall conn fd ptr,
             In (conn, fd, ptr) connections ->
             descriptor server_fd <> descriptor fd) as all_fds_not_server_fd.
  { 
    intros conn fd ptr HIn.
    unfold not.
    intros fd_eq.
    apply is_fd_irrelevant in fd_eq.
    rewrite fd_eq in *.
    
    match goal with
    | [H: Forall _ connections |- _] =>
      rewrite Forall_forall in H;
        specialize (H (conn, fd, ptr) HIn);
        simpl in H;
        apply consistent_connection_not_listening
          with (addr := server_addr) in H
    end.
    tauto.

  } 

  set (inv := process_loop_invar k server_addr server_fd read_set write_set
                                 connections conn_ptr
                                 read_set_ptr write_set_ptr
                                 msg_store_ptr).
  set (postcond :=
         process_loop_postcond k server_addr server_fd read_set write_set
                               connections conn_ptr
                               read_set_ptr write_set_ptr
                               msg_store_ptr).

  unfold Swhile.
  forward_loop inv break:postcond.

  { (* precondition *)

    unfold process_loop_invar.
    Exists ([] : list (connection * sockfd * val)).
    Exists connections.
    Exists st.
    Exists last_msg.
    Exists conn_ptr.

    entailer!.

    exists ([] : list (connection * sockfd * val)).
    auto.

  }
  
  { (* body of while *)

    unfold inv, process_loop_invar.
    Intros prefix.
    Intros suffix.
    Intros st0.
    Intros last_msg0.
    Intros curr_ptr.

    focus_SEP 5; simpl.
    unfold process_loop_prop_invar.

    forward_if.
    {
      prove_lseg_ptr_null_test.
    }

    rewrite lseg_unfold.
    destruct suffix as [| [[conn fd] ptr] rest].
    { 
      simpl.
      Intros; tauto.
    }

    simpl.
    Intros tail.
    subst curr_ptr.

    assert_PROP (field_compatible (Tstruct _connection noattr) []
                                  ptr)
      by entailer!.

    assert (consistent_state BUFFER_SIZE st0 (conn, fd)) as Hconsistent.
    { 
      match goal with
      | [H: Forall _  ((conn, fd, ptr) :: rest) |- _] =>
        apply Forall_inv in H
      end; assumption.
    } 

    focus_SEP 1.

    unfold rep_connection.
    rewrite connection_list_cell_eq; [| assumption].

    Intros.

    forward.

    forward_call (fd, read_set, read_set_ptr, Tsh).
    { split; auto.
      eapply consistent_connection_fd_bound; eassumption.
    }

    Intro read_ready.

    forward_call (fd, write_set, write_set_ptr, Tsh).
    { split; auto.
      eapply consistent_connection_fd_bound; eassumption.
    }

    Intro write_ready.

    Intros.

    forward.

    (* FIXME: Freeze takes too long:
       freeze [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] FR1; 
       simpl. *)

    Local Ltac post_socket_ready read_ready write_ready :=
      match goal with
      | [|- context[LOCALx (_ :: ?locs) (SEPx ?sep)]] =>
        forward_if
          (EX socket_ready : Z,
           PROP (socket_ready = 0 \/ socket_ready = 1;
                 socket_ready = 1 -> read_ready <> 0 \/ write_ready <> 0)
           (LOCALx (temp _socket_ready (Vint (Int.repr socket_ready)) :: locs)
           (SEPx sep)))
      end.
    
    post_socket_ready read_ready write_ready.
    
    { (* if read_ready *)
      
      forward.
      Exists 1.

      go_lower.
      repeat apply andp_right; auto.
      - apply prop_right; repeat split; auto. 
      - apply prop_right; repeat split; auto.
    }

    (* else if write_ready *)
    post_socket_ready read_ready write_ready.
    
    {
      (* if write_ready *)
      forward.
      Exists 1.

      go_lower.
      repeat apply andp_right; auto.
      - apply prop_right; repeat split; auto. 
      - apply prop_right; repeat split; auto.
        
    }

    { (* else *)
      forward.
      Exists 0.

      go_lower.
      repeat apply andp_right; auto.
      - apply prop_right; repeat split; auto.
        intros; omega.
      - apply prop_right; repeat split; auto.

    }

    Intro socket_ready.
    Intros.

    gather_SEP 2 3 4 5 6 7 8.
    repeat rewrite <- sepcon_assoc.
    rewrite <- connection_list_cell_eq; [| assumption].
    fold_rep_connection conn fd.
    { 
      unfold rep_connection.
      go_lower.
      cancel.
    }

    freeze [1; 2; 3; 4; 5; 8] FR1; simpl.
    
    set (tr conn last_msg :=
           select_loop
             server_addr
             BUFFER_SIZE
             (true, (map proj_conn
                         (prefix ++ conn :: rest), last_msg))
             ;; k).

    (* process if ready *)

    gather_SEP 1 2 3 4.
    
    Local Ltac post_process prefix suffix tr :=
    match goal with
    | [H: lookup_socket _ ?server_fd = ListeningSocket ?server_addr
       |- context[LOCALx (?locs) (SEPx (?process_pred :: ?seps)) ]] =>
    match process_pred with 
    | context[list_cell _ _ (rep_connection ?conn ?fd) ?ptr] =>
    match process_pred with 
    | context[SOCKAPI ?st] => 
    match process_pred with 
    | context[field_at _ (Tstruct _store noattr) _
                       (rep_store ?last_msg) ?msg_store_ptr] => 
      forward_if
      (EX conn' : connection,
       EX last_msg' : string,              
       EX st' : SocketMap,
       PROP ( 
           consistent_world st';
           consistent_state BUFFER_SIZE st' (conn', fd);
           Forall (fun '(conn, fd, _) =>
                     consistent_state BUFFER_SIZE st' (conn, fd)) prefix;
           Forall (fun '(conn, fd, _) =>
                     consistent_state BUFFER_SIZE st' (conn, fd)) suffix;
           lookup_socket st' server_fd = ListeningSocket server_addr;
           conn_id conn = conn_id conn';
           NoDup
             (map conn_id
                  (map proj_conn
                       (filter
                          (fun c : connection * sockfd * val =>
                             (has_conn_state RECVING c
                              || has_conn_state SENDING c)%bool)
                          (prefix ++ (conn', fd, ptr) :: suffix))))
         )
       (LOCALx locs
       (SEPx ( SOCKAPI st' ::
               ITREE (tr (conn', fd, ptr) last_msg') ::
               list_cell LS Tsh (rep_connection conn' fd) ptr ::
               field_at Tsh (Tstruct _store noattr) []
                        (rep_store last_msg') msg_store_ptr ::
               seps )
      )))
    end
    end
    end
    end.

    post_process prefix rest tr.

    { (* if (socket_ready > 0) *)

      Intros.

      unfold select_loop.
      rewrite while_loop_unfold.
      simpl.
      rewrite trace_bind_assoc.
      take_branch2 2.
      rewrite trace_bind_assoc.

      assert (socket_ready = 1) by omega.

      match goal with
      | [H1 : socket_ready = 1, H2 : socket_ready = 1 -> _ |- _] =>
        pose proof (H2 H1); clear H1 H2
      end.
      
      match goal with
      | [H: exists old_prefix, _ |- _] =>
        destruct H
          as [old_prefix
                [connections_eq
                   [fds_preserved
                      [ptrs_preserved ids_preserved]]]]
      end.

      rewrite connections_eq in *.

      assert (In (descriptor fd) (map descriptor read_set)
              \/ In (descriptor fd) (map descriptor write_set))
        as fd_in_read_or_write.
      { 
        match goal with
        | [H: read_ready <> 0 \/ _ |- _] =>
          destruct H as [Hready | Hready]
        end;
          match goal with
          | [H1 : read_ready <> 0 -> _,
             H2 : write_ready <> 0 -> _ |- _] =>
            try pose proof (H1 Hready) as in_set;
              try pose proof (H2 Hready) as in_set
          end.
        - left; assumption.
        - right; assumption.
          
      }

      set (waiting_to_recv :=
             map proj_fd
                 (filter (has_conn_state RECVING)
                         (old_prefix ++ (conn, fd, ptr) :: rest))).
      
      set (waiting_to_send :=
             map proj_fd
                 (filter (has_conn_state SENDING)
                         (old_prefix ++ (conn, fd, ptr) :: rest))).
      
      assert (In (conn, fd, ptr) (old_prefix ++ (conn, fd, ptr) :: rest))
        as conn_in.
      {
        apply in_or_app.
        right.
        simpl.
        left; auto.
      }

      assert
        (In (descriptor fd) (map descriptor waiting_to_recv)
         \/ In (descriptor fd) (map descriptor waiting_to_send))
        as fd_in_filtered.
      { 
        destruct fd_in_read_or_write
          as [fd_in_read | fd_in_write]; [left | right];
          match goal with
          | [H1: context[fd_subset read_set _],
             H2: context[fd_subset write_set _] |- _] =>
            unfold fd_subset, incl in H1, H2;
              try pose proof (H1 _ fd_in_read) as fd_in_recving;
              try apply (H2 _ fd_in_write)
          end.

        specialize (all_fds_not_server_fd conn fd ptr conn_in).
        simpl in fd_in_recving.
        destruct fd_in_recving as [fd_eq |]; auto.
        rewrite fd_eq in *; tauto.

      }

      assert (has_conn_state RECVING conn = true
              \/ has_conn_state SENDING conn = true)
        as conn_recving_sending.
      {
        destruct fd_in_filtered; [left | right];
          eapply fd_in_filtered_implies_conn_state;
          eauto.
      }

      match goal with
      | [|- context[choose ?l]] =>
        remember l as filtered_conns
      end.

      assert (In conn filtered_conns).
      {

        assert (In conn (map proj_conn (prefix ++ (conn, fd, ptr) :: rest))).
        {
          rewrite map_app.
          simpl.
          apply in_or_app.
          right.
          simpl.
          left; auto.
        }
        
        destruct conn_recving_sending; subst; apply in_or_app;
          [left | right]; rewrite filter_In; split; auto.
        
      }

      (* Choose conn in interaction tree. *)
      rem_trace_tail process_tr.
      replace_SEP 2 (ITREE (process_tr conn)).
      {
        go_lower.
        apply internal_nondet3.
        assumption.
      }

      subst process_tr.

      rewrite trace_bind_assoc.

      rem_trace_tail after_process.
      forward_call (after_process, st0, conn, fd,
                    last_msg0, ptr, msg_store_ptr).
      { unify_trace.
        cancel.
      }
      
      (* after process *)
      
      Intro vret.
      subst after_process.
      destruct vret as [[[conn' last_msg'] st'] process_ret].
      simpl fst; simpl snd.
      Intros.
      
      assert (conn_state conn = RECVING \/ conn_state conn = SENDING)
        as conn_RECVING_or_SENDING.
      {
        destruct conn_recving_sending as [Hconn_st | Hconn_st];
          [left | right];
          unfold has_conn_state in Hconn_st;
          destruct QuickChick.Decidability.dec; try discriminate; auto.
      }

            
      Local Ltac elim_conn_state conn :=
        let Hconn_state := fresh "Hconn_state" in
        match goal with
        | [H: conn_state conn = _ \/ _ |- _] =>
          destruct H as [ Hconn_state | Hconn_state ]
        end;
        match goal with
        | [H1: conn_state conn = RECVING -> _,
               H2: conn_state conn = SENDING -> _ |- _] =>
          try (pose proof (H1 Hconn_state) as Hstep);
          try (pose proof (H2 Hconn_state) as [Hstep last_msg'_eq])
        end.        

      assert
        (Forall (fun '(conn0, fd0, _) =>
                   consistent_state BUFFER_SIZE st' (conn0, fd0)) prefix
         /\ Forall (fun '(conn0, fd0, _) =>
                     consistent_state BUFFER_SIZE st' (conn0, fd0)) rest)
        as frame_consistent.
      {

        elim_conn_state conn.
        - eapply recv_step_preserves_frame_consistency
            with (prefix := prefix) (suffix := rest); eauto.
          Unshelve.
          3 : { exact nullval. (* Irrelevant. *) } 
          + match goal with
            | [H: Forall _ (_ :: rest) |- _] =>
              apply Forall_skipn with (n := 1%nat) in H; simpl in H
            end.
            assumption.
          + repeat rewrite map_app in *.
            rewrite <- fds_preserved.
            auto.
            
        - eapply send_step_preserves_frame_consistency
            with (prefix := prefix) (suffix := rest); eauto.
          Unshelve.
          3 : { exact nullval. (* Irrelevant. *) } 
          + match goal with
            | [H: Forall _ (_ :: rest) |- _] =>
              apply Forall_skipn with (n := 1%nat) in H; simpl in H
            end.
            assumption.
          + repeat rewrite map_app in *.
            rewrite <- fds_preserved.
            auto.
            
      } 

      assert (conn_id conn = conn_id conn') as conn_id_preserved.
      {
        destruct conn_RECVING_or_SENDING as [ Hconn_state | Hconn_state ];
          match goal with
          | [H1: conn_state conn = RECVING -> _,
                 H2: conn_state conn = SENDING -> _ |- _] =>
            try (pose proof (H1 Hconn_state) as Hstep);
              try (pose proof (H2 Hconn_state) as [Hstep last_msg'_eq])
          end.
        
        - eapply recv_step_preserves_conn_ids; eauto.
        - eapply send_step_preserves_conn_ids; eauto.
      } 
      
      Exists conn'.
      Exists last_msg'.
      Exists st'.

      entailer!.
      
      {
        elim_conn_state conn.

        (* RECVING *)
        - repeat split; auto.
          + eapply recv_step_preserves_consistency; eauto.
          + destruct frame_consistent; auto.
          + destruct frame_consistent; auto.
          + match goal with
            | [H: lookup_socket _ _ = _ |- _] =>
              rewrite <- H
            end.
            symmetry.
            eapply recv_step_preserves_frame_lookup; eauto.
          + (* NoDup conn_ids preserved *)
            match goal with
            | [H: NoDup (map _ (map _ (filter _ (prefix ++ _ :: _)))) |- _] =>
              revert H
            end.
            
            repeat rewrite filter_app; repeat rewrite map_app.
            simpl.

            replace ((has_conn_state _ _ || _)%bool) with true
              by (symmetry; apply orb_true_intro; auto).

            simpl.
            destruct ((has_conn_state _ _ || _)%bool);
              try (simpl; rewrite conn_id_preserved;
                   intros; assumption);
              try (intros HNoDup;
                   eapply NoDup_remove_1; eassumption).
            
        - (* SENDING *)
          repeat split; auto.
          + eapply send_step_preserves_consistency; eauto.
          + destruct frame_consistent; auto.
          + destruct frame_consistent; auto.
          + match goal with
            | [H: lookup_socket _ _ = _ |- _] =>
              rewrite <- H
            end.
            symmetry.
            eapply send_step_preserves_frame_lookup; eauto.
          + (* NoDup conn_ids preserved *)
            match goal with
            | [H: NoDup (map _ (map _ (filter _ (prefix ++ _ :: _)))) |- _] =>
              revert H
            end.
            
            repeat rewrite filter_app; repeat rewrite map_app.
            simpl.

            replace ((has_conn_state _ _ || _)%bool) with true
              by (symmetry; apply orb_true_intro; auto).

            simpl.
            destruct ((has_conn_state _ _ || _)%bool);
              try (simpl; rewrite conn_id_preserved;
                   intros; assumption);
              try (intros HNoDup;
                   eapply NoDup_remove_1; eassumption).
            
      } 

      trace_bind_ret.  
      subst tr.
      unfold select_loop.
      replace
        (replace_when _ conn' _)
        with 
          (map proj_conn (prefix ++ (conn', fd, ptr) :: rest));
        [cancel |].
      
      repeat rewrite map_app.
      simpl.

      rewrite replace_when_NoDup
        with (g := conn_id)
             (p2 := (fun c => has_conn_state RECVING c
                           || has_conn_state SENDING c)%bool)
             (n := conn_id conn'); auto.
      
      - (* discriminator *)
        intros.
        rewrite conditional_bool.
        rewrite conditional_dec_true.
        reflexivity.
        
      - (* conn_id the same and matches filter condition *)
        split; auto.
        apply orb_true_intro.
        destruct conn_RECVING_or_SENDING; [left | right];
          unfold has_conn_state;
          destruct (QuickChick.Decidability.dec);
          auto;
          tauto.

      - rewrite filter_app.
        rewrite map_app.
        apply NoDup_remove_2.

        match goal with
        | [H: NoDup
                (map _ (map _ (filter _ (prefix ++ (conn, fd, ptr) :: rest))))
           |- _] =>
          revert H
        end.
        
        rewrite filter_app.
        rewrite map_app.
        simpl.

        assert (has_conn_state RECVING (conn, fd, ptr) = true
                \/ has_conn_state SENDING (conn, fd, ptr) = true) as cond_true.
        { 
          destruct conn_RECVING_or_SENDING;
            [left | right];
            unfold has_conn_state;
            destruct (QuickChick.Decidability.dec);
            auto;
            tauto.
        }

        apply orb_true_intro in cond_true.
        rewrite cond_true.
        rewrite map_app.
        simpl.

        do 2 rewrite filter_proj_commutes
          with (p2 := fun c : connection =>
                        (has_conn_state RECVING c || has_conn_state SENDING c)%bool)
          by (apply proj_RECVING_SENDING).          

        intros; assumption.

    } (* end if (socket_ready > 0) { process; } *)


    { (* else *)

      forward.
      Exists conn.
      Exists last_msg0.
      Exists st0.

      go_lower.
      repeat apply andp_right; auto.
      - apply prop_right; repeat split; auto.
        (* prefix still consistent *)
        match goal with
        | [H: Forall _ ((conn, fd, ptr) :: rest) |- _] => 
          apply (Forall_skipn _ _ 1%nat) in H;
            simpl in H
        end.
        assumption.
      - apply prop_right; repeat split; auto.
      - subst tr.
        cancel.

    }

    Intro conn'.
    Intro last_msg'.
    Intro st'.
    Intros.

    match goal with
    | [H: exists old_prefix, _ |- _] =>
      destruct H
        as [old_prefix
              [connections_eq
                 [fds_preserved
                    [ids_preserved ptrs_preserved]]]]
    end.

    thaw FR1; simpl.

    forward.    

    gather_SEP 2 7 8.
    Intros.
    gather_SEP 0 8 2 1.
    fold_conn_cell_into_prefix.
    Intros.    

    unfold inv, process_loop_invar.

    Exists (prefix ++ [(conn', fd, ptr)]) .
    Exists rest.
    Exists st'.
    Exists last_msg'.
    Exists tail.
        
    go_lower.
    repeat apply andp_right; auto.
    
    - apply prop_right; repeat split; auto.
      + (* Consistency of prefix *)
        rewrite Forall_app; split; auto.

      + (* Extend old prefix *)
        exists (old_prefix ++ [(conn, fd, ptr)]).
        repeat split; [ rewrite <- app_assoc; auto | ..].
        * repeat rewrite map_app; simpl.
          rewrite fds_preserved.
          reflexivity.
        * repeat rewrite map_app; simpl.
          rewrite ids_preserved.
          replace (conn_id conn) with (conn_id conn') by assumption.
          reflexivity.
        * repeat rewrite map_app; simpl.
          rewrite ptrs_preserved.
          reflexivity.
      + (* NoDup conn_ids *)
        rewrite <- app_assoc.
        simpl.
        assumption.
    - apply prop_right; repeat split; auto.
      
    - cancel.
      subst tr.
      simpl.
      repeat rewrite <- app_assoc; simpl.
      cancel.
      rewrite map_app.
      simpl.
      cancel.

    - (* break *)
      forward.
      subst postcond; unfold process_loop_postcond.
      Exists prefix.
      Exists suffix.
      Exists st0.
      Exists last_msg0.
      Exists curr_ptr.
      entailer!.
      
  }
  
  (* Exit from loop *)

  subst postcond.
  unfold process_loop_postcond.

  Intros prefix.
  Intros suffix.
  Intros st'.
  Intros last_msg'.
  Intros curr_ptr.
  unfold process_loop_prop_invar, process_loop_sep_invar.
  
  subst curr_ptr.
  rewrite lseg_eq; auto.
  Intros.
  assert (suffix = []) by (eapply map_eq_nil; eassumption).
  subst suffix.
  rewrite app_nil_r.
  
  match goal with
  | [H: exists old_prefix, _ |- _] =>
    destruct H
      as [connections'
            [connections_eq
               [fds_preserved
                  [ids_preserved ptrs_preserved]]]];
      rewrite app_nil_r in connections_eq;
      subst connections'
  end.

  match goal with
  | [H: NoDup (map _ (map _ (filter _ (prefix ++ [])))) |- _] =>
    rewrite app_nil_r in H
  end.
  
  forward.

  Exists prefix.
  Exists last_msg'.
  Exists st'.

  entailer!.
  
Qed.
