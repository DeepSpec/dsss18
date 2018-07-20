
Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog
     SocketSpecs AppLogic Representation monitor_connections_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib SocketTactics
     Connection AppLib.

Import FDSetPred.

Open Scope list.
Open Scope logic.

Set Bullet Behavior "Strict Subproofs".

Definition add_fd_set_loop_invar
           (connections : list (connection * sockfd * val))
           (read_set : FD_Set)
           (write_set : FD_Set)
           (head_ptr : val)
           (read_set_ptr : val)
           (write_set_ptr : val)
           (max_fd_ptr : val) (sh : share) : environ -> mpred :=
  EX connections_prefix : list (connection * sockfd * val),
  EX connections_suffix : list (connection * sockfd * val),
  EX curr_read_set : FD_Set,
  EX curr_write_set : FD_Set,
  EX max_fd : Z,
  EX curr_ptr : val,
  PROP ( connections = connections_prefix ++ connections_suffix;
         -1 <= max_fd < FD_SETSIZE;
         
         let waiting_to_recv :=
             map proj_fd (filter (has_conn_state RECVING) connections_prefix) in
         fd_subset curr_read_set (read_set ++ waiting_to_recv) ;

         let waiting_to_send :=
             map proj_fd (filter (has_conn_state SENDING) connections_prefix) in
         fd_subset curr_write_set (write_set ++ waiting_to_send)
       )
  LOCAL (
      temp _curr curr_ptr;
      temp _max_fd max_fd_ptr;
      temp _rs read_set_ptr;
      temp _ws write_set_ptr
  )
  SEP ( FD_SET Tsh curr_read_set read_set_ptr;
        FD_SET Tsh curr_write_set write_set_ptr;
        lseg LS sh sh
             (List.map rep_full_conn connections_prefix)
             head_ptr curr_ptr;
        lseg LS sh sh
             (List.map rep_full_conn connections_suffix)
             curr_ptr nullval;
        field_at Tsh tint [] (Vint (Int.repr max_fd)) max_fd_ptr
      ).

Lemma body_monitor_connections:
  semax_body Vprog Gprog f_monitor_connections monitor_connections_spec.
Proof.
  start_function.

  forward.
  deadvars!.
  
  forward_while (add_fd_set_loop_invar
                   connections
                   read_set
                   write_set
                   conn_ptr
                   read_set_ptr
                   write_set_ptr
                   max_fd_ptr
                   sh).

  {
    (* precondition *)
    unfold add_fd_set_loop_invar.
    Exists ([] : list (connection * sockfd * val));
      Exists connections;
      Exists read_set; Exists write_set; Exists max_fd; Exists conn_ptr.

    entailer!.
    repeat rewrite app_nil_r; split; auto.
  }

  {
    (* precondition for loop test *)
    focus_SEP 3.
    prove_lseg_ptr_null_test.
  }       

  { 
    (* body of while *)
    freeze [2] FR1; simpl.
    destruct connections_suffix as [| [[conn fd] ptr] rest].
    rewrite lseg_unfold.
    { simpl; Intros; tauto. }

    simpl.
    Intros tail.

    assert_PROP (field_compatible (Tstruct _connection noattr) [] curr_ptr)
      by entailer!.

    unfold rep_connection.
    rewrite connection_list_cell_eq; [| assumption].
    Intros.

    forward.
    forward.

    freeze [0; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] FR2; simpl.

    match goal with
    | [|- context[PROPx _ (LOCALx ?locs (SEPx ?seps))]] =>
      forward_if
        (EX read_set' : FD_Set,
         EX max_fd1 : Z,
        (PROPx [ conn_state conn = RECVING ->
                 fd_subset read_set' (insert_fd fd curr_read_set);
                 conn_state conn <> RECVING ->
                 fd_subset read_set' curr_read_set ;
                 -1 <= max_fd1 < FD_SETSIZE ]
         (LOCALx locs
         (SEPx [FRZL FR2 ; FD_SET Tsh read_set' read_set_ptr;
                field_at Tsh tint [] (Vint (Int.repr max_fd1)) max_fd_ptr]))))
    end.

    { 
      forward_call (fd, curr_read_set, read_set_ptr, max_fd_ptr, max_fd0).
      Intro vret.
      destruct vret as [[read_set1 new_max] add_to_fd_set_ret].
      simpl fst; simpl snd.
      Intros.

      Exists read_set1 new_max.
      entailer!.

      unfold YES, NO in *.
      match goal with
      | [H: add_to_fd_set_ret = _ \/ _ |- _] =>
        destruct H;
          [ assert (add_to_fd_set_ret >= 0) as ret_ineq by omega
          | assert (add_to_fd_set_ret < 0) as ret_ineq by omega];
          match goal with
          | [H1 : add_to_fd_set_ret >= 0 -> _,
                  H2 : add_to_fd_set_ret < 0 -> _ |- _] =>
            try destruct (H1 ret_ineq)
              as [read_set1_eq [new_max_eq new_max_bound]];
              try destruct (H2 ret_ineq)
              as [read_set1_ineq new_max_eq]
          end
      end; destruct (conn_state conn); try discriminate.

      - split; intros Hcontra; [subst; auto | tauto].
      - split; intros Hcontra; [subst; auto | tauto].
        
    }

    { (* else skip *)
      forward.
      Exists curr_read_set max_fd0; entailer!.
    }

    Intros read_set' max_fd1.

    thaw FR2; simpl.
    freeze [0; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] FR2; simpl.

    (* Repeat *)
    match goal with
    | [|- context[PROPx _ (LOCALx ?locs (SEPx ?seps))]] =>
      forward_if
        (EX write_set' : FD_Set,
         EX max_fd2 : Z,
        (PROPx [ conn_state conn = SENDING ->
                 fd_subset write_set' (insert_fd fd curr_write_set) ;
                 conn_state conn <> SENDING ->
                 fd_subset write_set' curr_write_set ;
                 -1 <= max_fd2 < FD_SETSIZE]
         (LOCALx locs
         (SEPx [FRZL FR2 ; FD_SET Tsh write_set' write_set_ptr;
                field_at Tsh tint [] (Vint (Int.repr max_fd2)) max_fd_ptr]))))
    end.

    { 
      forward_call (fd, curr_write_set, write_set_ptr, max_fd_ptr, max_fd1).
      Intro vret.
      destruct vret as [[write_set1 new_max] add_to_fd_set_ret].
      simpl fst; simpl snd.
      Intros.

      Exists write_set1 new_max.
      entailer!.

      unfold YES, NO in *.
      match goal with
      | [H: add_to_fd_set_ret = _ \/ _ |- _] =>
        destruct H;
          [ assert (add_to_fd_set_ret >= 0) as ret_ineq by omega
          | assert (add_to_fd_set_ret < 0) as ret_ineq by omega];
          match goal with
          | [H1 : add_to_fd_set_ret >= 0 -> _,
             H2 : add_to_fd_set_ret < 0 -> _ |- _] =>
            try destruct (H1 ret_ineq)
              as [write_set1_eq [new_max_eq new_max_bound]];
              try destruct (H2 ret_ineq)
              as [write_set1_ineq new_max_eq]
          end
      end; destruct (conn_state conn); try discriminate.
      
      - split; intros Hcontra; [subst; auto | tauto].
      - split; intros Hcontra; [subst; auto | tauto].
        
    }

    { (* else skip *)
      forward.
      Exists curr_write_set max_fd1; entailer!.
    }

    Intro write_set'.
    Intro max_fd2.
    
    thaw FR2; simpl.
    thaw FR1; simpl.

    Intros.
    gather_SEP 1 2 3 4 5 6 7.
    repeat rewrite <- sepcon_assoc.
    rewrite <- connection_list_cell_eq; [| assumption].
    fold_rep_connection conn fd.
    { 
      unfold rep_connection.
      entailer!.
    }

    forward.

    gather_SEP 0 2 1 3.

    fold_conn_cell_into_prefix.
    
    Exists (connections_prefix ++ [(conn, fd, ptr)], rest,
            read_set', write_set', max_fd2, tail).

    entailer!.
    2: {
      rewrite map_app.
      simpl.
      cancel.
    }
    
    split.
    { rewrite <- app_assoc; reflexivity. }

    repeat rewrite filter_app.
    repeat rewrite map_app.
    simpl.

    
    remember (map _ (filter (_ RECVING) connections_prefix))
      as to_read.
    remember (map _ (filter (_ SENDING) connections_prefix))
      as to_write.

    match goal with
    | [H1: conn_state conn = RECVING -> _,
       H2: conn_state conn <> RECVING -> _,
       H3: conn_state conn = SENDING -> _,
       H4: conn_state conn <> SENDING -> _,
       H5: fd_subset curr_read_set _,
       H6: fd_subset curr_write_set _ |- _] =>
      rename H1 into subset_recving;
        rename H2 into subset_not_recving;
        rename H3 into subset_sending;
        rename H4 into subset_not_sending;
        rename H5 into curr_read_subset;
        rename H6 into curr_write_subset
    end.

    split;
      destruct has_conn_state eqn:Hstate;
      [ assert (conn_state conn = RECVING) as Hconn_state
      | assert (conn_state conn <> RECVING) as Hconn_state
      | assert (conn_state conn = SENDING) as Hconn_state
      | assert (conn_state conn <> SENDING) as Hconn_state
      ];
      try solve [destruct conn; simpl;
                 unfold has_conn_state in Hstate;
                 destruct QuickChick.Decidability.dec; auto; discriminate].
     

    Local Ltac use_hyp :=
      match goal with
      | [H: _ -> ?G |- ?G] =>
        eapply H;
        try solve [unfold not; intros; discriminate];
        auto
      end.
    
    all:
      try
        (assert (fd_subset read_set' curr_read_set) by use_hyp);
      try
        (assert (fd_subset read_set' (insert_fd fd curr_read_set)) by use_hyp);
      try 
        (assert (fd_subset write_set' curr_write_set) by use_hyp);
      try
        (assert (fd_subset write_set' (insert_fd fd curr_write_set))
          by use_hyp);
      try solve [split; eapply fd_subset_trans; eassumption];
      simpl map; simpl proj_fd; try rewrite app_nil_r; try assumption.
    
    all: eapply fd_subset_trans; [eassumption |]; eauto.
    all: apply fd_subset_insert1.

    all: try solve [rewrite app_assoc;
                    rewrite map_app;
                    apply in_or_app;
                    right; simpl; auto].

    all:
      solve [unfold fd_subset in *;
             rewrite app_assoc;
             rewrite map_app;
             apply incl_appl;
             assumption].

  } 

  (* end while *)
    
  subst curr_ptr.
  rewrite lseg_eq; auto.
  Intros.

  match goal with
  | [H: _ = [] |- _] =>
    apply map_eq_nil in H; subst
  end.

  forward.

  Exists curr_read_set curr_write_set max_fd0.
  repeat rewrite app_nil_r.
  entailer!.

Qed.