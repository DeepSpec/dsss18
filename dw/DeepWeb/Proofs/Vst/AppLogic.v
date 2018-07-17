Require Import String.

Require Import Custom.Decidability.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib AppLib SocketSpecs Connection Store.

Require Import DeepWeb.Spec.ITreeSpec.

Import SockAPIPred.
Import TracePred.

Open Scope logic.
Open Scope list.

Set Bullet Behavior "Strict Subproofs".

(***************************** Application Logic ******************************)


Inductive recv_step (buffer_size : Z):
  (connection * sockfd * SocketMap * string) ->
  (connection * sockfd * SocketMap * string) -> Prop :=
| Conn_RECVING_RECVING:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (msg_in_store : string)
      (recved_msg : string)
      (conn' : connection),
      conn_state conn = RECVING ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := (conn_request conn) ++ recved_msg;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := conn_response_bytes_sent conn;
                 conn_state := RECVING
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      recv_step buffer_size
                (conn, fd, sock_st, msg_in_store)
                (conn', fd, sock_st, msg_in_store)
| Conn_RECVING_SENDING:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (msg_in_store : string)
      (recved_msg : string)
      (conn' : connection),
      let full_request := (conn_request conn ++ recved_msg)%string in
      conn_state conn = RECVING ->
      is_complete buffer_size full_request = true ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := full_request;
                 conn_response := msg_in_store;
                 conn_response_bytes_sent := 0;
                 conn_state := SENDING
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      recv_step buffer_size
                (conn, fd, sock_st, msg_in_store)
                (conn', fd, sock_st, full_request)
| Conn_RECVING_EOF:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (msg_in_store : string)
      (conn' : connection) (sock_st' : SocketMap),
      conn_state conn = RECVING ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := conn_response_bytes_sent conn;
                 conn_state := DELETED
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      sock_st' = update_socket_state sock_st fd OpenedSocket ->
      recv_step buffer_size
                (conn, fd, sock_st, msg_in_store)
                (conn', fd, sock_st', msg_in_store)
| Conn_RECVING_Id:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (msg_in_store : string), 
      recv_step buffer_size
                (conn, fd, sock_st, msg_in_store)
                (conn, fd, sock_st, msg_in_store).


Inductive send_step:
  (connection * sockfd * SocketMap) ->
  (connection * sockfd * SocketMap) -> Prop :=
| Conn_SENDING_SENDING:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (num_bytes_sent : Z) (conn' : connection),
      conn_state conn = SENDING ->
      num_bytes_sent >= 0 ->
      let response_length := Zlength (val_of_string (conn_response conn)) in
      let total_num_bytes_sent :=
          conn_response_bytes_sent conn + num_bytes_sent in
      total_num_bytes_sent < response_length ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := total_num_bytes_sent;
                 conn_state := SENDING
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      send_step (conn, fd, sock_st) (conn', fd, sock_st)
| Conn_SENDING_RECVING:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (num_bytes_sent : Z) (conn' : connection),
      conn_state conn = SENDING ->
      let response_length := Zlength (val_of_string (conn_response conn)) in
      let total_num_bytes_sent :=
          conn_response_bytes_sent conn + num_bytes_sent in
      total_num_bytes_sent = response_length ->
      conn' = {| conn_id := conn_id conn;
                 conn_request := "";
                 conn_response := "";
                 conn_response_bytes_sent := 0;
                 conn_state := RECVING
              |} ->
      lookup_socket sock_st fd = ConnectedSocket (conn_id conn) ->
      send_step (conn, fd, sock_st) (conn', fd, sock_st)
| Conn_SENDING_Fail:
    forall (conn : connection) (fd : sockfd) (sock_st : SocketMap)
      (conn' : connection) (sock_st' : SocketMap),
      conn' = {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := conn_response_bytes_sent conn;
                 conn_state := DELETED
              |} ->
      (sock_st' = sock_st \/
       sock_st' = update_socket_state sock_st fd OpenedSocket) ->
      send_step (conn, fd, sock_st) (conn', fd, sock_st').


Inductive consistent_state (buffer_size : Z)
  : SocketMap -> (connection * sockfd) -> Prop :=
| Consistent_RECVING:
    forall (client_fd : sockfd) (client_id : connection_id) (request : string)
      (conn: connection) (sock_st : SocketMap),
      descriptor (client_fd) < FD_SETSIZE ->
      conn = {| conn_id := client_id ;
                conn_request := request;
                conn_response := "";
                conn_response_bytes_sent := 0;
                conn_state := RECVING
             |} ->
      lookup_socket sock_st client_fd = ConnectedSocket client_id ->
      consistent_state buffer_size sock_st (conn, client_fd)
| Consistent_SENDING:
    forall (client_fd : sockfd) (client_id : connection_id)
      (request : string) (response: string) (num_bytes_sent : Z)
      (conn: connection) (sock_st : SocketMap),
      descriptor (client_fd) < FD_SETSIZE ->
      conn = {| conn_id := client_id ;
                conn_request := request;
                conn_response := response;
                conn_response_bytes_sent := num_bytes_sent;
                conn_state := SENDING
             |} ->
      lookup_socket sock_st client_fd = ConnectedSocket client_id ->
      is_complete buffer_size request = true ->
      0 <= num_bytes_sent <= Zlength (val_of_string response) ->      
      consistent_state buffer_size sock_st (conn, client_fd)
| Consistent_DELETED:
    forall (client_fd : sockfd) (client_id : connection_id)
      (request : string) (response : string)
      (num_bytes_sent : Z)
      (conn: connection) (sock_st : SocketMap),
      descriptor client_fd < FD_SETSIZE ->
      conn = {| conn_id := client_id;
                conn_request := request;
                conn_response := response;
                conn_response_bytes_sent := num_bytes_sent;
                conn_state := DELETED
             |} ->
      (lookup_socket sock_st client_fd = OpenedSocket \/
       lookup_socket sock_st client_fd = ConnectedSocket client_id) ->
      0 <= num_bytes_sent <= Zlength (val_of_string response) ->
      consistent_state buffer_size sock_st (conn, client_fd).


Section Consistent_Facts.
  Lemma consistent_connection_not_closed:
    forall (buffer_size : Z) (st : SocketMap) (conn : connection) (fd: sockfd), 
      consistent_state buffer_size st (conn, fd) ->
      lookup_socket st fd <> ClosedSocket.
  Proof.
    intros.
    inversion H; subst; simpl in *; unfold not; intros;
      try (match goal with
           | [H1: lookup_socket _ _ = _, H2 : lookup_socket _ _ = _ |- _] =>
             rewrite H2 in H1; inversion H1
           end).
    match goal with
    | [H1: lookup_socket _ _ = _ \/ _, H2: lookup_socket _ _ = _ |- _ ] =>
      destruct H1 as [Open | Open];
        rewrite H2 in Open; inversion Open
    end.
  Qed.

  Lemma consistent_connection_not_listening:
    forall (buffer_size : Z) (st : SocketMap) (conn : connection) (fd : sockfd), 
      consistent_state buffer_size st (conn, fd) ->
      (forall addr, lookup_socket st fd <> ListeningSocket addr).
  Proof.
    intros.
    inversion H; subst; simpl in *; unfold not; intros;
      try (match goal with
           | [H1: lookup_socket _ _ = _, H2 : lookup_socket _ _ = _ |- _] =>
             rewrite H2 in H1; inversion H1
           end).
    match goal with
    | [H1: lookup_socket _ _ = _ \/ _, H2: lookup_socket _ _ = _ |- _ ] =>
      destruct H1 as [Open | Open];
        rewrite H2 in Open; inversion Open
    end.
  Qed.

  Lemma consistent_RECVING_SENDING_connected:
    forall (buffer_size : Z) (st : SocketMap) (conn : connection) (fd : sockfd), 
      consistent_state buffer_size st (conn, fd) ->
      conn_state conn = RECVING \/ conn_state conn = SENDING -> 
      lookup_socket st fd = ConnectedSocket (conn_id conn).
  Proof.
    intros ? ? ? ? H Hconn_state.
    inversion H; subst; simpl in *; auto.
    destruct Hconn_state; discriminate.
  Qed.    

  Lemma consistent_connection_fd_bound:
    forall (buffer_size : Z) (st : SocketMap) (conn : connection) (fd : sockfd), 
      consistent_state buffer_size st (conn, fd) ->
      0 <= descriptor fd < FD_SETSIZE.
  Proof.
    intros.
    destruct conn.
    simpl.
    inversion H;
      inversion H4;
      split; try apply fd_bound; auto; apply (is_descriptor fd).
  Qed.

  Lemma consistent_connection_response_bytes_sent_bound:
    forall (buffer_size : Z) (st : SocketMap) (conn : connection) (fd : sockfd), 
      consistent_state buffer_size st (conn, fd) ->
      conn_state conn = SENDING ->
      0 <= conn_response_bytes_sent conn
      <= Zlength (val_of_string (conn_response conn)).
  Proof.
    intros ? ? conn ? Hconsistent ?.
    inversion Hconsistent; subst conn; simpl; split;
      try omega; [apply Zlength_nonneg |..].
  Qed.
  
End Consistent_Facts.

Section Preservation.
  
  Lemma update_preserves_frame_consistency:
    forall (buffer_size : Z) (st1 st2 : SocketMap)
      (fd : sockfd)
      (new_state : socket_status)
      (connections : list (connection * sockfd * val)),
      ~In (descriptor fd) (map descriptor (map proj_fd connections)) ->
      st2 = update_socket_state st1 fd new_state ->
      Forall (fun '(conn, fd, _) =>
                consistent_state buffer_size st1 (conn, fd)) connections ->
      Forall (fun '(conn, fd, _) =>
                consistent_state buffer_size st2 (conn, fd)) connections.
  Proof.
    intros buffer_size
           st1 st2 fd new_state connections not_in st2_eq all_consistent.
    rewrite Forall_forall in *.
    intros [[conn conn_fd] ptr] conn_in.
    assert (descriptor fd <> descriptor conn_fd) as Hneq.
    { unfold not.
      intros Heq.
      apply not_in.
      rewrite Heq.
      apply List.in_map.
      change conn_fd with (proj_fd (conn, conn_fd, ptr)).
      apply List.in_map.
      trivial.
    }
    
    specialize (all_consistent (conn, conn_fd, ptr) conn_in).
    simpl in all_consistent.

    inversion all_consistent;
      [ eapply Consistent_RECVING; eauto
      | eapply Consistent_SENDING; eauto
      | eapply Consistent_DELETED; eauto];
      rewrite st2_eq;
      repeat rewrite lookup_update_socket_neq;
      trivial.
  Qed.
  
End Preservation.
  
Section Step_Preservation.
  
  Lemma recv_step_preserves_descriptors:
    forall (buffer_size : Z) (conn conn' : connection) (fd fd' : sockfd)
      (st st' : SocketMap) (msg_in_store msg_in_store' : string),
      recv_step buffer_size
                (conn, fd, st, msg_in_store)
                (conn', fd', st', msg_in_store') ->
      fd = fd'.
  Proof.
    intros.
    inversion H;
      match goal with
      | [H1: conn' = _ |- _] =>
        rewrite H1; reflexivity
      | _ =>
        reflexivity
      end.
  Qed.

  Lemma send_step_preserves_descriptors:
    forall (conn conn' : connection) (fd fd' : sockfd)
      (st st' : SocketMap),
      send_step (conn, fd, st) (conn', fd', st') ->
      fd = fd'.
  Proof.
    intros.
    inversion H;
      match goal with
      | [H1: conn' = _ |- _] =>
        rewrite H1; reflexivity
      | _ =>
        reflexivity
      end.
  Qed.

  Lemma recv_step_preserves_consistency:
    forall buffer_size conn fd st conn' fd' st' msg_in_store msg_in_store',
      recv_step buffer_size
                (conn, fd, st, msg_in_store)
                (conn', fd', st', msg_in_store') ->
      consistent_state buffer_size st (conn, fd) ->
      consistent_state buffer_size st' (conn', fd').
  Proof.
    intros ? conn fd st conn' fd' st' msg_in_store msg_in_store'
           Hrecv Hconsistent.
    inversion Hrecv.
    - (* Conn_RECVING_RECVING *)
      inversion Hconsistent.
      all:
        subst;
        simpl in *;
        match goal with
        | [H: _ = RECVING |- _] =>
          try inversion H
        end.
      + eapply Consistent_RECVING;
          [eauto | subst; auto..].
    - (* Conn_RECVING_SENDING *)
      inversion Hconsistent.
      all:
        subst;
        simpl in *;
        match goal with
        | [H: _ = RECVING |- _] =>
          try inversion H
        end.
      + eapply Consistent_SENDING;
          [eauto | reflexivity | subst; auto | eauto |].
        split; [omega | apply Zlength_nonneg].
    - (* Conn_RECVING_EOF *)
      inversion Hconsistent.
      all:
        subst;
        simpl in *;
        match goal with
        | [H: _ = RECVING |- _] =>
          try inversion H
        end.    
      + eapply Consistent_DELETED;
          [eauto | subst; auto..].
        rewrite lookup_update_socket_eq; auto.
        split; try omega; apply Zlength_nonneg.
    - (* Conn_RECVING_Id *)
      subst; auto.
  Qed.    

  Lemma send_step_preserves_consistency:
    forall buffer_size conn fd st conn' fd' st',
      send_step (conn, fd, st) (conn', fd', st') ->
      consistent_state buffer_size st (conn, fd) ->
      consistent_state buffer_size st' (conn', fd').
  Proof.
    intros ? conn fd st conn' fd' st' Hsend Hconsistent.
    inversion Hsend.
    - (* Conn_SENDING_SENDING *)
      inversion Hconsistent.
      all:
        subst;
        simpl in *;
        match goal with
        | [H: _ = SENDING |- _] =>
          try inversion H
        end.
      + eapply Consistent_SENDING;
          [eauto | subst; auto..].
        subst total_num_bytes_sent response_length.
        split; omega.
    - (* Conn_SENDING_RECVING *)
      inversion Hconsistent.
      all:
        subst;
        simpl in *;
        match goal with
        | [H: _ = SENDING |- _] =>
          try inversion H
        end.
      + eapply Consistent_RECVING;
          [eauto | subst; auto..].
    - (* Conn_SENDING_Fail *)
      eapply Consistent_DELETED with (client_fd := fd');
        [| subst; auto .. ].
      + inversion Hconsistent; subst; trivial.
      + match goal with
        | [H: st' = _ \/ _ |- _] =>
          destruct H; 
            [inversion Hconsistent; subst; auto |]
        end.
        subst; auto.
        left; unfold update_socket_state.
        simpl.
        assert ((descriptor fd' =? descriptor fd') = true)
          by (rewrite Z.eqb_eq; reflexivity).
        rewrite H; reflexivity.
      + inversion Hconsistent; subst; simpl; split;
          try omega; apply Zlength_nonneg.
  Qed.
  
  Lemma recv_step_preserves_frame_consistency:
    forall (buffer_size : Z) (st1 st2 : SocketMap)
      (prefix suffix : list (connection * sockfd * val))
      (conn1 conn2 : connection)
      (fd : sockfd) (ptr : val)
      (msg_in_store1 msg_in_store2 : string),
      Forall (fun '(conn, fd, ptr) =>
                consistent_state buffer_size st1 (conn, fd))
             prefix ->
      Forall (fun '(conn, fd, ptr) =>
                consistent_state buffer_size st1 (conn, fd))
             suffix ->
      NoDup
        (map descriptor
             (map proj_fd (prefix ++ (conn1, fd, ptr) :: suffix))) ->
      recv_step buffer_size
                (conn1, fd, st1, msg_in_store1)
                (conn2, fd, st2, msg_in_store2) ->
      Forall (fun '(conn, fd, ptr) =>
                consistent_state buffer_size st2 (conn, fd))
             prefix /\
      Forall (fun '(conn, fd, ptr) =>
                consistent_state buffer_size st2 (conn, fd))
             suffix.
  Proof.
    intros ? st1 st2 prefix suffix conn1 conn2 fd ptr
           msg_in_store1 msg_in_store2
           prefix_consistent suffix_consistent
           HNoDup Hstep.
    pose proof (recv_step_preserves_descriptors _ _ _ _ _ _ _ _ _ Hstep).
    repeat rewrite map_app in HNoDup.
    simpl in HNoDup.
    apply NoDup_remove_2 in HNoDup.
    rewrite in_app in HNoDup.
    apply Classical_Prop.not_or_and in HNoDup.
    destruct HNoDup.
    
    split; inversion Hstep;
      subst.
    
    all:
      eapply update_preserves_frame_consistency;
      [ eassumption
      | rewrite <- update_socket_id; auto
      | trivial].

    all:
      eapply update_preserves_frame_consistency;
      [ eassumption
      | reflexivity
      | assumption].
  Qed.

  Lemma send_step_preserves_frame_consistency:
    forall (buffer_size : Z) (st1 st2 : SocketMap)
      (prefix suffix : list (connection * sockfd * val))
      (conn1 conn2 : connection)
      (fd : sockfd) (ptr : val),
      Forall (fun '(conn, fd, ptr) =>
                consistent_state buffer_size st1 (conn, fd))
             prefix ->
      Forall (fun '(conn, fd, ptr) =>
                consistent_state buffer_size st1 (conn, fd))
             suffix ->
      NoDup
        (map descriptor (map proj_fd (prefix ++ (conn1, fd, ptr) :: suffix))) ->
      send_step (conn1, fd, st1) (conn2, fd, st2) ->
      Forall (fun '(conn, fd, ptr) =>
                consistent_state buffer_size st2 (conn, fd))
             prefix /\
      Forall (fun '(conn, fd, ptr) =>
                consistent_state buffer_size st2 (conn, fd))
             suffix.
  Proof.
    intros ? st1 st2 prefix suffix conn1 conn2 fd ptr
           prefix_consistent suffix_consistent
           HNoDup Hstep.
    pose proof (send_step_preserves_descriptors _ _ _ _ _ _ Hstep).
    repeat rewrite map_app in HNoDup.
    simpl in HNoDup.
    apply NoDup_remove_2 in HNoDup.
    rewrite in_app in HNoDup.
    apply Classical_Prop.not_or_and in HNoDup.
    destruct HNoDup.
    
    split; inversion Hstep;
      subst.
    
    all:
      eapply update_preserves_frame_consistency;
      [ eassumption
      | rewrite <- update_socket_id; auto
      | trivial].

    all:
      match goal with
      | [H: _ \/ _ |- _] =>
        destruct H; subst
      end;
      eapply update_preserves_frame_consistency;
      [ eassumption
      | apply update_socket_id
      | trivial
      | eassumption
      | reflexivity
      | trivial
      ].
  Qed.

  Lemma recv_step_preserves_frame_lookup:
    forall buffer_size conn conn' fd st st' msg_in_store msg_in_store' frame_fd,
      recv_step buffer_size
                (conn, fd, st, msg_in_store)
                (conn', fd, st', msg_in_store') ->
      descriptor frame_fd <> descriptor fd ->
      lookup_socket st frame_fd = lookup_socket st' frame_fd.
  Proof.
    intros ? ? ? ? ? ? ? ? ? Hstep Hdescr.
    inversion Hstep; subst; auto.
    rewrite lookup_update_socket_neq; auto.
  Qed.

  Lemma send_step_preserves_frame_lookup:
    forall conn conn' fd st st' frame_fd,
      send_step (conn, fd, st) (conn', fd, st') ->
      descriptor frame_fd <> descriptor fd ->
      lookup_socket st frame_fd = lookup_socket st' frame_fd.
  Proof.
    intros ? ? ? ? ? ? Hstep Hdescr.
    inversion Hstep; subst; auto.
    match goal with
    | [H: _ \/ _ |- _] =>
      destruct H; subst; auto
    end.
    rewrite lookup_update_socket_neq; auto.
  Qed.
 
  Lemma recv_step_preserves_conn_ids:
    forall (buffer_size : Z) (conn conn' : connection) (fd fd' : sockfd)
      (st st' : SocketMap) (msg_in_store msg_in_store' : string),
      recv_step buffer_size
                (conn, fd, st, msg_in_store)
                (conn', fd', st', msg_in_store') ->
      conn_id conn = conn_id conn'.
  Proof.
    intros.
    inversion H;
      match goal with
      | [H1: conn' = _ |- _] =>
        rewrite H1; reflexivity
      | _ =>
        reflexivity
      end.
  Qed.

  Lemma send_step_preserves_conn_ids:
    forall (conn conn' : connection) (fd fd' : sockfd)
      (st st' : SocketMap),
      send_step (conn, fd, st) (conn', fd', st') ->
      conn_id conn = conn_id conn'.
  Proof.
    intros.
    inversion H;
      match goal with
      | [H1: conn' = _ |- _] =>
        rewrite H1; reflexivity
      | _ =>
        reflexivity
      end.
  Qed.

End Step_Preservation.

Section New_Descriptor.
  
  Lemma new_descriptor_is_distinct: forall buffer_size st connections fd,
    Forall (fun '(conn, fd, _) =>
              consistent_state buffer_size st (conn, fd)) connections ->
    lookup_socket st fd = ClosedSocket ->
    ~ In (descriptor fd) (map descriptor (map proj_fd connections)).
  Proof.
    intros ? st connections fd all_consistent lookup_closed.
    unfold not; intros Hcontra.
    apply list_in_map_inv in Hcontra.
    destruct Hcontra
      as [fd' [fd'_eq fd'_in]].
    apply list_in_map_inv in fd'_in.
    destruct fd'_in
      as [[[conn' fd''] ptr] [fd''_eq conn_in]].
    simpl in fd''_eq; subst fd''.
    rewrite Forall_forall in all_consistent;
      apply all_consistent in conn_in.
    apply consistent_connection_not_closed in conn_in.
    apply lookup_descriptor with (api_st := st) in fd'_eq.
    rewrite lookup_closed in fd'_eq.
    rewrite <- fd'_eq in conn_in.
    tauto.
  Qed.
  
  Lemma new_descriptor_preserves_consistency:
    forall (buffer_size : Z) (st1 st2 : SocketMap)
      (client_conn : connection_id)
      (client_fd : sockfd)
      (connections : list (connection * sockfd * val)),
      lookup_socket st1 client_fd = ClosedSocket ->
      st2 = update_socket_state st1 client_fd
                                (ConnectedSocket client_conn) ->
      Forall (fun '(conn, fd, _) =>
                consistent_state buffer_size st1 (conn, fd)) connections ->
      Forall (fun '(conn, fd, _) =>
                consistent_state buffer_size st2 (conn, fd)) connections.
  Proof.
    intros.
    eapply update_preserves_frame_consistency; eauto.
    eapply new_descriptor_is_distinct; eauto.
  Qed.

  
  Lemma new_descriptor_preserves_NoDup:
    forall (buffer_size : Z) (st : SocketMap) (new_fd : sockfd)
      (connections : list (connection * sockfd * val)) (descriptors : list Z),
      lookup_socket st new_fd = ClosedSocket ->
      Forall (fun '(conn, fd, _) => 
                consistent_state buffer_size st (conn, fd))
             connections ->
      descriptors = map descriptor (map proj_fd connections) ->
      NoDup descriptors ->
      NoDup ((descriptor new_fd) :: descriptors).
  Proof.
    intros.
    rewrite NoDup_cons_iff.
    subst.
    split; [eapply new_descriptor_is_distinct; eauto |].
    assumption.
  Qed.
  
End New_Descriptor.

Lemma fd_in_filtered_implies_conn_state:
  forall (l : list (connection * sockfd * val)) conn fd ptr st filtered,
    In (conn, fd, ptr) l -> 
    filtered = map proj_fd (filter (has_conn_state st) l) ->
    In (descriptor fd) (map descriptor filtered) ->
    NoDup (map descriptor (map proj_fd l)) ->
    has_conn_state st conn = true.
Proof.
  intros l ? ? ? ? ? ? ? in_filtered HNoDup.
  change (descriptor fd)
    with (descriptor (proj_fd (conn, fd, ptr))) in in_filtered.
  subst filtered.
  rewrite map_map in in_filtered.
  apply projected_filter_reflects_cond with (x := (conn, fd, ptr))
    in in_filtered; auto.
  rewrite <- map_map.
  assumption.
Qed.
