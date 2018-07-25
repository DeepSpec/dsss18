Require Import String.
Require Import List.
Import ListNotations.

From DeepWeb.Free.Monad Require Import Free Common Verif.
Require Import DeepWeb.Lib.VstLib.

Require Import Custom.Monad.
Import MonadNotations.
Open Scope monad_scope.

Require Export DeepWeb.Lib.Socket.

Export SocketConstants.
Export SocketAPI.

Require Import DeepWeb.Spec.Vst.MainInit.

Module SockAPIPred.

  Parameter SOCKAPI: SocketMap -> mpred.

  Definition update_socket_state
             (api_st: SocketMap)
             (fd : sockfd) (new_status: socket_status) : 
    SocketMap := 
    {| lookup_socket fd' := 
         if Z.eqb (descriptor fd) (descriptor fd') then new_status
         else lookup_socket api_st fd';
    |}.
  
  Lemma lookup_update_socket_neq:
    forall (api_st : SocketMap)
      (fd : sockfd) (new_status : socket_status)
      (fd' : sockfd),
      descriptor fd <> descriptor fd' ->
      lookup_socket (update_socket_state api_st fd new_status) fd' =
      lookup_socket api_st fd'.
  Proof.
    intros.
    unfold update_socket_state.
    simpl.
    destruct (descriptor fd =? descriptor fd') eqn:Heq.
    rewrite Z.eqb_eq in Heq;
      exfalso; apply H; auto.
    reflexivity.
  Qed.

  Lemma lookup_update_socket_eq:
    forall (api_st : SocketMap)
      (fd : sockfd) (new_status : socket_status)
      (fd' : sockfd),
      descriptor fd = descriptor fd' ->
      lookup_socket (update_socket_state api_st fd new_status) fd' = new_status.
  Proof.
    intros.
    unfold update_socket_state.
    simpl.
    rewrite <- Z.eqb_eq in H.
    rewrite H.
    reflexivity.
  Qed.

  Lemma restore_update_socket:
    forall (api_st0 : SocketMap)
      (fd : sockfd) (st st' : socket_status),
      lookup_socket api_st0 fd = st ->
      let api_st1 := update_socket_state api_st0 fd st' in
      let api_st2 := update_socket_state api_st1 fd st in 
      api_st0 = api_st2.
  Proof.
    unfold update_socket_state.
    simpl.
    intros.
    destruct api_st0 as [lookup0] eqn:Hapi.
    f_equal.
    apply functional_extensionality.
    simpl in *.
    intros fd0.
    destruct (descriptor fd =? descriptor fd0) eqn:Heq;
      auto.
    rewrite Z.eqb_eq in Heq.
    pose proof (lookup_descriptor api_st0 fd fd0 Heq)
      as lookup_eq.
    rewrite Hapi in *; simpl in *.
    rewrite <- lookup_eq.
    auto.
  Qed.    

  Lemma update_socket_id:
    forall (st : SocketMap) (fd : sockfd),
      st = update_socket_state st fd (lookup_socket st fd).
  Proof.
    intros.
    unfold update_socket_state, lookup_socket.
    destruct st eqn:Hst.
    f_equal.
    apply functional_extensionality.
    intros fd'.
    destruct (descriptor fd =? descriptor fd') eqn:Heq; auto.
    rewrite Z.eqb_eq in Heq.
    apply lookup_descriptor with (api_st := st) in Heq.
    subst.
    auto.
  Qed.

  Definition consistent_world (st : SocketMap) :=
    forall fd1 fd2 id1 id2,
      lookup_socket st fd1 = ConnectedSocket id1 ->
      lookup_socket st fd2 = ConnectedSocket id2 ->
      fd1 <> fd2 -> id1 <> id2.
  
End SockAPIPred.
  
Module TracePred.

  Import TraceIncl.

  Definition SocketM := M socketE.

  Definition ITREE {T} (t : SocketM T) :=
    EX t' : SocketM T, !!(trace_incl t t') && has_ext t'.

  Lemma trace_pred_incl:
    forall {T : Type} (t1 t2 : SocketM T),
      trace_incl t2 t1 ->
      ITREE t1 |-- ITREE t2.
  Proof.
    unfold ITREE.
    intros.
    Intro t'.
    Exists t'.
    entailer!.
    eapply trace_incl_trans; eassumption.
  Qed.    
  
  Lemma trace_pred_eq:
    forall {T : Type} (t1 t2 : SocketM T),
      trace_eq t1 t2 ->
      ITREE t1 = ITREE t2.
  Proof.
    unfold TraceIncl.trace_eq.
    intros T t1 t2 H.
    apply pred_ext; apply trace_pred_incl; intros t r; apply H.
  Qed.

  (* Interface *)
  
  Lemma internal_nondet1: 
    forall {T1 T2 : Type} (k1 k2 : SocketM T1) (k3 : T1 -> SocketM T2),
      ITREE (r <- or k1 k2 ;; k3 r) |--
      ITREE (r <- k1 ;; k3 r).
  Proof.
    intros. apply trace_pred_incl.
    apply trace_or_incl_bind.
  Qed.

  Lemma internal_nondet2:
    forall {T1 T2 : Type} (k1 k2 : SocketM T1) (k3 : T1 -> SocketM T2),
      ITREE (r <- or k1 k2 ;; k3 r) |--
      ITREE (r <- k2 ;; k3 r).
  Proof.
    intros. apply trace_pred_incl.
    apply trace_or_incl_bind.
  Qed.
    
  Lemma internal_nondet3:
    forall {T1 T2 : Type} (k : T1 -> SocketM T2) (xs : list T1) (x : T1),
      In x xs ->
      ITREE (r <- choose xs ;; k r) |--
      ITREE (k x).
  Proof.
    intros.
    apply trace_pred_incl.
    apply trace_choose_incl.
    trivial.
  Qed.

  Lemma trace_bind_ret :
    forall {A B} a (f : A -> SocketM B),
      ITREE (r <- ret a ;; f r) = ITREE (f a).
  Proof.
    intros.
    apply trace_pred_eq.
    apply trace_eq_incl2.
    split; apply trace_incl_eutt;
      [| apply eutt_sym ]; apply leftId .
  Qed.
  
  Lemma trace_bind_assoc:
    forall {A B C : Type} (m : SocketM A) (f : A -> SocketM B)
      (g : B -> SocketM C),
      ITREE ( b <- (a <- m ;; f a) ;; g b ) =
      ITREE ( a <- m ;; b <- f a ;; g b ).
  Proof.
    intros.
    apply trace_pred_eq.
    split;
      apply trace_incl_eutt;
      [apply eutt_sym | ]; apply bindAssoc.
  Qed.
  
  Lemma trace_drop_tau:
    forall (T : Type) (k : SocketM T), 
      ITREE (Tau k) = ITREE k.
  Proof.
    intros.
    apply trace_pred_eq.
    split;
      apply trace_incl_eutt;
      [apply eutt_sym | ]; apply push_tau; apply eutt_refl.
  Qed.
  
  Lemma trace_bind_cancel:
    forall {A B : Type} (m : SocketM A) (f g : SocketM B),
      EquivUpToTau f g ->
      ITREE ( m ;; f ) = ITREE ( m ;; g ).
  Proof.
    intros.
    apply trace_pred_eq.
    apply trace_eq_incl2.
    split; apply trace_incl_eutt; apply cong_bind;
      [ apply eutt_refl
      | intros; assumption
      | apply eutt_refl
      | intros; apply eutt_sym; assumption
      ].
  Qed.
  
End TracePred.

Module FDSetPred.

  Definition FD_Set : Type := list sockfd.
    
  Definition insert_fd (fd : sockfd) (set : FD_Set) : FD_Set :=
    if List.existsb (fd_eqb fd) set
    then set
    else (fd :: set).

  Definition remove_fd (fd : sockfd) (set : FD_Set) : FD_Set :=
    List.filter (fun fd' => negb (fd_eqb fd fd')) set.

  Definition fd_subset (fdset1 fdset2 : FD_Set) : Prop :=
    List.incl (List.map descriptor fdset1)
              (List.map descriptor fdset2).

  Lemma fd_subset_refl:
    forall (fd_set : FD_Set), fd_subset fd_set fd_set.
  Proof.
    intros; unfold fd_subset; apply incl_refl.
  Qed.

  Lemma fd_subset_trans:
    forall (fd_set1 fd_set2 fd_set3: FD_Set),
      fd_subset fd_set1 fd_set2 ->
      fd_subset fd_set2 fd_set3 ->
      fd_subset fd_set1 fd_set3.
  Proof.
    unfold fd_subset; intros; eapply incl_tran; eassumption.
  Qed.
  
  Lemma fd_subset_insert1:
    forall (fd_set1 fd_set2 : FD_Set) (fd : sockfd), 
      fd_subset fd_set1 fd_set2 ->
      In (descriptor fd) (map descriptor fd_set2) -> 
      fd_subset (insert_fd fd fd_set1) fd_set2.
  Proof.
    intros.
    unfold insert_fd.
    destruct (existsb (fd_eqb fd)); trivial.
    unfold fd_subset.
    simpl.
    apply incl_cons; trivial.
  Qed.

  Lemma fd_subset_insert2:
    forall (fd_set1 fd_set2 : FD_Set) (fd : sockfd), 
      fd_subset fd_set1 fd_set2 ->
      fd_subset fd_set1 (insert_fd fd fd_set2).
  Proof.
    intros; unfold insert_fd; destruct (existsb (fd_eqb fd)); trivial.
    unfold fd_subset in *.
    simpl.
    apply incl_tl; assumption.
  Qed.

  (*
  Eval compute in (reptype (Tstruct _fd_set noattr)).

  Eval compute in (nested_field_type (Tstruct _fd_set noattr) []).
  Eval compute in (reptype (Tstruct 15%positive noattr)).
  *)

  Axiom rep_fd_set : FD_Set -> reptype (Tstruct _fd_set noattr).
  Definition FD_SET
             (sh : share) (set : FD_Set)
             (ptr : val) : mpred :=
    field_at sh (Tstruct _fd_set noattr) [] (rep_fd_set set) ptr.
  
  Axiom buffer_to_fd_set :
    forall (sh : share) (ptr : val), exists (set : FD_Set),
        data_at_ sh (Tstruct _fd_set noattr) ptr |-- FD_SET sh set ptr.

  Lemma fd_set_to_buffer :
    forall (sh : share) (set : FD_Set) (ptr : val), 
      FD_SET sh set ptr |-- data_at_ sh (Tstruct _fd_set noattr) ptr.
  Proof.
    intros.
    unfold FD_SET.
    pose proof field_at__data_at as H.
    eapply derives_trans; [| apply H; reflexivity].
    apply field_at_field_at_.
  Qed.
  
End FDSetPred.

Module SockAddr.
  
  Record sockaddr :=
    { sin_family : Z ; sin_port : Z ; sin_addr : Z }.
  
  Definition rep_sockaddr (addr : sockaddr) :
    reptype (Tstruct _sockaddr_in noattr) :=
    (Vint (Int.repr (sin_family addr)),
     (Vint (Int.repr (sin_port addr)),
      (Vint (Int.repr (sin_addr addr)),
       list_repeat 8 (Vint (Int.repr 0))))).
  
  Definition rep_endpoint (id : endpoint_id) :=
    rep_sockaddr
      {| sin_family := AF_INET;
         sin_port := port_number id;
         sin_addr := 0;
      |}.
  
End SockAddr.

Import TraceIncl.
Import TracePred.
Import FDSetPred.
Import SockAPIPred.
Import SockAddr.

Section HoareSocket.
  
Definition socket_spec :=
  DECLARE _socket
  WITH st : SocketMap
  PRE [ 1%positive OF tint, 2%positive OF tint, 3%positive OF tint ]
    PROP ( consistent_world st )
    LOCAL ()
    SEP ( SOCKAPI st )
  POST [ tint ]
    EX st' : SocketMap,                   
    EX r : Z,
    PROP ( -1 <= r < Int.max_signed;
           r >= 0 -> (exists fd, r = descriptor fd /\
                          lookup_socket st fd = ClosedSocket /\
                          st' = update_socket_state st fd OpenedSocket) ;
           r = -1 -> st' = st ;
           consistent_world st'
      )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ).

(* shutdown never fails for now *)
Definition shutdown_spec (T : Type) :=
  DECLARE _shutdown
  WITH t: SocketM T,
       k: SocketM T,
       client_conn : connection_id,
       st: SocketMap,
       fd: sockfd
  PRE [ 1%positive OF tint, 2%positive OF tint ]
    PROP ( consistent_world st;
           lookup_socket st fd = ConnectedSocket client_conn; 
           trace_incl (shutdown client_conn ;; k) t
         )
    LOCAL ( temp 1%positive (Vint (Int.repr (descriptor fd))) ;
            temp 2%positive (Vint (Int.repr 2))
          )
    SEP ( SOCKAPI st ; ITREE t )
  POST [ tint ]
    EX st': SocketMap,
    EX r : Z,
    PROP ( r = YES \/ r = NO;
             st' = update_socket_state st fd OpenedSocket;
             consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ; ITREE (k) ).

Definition close_spec (T : Type) :=
  DECLARE _close
  WITH st: SocketMap,
       fd: sockfd
  PRE [ 1%positive OF tint ]
    PROP ( consistent_world st )
    LOCAL ( temp 1%positive (Vint (Int.repr (descriptor fd))) )
    SEP ( SOCKAPI st )
  POST [ tint ]
    EX st': SocketMap,
    EX r : Z,
    PROP ( r = YES \/ r = NO;
           st' = update_socket_state st fd ClosedSocket;
           consistent_world st'  
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ).

Definition bind_spec :=
  DECLARE _bind
  WITH st : SocketMap,
       fd : sockfd,
       addr : endpoint_id,
       addr_ptr : val,
       addr_len : Z
  PRE [ 1%positive OF tint,
        2%positive OF (tptr (Tstruct _sockaddr noattr)),
        3%positive OF tuint ]
    PROP ( consistent_world st )
    LOCAL ( temp 1%positive (Vint (Int.repr (descriptor fd))) ;
            temp 2%positive addr_ptr ;
            temp 3%positive (Vint (Int.repr addr_len))
          )
    SEP ( SOCKAPI st ;
            data_at Tsh (Tstruct _sockaddr_in noattr) (rep_endpoint addr)
                    addr_ptr
        )
  POST [ tint ]
    EX st' : SocketMap,
    EX r : Z, 
    PROP ( r = YES \/ r = NO ;
           r = YES ->
           lookup_socket st fd = OpenedSocket /\
           st' = update_socket_state st fd (BoundSocket addr) ;
           r = NO -> st' = st;
           consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ;
            data_at Tsh (Tstruct _sockaddr_in noattr) (rep_endpoint addr)
                    addr_ptr
        ).

Definition listen_spec (T : Type) :=
  DECLARE _listen
  WITH t : SocketM T, 
       k : SocketM T,
       addr : endpoint_id,
       st : SocketMap,
       fd : sockfd,
       backlog : Z
  PRE [ 1%positive OF tint, 2%positive OF tint ]
    PROP ( consistent_world st;
           trace_incl (listen addr ;; k) t ;
           lookup_socket st fd = BoundSocket addr )
    LOCAL ( temp 1%positive (Vint (Int.repr (descriptor fd)));
            temp 2%positive (Vint (Int.repr backlog))
          )
    SEP ( SOCKAPI st; ITREE t )
  POST [ tint ]
    EX result : option unit,
    EX st' : SocketMap,
    EX r : Z, 
    PROP ( r = YES \/ r = NO ;
           r = YES ->
           result = Some tt /\
           st' = update_socket_state st fd (ListeningSocket addr) ;
           r = NO -> result = None /\ st' = st;
           consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st';
          ITREE ( match result with Some tt => k | None => t end )
        ).

Definition accept_spec (T : Type) :=
  DECLARE _accept
  WITH t : SocketM T,
       k : connection_id -> SocketM T,
       server_addr : endpoint_id,
       st : SocketMap,
       fd : sockfd
  PRE [ 1%positive OF tint,
        2%positive OF tptr (Tstruct _sockaddr noattr),
        3%positive OF tptr tuint
      ] 
  PROP ( consistent_world st;
         trace_incl (r <- accept server_addr ;; k r) t ;
         lookup_socket st fd = ListeningSocket server_addr
       )
    LOCAL ( temp 1%positive (Vint (Int.repr (descriptor fd))) ;
            temp 2%positive nullval ;
            temp 3%positive nullval
          )
    SEP ( SOCKAPI st ; ITREE t )
  POST [ tint ]
    EX result : option connection_id,
    EX st' : SocketMap,
    EX r : Z, 
    PROP ( (is_fd r /\ 0 <= r < Int.max_signed) \/ r = NO ;
             r = NO -> result = None /\ st' = st ;
             r <> NO -> (exists client_conn client_fd,
                          result = Some client_conn /\
                          r = descriptor client_fd /\
                          lookup_socket st client_fd = ClosedSocket /\
                          st' = update_socket_state
                                  st client_fd (ConnectedSocket client_conn)
                      );
             consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ;
            ITREE (
                match result with
                | Some client_conn => k client_conn 
                | None => t
                end
              )
        ).

Definition send_spec (T : Type) :=
  DECLARE _send
  WITH t : SocketM T,
       k : nat -> SocketM T,
       client_conn : connection_id,
       st : SocketMap,
       fd: sockfd,
       msg : string,
       buf_ptr : val,
       sh: share
  PRE [ 1%positive OF tint, 2%positive OF (tptr tvoid),
        3%positive OF tuint, 4%positive OF tint]
    PROP ( consistent_world st;
           lookup_socket st fd = ConnectedSocket client_conn;
           readable_share sh; 
           forall l, 0 <= l <= Zlength (val_of_string msg) ->
                trace_incl
                  (r <- send_any_prefix client_conn msg ;; k r)
                  t
         )
    LOCAL ( temp 1%positive (Vint (Int.repr (descriptor fd)));
            temp 2%positive buf_ptr;
            temp 3%positive (Vint (Int.repr (Zlength (val_of_string msg))));
            temp 4%positive (Vint (Int.repr 0))
          )
    SEP ( SOCKAPI st; ITREE (t) ;
            data_at sh
                    (tarray tuchar (Zlength (val_of_string msg)))
                    (val_of_string msg) buf_ptr )
  POST [ tint ]
    EX result : option unit,
    EX st' : SocketMap,
    EX r : Z,
    PROP ( 0 <= r <= Zlength (val_of_string msg) \/ r = NO ; 
             r <> NO ->
             result = Some tt /\ st' = st ;
             r = NO ->
             result = None /\
             (st' = st \/ st' = update_socket_state st fd OpenedSocket);
             consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st';
            ITREE (match result with
                   | None => t
                   | Some tt => k (Z.to_nat r)
                   end 
                  );
            data_at sh
                    (tarray tuchar (Zlength (val_of_string msg)))
                    (val_of_string msg) buf_ptr ).

Definition recv_spec (T : Type) :=
  DECLARE _recv
  WITH t : SocketM T,
       k : option string -> SocketM T,
       client_conn : connection_id,
       st : SocketMap,
       fd: sockfd,
       buf_ptr: val,
       alloc_len: Z,
       sh: share
  PRE [ 1%positive OF tint, 2%positive OF (tptr tvoid),
        3%positive OF tuint, 4%positive OF tint ]
    PROP ( consistent_world st;
           lookup_socket st fd = ConnectedSocket client_conn;
           writable_share sh ;
           trace_incl (r <- recv client_conn (Z.to_nat alloc_len) ;; k r) t
       )
    LOCAL (temp 1%positive (Vint (Int.repr (descriptor fd)));
           temp 2%positive buf_ptr;
           temp 3%positive (Vint (Int.repr alloc_len));
           temp 4%positive (Vint (Int.repr 0))
          )
    SEP ( SOCKAPI st;
            ITREE t;
            data_at_ sh (Tarray tuchar alloc_len noattr) buf_ptr
        )
  POST [ tint ]
    EX result : unit + option string,
    EX st' : SocketMap, 
    EX r : Z,
    EX contents: list val,
    PROP ( (0 <= r <= alloc_len) \/ r = NO;
             r > 0 ->
             (exists msg, result = inr (Some msg) /\
                     Zlength (val_of_string msg) = r /\
                     sublist 0 r contents = (val_of_string msg) /\
                     sublist r alloc_len contents =
                     list_repeat (Z.to_nat (alloc_len - r)) Vundef
             ) /\ (st' = st) ;
             r = 0 -> (result = inr None /\
                      contents = list_repeat (Z.to_nat alloc_len) Vundef /\
                      st' = update_socket_state st fd OpenedSocket) ;
             r < 0 -> (result = inl tt /\
                      contents = list_repeat (Z.to_nat alloc_len) Vundef /\
                      st' = st)
             ;
             Zlength contents = alloc_len;
             consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ;
            ITREE (match result with
                   | inl tt => t 
                   | inr msg_opt => k msg_opt
                   end
                  );
            data_at sh (tarray tuchar alloc_len)
                    contents buf_ptr
        ).

Definition select_spec (T : Type) :=
  DECLARE _select
  WITH st : SocketMap,
       max_fd : Z,
       read_set : FD_Set,
       write_set : FD_Set,
       exception_set : FD_Set,
       read_set_ptr : val,
       write_set_ptr : val,
       exception_set_ptr : val,
       timeval_ptr : val,
       read_sh: share,
       write_sh: share,
       exception_sh: share
  PRE [ 1%positive OF tint,
        2%positive OF (tptr (Tstruct _fd_set noattr)),
        3%positive OF (tptr (Tstruct _fd_set noattr)),
        4%positive OF (tptr (Tstruct _fd_set noattr)),
        5%positive OF (tptr (Tstruct _timeval noattr))
      ]
    PROP ( writable_share read_sh ;
           writable_share write_sh ;
           writable_share exception_sh;
           max_fd >= 0 (* not really necessary, but safeguard *)
         )
    LOCAL ( temp 1%positive (Vint (Int.repr max_fd));
              temp 2%positive read_set_ptr;
              temp 3%positive write_set_ptr;
              temp 4%positive exception_set_ptr;
              temp 5%positive timeval_ptr
          )
    SEP ( SOCKAPI st ;
            FD_SET read_sh read_set read_set_ptr ;
            FD_SET write_sh write_set write_set_ptr ;
            FD_SET exception_sh exception_set exception_set_ptr )
  POST [ tint ]
    EX st' : SocketMap,
    EX read_set' : FD_Set,
    EX write_set' : FD_Set,
    EX exception_set' : FD_Set, 
    EX r : Z,
    PROP ( -1 <= r <= max_fd ;
             r < 0 -> read_set' = read_set /\ write_set' = write_set /\
                     exception_set' = exception_set /\
                     st' = st
             ; 
             r >= 0 ->
             fd_subset read_set' read_set /\
             fd_subset write_set' write_set /\
             fd_subset exception_set' exception_set /\
             r = Z.of_nat
                   (length (read_set' ++ write_set' ++ exception_set')%list) /\
             Forall (fun fd => descriptor fd < max_fd) read_set' /\ 
             st' = st 
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ;
            FD_SET read_sh read_set' read_set_ptr ;
            FD_SET write_sh write_set' write_set_ptr ;
            FD_SET exception_sh exception_set' exception_set_ptr ).

End HoareSocket.

Section HoareFD.
  
Definition fd_zero_macro_spec :=
  DECLARE _fd_zero_macro
  WITH fdset : FD_Set,
       set_ptr : val,
       sh: share
  PRE [ _set OF (tptr (Tstruct _fd_set noattr)) ]
    PROP ( writable_share sh )
    LOCAL ( temp _set set_ptr )
    SEP ( FD_SET sh fdset set_ptr )
  POST [ Tvoid ]
    PROP ( )
    LOCAL ( )
    SEP ( FD_SET sh ([] : FD_Set) set_ptr ).

Definition fd_set_macro_spec :=
  DECLARE _fd_set_macro
  WITH fd : sockfd,
       fdset : FD_Set,
       set_ptr : val,
       sh: share
    PRE [ _fd OF tint, _set OF (tptr (Tstruct _fd_set noattr)) ]
    PROP ( writable_share sh ; 0 <= descriptor fd < FD_SETSIZE )
    LOCAL ( temp _fd (Vint (Int.repr (descriptor fd))) ;
            temp _set set_ptr )
    SEP ( FD_SET sh fdset set_ptr )
  POST [ Tvoid ]
    EX fdset' : FD_Set, 
    PROP ( fdset' = insert_fd fd fdset )
    LOCAL ( )
    SEP ( FD_SET sh fdset' set_ptr ).

Definition fd_isset_macro_spec :=
  DECLARE _fd_isset_macro
  WITH fd: sockfd,
       fdset : FD_Set,
       set_ptr : val,
       sh: share
  PRE [ _fd OF tint, _set OF (tptr (Tstruct _fd_set noattr)) ]
    PROP ( readable_share sh; 0 <= descriptor fd < FD_SETSIZE
         )
    LOCAL ( temp _fd (Vint (Int.repr (descriptor fd)));
            temp _set set_ptr
          )
    SEP ( FD_SET sh fdset set_ptr )
  POST [ tint ]
    EX r : Z,
    PROP ( Int.min_signed <= r <= Int.max_signed ;
             r <> 0 -> In (descriptor fd) (map descriptor fdset);
             r = 0 -> ~In (descriptor fd) (map descriptor fdset)
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( FD_SET sh fdset set_ptr ).

End HoareFD.

Section HoareInet.

Definition htons_spec :=
  DECLARE _htons
  WITH n : Z
  PRE [ 1%positive OF tushort ]
    PROP ( 0 <= n <= two_p 16 - 1 )
    LOCAL ( temp 1%positive (Vint (Int.repr n)) )
    SEP ( )
  POST [ tushort ]
    PROP ( 0 <= n <= two_p 16 - 1 (* to typecheck return value *) )
    LOCAL ( temp ret_temp (Vint (Int.repr n)) )
    SEP ( ).
  
End HoareInet.

(*
Ltac forward_select max_fd rs ws es timeval_ptr :=
  match goal with
  | [|- context[SOCKAPI ?st]] =>
  match goal with
  | [|- context[FD_SET ?read_sh rs ?read_set_ptr]] =>
  match goal with
  | [|- context[FD_SET ?write_sh ws ?write_set_ptr]] =>
  match goal with
  | [|- context[FD_SET ?exception_sh ?exception_set_ptr es]] =>
    (* replace fds_in_read_set with (fds_in rs); *)
    forward_call (st, max_fd,
                  rs, ws, es,
                  read_set_ptr, write_set_ptr, exception_set_ptr,
                  timeval_ptr,
                  read_sh, write_sh, exception_sh) (* | auto] *)
  end
  end
  end
  end.
 *)

Definition socket_specs :=
  [socket_spec;
     bind_spec;
     listen_spec unit;
     accept_spec unit;
     recv_spec unit;
     send_spec unit;
     select_spec unit;
     close_spec unit;
     shutdown_spec unit].
