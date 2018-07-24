Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs Swap_CLikeSpec.

From DeepWeb.Lib
     Require Import VstLib.

Import SockAPIPred.
Import TracePred.

Section Connection.
    
  Global Instance LS: listspec _connection _next (fun _ _ => emp).
  Proof. eapply mk_listspec; reflexivity. Defined.

  Definition rep_connection_state (st : connection_state) :
    reptype (nested_field_type (Tstruct _connection noattr)
                               [StructField _st]) :=
    Vint (Int.repr 
            match st with
            | RECVING => 0
            | SENDING => 1
            | DONE => 2
            | DELETED => 3
            end
         ).

  Definition rep_connection (conn : connection) (fd : sockfd)
    : elemtype LS :=
    let fd_rep := Vint (Int.repr (descriptor fd)) in
    let request_len_rep := rep_msg_len (conn_request conn) in
    let request_rep := rep_msg (conn_request conn) BUFFER_SIZE in
    let response_len_rep := rep_msg_len (conn_response conn) in
    let response_rep := rep_msg (conn_response conn) BUFFER_SIZE in
    let conn_state_rep := rep_connection_state (conn_state conn) in  
    (fd_rep,
     (request_len_rep,
      (request_rep,
       (response_len_rep,
        (response_rep,
         (Vint (Int.repr (conn_response_bytes_sent conn)),
          conn_state_rep)))))).

  Definition rep_full_conn (conn_fd_ptr : connection * sockfd * val)
    : val * elemtype LS :=
    let '(conn, fd, ptr) := conn_fd_ptr in (ptr, rep_connection conn fd).

  Definition proj_conn (conn_fd_ptr : connection * sockfd * val) :=
    let '(conn, fd, ptr) := conn_fd_ptr in conn.

  Definition proj_fd (conn_fd_ptr : connection * sockfd * val) :=
    let '(conn, fd, ptr) := conn_fd_ptr in fd.

  Definition proj_ptr (conn_fd_ptr : connection * sockfd * val) :=
    let '(conn, fd, ptr) := conn_fd_ptr in ptr.

  Global Instance connection_triple_has_conn_state
    : HasConnectionState (connection * sockfd * val).
  Proof. constructor. intros [[conn ?] ?]; destruct conn; assumption. Defined.
  
End Connection.


Section Store.
  Record store := { stored_msg : string }.

  Definition rep_store (s : string) : reptype (Tstruct _store noattr) :=
    (rep_msg_len s, rep_msg s BUFFER_SIZE).

End Store.
