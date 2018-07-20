Require Import String.

From DeepWeb.Lib Require Import
     VstLib.

From DeepWeb.Spec Require Import
     Vst.MainInit
     Vst.SocketSpecs
     Swap_CLikeSpec.

Require Import DeepWeb.Lib.VstLib.

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

