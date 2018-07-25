Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs Vst.Representation
     Vst.MonadExports Swap_CLikeSpec.

Require Import DeepWeb.Lib.VstLib.

Set Bullet Behavior "Strict Subproofs".

Import SockAPIPred.
Import TracePred.

(***************************** accept_connection ******************************)

Definition accept_connection_spec (T : Type) :=
  DECLARE _accept_connection
  WITH k : option connection -> SocketM T,
       addr : endpoint_id,
       st : SocketMap,
       fd : sockfd,
       elems : list (val * elemtype LS),
       ptr_to_head : val,
       curr_head : val                
  PRE [ _socket__1 OF tint, 
        _head OF (tptr (tptr (Tstruct _connection noattr)))
      ] 
    PROP ( consistent_world st;
           lookup_socket st fd = ListeningSocket addr )
    LOCAL ( temp _socket__1 (Vint (Int.repr (descriptor fd))) ;
            temp _head ptr_to_head
          )
    SEP ( SOCKAPI st ;
            ITREE (bind (accept_connection addr) (fun r => k r));
            data_at Tsh (tptr (Tstruct _connection noattr))
                    curr_head ptr_to_head ;
            lseg LS Tsh Tsh elems curr_head nullval
        )
  POST [ tint ]
    EX result : option (connection * sockfd * val),
    EX st' : SocketMap,
    EX r : Z, 
    PROP ( r = YES \/ r = NO ;
           r >= 0 ->
           (exists (client_conn : connection_id) (client_fd : sockfd)
              (new_head : val),
               (result = Some ({| conn_id := client_conn ;
                                  conn_request := "";
                                  conn_response := "";
                                  conn_response_bytes_sent := 0; 
                                  conn_state := RECVING |},
                               client_fd, new_head) /\
                descriptor client_fd < FD_SETSIZE /\
                (* lookup_socket st fd = ListeningSocket addr /\ *)
                lookup_socket st client_fd = ClosedSocket /\
                st' = update_socket_state
                        st client_fd (ConnectedSocket client_conn)))
           ;
           r < 0 -> result = None /\ st' = st;
           consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ; 
            match result with
            | Some (conn, fd, new_head) => 
              ITREE (k (Some conn)) *
              malloc_token Tsh (Tstruct _connection noattr) new_head * 
              data_at Tsh (tptr (Tstruct _connection noattr))
                       new_head ptr_to_head *
              lseg LS Tsh Tsh
                   ( (new_head, rep_connection conn fd) :: elems )
                   new_head nullval
            | None =>
              ITREE (k None) *
              data_at Tsh (tptr (Tstruct _connection noattr))
                      curr_head ptr_to_head *
              lseg LS Tsh Tsh elems curr_head nullval
            end
        ).
