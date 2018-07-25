Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs
     Vst.Representation Vst.MonadExports Vst.AppLogic Swap_CLikeSpec.

Import SockAPIPred.
Import FDSetPred.
Import TracePred.

Definition process_connections_spec (buffer_size : Z) :=
  DECLARE _process_connections
  WITH k : SocketM unit,
       st : SocketMap,
       server_addr : endpoint_id,
       server_fd : sockfd, 
       connections : list (connection * sockfd * val),
       read_set : FD_Set,
       write_set : FD_Set,
       last_msg : string,
       conn_ptr : val,
       read_set_ptr : val,
       write_set_ptr : val,
       msg_store_ptr : val
  PRE [ _head OF tptr (Tstruct _connection noattr), 
        _rs OF tptr (Tstruct _fd_set noattr),
        _ws OF tptr (Tstruct _fd_set noattr),
        _last_msg_store OF tptr (Tstruct _store noattr)
      ]
  PROP (
         consistent_world st;
         Forall (fun '(conn, fd, ptr) =>
                   consistent_state buffer_size st (conn, fd))
                connections;

         let waiting_to_recv :=
             map proj_fd (filter (has_conn_state RECVING) connections) in 
         fd_subset read_set (server_fd :: waiting_to_recv) ;

         let waiting_to_send :=
            map proj_fd (filter (has_conn_state SENDING) connections) in
         fd_subset write_set (waiting_to_send);

         lookup_socket st server_fd = ListeningSocket server_addr;
           
         (* Need this to make sure that 
            (1) each connection steps without interfering with another 
                connection's socket state, and
            (2) each fd is a unique key for connections, so that we can pick 
                out the connection that the C program has chosen to work on 
                in the interaction tree. 
          *)
         NoDup (map descriptor (map proj_fd connections));
         NoDup
           (map conn_id
                (map proj_conn
                     (filter
                        (fun c => (has_conn_state RECVING c
                                || has_conn_state SENDING c)%bool) connections)))
    
       )
  LOCAL ( temp _head conn_ptr ;
          temp _rs read_set_ptr ;
          temp _ws write_set_ptr ;
          temp _last_msg_store msg_store_ptr
        )
  SEP ( SOCKAPI st ;
        ITREE (r <- select_loop server_addr buffer_size
                 (true, (map proj_conn connections, last_msg))
                 ;; k);
        
        lseg LS Tsh Tsh
             (map rep_full_conn connections) conn_ptr nullval ;
        
        FD_SET Tsh read_set read_set_ptr ;
        FD_SET Tsh write_set write_set_ptr ;
        field_at Tsh (Tstruct _store noattr) [] (rep_store last_msg)
                 msg_store_ptr
        
      )
  POST [ tvoid ]
    EX connections' : list (connection * sockfd * val),
    EX last_msg' : string,
    EX st' : SocketMap,                                     
    PROP ( consistent_world st';
           Forall (fun '(conn, fd, ptr) =>
                     consistent_state buffer_size st' (conn, fd))
                  connections';
             
           lookup_socket st' server_fd = ListeningSocket server_addr;

           (* Retain this for malloc tokens *)
           map proj_ptr connections' = map proj_ptr connections;
           
           (* Retain this to preserve uniqueness *)
           map proj_fd connections' = map proj_fd connections;
           
           (* May be useful later *)
           map conn_id (map proj_conn connections')
           = map conn_id (map proj_conn connections);

           (* Need to assert separately because states can change *)
           NoDup
             (map conn_id
                  (map proj_conn
                       (filter
                          (fun c => (has_conn_state RECVING c
                                  || has_conn_state SENDING c)%bool) connections')))
         )
    LOCAL ( )
    SEP ( SOCKAPI st' ;
          ITREE (r <- select_loop server_addr buffer_size
                   (true, (map proj_conn connections', last_msg'))
                 ;; k);
          
          lseg LS Tsh Tsh
               (map rep_full_conn connections') conn_ptr nullval ;
          
          FD_SET Tsh read_set read_set_ptr ;
          FD_SET Tsh write_set write_set_ptr ;
          field_at Tsh (Tstruct _store noattr) [] (rep_store last_msg')
                 msg_store_ptr
        ).