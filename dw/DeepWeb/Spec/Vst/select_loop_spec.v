Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs Vst.MonadExports
     Vst.Representation Swap_CLikeSpec.

Import SockAPIPred.
Import TracePred.

Definition select_loop_spec :=
  DECLARE _select_loop
  WITH k : SocketM unit,
       st : SocketMap,
       server_addr : endpoint_id,
       server_fd : sockfd,
       initial_msg : string,
       msg_store_ptr : val
  PRE [ _server_socket OF tint, 
        _last_msg_store OF tptr (Tstruct _store noattr) ]
  PROP ( consistent_world st;
         lookup_socket st server_fd = ListeningSocket server_addr ;
         0 <= descriptor server_fd < FD_SETSIZE
       )
  LOCAL ( temp _server_socket (Vint (Int.repr (descriptor server_fd))) ;
          temp _last_msg_store msg_store_ptr 
        )
  SEP ( SOCKAPI st ;
        ITREE ( select_loop server_addr BUFFER_SIZE (true, ([], initial_msg))
                ;; k ) ;
        field_at Tsh (Tstruct _store noattr) [] (rep_store initial_msg)
                 msg_store_ptr  
      )
  POST [ tint ]
    PROP ( False )
    LOCAL ( temp ret_temp (Vint (Int.repr 0)) )
    SEP ( ).  