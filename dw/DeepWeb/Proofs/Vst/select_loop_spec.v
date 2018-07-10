Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib SocketSpecs MonadExports Store.

Require Import DeepWeb.Spec.ITreeSpec.

Set Bullet Behavior "Strict Subproofs".

Import SockAPIPred.
Import TracePred.

(******************************** select_loop *********************************)

Definition select_loop_spec (T : Type) :=
  DECLARE _select_loop
  WITH k : SocketMonad unit,
       st : SocketMap,
       server_addr : endpoint_id,
       server_fd : sockfd,
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
        TRACE ( r <- select_loop server_addr (true, ([], "")) ;; k ) ;
        field_at Tsh (Tstruct _store noattr) [] (rep_store "")
                 msg_store_ptr  
      )
  POST [ tint ]
    EX st' : SocketMap, 
    PROP ( consistent_world st' )
    LOCAL ( temp ret_temp (Vint (Int.repr 0)) )
    SEP ( SOCKAPI st' ;
          TRACE ( k ) ;
          field_at Tsh (Tstruct _store noattr) [] (rep_store "")
                   msg_store_ptr
        ).
