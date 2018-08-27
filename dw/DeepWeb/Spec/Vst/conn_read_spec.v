Require Import String.

From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs Vst.MonadExports
     Vst.Representation Vst.AppLogic Swap_CLikeSpec.

Import SockAPIPred.
Import TracePred.

(********************************* conn_read **********************************)

Definition conn_read_spec (T : Type) (buffer_size : Z) :=
  DECLARE _conn_read
  WITH k : (connection * string) -> SocketM T,
       st : SocketMap,
       conn : connection,
       fd : sockfd,
       last_msg : string,
       conn_ptr : val,
       msg_store_ptr : val 
  PRE [ _conn OF (tptr (Tstruct _connection noattr)),
        _last_msg_store OF (tptr (Tstruct _store noattr))
      ]
    PROP ( consistent_world st;
           conn_state conn = RECVING ;
           consistent_state buffer_size st (conn, fd)
         )
    LOCAL ( temp _conn conn_ptr ; temp _last_msg_store msg_store_ptr )
    SEP ( ITREE (r <- conn_read buffer_size conn last_msg ;; k r) st;
            list_cell LS Tsh (rep_connection conn fd) conn_ptr ;
            field_at Tsh (Tstruct _store noattr) []
                     (rep_store last_msg) msg_store_ptr
        )
  POST [ tint ]
    EX conn' : connection,
    EX last_msg' : string,
    EX st' : SocketMap,
    EX r : Z, 
    PROP ( r = YES ;
           recv_step buffer_size
                     (conn, fd, st, last_msg) (conn', fd, st', last_msg');
           consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP (ITREE (k (conn', last_msg')) st';
            list_cell LS Tsh (rep_connection conn' fd) conn_ptr ;
            field_at Tsh (Tstruct _store noattr) []
                     (rep_store last_msg') msg_store_ptr
        ).