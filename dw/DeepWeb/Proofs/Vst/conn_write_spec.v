Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib Connection SocketSpecs MonadExports AppLogic.

Require Import DeepWeb.Spec.ITreeSpec.

Set Bullet Behavior "Strict Subproofs".

Import SockAPIPred.
Import TracePred.

(********************************* conn_write **********************************)

Definition conn_write_spec (T : Type) (buffer_size : Z) :=
  DECLARE _conn_write
  WITH k : connection -> SocketMonad T,
       st : SocketMap,
       conn : connection,
       fd : sockfd, 
       conn_ptr : val
  PRE [ _conn OF (tptr (Tstruct _connection noattr)) ] 
    PROP ( consistent_world st;
           conn_state conn = SENDING ;
           consistent_state buffer_size st (conn, fd) )
    LOCAL ( temp _conn conn_ptr )
    SEP ( SOCKAPI st ;
            TRACE (r <- conn_write conn ;; k r) ;
            list_cell LS Tsh (rep_connection conn fd) conn_ptr
        )
  POST [ tint ]
    EX result : connection,
    EX st' : SocketMap,
    EX r : Z, 
    PROP ( r = YES ; 
           send_step (conn, fd, st) (result, fd, st');
           consistent_world st' )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ; TRACE (k result) ;
            list_cell LS Tsh (rep_connection result fd) conn_ptr
        ).