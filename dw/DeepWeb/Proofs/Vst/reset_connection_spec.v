Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib Connection.

Require Import DeepWeb.Spec.ITreeSpec.

Set Bullet Behavior "Strict Subproofs".

Definition reset_connection_spec :=
  DECLARE _reset_connection
  WITH conn : connection,
       curr_fd : sockfd, 
       new_fd : sockfd,
       conn_ptr : val
  PRE [ _conn OF tptr (Tstruct _connection noattr), _fd OF tint ] 
    PROP ( )
    LOCAL ( temp _conn conn_ptr ;
            temp _fd (Vint (Int.repr (descriptor new_fd)))
          )
    SEP ( list_cell LS Tsh (rep_connection conn curr_fd) conn_ptr )
  POST [ tvoid ]
    PROP ( )
    LOCAL ( )
    SEP (
      let conn' :=
          (upd_conn_request 
             (upd_conn_response_bytes_sent 
                (upd_conn_response 
                   (upd_conn_state conn RECVING) "") 0) "") in
                         
      list_cell LS Tsh (rep_connection conn' new_fd) conn_ptr
    ).