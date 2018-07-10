From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib Connection SocketSpecs AppLogic.

Import FDSetPred.

Require Import DeepWeb.Spec.ITreeSpec.

Definition monitor_connections_spec :=
  DECLARE _monitor_connections
  WITH connections : list (connection * sockfd * val),
       read_set : FD_Set,
       write_set : FD_Set,
       max_fd : Z,
       conn_ptr : val,
       read_set_ptr : val,
       write_set_ptr : val,
       max_fd_ptr : val,
       sh : share 
  PRE [ _head OF tptr (Tstruct _connection noattr), 
        _rs OF tptr (Tstruct _fd_set noattr),
        _ws OF tptr (Tstruct _fd_set noattr),
        _max_fd OF tptr tint
      ]
  PROP ( readable_share sh ;
         -1 <= max_fd < FD_SETSIZE
       )
  LOCAL ( temp _head conn_ptr ;
          temp _rs read_set_ptr ;
          temp _ws write_set_ptr ;
          temp _max_fd max_fd_ptr
        )
  SEP ( lseg LS sh sh
             (map rep_full_conn connections) conn_ptr nullval ; 
        FD_SET Tsh read_set read_set_ptr ;
        FD_SET Tsh write_set write_set_ptr ;
        field_at Tsh tint [] (Vint (Int.repr max_fd)) max_fd_ptr
      )
  POST [ tvoid ]
    EX read_set' : FD_Set,
    EX write_set' : FD_Set,
    EX max_fd' : Z,
    PROP (
        -1 <= max_fd' < FD_SETSIZE;

        let waiting_to_recv :=
            map proj_fd (filter (has_conn_state RECVING) connections) in 
        fd_subset read_set' (read_set ++ waiting_to_recv) ;

        let waiting_to_send :=
            map proj_fd (filter (has_conn_state SENDING) connections) in
        fd_subset write_set' (write_set ++ waiting_to_send)
      )
    LOCAL ( )
    SEP ( lseg LS sh sh
             (map rep_full_conn connections) conn_ptr nullval ;
          FD_SET Tsh read_set' read_set_ptr ;
          FD_SET Tsh write_set' write_set_ptr ;
          field_at Tsh tint [] (Vint (Int.repr max_fd')) max_fd_ptr
        ).