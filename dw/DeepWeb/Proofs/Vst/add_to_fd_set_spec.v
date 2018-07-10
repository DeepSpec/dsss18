Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib SocketSpecs Connection Store
     MonadExports.

Import SockAPIPred.
Import FDSetPred.

(******************************* add_to_fd_set ********************************)

Definition add_to_fd_set_spec :=
  DECLARE _add_to_fd_set
  WITH fd : sockfd,
       fdset : FD_Set,
       set_ptr : val,
       max_fd_ptr : val,
       max_fd : Z
  PRE [ _fd OF tint, 
        _set OF (tptr (Tstruct _fd_set noattr)), 
        _max_fd OF (tptr tint)
      ] 
    PROP ( (* lookup_socket st fd <> ClosedSocket; *)
            -1 <= max_fd < FD_SETSIZE
         )
    LOCAL ( temp _fd (Vint (Int.repr (descriptor fd))) ;
            temp _set set_ptr ;
            temp _max_fd max_fd_ptr
          )
    SEP ( FD_SET Tsh fdset set_ptr;
            data_at Tsh tint (Vint (Int.repr max_fd)) max_fd_ptr)
  POST [ tint ]
    EX fdset' : FD_Set, 
    EX max_fd' : Z, 
    EX r : Z, 
    PROP ( r = YES \/ r = NO ;
             r >= 0 -> fdset' = insert_fd fd fdset /\
                     (max_fd' =
                      if (descriptor fd) >? max_fd then 
                        descriptor fd
                      else
                        max_fd) /\
                     0 <= max_fd' < FD_SETSIZE ;
             r < 0 -> fdset' = fdset /\
                     max_fd' = max_fd
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( FD_SET Tsh fdset' set_ptr;
            data_at Tsh tint (Vint (Int.repr max_fd')) max_fd_ptr
        ).
