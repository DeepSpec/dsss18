From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs.

Import SockAddr.

Definition zeroize_addr_spec :=
  DECLARE _zeroize_addr
  WITH ptr : val
  PRE [ _addr OF tptr (Tstruct _sockaddr_in noattr) ]
    PROP ( ) 
    LOCAL ( temp _addr ptr )
    SEP ( data_at_ Tsh (Tstruct _sockaddr_in noattr) ptr )
  POST [ tvoid ]
    PROP ( )
    LOCAL ( )
    SEP ( data_at Tsh (Tstruct _sockaddr_in noattr)
                  (rep_sockaddr {| sin_family := 0;
                                   sin_port := 0;
                                   sin_addr := 0
                                |})
                  ptr
        ).