Require Import String.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.NetworkInterface.
From DeepWeb.Spec
     Require Import Vst.MainInit Vst.SocketSpecs.

Import SockAPIPred.

Definition bind_socket_spec :=
  DECLARE _bind_socket
  WITH st : SocketMap,
       fd : sockfd,
       addr : endpoint_id
  PRE [ _fd OF tint, _port OF tint ] 
    PROP ( consistent_world st ; 0 <= port_number addr <= two_p 16 - 1 )
    LOCAL ( temp _fd (Vint (Int.repr (descriptor fd)));
            temp _port (Vint (Int.repr (port_number addr)))
          )
    SEP ( SOCKAPI st )
  POST [ tint ]
    EX st' : SocketMap,
    EX r : Z, 
    PROP ( r = YES \/ r = NO ;
             r = YES -> lookup_socket st fd = OpenedSocket /\
                       st' = update_socket_state st fd (BoundSocket addr) ;
             r = NO -> st' = st;
             consistent_world st'
         )
    LOCAL ( temp ret_temp (Vint (Int.repr r)) )
    SEP ( SOCKAPI st' ).
