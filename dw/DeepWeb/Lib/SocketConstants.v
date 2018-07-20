(* POSIX socket API constants *)

Require Import Coq.ZArith.ZArith.

Definition YES : Z := 0.
Definition NO : Z := -1.
Definition EOF : Z := 0.

Definition MAX_FD : Z:= 4096.

Definition AF_INET : Z := 2.

Definition SOCK_STREAM : Z := 1.
Definition SOCK_DGRAM : Z := 2.
Definition SOCK_RAW : Z := 3.
Definition SOCK_RD : Z := 4.
Definition SOCK_SEQPACKET : Z := 5.
Definition SOCK_PACKET : Z := 10.

Definition INVALID_SOCKET : Z := -1.
Definition FD_SETSIZE : Z := 1024.
