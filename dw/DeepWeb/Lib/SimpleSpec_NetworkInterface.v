From Custom Require Import String.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import NonDeterminismBis.
Import SumNotations.
Import MonadNotations.

Require Import DeepWeb.Lib.Util.

(* A simple interface of server-side network effects. *)
Inductive networkE : Type -> Type :=
| Accept   : networkE connection_id
| RecvByte : connection_id -> networkE byte
| SendByte : connection_id -> byte -> networkE unit
.

(* A server is a program with internal nondeterminism and
   external network effects. *)
Definition serverE := nondetE +' networkE.

(* The server itree type. *)
Definition itree_server := M (nondetE +' networkE) unit.

Definition accept {E} `{networkE -< E}
  : M E connection_id := embed Accept.

Definition recv_byte {E} `{networkE -< E}
  : connection_id -> M E byte := embed RecvByte.

Definition send_byte {E} `{networkE -< E}
  : connection_id -> byte -> M E unit := embed SendByte.

(* Receive up to [n] bytes. *)
Fixpoint recv {E} `{networkE -< E} `{nondetE -< E}
           (c : connection_id) (n : nat) : M E bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- recv_byte c;;
    bs <- recv c n;;
    ret (b ::: bs)
  end%string.

(* Receive a bytestring of length [n] exactly. *)
Definition recv_full {E} `{networkE -< E}
           (c : connection_id) (n : nat) : M E bytes :=
  replicate_bytes n (recv_byte c).

(* Send all bytes in a bytestring. *)
Fixpoint send {E} `{networkE -< E}
         (c : connection_id) (bs : bytes) : M E unit :=
  for_bytes bs (send_byte c).
