Generalizable Variable E.
Typeclasses eauto := 6.

From Coq Require Import List ZArith.
Import ListNotations.

From QuickChick Require Import
     Decidability Show.

From Custom Require Import String.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

Module Export Network.

Record endpoint_id : Type := Endpoint
  { port_number : Z;
  }.

Instance Eq_endpoint_id : Eq endpoint_id := {}.
Proof. intros; dec_eq. Defined.

Instance Show_endpoint_id : Show endpoint_id :=
  { show := fun '(Endpoint p) => show p }.

(* Dummy value for the endpoint (ignored). *)
Definition dummy_endpoint : endpoint_id
  := Endpoint 0.

Inductive networkE : Type -> Type :=
| Listen : endpoint_id -> networkE unit
| Accept : endpoint_id -> networkE connection_id
| Shutdown : connection_id -> networkE unit
| RecvByte : connection_id -> networkE byte
| SendByte : connection_id -> byte -> networkE unit.
  
Definition listen `{networkE -< E}
  : endpoint_id -> M E unit := embed Listen.

Definition accept `{networkE -< E}
  : endpoint_id -> M E connection_id := embed Accept.

Definition shutdown `{networkE -< E}
  : connection_id -> M E unit := embed Shutdown.

Definition recv_byte `{networkE -< E}
  : connection_id -> M E byte := embed RecvByte.

Definition send_byte `{networkE -< E}
  : connection_id -> byte -> M E unit := embed SendByte.

(* Helper for [recv]. *)
Fixpoint recv' `{networkE -< E} `{nondetE -< E}
         (c : connection_id) (len : nat) : M E bytes :=
  match len with
  | O => ret ""
  | S len =>
    b <- recv_byte c ;;
    or (ret (b ::: ""))
       (bs <- recv' c len ;;
        ret (b ::: bs))
  end%string.

(* Receive a string of length at most [len].
   The return value [None] signals that a connection was closed,
   when modelling the [recv()] POSIX syscall. *)
Definition recv `{networkE -< E} `{nondetE -< E}
           (c : connection_id) (len : nat) : M E (option bytes) :=
  or (ret None)
     (bs <- recv' c len;;
      ret (Some bs)).

(* Receive a string of length [len] exactly. *)
Definition recv_full `{networkE -< E}
           (c : connection_id) (len : nat) : M E bytes :=
  replicate_bytes len (recv_byte c).

(* Send all bytes in a bytestring. *)
Fixpoint send `{networkE -< E}
         (c : connection_id) (bs : bytes) : M E unit :=
  for_bytes bs (send_byte c).

(* All numbers between 0 and [n-1] included. *)
Fixpoint range (n : nat) : list nat :=
    match n with
    | O => []
    | S n' => range n' ++ [n']
    end.

Definition send_any_prefix (conn : connection_id) (msg : string)
           `{nondetE -< E} `{failureE -< E} `{networkE -< E} :
  M E nat :=
  len <- choose (range (String.length msg + 1)) ;;
  send conn (substring 0 len msg) ;;
  ret len.

End Network.

