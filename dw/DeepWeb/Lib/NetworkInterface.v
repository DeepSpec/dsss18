Generalizable Variable E.
Typeclasses eauto := 6.

Require Import String.
Require Import List.
Require Import PArith.
Import ListNotations.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.

Require Import DeepWeb.Util.ByteType.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Open Scope string_scope.
(* end hide *)

Definition connection_id : Type := nat.
Definition endpoint_id : Type := nat.

Inductive networkE : Type -> Type :=
| Listen : endpoint_id -> networkE unit
| Accept : endpoint_id -> networkE connection_id
| ConnectTo: endpoint_id -> networkE connection_id
| Shutdown : connection_id -> networkE unit
| Recv : connection_id -> networkE (option string)
| Send : connection_id -> string -> networkE unit.
(* Note: Recv returns [None] if connection is empty AND closed.
   It blocks if connection is empty. *)
  
Definition listen `{networkE -< E}
  : endpoint_id -> M E unit := embed Listen.

Definition accept `{networkE -< E}
  : endpoint_id -> M E connection_id := embed Accept.

Definition connect_to `{networkE -< E}
  : endpoint_id -> M E connection_id := embed ConnectTo.

Definition shutdown `{networkE -< E}
  : connection_id -> M E unit := embed Shutdown.

Definition recv `{networkE -< E}
  : connection_id -> M E (option string) := embed Recv.

Definition send `{networkE -< E}
  : connection_id -> string -> M E unit := embed Send.

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

  