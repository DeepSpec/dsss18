(* Effects for servers *)

(* If you come from [SimpleSpec] the types here will look
   different from those over there.
   The functions below are actually more polymorphic, so that
   they can be used with different effect types.
   You actually use the functions below when you import
   [SimpleSpec]; the module types with simpler signatures
   are only for the sake of exposition.

   This is also the case for [SimpleSpec_Observer].
 *)

From Custom Require Import String.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Import MonadNotations.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.SimpleSpec_Traces.

Module Export ServerType.
(* A simple interface of server effects. *)
Inductive serverE : Type -> Type :=
| Accept   : serverE connection_id
| RecvByte : connection_id -> serverE byte
| SendByte : connection_id -> byte -> serverE unit
.
End ServerType.

(* The server monad we write implementations in.
   A server is a program with internal nondeterminism and
   external network effects. *)
Definition ServerM := M (failureE +' nondetE +' serverE).

(* Accept a new connection. *)
Definition accept {E} `{serverE -< E}
  : M E connection_id := embed Accept.

(* Receive one byte from a connection. *)
Definition recv_byte {E} `{serverE -< E}
  : connection_id -> M E byte := embed RecvByte.

(* Send one byte to a connection. *)
Definition send_byte {E} `{serverE -< E}
  : connection_id -> byte -> M E unit := embed SendByte.

(* Receive up to [n] bytes. *)
Fixpoint recv {E} `{serverE -< E} `{nondetE -< E}
           (c : connection_id) (n : nat) : M E bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- recv_byte c;;
    bs <- recv c n;;
    ret (b ::: bs)
  end%string.

(* Receive a bytestring of length [n] exactly. *)
Definition recv_full {E} `{serverE -< E}
           (c : connection_id) (n : nat) : M E bytes :=
  replicate_bytes n (recv_byte c).

(* Send all bytes in a bytestring. *)
Fixpoint send {E} `{serverE -< E}
         (c : connection_id) (bs : bytes) : M E unit :=
  for_bytes bs (send_byte c).

(* A [real_event] is a [serverE] effect ([serverE X])
   together with its result ([X]) *)
Definition event_to_serverE (ev : real_event) :
  { X : Type & (serverE X * X)%type } :=
  match ev with
  | NewConnection c => existT _ _ (Accept, c)
  | ToServer c b => existT _ _ (RecvByte c, b)
  | FromServer c b => existT _ _ (SendByte c b, tt)
  end.

Instance EventType_serverE : EventType real_event serverE := {|
    from_event := event_to_serverE;
  |}.

(* [is_server_trace server tr] holds if [tr] is a trace of the [server]. *)
Definition is_server_trace : ServerM unit -> real_trace -> Prop :=
  is_trace.
