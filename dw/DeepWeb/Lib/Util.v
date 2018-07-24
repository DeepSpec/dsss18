From Custom Require Import
     Monad String List.
Import MonadNotations.

From QuickChick Require Import
     Decidability Show.

From DeepWeb.Free Require Import
     Monad.Free.

(* Bytes *)

(* We use Coq's standard [string] type to use its
   pretty-printing niceness. *)

(* Single byte *)
Definition byte : Type := Ascii.ascii.

(* Bytestring *)
Definition bytes : Type := String.string.

(* Iterate a byte-producing process [n] times. *)
Fixpoint replicate_bytes {E} (n : nat) (get_byte : M E byte) :
  M E bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- get_byte;;
    bs <- replicate_bytes n get_byte;;
    ret (b ::: bs)
  end%string.

(* Loop over each byte. *)
Fixpoint for_bytes {E} (bs : bytes) (eat_byte : byte -> M E unit) :
  M E unit :=
  match bs with
  | "" => ret tt
  | b ::: bs => eat_byte b;; for_bytes bs eat_byte
  end%string.

(* Get a null-terminated sequence of bytes, excluding the zero-byte
   delimiter. Loops infinitely if there is no zero-byte. *)
Definition get_str {E} (get_byte : M E byte) : M E bytes :=
  (cofix get_str' (mk_bytes : bytes -> bytes) : M E bytes :=
     bindM get_byte (fun b =>
     if b = "000"%char ? then
       ret (mk_bytes "")%string
     else
       Tau (get_str' (fun bs => mk_bytes (b ::: bs)%string))))
    (fun bs => bs).

(* Loop over each byte and an extra null byte at the end. *)
Fixpoint for_str {E} (bs : bytes) (eat_byte : byte -> M E unit) :
  M E unit :=
  match bs with
  | "" => eat_byte "000"%char
  | b ::: bs => eat_byte b;; for_str bs eat_byte
  end%string.

(* Network *)

Require Import ZArith.

Inductive connection_id : Type := Connection (c : nat).

Definition eqb_connection_id :
  forall c1 c2 : connection_id, {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; dec_eq. Defined.

Instance Eq_connection_id : Eq connection_id :=
  { dec_eq := eqb_connection_id }.

Instance Show_connection_id : Show connection_id :=
  { show := fun '(Connection c) => show c }.

Instance show_unit : Show unit :=
  { show _ := "tt"%string }.

Module TestDefault.

(* A short buffer size for easier testing. *)
Definition buffer_size : nat
  := 3.

(* "000" *)
Definition init_message : bytes
  := repeat_string "0"%char buffer_size.

End TestDefault.

(**)

(* Partial test result type. *)

Inductive result (W CE : Type) :=
| OK (witness : W)       (* Success, with a witness *)
| FAIL (counterex : CE)  (* Failure, with a counterexample *)
| DONTKNOW               (* Test ran out of fuel or something *)
.

Arguments OK {W} {CE}.
Arguments FAIL {W} {CE}.
Arguments DONTKNOW {W} {CE}.

(* A result with no meaningful witnesses of success or
   counterexamples. *)
Definition simple_result := result unit unit.
