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

(* Testing *)

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

(* We restrict this to [unit] counterexamples to
   avoid losing information accidentally. *)
Definition or_result {W : Type} :
  result W unit -> (unit -> result W unit) -> result W unit :=
  fun r1 r2 =>
    match r1 with
    | OK w => OK w
    | FAIL tt | DONTKNOW => r2 tt
    end.

Notation "x || y" := (or_result x (fun _ => y)) : result_scope.

Delimit Scope result_scope with result.

From QuickChick Require QuickChick.

Section CheckableResult.
Import QuickChick.

Definition collectResult {A CE} (r : result A CE) : string :=
  match r with
  | OK _    => "Found"
  | FAIL _ => "Not Found"
  | DONTKNOW  => "Out of Fuel"
  end.

Global Instance Checkable_result {A CE : Type} `{Show A} `{Show CE}
  : Checkable (@result A CE)  :=
  {| checker r :=
       collect (collectResult r)
       match r with
       | OK _ => checker true
       | FAIL _ => checker false
       | DONTKNOW => checker tt
       end |}.

End CheckableResult.

(* Option type *)

Definition or_option {A : Type} :
  option A -> (unit -> option A) -> option A :=
  fun r1 r2 =>
    match r1 with
    | None => r2 tt
    | Some a => Some a
    end.

Notation "x <|> y" := (or_option x (fun _ => y))
(at level 30) : option_scope.

Delimit Scope option_scope with option.

(* Trick extraction for big numbers. *)
Definition _10 : nat := 5 * 2.
Definition _100 : nat := _10 * _10.
Definition _1000 : nat := _100 * _10.
