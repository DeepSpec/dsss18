From Custom Require Import String.

Require Import DeepWeb.Util.ByteType.
Require Import DeepWeb.Lib.NetworkInterface.

(* Dummy value for the endpoint (ignored). *)
Definition default_endpoint : endpoint_id := 0.

(* A short buffer size for easier testing. *)
Definition default_buffer_size : nat := 3.

(* "000" *)
Definition default_init_message : bytes :=
  repeat_string "0"%char default_buffer_size.
