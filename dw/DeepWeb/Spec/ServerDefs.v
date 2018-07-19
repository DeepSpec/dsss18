Require Import Coq.ZArith.ZArith.
Open Scope Z.

From Custom Require Import String.

Definition BUFFER_SIZE : Z := 1024.
Definition SERVER_PORT : Z := 8000.

Definition INIT_MSG := repeat_string "0"%char (Z.to_nat BUFFER_SIZE).
