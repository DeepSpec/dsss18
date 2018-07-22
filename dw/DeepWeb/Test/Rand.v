From Coq Require Extraction.
Require Import DeepWeb.Test.Client.

Parameter flip : IO bool.
Parameter rand : nat -> IO nat.

Extract Constant flip => "Random.bool".
Extract Constant rand => "fun n () -> Random.int n".
