From Coq Require Extraction.

Parameter flip : unit -> bool.
Parameter rand : nat -> nat.

Extract Constant flip => "Random.bool".
Extract Constant rand => "Random.int".
