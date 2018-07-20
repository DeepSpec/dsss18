From DeepWeb Require Import
     Spec.Swap_SimpleSpec.

From DeepWeb.Spec.Vst Require Import
     MainInit
     Gprog
     SocketSpecs
     main_spec.

Import TracePred.

(* *** The top-level correctness property.  (Proof of this is in 
   Proofs/TopLevelProof.v) *)

Definition swap_server_correct :=
  exists (tree : SocketMonad unit),
    (* tree refines simple_spec /\ *) 
    semax_body Vprog Gprog f_main (main_spec tree).
