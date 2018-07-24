From DeepWeb Require Import
     Lib.SimpleSpec
     Lib.NetworkAdapter
     Spec.Swap_SimpleSpec.

From DeepWeb.Spec.Vst Require Import
     MainInit
     Gprog
     SocketSpecs.

Import TracePred.

Definition swap_spec := swap_spec_ (Z.to_nat BUFFER_SIZE) INIT_MSG.

(* *** The top-level correctness property.  (Proof of this is in 
   Proofs/TopLevelProof.v) *)

Definition swap_server_correct :=
  exists (tree : SocketMonad unit),
    refines_mod_network (simplify_network tree) swap_spec /\
    semax_prog_ext prog tree Vprog Gprog.
