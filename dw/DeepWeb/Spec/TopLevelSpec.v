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

(** * The top-level correctness property. *)

(* BCP: Every word in the following definition needs some explanation!
   :-) *)

(* BCP: Why is the result type unit instead of void? *)
Definition swap_server_correct :=
  exists (tree : SocketMonad unit),
    refines_mod_network (simplify_network tree) swap_spec /\
    semax_prog_ext prog tree Vprog Gprog.
(* BCP: Can we expand SocketMonad to [M SocketE] here, to avoid
   defining it? *)

(* (The proof can be found in Proofs/TopLevelProof.v) *)