From DeepWeb Require Import
     Free.Monad.Free
     Lib.SimpleSpec
     Lib.NetworkAdapter
     Spec.Swap_SimpleSpec.

From DeepWeb.Spec.Vst Require Import
     MainInit
     Gprog
     SocketSpecs.

Import TracePred.

Definition swap_observer := swap_observer_ (Z.to_nat BUFFER_SIZE) INIT_MSG.

(** * The top-level correctness property. *)

(* BCP: Every word in the following definition needs some explanation!

   - simplify_network translates between two different variants of the
     network effect type (the Vst proofs use a richer variant with
     Shutdown and Listen events, which are not (yet!) handled by our
     high-level spec)
   - refines_mod_network needs explanation and maybe examples (in a
     separate file)
   - semax_prog_ext - i.e., valid hoare triple (from Vst)
   - prog - the program (as a CompCert AST, from MainInit - ultimately
     from main.v)
   - Vprog - the variables for prog
   - Gprog - the function specifications for prog
*)

Definition swap_server_correct :=
  exists (tree : M socketE unit),
    refines_mod_network swap_observer (simplify_network tree) /\
    semax_prog_ext prog tree Vprog Gprog.

(* (The proof can be found in [Proofs/TopLevelProof.v]) *)
