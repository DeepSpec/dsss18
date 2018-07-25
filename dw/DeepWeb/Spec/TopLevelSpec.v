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

Definition swap_server_correct :=
  exists (tree : SocketM unit),
    refines_mod_network swap_observer (simplify_network tree) /\
    semax_prog_ext prog tree Vprog Gprog.

(* Notes:
   - [tree] will be instantiated with the intermediate "C-like"
     interaction tree found in Swap_CLikeSpec.v
   - [simplify_network] translates between two different variants of
     the network effect type (the Vst proofs use a richer variant with
     Shutdown and Listen events, which are not yet considered by our
     high-level spec).
   - [refines_mod_network] is "refinement modulo scrambling by the
     network".
   - [semax_prog_ext] is the Vst property for Valid Hoare triples
   - [prog] is the C program (as a CompCert AST: it is imported from
     MainInit.v, which gets it from main.v)
   - [Vprog] is the set of variables for [prog]
   - [Gprog] is the function specifications for prog

  The proof of this theorem can be found in [Proofs.TopLevelProof]. *)


