From DeepWeb.Spec
     Require Import TopLevelSpec Swap_CLikeSpec
     Vst.MainInit Vst.Gprog Vst.SocketSpecs.

From DeepWeb.Proofs.Vst
     Require Import verif_prog.
  
Theorem prog_correct: semax_prog_ext prog server Vprog Gprog.
Proof.
  unfold semax_prog_ext.
  split.
  { auto. }
  split.
  { reflexivity. }
  split.
  { admit. }
  split. 
  { apply all_funcs_correct. }
  split.
  { auto. }
  admit.
Admitted.

Theorem swap_server_is_correct : swap_server_correct.
Proof.
  unfold swap_server_correct.
  exists server.
  split.
  - admit.
  - apply prog_correct.
Admitted.