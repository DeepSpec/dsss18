Require Import DeepWeb.Spec.TopLevelSpec.
Require Import DeepWeb.Spec.Swap_CLikeSpec.
Require Import DeepWeb.Proofs.Vst.verif_main.

Theorem swap_server_is_correct : swap_server_correct.
Proof.
  unfold swap_server_correct.
  exists server.
  apply body_main.
Qed.