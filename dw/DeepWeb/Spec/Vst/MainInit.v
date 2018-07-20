Require Export VST.floyd.proofauto.
Require Export VST.floyd.library.
Require Export VST.progs.list_dt.
Export LsegGeneral.

Require Export DeepWeb.Spec.main.
Require Export DeepWeb.Spec.ServerDefs.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Lemma buffer_size_bounds: 0 < BUFFER_SIZE < Int.max_signed.
Proof.
  unfold BUFFER_SIZE.
  rep_omega.
Qed.
