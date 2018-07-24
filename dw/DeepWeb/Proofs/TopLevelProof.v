From DeepWeb.Spec
     Require Import TopLevelSpec Swap_CLikeSpec
     Vst.MainInit Vst.Gprog Vst.SocketSpecs.

From DeepWeb.Proofs.Vst
     Require Import verif_prog.
  
Theorem prog_correct: semax_prog_ext prog server Vprog Gprog.
Proof.
  unfold semax_prog_ext.

  Print Ltac prove_semax_prog.
  split3; [| | split3; [| | split ] ].
  { auto. }
  { reflexivity. }
  { unfold cenv_cs, prog_comp_env.
    unfold prog.
    unfold CompSpecs.
    match goal with
    | |- ?LHS = _ =>
      remember LHS as lhs
    end.

    unfold prog_comp_env.
    unfold Clightdefs.mkprogram.
    unfold build_composite_env'.
    unfold build_composite_env.
    simpl add_composite_definitions.
    idtac.
    simpl.
    


    
    subst lhs.
    f_equal.
    repeat f_equal.
    idtac.
    apply proof_irr.
    Set Printing All.
l    
    compute; repeat f_equal; apply proof_irr. 

    unfold cenv_cs.
    unfold prog_comp_env.
    Print Ltac prove_semax_prog.
    Print split3.
    simpl.
  } 
    
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
  apply prog_correct.
Qed.