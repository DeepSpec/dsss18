From DeepWeb.Spec
     Require Import TopLevelSpec Swap_CLikeSpec
     Vst.MainInit Vst.Gprog Vst.SocketSpecs.

From DeepWeb.Proofs.Vst
     Require Import verif_prog.
(*Original proof  
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
Admitted.*)

  Ltac prove_semax_prog :=
 split3; [ | | split3; [ | | split]];
 [ reflexivity || fail "duplicate identifier in prog_defs"
 | reflexivity || fail "unaligned initializer"
 | solve [compute; repeat f_equal; apply proof_irr] || fail "comp_specs not equal"
 |
 | reflexivity || fail "match_globvars failed"
 | match goal with |- match ?A with _ => _ end =>
      let fs := fresh "fs" in set (fs := A); hnf in fs; subst fs; cbv iota beta;
      lazymatch goal with
      | |- False => fail "Can't find _main in Gprog" 
      | |- _ =>  idtac 
      end;
      (eexists; reflexivity) || 
        fail "Funspec of _main is not in the proper form"
    end
 ];
 repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).

  Lemma extract_prog_main t d p m w: prog_main (Clightdefs.mkprogram t d p m w) = m.
  Proof. unfold Clightdefs.mkprogram. destruct (build_composite_env' t w). reflexivity. Qed.

  Lemma extract_compEnv t a (H: build_composite_env t = Errors.OK a)
    d p m w:
    a=prog_comp_env (Clightdefs.mkprogram t d p m w).
  Proof. unfold Clightdefs.mkprogram.
         destruct (build_composite_env' t w). 
         rewrite e in H. inv H. reflexivity.
  Qed.

  Lemma extract_compEnv' {T} t d p m w x q:
    (*build_composite_env t =  Errors.OK a -> x=w ->*)
    x=w ->
    x = 
  @Ctypes.prog_comp_env T
    {|
    prog_defs := d;
    prog_public := p;
    prog_main := m;
    prog_types := t;
    prog_comp_env := w;
    prog_comp_env_eq := q |}.
  Proof. intros. subst. reflexivity. Qed.
  
Lemma FEqual {A} t t' (x x': option A) s s':
  t=t' -> x=x' -> s=s' ->
  PTree.Node t x s = PTree.Node t' x' s'.
Proof. intros; subst. trivial. Qed.

Lemma FEqual' {A} t t' (x x': option A) s s' c:
  c = PTree.Node t' x' s' -> t=t' -> x=x' -> s=s' ->
  PTree.Node t x s = c.
Proof. intros; subst. trivial. Qed.

Theorem prog_correct: semax_prog_ext prog server Vprog Gprog.
Proof. (*
  split3; [ | | split3; [ | | split]].
 + reflexivity || fail "duplicate identifier in prog_defs".
 + reflexivity || fail "unaligned initializer".
 +  admit. (* solve [compute; repeat f_equal; apply proof_irr] || fail "comp_specs not equal".*)
 + do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ].
   apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ].
   apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ].
   Check all_funcs_correct.
   SearchAbout semax_func semax_prog_ext.
   apply semax_func_cons_ext_vacuous. [reflexivity | reflexivity | ].
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   do 4 (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
   
   apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ].
 + reflexivity || fail "match_globvars failed".
 + match goal with |- match ?A with _ => _ end =>
      let fs := fresh "fs" in set (fs := A); hnf in fs; subst fs; cbv iota beta;
      lazymatch goal with
      | |- False => fail "Can't find _main in Gprog" 
      | |- _ =>  idtac 
      end;
      (eexists; reflexivity) || 
        fail "Funspec of _main is not in the proper form"
    end.
 ];
 repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).*)
  unfold semax_prog_ext.
  split.
  { auto. }
  split.
  { reflexivity. }
  split. 
  { remember prog as p. destruct prog.
    specialize (extract_compEnv _ _  prog_comp_env_eq).
    intros. specialize (H prog_defs prog_public prog_main).
    assert (exists w: wf_composites prog_types, True).
    { unfold wf_composites. rewrite prog_comp_env_eq. eexists; trivial. }
    destruct H0 as [w _]. specialize (H w).
    unfold cenv_cs. unfold CompSpecs.
    assert (X: Ctypes.prog_comp_env p = prog_comp_env) by (subst p; reflexivity).

    rewrite X, H; clear X H Heqp.
    apply extract_compEnv. (*compute. 
    rewrite H.
    remember (Ctypes.prog_comp_env p).  CompSpecs.
    unfold cenv_cs. Locate CompSpecs.
    assert (Ctypes.prog_comp_env p = prog_comp_env). subst p. reflexivity.
    rewrite H0; clear H0. erewrite H. unfold Clightdefs.mkprogram.
    simpl. remember ( build_composite_env' prog_types w ). destruct s.
    simpl. subst p. rewrite e in   prog_comp_env_eq.
    inv   prog_comp_env_eq. apply extract_compEnv. rewrite e; clear Heqs e.
    f_equal. compute. f_equal. f_equal.
    clear e Heqs. unfold prog_types. Print build_composite_env. compute. unfold Ctypes.prog_comp_env.
    simpl. Print wf_composites.  simpl.
    simpl in H.
     rewrite Heqp. apply extract_compEnv'.
     remember (Errors.OK cenv_cs) as e.
     unfold composites.
Locate build_composite_env. 
     simpl. compute. Locate composites.
     remember prog as p. destruct p. 
    apply extract_compEnv'.
    specialize (compute. simpl. remember (prog_comp_env prog).
    unfold prog in Heqc. Print prog_comp_env.
    prog_comp_env
           (Clightdefs.mkprogram c g 
    cbn in Heqc. Time compute.
    Time compute in Heqc.
    eapply FEqual'. eassumption. clear Heqc.
    apply FEqual. trivial. reflexivity. (*20s; wrongly reported to take 0.5s, probably displaying takes majority of time*)
    Time compute. (*instantaneous*)
    Time compute Locate prog_comp_env. Locate cenv_cs. compute. admit. }
  split. 
  { apply all_funcs_correct. }
  split.
  { auto. }
  remember (initial_world.find_id (prog_main prog) Gprog) as q. unfold prog in Heqq. rewrite extract_prog_main in Heqq.
  subst q. cbv iota beta. eexists. hnf.
(*  unfold main_pre_ext.
  reflexivity.
  match goal with |- match ?A with _ => _ end =>
      let fs := fresh "fs" in set (fs := A); hnf in fs; subst fs; cbv iota beta;
      lazymatch goal with
      | |- False => fail "Can't find _main in Gprog" 
      | |- _ =>  idtac 
      end;
      (eexists; reflexivity) || 
        fail "Funspec of _main is not in the proper form"
    end.
  compute in Heqq. idtac. Print initial_world.find_id.
  Search Clightdefs.mkprogram. prog_main. unfold prog_main in Heqq.
  hnf.*)*)
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