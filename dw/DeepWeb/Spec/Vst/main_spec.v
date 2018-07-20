Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.semax_ext.

From DeepWeb.Spec.Vst
     Require Import MainInit SocketSpecs.

Import TracePred.

Definition void_spec T : external_specification juicy_mem external_function T :=
    Build_external_specification
      juicy_mem external_function T
      (fun ef => False)
      (fun ef Hef ge tys vl m z => False)
      (fun ef Hef ge ty vl m z => False)
      (fun rv m z => False).

Definition ok_void_spec (T : Type) : OracleKind.
 refine (Build_OracleKind T (Build_juicy_ext_spec _ (void_spec T) _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
Defined.

Definition ext_link := ext_link_prog main.prog.

Definition socket_ext_spec
  :=
  add_funspecs_rec
    ext_link
    (ok_void_spec (SocketMonad unit)).(@OK_ty)
    (ok_void_spec (SocketMonad unit)).(@OK_spec)
    socket_specs.

Instance Socket_Espec : OracleKind :=
  Build_OracleKind
    (SocketMonad unit)
    (socket_ext_spec).

Definition main_spec (tree : SocketMonad unit) :=
  DECLARE _main
  WITH gv : globals
  PRE [ _argc OF tint, _argv OF (tptr (tptr tschar)) ]
  (main_pre_ext prog tree [] gv)
  POST [ tint ]
  PROP ( False )
  LOCAL ( temp ret_temp (Vint (Int.repr 0)) )
  SEP ( ).
