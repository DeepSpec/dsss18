Require Import String.

Require Import DeepWeb.Spec.Swap_CLikeSpec.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs MonadExports.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib SocketTactics.

Import SockAPIPred.
Import TracePred.
Import FDSetPred.

Open Scope list.
Open Scope logic.

Opaque bind.
Opaque SERVER_PORT.

Set Bullet Behavior "Strict Subproofs".

Lemma body_main:
  semax_body Vprog Gprog f_main (main_spec server).
Proof.
  start_function.

  remember ({| lookup_socket := _ |}) as st0.
  assert_PROP (consistent_world st0).
  { entailer!.
    unfold consistent_world; intros.
    simpl in *; discriminate.
  } 
  
  Intros.

  (* new store *)
  forward_call tt.
  Intro vret.
  destruct vret as [store_opt store_ret].
  simpl.

  Intros.

  Local Ltac cases_on_store_ret store_ret :=
    match goal with
    | [H1: isptr store_ret \/ _,
       H2: isptr store_ret -> _ ,
       H3: store_ret = nullval -> _ |- _] =>
      destruct H1 as [store_ret_eq | store_ret_eq];
      [ try solve [subst; contradiction];
        try rewrite (H2 store_ret_eq)
      | try solve [subst; contradiction];
        try rewrite (H3 store_ret_eq)
      ]
    end.
  
  forward_if (isptr store_ret);
    [| forward_call tt; contradiction | forward; entailer! | ].
  {
    cases_on_store_ret store_ret;
     entailer!.
  }

  cases_on_store_ret store_ret; assumption.
  Intros.

  cases_on_store_ret store_ret.

  forward_call store_ret.
  { cancel. }
  
  unfold server, server_.

  forward_call st0.
  Intro vret.
  destruct vret as [st_post_socket socket_ret].
  simpl.
  Intros.
  
  forward_if (socket_ret >= 0);
    [ forward_call tt; contradiction | forward; entailer! |].

  Intros.

  forward_if (socket_ret < FD_SETSIZE);
    [ forward_call tt; contradiction | forward; entailer! |].

  Intros.
  
  match goal with
  | [H1 : socket_ret >= 0, H2: socket_ret >= 0 -> _ |- _] =>
    destruct (H2 H1)
      as [server_fd [socket_ret_eq [? st_post_socket_eq]]]
  end.

  rewrite socket_ret_eq.

  forward.

  remember 8000 as server_port.
  
  forward_call (st_post_socket, server_fd, Endpoint server_port).
  { split; auto; subst; simpl; omega. }

  Intro vret.
  destruct vret as [st_post_bind bind_ret].
  simpl.

  Intros.
  unfold YES, NO in *.
  forward_if (bind_ret = 0);
    [ forward_call tt; contradiction | forward; entailer! | ].

  Intros.
  
  match goal with
  | [H1: bind_ret = 0, H2: bind_ret = 0 -> _ |- _] =>
    destruct (H2 H1)
      as [server_fd_open st_post_bind_eq]
  end.
  
  forward_listen server_fd 128.
  { unify_trace; cancel. }
  { repeat split; auto.
    - apply trace_or_incl.
    - subst.
      rewrite lookup_update_socket_eq; reflexivity.
  }

  Intro vret.
  destruct vret as [[listen_res st_post_listen] listen_ret].
  simpl.
  Intros.

  forward_if (listen_ret = 0);
    [ forward_call tt; contradiction | forward; entailer! |].

  Intros.

  match goal with
  | [H1: listen_ret = 0, H2: listen_ret = 0 -> _ |- _] =>
    destruct (H2 H1)
      as [listen_res_eq st_post_listen_eq]
  end.

  rewrite listen_res_eq.

  forward_call (@ret SocketM _ _ tt, st_post_listen,
                SERVER_PORT,
                server_fd,
                INIT_MSG,
                store_ret).
  {
    unify_trace.
    cancel.
  } 
  {
    repeat split; subst; auto.
    2 : { apply fd_bound; destruct server_fd; auto. }
    
    rewrite lookup_update_socket_eq; auto.
  } 

Qed.
