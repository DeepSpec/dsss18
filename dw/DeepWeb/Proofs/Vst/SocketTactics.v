
From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib VerifHelpers SocketSpecs MonadExports.

Import SockAPIPred.
Import TracePred.
Import FDSetPred.

(* Tries to prove that a series of SocketMap updates on the same fd results 
   in the identity *)
Ltac prove_socket_map_eq initial_st updated_fd :=
  let lookup0 := fresh "lookup0" in
  let fd0 := fresh "fd0" in
  subst;
  unfold update_socket_state;
  simpl;
  destruct initial_st as [lookup0];
  f_equal;
  apply functional_extensionality;
  intros fd0;
  destruct (descriptor updated_fd =? descriptor fd0) eqn:Heq;
  auto;
  rewrite Z.eqb_eq in Heq;
  try apply (lookup_descriptor {| lookup_socket := lookup0 |}) in Heq;
  simpl in Heq;
  try rewrite <- Heq;
  auto.

Ltac forward_recv fd buf_ptr alloc_len :=
  let HTrace := fresh "HTrace" in
  let left_tree := fresh "left_tree" in 
  intro_trace_or_incl HTrace left_tree;
  simpl_trace_incl HTrace;
  match goal with
  | [H: trace_incl (bind (recv ?client_conn) ?k) ?t |- _] =>
    match goal with
    | [|- context[SOCKAPI ?st]] =>
      match goal with
      | [|- context[data_at_ ?sh _ buf_ptr]] =>
        forward_call (t, k, client_conn, st, fd, buf_ptr, alloc_len, sh)
      | [|- context[data_at ?sh _ _ buf_ptr]] =>
        forward_call (t, k, client_conn, st, fd, buf_ptr, alloc_len, sh)
      end
    end
  end;
  subst left_tree; clear HTrace.

Ltac forward_send fd buf_ptr :=
  let HTrace := fresh "HTrace" in
  let left_tree := fresh "left_tree" in 
  intro_trace_or_incl HTrace left_tree;
  simpl_trace_incl HTrace;
  match goal with
  | [H: trace_incl (bind (send_any_prefix ?client_conn ?msg) ?k) ?t |- _] =>
    match goal with
    | [|- context[SOCKAPI ?st]] =>
      match goal with
      | [|- context[data_at ?sh _ _ buf_ptr]] =>
        forward_call (t, k, client_conn, st, fd, msg,
                      buf_ptr, sh)
      end
    end
  end;
  subst left_tree; clear HTrace.

Ltac forward_accept fd :=
  let HTrace := fresh "HTrace" in
  let left_tree := fresh "left_tree" in 
  intro_trace_or_incl HTrace left_tree;
  simpl_trace_incl HTrace;
  match goal with
  | [H: trace_incl (bind (accept ?server_addr) ?k) ?t |- _] =>
    match goal with
    | [|- context[SOCKAPI ?st]] =>
      forward_call (t, k, server_addr, st, fd)
    end
  end;
  subst left_tree; clear HTrace.

Ltac forward_shutdown fd :=
  let HTrace := fresh "HTrace" in
  (* expecting ITree to have no alternatives because [shutdown] never 
     fails *)
  intro_trace_refl_incl HTrace; 
  simpl_trace_incl HTrace;
  match goal with
  | [H: trace_incl ((shutdown ?conn_id) ;; ?k) ?t |- _] =>
    match goal with
    | [|- context[SOCKAPI ?st]] =>
      forward_call (t, k, conn_id, st, fd)
    end
  end;
  clear HTrace.


Ltac init_fd_set fdset ptr idx :=
  let H := fresh "H" in 
  destruct (buffer_to_fd_set Tsh ptr) as [fdset H];
  apply (replace_SEP' idx (FD_SET Tsh fdset ptr));
  simpl canon.my_nth; simpl replace_nth;
  [entailer! | clear H].

Ltac teardown_fd_set fdset ptr idx :=
  let H := fresh "H" in 
  pose proof (fd_set_to_buffer Tsh fdset ptr) as H;
  apply (replace_SEP' idx (data_at_ Tsh (Tstruct _fd_set noattr) ptr));
  simpl canon.my_nth; simpl replace_nth;
  [entailer! | clear H].


Ltac forward_fd_zero_macro set :=
  match goal with
  | [|- context[FD_SET ?sh set ?ptr :: _]] =>
    forward_call (set, ptr, sh)
  end.

Ltac forward_fd_isset_macro fd set :=
  match goal with
  | [|- context[FD_SET ?sh set ?ptr :: _]] =>
    forward_call (fd, set, ptr, sh)
  end.

Ltac forward_fd_set_macro fd set :=
  match goal with
  | [|- context[FD_SET ?sh set ?ptr :: _]] =>
    forward_call (fd, set, ptr, sh)
  end.

(* FD_SET *)
Hint Resolve fd_subset_insert1.
Hint Resolve fd_subset_insert2.
Hint Resolve fd_subset_refl.
