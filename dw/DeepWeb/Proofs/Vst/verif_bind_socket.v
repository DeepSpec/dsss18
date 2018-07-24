From Custom Require Import String.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs bind_socket_spec.

From DeepWeb.Lib
     Require Import VstLib.

From DeepWeb.Proofs.Vst
     Require Import VerifLib.

Import SockAPIPred.
Import SockAddr.

Lemma body_bind_socket:
  semax_body Vprog Gprog f_bind_socket bind_socket_spec.
Proof.
  start_function.

  forward_call v_addr.
  unfold_data_at 1%nat.
  simpl.

  forward.
  forward.

  assert
    (Int.zero_ext 16 (Int.repr (port_number addr)) = Int.repr (port_number addr))
    as addr_eq.
  { rewrite zero_ext_inrange; [reflexivity |].
    rewrite Int.unsigned_repr.
    2: {
      unfold Int.max_unsigned, two_p, two_power_pos in *.
      simpl in *.
      rep_omega.
    }
    omega.
  } 
  
  forward_call (port_number addr).
  { rewrite addr_eq. entailer!. }

  forward.

  forward_call (st, fd, addr, v_addr, sizeof (Tstruct _sockaddr_in noattr)).
  { 
    unfold_data_at 1%nat.
    rewrite addr_eq.
    cancel.
  } 

  Intro vret.
  destruct vret as [st' bind_ret].
  simpl.
  Intros.

  unfold YES, NO in *.

  forward_if.
  {
    assert (bind_ret = -1) by omega.
    match goal with
    | [H1: bind_ret = -1, H2 : bind_ret = -1 -> _ |- _] =>
      rewrite (H2 H1)
    end.
    forward.
    Exists st.
    Exists (-1).
    entailer!.

  }

  assert (bind_ret = 0) by omega.
  match goal with
  | [H1: bind_ret = 0, H2 : bind_ret = 0 -> _ |- _] =>
    destruct (H2 H1)
      as [lookup_fd st'_eq]
  end.

  forward.
  Exists (update_socket_state st fd (BoundSocket addr)).
  Exists 0.
  entailer!.

Qed.
