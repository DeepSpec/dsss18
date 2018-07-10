Require Import String.

From DeepWeb.Proofs.Vst
     Require Import VstInit VstLib VerifHelpers
     add_to_fd_set_spec SocketSpecs SocketTactics ServerSpecs.

Import FDSetPred.
Import SockAPIPred.

Open Scope list.
Open Scope logic.

Set Bullet Behavior "Strict Subproofs".

Lemma body_add_to_fd_set:
  semax_body Vprog Gprog f_add_to_fd_set add_to_fd_set_spec.
Proof.
  start_function.

  (* get bounds on fd first for VST to simplify *)
  destruct (fd_bound (descriptor fd) (is_descriptor fd));
    unfold MAX_FD in *.
  (* ditto *)
  unfold FD_SETSIZE in *.
  
  forward_if.
  {
    apply denote_tc_test_eq_split;
      [ | apply valid_pointer_zero].
    apply sepcon_valid_pointer1.
    eapply derives_trans;
      [apply fd_set_to_buffer | apply data_at_valid_ptr];
      simpl; auto; omega.
  }
  
  { (* if *)
    forward.
    Exists fdset.
    Exists max_fd.
    Exists NO.
    entailer!.
  }

  forward_if.
  { forward.
    Exists fdset.
    Exists max_fd.
    Exists NO.
    entailer!.
  }

  forward_if.
  {
    forward.
    Exists fdset.
    Exists max_fd.
    Exists NO.
    entailer!.
  }

  forward_if.
  {
    forward.
    Exists fdset.
    Exists max_fd.
    Exists NO.
    entailer!.
  }

  forward_if.
  {
    forward.
    Exists fdset.
    Exists max_fd.
    Exists NO.
    entailer!.
  }

  forward_fd_set_macro fd fdset.
  Intro fdset'.

  forward.
  remember (descriptor fd) as n.

  focus_SEP 1.
  
  match goal with
  | [|- semax Delta
             (PROPx ?P (LOCALx ?L (SEPx (_ :: ?SP))))
             _ _] =>
    forward_if
      (EX max : Z,
       PROPx ((max = (if n >? max_fd then n else max_fd)) :: P)
       (LOCALx L 
       (SEPx (data_at Tsh tint (Vint (Int.repr max)) max_fd_ptr :: SP))))
  end.
  { (* if *)
    forward.
    Exists n.
    assert (n >? max_fd = true) as Hgt by
          (rewrite <- Zgt_is_gt_bool; omega).
    rewrite Hgt.
    entailer!.
  } 

  { (* else *)
    forward.
    assert (n >? max_fd <> true) as Hgt by
          (rewrite <- Zgt_is_gt_bool; omega).      
    apply not_true_is_false in Hgt.
    rewrite Hgt.
    Exists max_fd.
    entailer!.
  }

  Intros max.
  to_equal.
  forward.
  from_equal.

  Exists fdset'.
  Exists max.
  Exists YES.

  entailer!.

  split; auto.
  split; auto.

  destruct (descriptor fd >? max_fd) eqn:Hmax; split; auto; [| omega].
  rewrite Z.gtb_ltb in Hmax;
    rewrite Z.ltb_ge in Hmax;
    omega.

Qed.