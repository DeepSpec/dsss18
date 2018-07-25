Generalizable Variable E.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.

Require Import ZArith.
Require Import String.
Require Import List.
Import ListNotations.

From Custom Require Monad.
Import MonadNotations.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Internal.
Require Import DeepWeb.Free.Monad.Common.
Require Import DeepWeb.Free.Monad.Verif.

Require Import DeepWeb.Lib.Util.
Require Import DeepWeb.Lib.SocketConstants.
Require Export DeepWeb.Lib.NetworkInterface.

Module SocketAPI.

  Open Scope Z.
  
  Parameter is_fd: Z -> Prop.
  Axiom fd_nonneg: forall i : Z, is_fd i -> i < 0 -> False.
  Axiom fd_bound: forall i, is_fd i -> 0 <= i <= MAX_FD.
  Axiom zero_is_fd : is_fd 0.

  Record sockfd: Type :=
    { descriptor: Z; is_descriptor: is_fd descriptor }.

  Definition fd_eqb (fd1 fd2 : sockfd) : bool :=
    descriptor fd1 =? descriptor fd2.

  Lemma is_fd_irrelevant: forall fd1 fd2,
      descriptor fd1 = descriptor fd2 -> fd1 = fd2.
  Proof.
    intros [] [] Heqb.
    simpl in Heqb.
    Import ProofIrrelevance.
    pose proof proof_irrelevance.
    subst.
    specialize (H (is_fd descriptor1) is_descriptor0 is_descriptor1).
    subst.
    reflexivity.
  Qed.
      
  Definition socketE : Type -> Type := (nondetE +' failureE +' networkE).

  Instance socketE_networkE : networkE -< socketE.
  constructor.
  intros.
  unfold socketE.
  apply inr.
  trivial.
  Defined.

  Instance socketE_nondetE: nondetE -< socketE.
  repeat constructor; trivial.
  Defined.

  Instance socketE_failureE: failureE -< socketE.
  constructor.
  intros.
  apply inl.
  apply inr.
  trivial.
  Defined.

  Inductive socket_status :=
  | ClosedSocket
  | OpenedSocket
  | BoundSocket (addr : endpoint_id)
  | ListeningSocket (addr : endpoint_id)
  | ConnectedSocket (conn : connection_id).

  Record SocketMap : Type :=
    { lookup_socket: sockfd -> socket_status }.
  
  Lemma lookup_descriptor:
    forall (api_st : SocketMap) (fd1 fd2 : sockfd),
      descriptor fd1 = descriptor fd2 -> 
      lookup_socket api_st fd1 = lookup_socket api_st fd2.
  Proof.
    intros ? ? ? H.
    apply is_fd_irrelevant in H.
    subst.
    reflexivity.
  Qed.
  
  Definition connection_of_fd (api_st: SocketMap) (fd : sockfd)
    : option connection_id := 
    match lookup_socket api_st fd with
    | ConnectedSocket conn => Some conn
    | _ => None
    end.

  Definition endpoint_of_fd (api_st: SocketMap) (fd : sockfd)
    : option endpoint_id := 
    match lookup_socket api_st fd with
    | BoundSocket addr => Some addr
    | ListeningSocket addr => Some addr
    | _ => None
    end.

  Module TraceIncl.
  Section TraceIncl.

  Definition M_ := M socketE.

  Definition trace := list (sigT (fun Y => networkE Y * Y)%type).

  Inductive is_trace_of {R : Type}: trace -> option R -> M_ R -> Prop :=
  | Trace_Ret : forall r, is_trace_of [] (Some r) (Ret r)
  | Trace_Empty : forall m, is_trace_of [] None m
  | Trace_Tau : forall t m r,
      is_trace_of t r m -> is_trace_of t r (Tau m)
  | Trace_Or : forall b t k r,
      is_trace_of t r (k b) -> is_trace_of t r (Vis (inl (inl Or)) k)
  | Trace_Vis : forall Y (e : _ Y) y t k r,
      is_trace_of t r (k y) ->
      is_trace_of (existT _ Y (e, y) :: t) r (Vis (inr e) k).

  Definition trace_incl {R : Type} (m m' : M_ R) : Prop :=
    forall t r,
      is_trace_of t r m -> is_trace_of t r m'.
  
  Definition trace_eq {R : Type} (m m' : M_ R) : Prop :=
    forall t r,
      is_trace_of t r m <-> is_trace_of t r m'.

  Lemma trace_eq_incl2 {R : Type} (m m' : M_ R) :
    trace_incl m m' /\ trace_incl m' m <-> trace_eq m m'.
  Proof.
    split.
    - intros H t; split; apply H.
    - intros H; split; intro t; apply H.
  Qed.

  Lemma trace_incl_refl {R : Type} (m : M_ R) : trace_incl m m.
  Proof. intro; auto. Qed.

  Lemma trace_incl_trans {R: Type} (m n p : M_ R) :
    trace_incl m n -> trace_incl n p -> trace_incl m p.
  Proof. intros; intro; auto. Qed.

  Import ProofIrrelevance.
    
  Lemma trace_incl_eutt {R : Type} (m m' : M_ R) :
    EquivUpToTau m m' -> trace_incl m m'.
  Proof.
    intros H t r Ht.
    generalize dependent m'.
    induction Ht; intros m' H.
    - inversion_clear H.
      induction H1.
      + constructor.
        apply IHUnTau.
        auto.
      + inversion H0.
        subst.
        inversion H2.
        constructor.
    - constructor.
    - apply IHHt.
      apply eutt_sym, pop_tau, eutt_sym, H.
    - inversion_clear H.
      induction H1.
      + constructor.
        apply IHUnTau.
        auto.
      + inversion H0.
        subst; clear H0.
        inversion H2.
        destruct e0; inversion H1.
        apply inj_pair2 in H1.
        apply inj_pair2 in H3.
        subst.
        rewrite H1 in *.
        econstructor.
        apply IHHt.
        apply H4.
    - inversion H; subst; clear H.
      induction H1.
      + constructor.
        apply IHUnTau.
        auto.
      + inversion H0; subst.
        inversion H2; subst.
        apply inj_pair2 in H3.
        apply inj_pair2 in H4.
        subst.
        constructor.
        auto.
  Qed.

  Lemma trace_incl_respects_bind_assoc:
    forall {X Y Z} 
      (m : M_ X) (f : X -> M_ Y) (g : Y -> M_ Z)
      (t : M_ Z),
      trace_incl ( b <- (a <- m ;; f a) ;; g b ) t ->
      trace_incl ( a <- m ;; b <- f a ;; g b ) t.
  Proof.
    intros.
    eapply trace_incl_trans;
      [apply trace_incl_eutt; apply bindAssoc |].
    assumption.
  Qed.
        
  Lemma trace_or_incl {R : Type} (k1 k2 : M _ R):
    trace_incl k1 (or k1 k2) /\ trace_incl k2 (or k1 k2).
  Proof.
    intros.
    unfold trace_incl; split; intros; unfold or; 
      [ apply Trace_Or with (b := true)
      | apply Trace_Or with (b := false)]; assumption.
  Qed.

  Lemma eutt_bind_or {X Y : Type} (m1 m2 : M_ X) (k : X -> M_ Y) :
    EquivUpToTau (x <- or m1 m2 ;; k x)
                 (or (x <- m1 ;; k x)
                     (x <- m2 ;; k x)).
  Proof.
    rewrite (matchM (bind (or _ _) (fun x => k x))).
    unfold or.
    simpl.
    eapply EquivTauExhaust; try constructor.
    intros.
    destruct y; apply eutt_refl.
  Qed.    

  Lemma trace_or_incl_bind {X Y : Type} (m1 m2 : M_ X) (k : X -> M_ Y):
    trace_incl (x <- m1 ;; k x)
               (x <- or m1 m2 ;; k x) /\
    trace_incl (x <- m2 ;; k x)
               (x <- or m1 m2 ;; k x).
  Proof.
    pose proof (@eutt_bind_or X Y m1 m2 k) as H.
    apply eutt_sym in H.
    apply trace_incl_eutt in H.
    destruct (trace_or_incl (x <- m1 ;; k x) (x <- m2 ;; k x))
      as [HIncl1 HIncl2].
    split; eapply trace_incl_trans; eassumption.
  Qed.

  Lemma trace_or_incl_bind1 {X Y : Type} (m1 m2 : M_ X) (k : X -> M_ Y):
    trace_incl (x <- m1 ;; k x)
               (x <- or m1 m2 ;; k x).
  Proof. destruct (trace_or_incl_bind m1 m2 k); assumption. Qed.

  Lemma trace_or_incl_bind2 {X Y : Type} (m1 m2 : M_ X) (k : X -> M_ Y):
    trace_incl (x <- m2 ;; k x)
               (x <- or m1 m2 ;; k x).
  Proof. destruct (trace_or_incl_bind m1 m2 k); assumption. Qed.
  
  Lemma trace_choose_incl:
    forall {X R} (x : X) (l : list X) (k : X -> M_ R),
      In x l -> trace_incl (k x) (x <- choose l ;; k x).
  Proof.
    intros X R x.
    induction l; intros k HIn; unfold choose;
      inversion HIn.
    - subst.
      eapply trace_incl_trans; [| apply trace_or_incl_bind1].
      apply trace_incl_eutt.
      apply eutt_sym.
      apply leftId.
    - eapply trace_incl_trans; [| apply trace_or_incl_bind2].
      apply IHl.
      assumption.
  Qed.

  End TraceIncl.
  End TraceIncl.

  Export TraceIncl.
  
End SocketAPI.
