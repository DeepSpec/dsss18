Require Import Verdi.Verdi.

Require Import LockServ.
Require Verdi.SeqNum.
Require Import Verdi.SeqNumCorrect.

Section LockServSeqNum.
  Variable num_Clients : nat.

  Instance transformed_base_params : BaseParams :=
    @SeqNum.base_params (LockServ_BaseParams num_Clients) (LockServ_MultiParams num_Clients).

  Instance transformed_multi_params : MultiParams _ :=
    @SeqNum.multi_params (LockServ_BaseParams num_Clients) (LockServ_MultiParams num_Clients).

  Theorem transformed_correctness :
    forall net tr,
      step_dup_star step_async_init net tr ->
      @mutual_exclusion num_Clients (nwState (revertNetwork net)).
  Proof using.
    intros.
    pose proof @true_in_reachable_transform _ (LockServ_MultiParams num_Clients)
         (fun net : network => mutual_exclusion (nwState net))
         (@true_in_reachable_mutual_exclusion num_Clients).
    unfold true_in_reachable in *.
    apply H0.
    unfold reachable.
    eauto.
  Qed.
End LockServSeqNum.
