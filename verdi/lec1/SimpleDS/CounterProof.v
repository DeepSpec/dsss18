Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import SysDef.
Require Import NetSem.
Require Import Counter.

Import Counter.
Include NetSem(Counter).

(* Trace-based spec is an exercise! See README. *)


(* a state-based spec *)
Definition backup_le_primary (w : world) : Prop :=
  locals w Backup <= locals w Primary.

(* this tactic "runs" handlers in proofs *)
Ltac do_handler :=
    unfold handle_input, handle_msg,
      do, nop, bind, ret, get, set in *;
   repeat break_let; repeat tuple_inversion.


(* first attempt at proof *)

Theorem counter_correct :
  forall w,
    reachable' shuffle_step w ->
    backup_le_primary w.
Proof.
  intros w Hreach.
  induction Hreach.
  - constructor.
  - invc H.
    + (* input *)
      unfold handle_input in *.
      destruct n, i; invc H0;
        unfold backup_le_primary, state in *;
        simpl; rewrite update_same, update_diff by congruence.
      * (* Primary *)
        omega.
      * (* Backup *)
        omega.
    + (* msg *)
      unfold handle_msg in *.
      destruct p; simpl in *.
      destruct dest, payload; invc H1;
        unfold backup_le_primary, state in *;
        simpl; rewrite update_same, update_diff by congruence;
        auto.
      
      (* ... huh? Backup can get ahead?!
         
         Similar to our first attempt in Fresh, we are stuck again!
         This time the problem is that we didn't relate the local
         state of the nodes to the state of the network.  Again,
         the solution is to prove something stronger.

       *)
Abort.



(* What we do know is that the Backup's state plus the number of
   _pending_ Inc messages in the network is equal to the Primary's
   state.

   For extra practice, below try deleting the proofs reproving some of
   the list-y lemmas that end up being pretty common when reasoning
   about networks. *)

Definition node_eqb (x y : node) : bool :=
  if node_eq_dec x y then true else false.

Definition msg_eqb (x y : msg) : bool :=
  if msg_eq_dec x y then true else false.

Definition count (l : list packet) : nat :=
  length
    (filter (fun p : packet =>
               node_eqb (dest p) Backup &&
               msg_eqb (payload p) Inc)
            l).

Definition backup_plus_count_eq_primary (w : world) : Prop :=
  locals w Backup + count (net w)
    = locals w Primary.

Lemma count_cons_backup_inc :
  forall l,
    count (mkpacket Backup Inc :: l) =
    S (count l).
Proof. reflexivity. Qed.

Lemma count_cons_primary :
  forall l m,
    count (mkpacket Primary m :: l) =
    count l.
Proof. reflexivity. Qed.

Lemma count_cons_ack :
  forall l n,
    count (mkpacket n Ack :: l) =
    count l.
Proof. destruct n; reflexivity. Qed.

Lemma count_remove_backup_inc :
  forall l,
    In (mkpacket Backup Inc) l ->
    S (count (remove_one (mkpacket Backup Inc) l)) = count l.
Proof.
  induction l; simpl; intuition.
  - subst. break_if; try congruence.
    now rewrite count_cons_backup_inc.
  - break_if.
    + find_inversion.
      now rewrite count_cons_backup_inc.
    + destruct dest, payload; try congruence;
        now rewrite ?count_cons_primary, ?count_cons_ack.
Qed.

Lemma count_remove_ack:
  forall l n,
    count (remove_one (mkpacket n Ack) l) = count l.
Proof.
  induction l; intuition.
  simpl count.
  simpl. break_if.
  + find_inversion. now rewrite count_cons_ack.
  + destruct dest, payload.
    * now rewrite !count_cons_primary.
    * now rewrite !count_cons_primary.
    * rewrite !count_cons_backup_inc. auto.
    * now rewrite !count_cons_ack.
Qed.

Lemma count_remove_primary :
  forall l m,
    count (remove_one (mkpacket Primary m) l) = count l.
Proof.
  induction l; simpl; intuition.
  break_if.
  - find_inversion. now rewrite count_cons_primary.
  - destruct dest, payload.
    * now rewrite !count_cons_primary.
    * now rewrite !count_cons_primary.
    * rewrite !count_cons_backup_inc. auto.
    * now rewrite !count_cons_ack.
Qed.

Lemma backup_plus_count_eq_primary_true :
  forall w,
    reachable' shuffle_step w ->
    backup_plus_count_eq_primary w.
Proof.
  intros w Hreach.
  induction Hreach.
  - reflexivity.
  - invc H.
    + (* input step *)
      unfold handle_input in *.
      destruct i, n; invc H0;
        unfold backup_plus_count_eq_primary, state in *;
        simpl; rewrite update_same, update_diff by congruence.
      * (* input delivered to primary *)
        rewrite count_cons_backup_inc.
        omega.
      * auto.
    + (* msg step *)
      unfold handle_msg in *.
      destruct p. simpl in *.
      destruct dest, payload;
        invc H1; unfold backup_plus_count_eq_primary, state in *;
          simpl; try rewrite update_same, update_diff by congruence.
      * (* primary, inc *)
        now rewrite <- IHHreach, count_remove_primary.
      * now rewrite <- IHHreach, count_remove_ack.
      * rewrite count_cons_primary.
        rewrite <- IHHreach.
        find_apply_lem_hyp count_remove_backup_inc.
        (* sorry! -- omega. *)
        admit.
      * now rewrite <- IHHreach, count_remove_ack.
Admitted.

Theorem backup_le_primary_true :
  forall w,
    reachable' shuffle_step w ->
    backup_le_primary w.
Proof.
  intros w Hreach.
  apply backup_plus_count_eq_primary_true in Hreach.
  unfold backup_plus_count_eq_primary, backup_le_primary in *.
  omega.
Qed.

