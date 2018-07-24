Require Import Relations.
Require Import RelationClasses.

From QuickChick Require Import QuickChick.
From Custom Require Import List.
Import ListNotations.
From Custom Require Map.

Require Import DeepWeb.Free.Monad.Free.
Require Import DeepWeb.Free.Monad.Common.
Import NonDeterminismBis.
Import SumNotations.

Require Import DeepWeb.Lib.Util.

From DeepWeb Require Import
     Lib.SimpleSpec_NetworkModel
     Lib.SimpleSpec_Traces.

Set Bullet Behavior "Strict Subproofs".

Module Type ScramblingTypes.

Parameter wf_trace : forall {byte'}, list (event byte') -> Prop.

Definition network_scrambled_wf ns (tr0 tr1 : real_trace) :=
  wf_trace tr0 ->
  wf_trace tr1 ->
  network_scrambled ns tr0 tr1.

Definition network_scrambled_wf0 := network_scrambled_wf initial_ns.

Declare Instance scrambled_transitive : Transitive network_scrambled0.

Declare Instance scrambled_reflexive : Reflexive network_scrambled_wf0.

End ScramblingTypes.

Module ScramblingFacts <: ScramblingTypes.

Definition project_trace_on {byte'} (c : connection_id) :
  list (event byte') -> list (event byte') :=
  filter (fun ev => event_connection ev = c ?).

Definition is_ToFromServer {byte'} (ev : event byte') : bool :=
  match ev with
  | NewConnection _ => false
  | ToServer _ _ | FromServer _ _ => true
  end.

Definition wf_projection {byte'} (tr : list (event byte')) : bool :=
  match tr with
  | [] => true
  | NewConnection _ :: tr' =>
    forallb is_ToFromServer tr'
  | (ToServer _ _ | FromServer _ _) :: _ => false
  end.

Definition wf_trace {byte'} (tr : list (event byte')) : Prop :=
  forall c,
    is_true (wf_projection (project_trace_on c tr)).

Fixpoint open_trace {byte'}
         (is_open : connection_id -> Prop) (tr : list (event byte')) :
  Prop :=
  match tr with
  | [] => True
  | NewConnection c :: tr =>
    ~is_open c /\ open_trace (fun c' => c = c' \/ is_open c') tr
  | (ToServer c _ | FromServer c _) :: tr =>
    is_open c /\ open_trace is_open tr
  end.

Lemma open_trace_prop {byte'}
           (is_open is_open' : _) (tr : list (event byte')) :
  open_trace is_open tr ->
  (forall c, is_open c <-> is_open' c) ->
  open_trace is_open' tr.
Proof.
  generalize dependent is_open.
  generalize dependent is_open'.
  induction tr as [ | [ c | c b | c b] tr ];
    intros is_open is_open' Htr_open Hopen.
  - auto.
  - split.
    + rewrite <- Hopen.
      apply Htr_open.
    + eapply IHtr.
      { apply Htr_open. }
      { intro c0.
        split; intros [Hc0 | Hc0];
          auto;
          right; apply Hopen; auto.
      }
  - split.
    + rewrite <- Hopen.
      apply Htr_open.
    + eapply IHtr.
      { apply Htr_open. }
      auto.
  - split.
    + rewrite <- Hopen.
      apply Htr_open.
    + eapply IHtr.
      { apply Htr_open. }
      auto.
Qed.

Axiom equiv_open_wf :
  forall {byte'} (tr : list (event byte')),
    open_trace (fun _ => False) tr <-> wf_trace tr.

Lemma scrambled_preserves_wf : forall tr str : real_trace,
    wf_trace tr ->
    network_scrambled0 tr str ->
    wf_trace str.
Proof.
Admitted.

Definition network_scrambled_wf ns (tr0 tr1 : real_trace) :=
  wf_trace tr0 ->
  wf_trace tr1 ->
  network_scrambled ns tr0 tr1.

Definition network_scrambled_wf0 := network_scrambled_wf initial_ns.

(* TODO: we can always append ServerSend and ClientSend
   and preserve the [network_scrambled] property. *)

Definition combined_networks (ns01 ns12 ns02 : network_state) : Prop :=
  forall c,
    let cs01 := Map.lookup ns01 c in
    let cs12 := Map.lookup ns12 c in
    let cs02 := Map.lookup ns02 c in
    match connection_status cs01, connection_status cs12 with
    | CLOSED, CLOSED => connection_status cs01 = CLOSED
    | CLOSED, PENDING
    | PENDING, PENDING =>
      connection_status cs01 = PENDING
    | ACCEPTED, PENDING
    | ACCEPTED, ACCEPTED =>
      connection_status cs01 = ACCEPTED
    | CLOSED, ACCEPTED
    | PENDING, ACCEPTED
    | ACCEPTED, CLOSED
    | PENDING, CLOSED => False
    end /\
    connection_inbytes cs01 ++ connection_inbytes cs12
    = connection_inbytes cs02 /\
    connection_outbytes cs12 ++ connection_outbytes cs01
    = connection_outbytes cs02.

Lemma scrambled_transitive_empty
      (ns12 ns02 ns01 : network_state) tr2 :
  combined_networks ns01 ns12 ns02 ->
  network_scrambled ns12 [] tr2 ->
  network_scrambled ns02 [] tr2.
Proof.
Admitted.

Lemma scrambled_transitive_ ns01 ns12 ns02 tr0 tr1 tr2 :
  combined_networks ns01 ns12 ns02 ->
  network_scrambled ns01 tr0 tr1 ->
  network_scrambled ns12 tr1 tr2 ->
  network_scrambled ns02 tr0 tr2.
Proof.
  intros Hcombined H01_scrambled.
  generalize dependent tr2.
  generalize dependent Hcombined.
  induction H01_scrambled;
    intros.
  - eapply scrambled_transitive_empty; eauto.
  - econstructor.

(*
Lemma scrambled_transitive_
*)

Admitted.

Instance scrambled_transitive : Transitive network_scrambled0.
Proof.
  unfold Transitive.
Admitted.

(* The notion of "open" connection is not quite the same
   depending on whether we're on the client side or server side. *)

(* For a client, open connections are those that are
   [PENDING] or [ACCEPTED]. *)
Definition is_open_conns_client ns : connection_id -> Prop :=
  fun c =>
    connection_status (Map.lookup ns c)
    <> CLOSED.

(* For a server, open connections are those that it [ACCEPTED]. *)
Definition is_open_conns_server ns : connection_id -> Prop :=
  fun c =>
    connection_status (Map.lookup ns c) = ACCEPTED.

(* [clean_state ns] holds when all connections [ns]
   have empty buffers. *)
Definition clean_state (ns : network_state) := forall c,
    let cs := Map.lookup ns c in
    connection_status cs <> PENDING /\
    connection_inbytes  cs = [] /\
    connection_outbytes cs = [].

(*
Lemma connect_accept ns c c0 :
  Map.lookup (unsafe_accept_ns (unsafe_connect_ns ns c) c) c0
  = if c = c0 ? then
      {| connection_status := ACCEPTED;
         connection_inbytes := [];
         connection_outbytes := []; |}
    else
      Map.lookup ns c0.
Proof.
Admitted.
*)

Definition bind_transition {S B}
           (a : option (S * unit)) (b : S -> option (S * B)) :
  option (S * B) :=
  match a with
  | Some (s, _) => b s
  | None => None
  end.

Infix ">>=" := bind_transition (at level 30).

Lemma direct_to_server ns c b :
  connection_inbytes (Map.lookup ns c) = [] ->
  (client_send c b ns >>= server_recv c) = Some (ns, b).
Proof.
  intro Hc.
  simpl.
  rewrite Hc.
  unfold server_recv.
  rewrite Map.update_lookup_eq by reflexivity.
  simpl.
  rewrite Map.update_update_eq by reflexivity.
  erewrite Map.lookup_update_eq; eauto.
  destruct Map.lookup.
  unfold update_in; simpl.
  f_equal; auto.
Qed.

Lemma direct_from_server ns c b :
  connection_outbytes (Map.lookup ns c) = [] ->
  server_send c b ns >>= client_recv c = Some (ns, b).
Proof.
  intro Hc.
  simpl.
  rewrite Hc.
  unfold client_recv.
  rewrite Map.update_lookup_eq by reflexivity.
  simpl.
  rewrite Map.update_update_eq by reflexivity.
  erewrite Map.lookup_update_eq; eauto.
  destruct Map.lookup.
  unfold update_out; simpl.
  f_equal; auto.
Qed.

Lemma open_scrambled_reflexive :
  forall ns tr,
    clean_state ns ->
    open_trace (is_open_conns_server ns) tr ->
    network_scrambled ns tr tr.
Proof.
  intros ns tr.
  generalize dependent ns.
  induction tr as [ | [ c | c b | c b ] tr ];
    intros ns Hns_clean Htr_open.
  - (* [] *) constructor.
  - (* NewConnection c :: tr *)
    eapply ScrambleClient.
    { simpl. rewrite connect_success.
      { reflexivity. }
      { destruct Htr_open.
        unfold is_open_conns_server in H.
        destruct (Hns_clean c) as [ ? ? ].
        destruct connection_status; auto.
        exfalso; auto.
        exfalso; auto. }
    }
    eapply ScrambleServer.
    { simpl. rewrite accept_success.
      { reflexivity. }
      { destruct Htr_open.
        unfold is_open_conns_server in H.
        rewrite Map.update_lookup_eq; auto. }
    }
    apply IHtr.
    + rewrite Map.update_update_eq by reflexivity.
      rewrite Map.update_lookup_eq by reflexivity.
      intro c0.
      destruct (@dec (c = c0)).
      { typeclasses eauto. }
      { rewrite Map.update_lookup_eq by assumption.
        simpl; split; auto; discriminate. }
      { rewrite Map.update_lookup_neq by assumption.
        apply Hns_clean. }
    + destruct Htr_open as [Htr0 Htr1].
      apply open_trace_prop with (1 := Htr1).
      intros c0.
      unfold is_open_conns_server.
      rewrite Map.update_update_eq by reflexivity.
      rewrite Map.update_lookup_eq with (1 := eq_refl).
      destruct (@dec (c = c0)).
      { typeclasses eauto. }
      { rewrite Map.update_lookup_eq by assumption.
        split; auto. }
      { rewrite Map.update_lookup_neq by assumption.
        split; auto.
        intros []; auto; contradiction. }
  - (* ToServer c b :: tr *)
    eapply ScrambleClient.
    { reflexivity. }
    eapply ScrambleServer.
    { simpl.
      pose proof direct_to_server as H.
      simpl in H.
      rewrite H.
      reflexivity.
      apply Hns_clean. }
    apply IHtr.
    { auto. }
    { apply Htr_open. }
  - (* FromServer c b :: tr *)
    eapply ScrambleServer.
    { reflexivity. }
    eapply ScrambleClient.
    { simpl.
      pose proof direct_from_server as H.
      simpl in H.
      rewrite H.
      reflexivity.
      apply Hns_clean. }
    apply IHtr.
    { auto. }
    { apply Htr_open. }
Qed.

Instance scrambled_reflexive : Reflexive network_scrambled_wf0.
Proof.
  unfold Reflexive.
  intros tr Htr_wf _H. clear _H.
  apply equiv_open_wf in Htr_wf.
  apply open_scrambled_reflexive.
  { intro c; split; auto; discriminate. }
  { apply open_trace_prop with (1 := Htr_wf).
    unfold is_open_conns_server.
    simpl.
    split; discriminate + intros []. }
Qed.

End ScramblingFacts.
