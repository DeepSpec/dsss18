Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import SysDef.

(* To prove our systems correct, we need some way of describing what
   they actually do when they run. For that, we'll define another
   functor which takes a system as an argument and gives us back a
   module with a small step operational semantics for the system. *)

Module NetSem (P : SystemParams).
  Import P.

  (* Specificatons of distributed systems are often phrased in terms
     of what clients can see when interacting with the system over
     time. To facilitate such specs, our semantics will keep track of
     the "trace" of all the interactions ("external events") any node
     has ever had with any client. *)

  Inductive client_event : Type :=
  | client_in : node -> input -> client_event
  | client_out : node -> output -> client_event.

  (* state of an entire system *)
  Record world : Type :=
    mkworld {
      locals : node -> state;
      net : list packet;
      trace : list client_event
    }.

  (* update the local state at node n *)
  Definition update S n s : node -> state :=
    fun m => if node_eq_dec n m
             then s
             else S m.

  Lemma update_same :
    forall f x v,
      update f x v x = v.
  Proof.
    intros. unfold update.
    break_if; congruence.
  Qed.

  Lemma update_diff :
    forall f x v y,
      x <> y ->
      update f x v y = f y.
  Proof.
    intros. unfold update.
    break_if; congruence.
  Qed.

  Definition packet_eq_dec :
    forall x y : packet, {x = y} + {x <> y}.
  Proof.
    decide equality.
    - apply msg_eq_dec.
    - apply node_eq_dec.
  Qed.

  (* helper for recording external events from a node's I/O *)
  Definition trace_io
    (n : node) (oi: option input) (outs : list output)
    : list client_event :=
    match oi with
     | None => []
     | Some i => [client_in n i]
    end
      ++ List.map (fun o => client_out n o) outs.

  (* intuitive, friendly network semantics *)
  Inductive ideal_step : world -> world -> Prop :=
  | ideal_input :
      forall w i n st' ms outs,
        handle_input n i (locals w n)
          = (st', ms, outs) ->
        ideal_step
          w
          (mkworld
             (update (locals w) n st')
             (ms ++ net w)
             (trace_io n (Some i) outs ++ trace w))
  | ideal_msg :
      forall locals net trace p st' ms outs,
        handle_msg (dest p) (payload p) (locals (dest p))
          = (st', ms, outs) ->
        ideal_step
          (mkworld locals (net ++ [p]) trace)
          (mkworld
             (update locals (dest p) st')
             (ms ++ net)
             (trace_io (dest p) None outs ++ trace)).

  (* remove at most one copy of packet p *)
  Fixpoint remove_one p net :=
    match net with
      | [] => []
      | x :: xs => if packet_eq_dec p x
                   then xs
                   else x :: remove_one p xs
    end.

  (* semantics with reordering and arbitrary delay failures *)
  Inductive shuffle_step : world -> world -> Prop :=
  | shuffle_input :
      forall w i n st' ms outs,
        handle_input n i (locals w n)
          = (st', ms, outs) ->
        shuffle_step
          w
          (mkworld
             (update (locals w) n st')
             (ms ++ net w)
             (trace_io n (Some i) outs ++ trace w))
  | shuffle_msg :
      forall w p st' ms outs,
        In p (net w) ->
        handle_msg (dest p) (payload p) (locals w (dest p))
          = (st', ms, outs) ->
        shuffle_step
          w
          (mkworld
             (update (locals w) (dest p) st')
             (ms ++ remove_one p (net w))
             (trace_io (dest p) None outs ++ trace w)).

  (* what the world looks like at the beginning of time *)
  Definition init_world : world :=
    mkworld init_state [] [].

  (* reflexive transitive closure of a step relation *)
  Inductive star step : world -> world -> Prop :=
  | star_refl :
      forall w,
        star step w w
  | star_trans :
      forall w x y,
        step w x ->
        star step x y ->
        star step w y.

  (* We will usually want to prove that all worlds reachable from the
     initial state are safe, so here's a small helper for making
     specifications a little more convenient. *)
  Definition reachable step (w : world) : Prop :=
    star step init_world w.

  (* alternate reachable definition that "inlines" star *)
  Inductive reachable' step : world -> Prop :=
  | reach_init :
      reachable' step init_world
  | reach_step :
      forall w1 w2,
        reachable' step w1 ->
        step w1 w2 ->
        reachable' step w2.

  (* EXERCISE *)
  Lemma reachable_reachable' :
    forall step w,
      reachable step w <-> reachable' step w.
  Proof.
    (* This one isn't too bad, but don't worry if you need to think on
       it a bit!  It may be useful to try proving helper lemmas if
       you're stuck. *)
  Admitted.
End NetSem.

(* Did we get these right?
   What happens if we screw up?
   Can we ever have "perfect" network semantics? *)
