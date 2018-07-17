(* The interpreter executes a server and a client concurrently,
   with nondeterministic interleaving of [networkE] effects. *)

Generalizable Variable E.
Typeclasses eauto := 6.

Require Import String.
Require Import List.
Import ListNotations.

Require Import Custom.Decidability.

Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Import SumNotations.
Require Import DeepWeb.Free.Monad.Spec.

Require Import DeepWeb.Util.ByteType.

Require Import DeepWeb.Lib.NetworkInterface.

Record conn_info : Type:=
  { conn_id : connection_id;
    conn_in : bytes;
    conn_out : bytes;
    conn_open : bool }.

Record world :=
  { next_connection : connection_id;
    active_conns : list conn_info }.

(* Constructor and setters.*)
Definition new_conn (c0 : connection_id) : conn_info :=
  {| conn_id := c0;
     conn_in := ""%string;
     conn_out := ""%string;
     conn_open := true |}.

Definition set_in (s0 : bytes) (conn : conn_info) : conn_info :=
  {| conn_id := conn_id conn;
     conn_in := s0;
     conn_out := conn_out conn;
     conn_open := conn_open conn;
  |}.

Definition set_out (s0 : bytes) (conn : conn_info) : conn_info :=
  {| conn_id := conn_id conn;
     conn_in := conn_in conn;
     conn_out := s0;
     conn_open := conn_open conn;
  |}.

Definition set_close (conn : conn_info) : conn_info :=
  {| conn_id := conn_id conn;
     conn_in := conn_in conn;
     conn_out := conn_out conn;
     conn_open := false;
  |}.

Definition make_new_conn (w : world)
  : world * connection_id :=
  let n := next_connection w in
  let conns := new_conn n :: active_conns w in
  let w := {| next_connection := n+1;
              active_conns := conns |} in
  (w, n).

Fixpoint get_conn' (c : connection_id) (conns : list conn_info)
  : option conn_info :=
  match conns with
  | [] => None
  | conn :: conns' =>
    if conn_id conn = c ? then
      Some conn
    else
      get_conn' c conns'
  end.

Definition new_world : world :=
  {| next_connection := 0;
     active_conns := [] |}.

Definition get_conn (c : connection_id) (w : world)
  : option conn_info :=
  get_conn' c (active_conns w).

Fixpoint set_conn' (conn : conn_info) (conns : list conn_info)
  : list conn_info :=
  match conns with
  | [] => []
  | conn' :: conns' =>
    if conn_id conn = conn_id conn' ? then
      conn :: conns'
    else
      conn' :: set_conn' conn conns'
  end.

Definition set_conn (conn : conn_info) (w : world)
  : world :=
  let conns' := set_conn' conn (active_conns w) in
  {| next_connection := next_connection w;
     active_conns := conns' |}.

Inductive interactE : Type -> Type :=
| Interact : forall X, (world -> world * X) -> interactE X.

(* [i_] for "interpret" *)
CoFixpoint i_recv {E R} `{interactE -< E} `{nondetE -< E}
           (c : connection_id) (ret_ : string -> M E R) :
  M E R :=
  x <- ^ Interact _ (fun w =>
    match get_conn c w with
    | None => (w, None)  (* must not happen *)
    | Some cinfo =>
      match conn_in cinfo with
      | "" => (w, None)  (* block on empty buffer *)
      | String b bs => (set_conn (set_in bs cinfo) w, Some b)
      end
    end) ;;
  match x with
  | None => i_recv c ret_
  | Some b =>
    or (i_recv c (fun bs => ret_ (String b bs)))
       (ret_ (String b ""))
  end.

CoFixpoint i_send {E} `{interactE -< E} `{nondetE -< E}
           (c : connection_id) (msg : string) : M E unit :=
  match msg with
  | "" => ret tt
  | String b msg =>
    ^ Interact _ (fun w =>
      match get_conn c w with
      | None => (w, tt)  (* must not happen *)
      | Some cinfo =>
        let out := conn_out cinfo ++ String b "" in
        (set_conn (set_out out cinfo) w, tt)
      end) ;;
    i_send c msg
  end.

Definition i_network {X E}
           `{interactE -< E}
           `{nondetE -< E}
           `{discardE -< E}
           (e : networkE X) :
  M E X :=
  match e with
  | Listen _ => ret tt
  | Accept _ => ^ Interact _ make_new_conn
  | Recv c => i_recv c (fun s => ret (Some s))
  | Send c msg => i_send c msg

  | ConnectTo _
  | Shutdown _ => discard "not implemented"
  end.
