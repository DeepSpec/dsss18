Generalizable Variable E.

From DeepWeb.Free.Monad
     Require Import Free Common Verif.

Require Import Custom.Decidability.

Require Import DeepWeb.Spec.ServerDefs.

Require Import DeepWeb.Lib.Socket.

Require Import String.
Require Import ZArith.
Require Import List.
Import ListNotations.

Import SocketAPI.

From Custom Require Monad.
Import MonadNotations.

Inductive connection_state : Type :=
  RECVING | SENDING | DONE | DELETED.

Record connection : Type :=
  { 
    conn_id : connection_id;
    conn_request : string;
    conn_response : string;
    conn_response_bytes_sent : Z;
    conn_state : connection_state
  }.

Definition upd_conn_request (conn : connection) (request : string)
  : connection :=
  {|
    conn_id := conn_id conn;
    conn_request := request;
    conn_response := conn_response conn;
    conn_response_bytes_sent := conn_response_bytes_sent conn;
    conn_state := conn_state conn
  |}.


Definition upd_conn_response (conn : connection) (response : string)
  : connection :=
  {|
    conn_id := conn_id conn;
    conn_request := conn_request conn;
    conn_response := response;
    conn_response_bytes_sent := conn_response_bytes_sent conn;
    conn_state := conn_state conn
  |}.

Definition upd_conn_response_bytes_sent
           (conn : connection) (response_bytes_sent : Z)
  : connection :=
  {|
    conn_id := conn_id conn;
    conn_request := conn_request conn;
    conn_response := conn_response conn;
    conn_response_bytes_sent := response_bytes_sent;
    conn_state := conn_state conn
  |}.

Definition upd_conn_state (conn : connection) (state : connection_state)
  : connection :=
  {|
    conn_id := conn_id conn;
    conn_request := conn_request conn;
    conn_response := conn_response conn;
    conn_response_bytes_sent := conn_response_bytes_sent conn;
    conn_state := state
  |}.

CoFixpoint while {E : Type -> Type} {T : Type}
           (cond : T -> bool)
           (body : T -> M E T) : T -> M E T :=
  fun t =>
    match cond t with
    | true =>
      r <- body t ;;
      while cond body r
    | false => ret t
    end.

Lemma while_loop_unfold :
  forall {E T} (cond : T -> bool) (P : T -> M E T) (t : T), 
    while cond P t = if (cond t) then
                       (r <- P t ;; while cond P r)
                     else ret t.
Proof.
  intros.
  rewrite matchM.
  simpl.
  destruct (cond t);
    auto.
  match goal with
  | [|- ?LHS = ?RHS] =>
    replace LHS with (idM RHS);
      auto
  end.
  rewrite <- matchM.
  auto.
Qed.

Definition accept_connection (addr : endpoint_id):
  M SocketM (option connection) :=
  or (client_conn <- accept addr ;;
      or (* possible internal malloc failure *)
        (ret (Some {| conn_id := client_conn ;
                      conn_request := "";
                      conn_response := "";
                      conn_response_bytes_sent := 0;
                      conn_state := RECVING |}))
        (r <- shutdown client_conn ;;
         ret None))
     (ret None).

Instance dec_eq_connection_state {st1 st2 : connection_state}
  : Dec (st1 = st2).
Proof. dec_eq. Defined.

Class HasConnectionState (A : Type) :=
  { get_conn_state : A -> connection_state }.

Instance connection_has_connection_state : HasConnectionState connection.
Proof. constructor. intros. apply conn_state. assumption. Defined.

Definition has_conn_state {A} `{HasConnectionState A}
           (st : connection_state) (conn : A) : bool :=
  ssrbool.is_left
    (@dec (st = get_conn_state conn) _).

Parameter is_complete : string -> bool.

Definition conn_read 
           (conn: connection) (last_full_msg : string)
  : M SocketM (connection * string) :=
  or (r <- recv (conn_id conn) ;;
      match r with
      | None => ret (upd_conn_state conn DELETED, last_full_msg)
      | Some msg =>
        let msg' := (conn_request conn ++ msg)%string in
        if is_complete msg' then
          let conn' :=  {| conn_id := conn_id conn ;
                           conn_request := msg';
                           conn_response := last_full_msg;
                           conn_response_bytes_sent := 0;
                           conn_state := SENDING
                        |}
          in ret (conn', msg')
        else
          let conn' := {| conn_id := conn_id conn ;
                          conn_request := msg';
                          conn_response := conn_response conn;
                          conn_response_bytes_sent := conn_response_bytes_sent conn;
                          conn_state := RECVING
                       |}
          in ret (conn', last_full_msg)
      end
     )
     (ret (conn, last_full_msg)).

Definition conn_write 
           (conn: connection) : M SocketM connection :=
  or (let num_bytes_sent := Z.to_nat (conn_response_bytes_sent conn) in
      r <- send_any_prefix
            (conn_id conn)
            (substring num_bytes_sent
                       (String.length (conn_response conn) - num_bytes_sent)
                       (conn_response conn)) ;;
      if (String.length (conn_response conn) <? r)%nat then fail "dead code"
      else
        let num_bytes_sent := conn_response_bytes_sent conn + Z.of_nat r in
        if (num_bytes_sent =? Z.of_nat (String.length (conn_response conn))) then
          ret {| conn_id := conn_id conn;
                 conn_request := "";
                 conn_response := "";
                 conn_response_bytes_sent := 0;
                 conn_state := RECVING
              |}
        else 
          ret {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := num_bytes_sent;
                 conn_state := conn_state conn
              |}
     )
     (ret (upd_conn_state conn DELETED)).

Definition replace_when {A : Type} (f : A -> bool) (new : A) (l : list A) :=
  List.fold_right
    (fun a tail => 
       if f a then
         new :: tail
       else
         a :: tail
    )
    [] l.

Definition process_conn
           (conn: connection) (last_full_msg : string)
  : M SocketM (connection * string) :=
  match conn_state conn with
  | RECVING => conn_read conn last_full_msg
  | SENDING =>
    conn' <- conn_write conn ;;
    ret (conn', last_full_msg)
  | _ => ret (conn, last_full_msg)
  end.

Definition select_loop_body
           (server_addr : endpoint_id)
           (server_st : list connection * string)
  : M SocketM (bool * (list connection * string)) :=
  let '(connections, last_full_msg) := server_st in
  or
    (or
       (r <- accept_connection server_addr ;;
          match r with
          | Some conn => ret (true, (conn :: connections, last_full_msg))
          | None =>
            ret (true, (connections, last_full_msg))
          end)
       (let waiting_to_recv := filter (has_conn_state RECVING) connections in
        let waiting_to_send := filter (has_conn_state SENDING) connections in
        conn <- choose (waiting_to_recv ++ waiting_to_send) ;;
        new_st <- process_conn conn last_full_msg ;;
        let '(conn', last_full_msg') := new_st in
        let connections' :=
            replace_when
              (fun c =>
                 if (has_conn_state RECVING c
                     || has_conn_state SENDING c)%bool then 
                   (conn_id c =? conn_id conn')%nat
                 else
                   false 
              )
              conn'
              connections in
        ret (true, (connections', last_full_msg'))
       )
    )
    (ret (false, (connections, last_full_msg))).

Definition select_loop (server_addr : endpoint_id)
  : (bool * (list connection * string))
    -> M SocketM (bool * (list connection * string)) :=
  while fst
        (fun '(_, server_st) => select_loop_body server_addr server_st).