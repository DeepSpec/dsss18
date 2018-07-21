(*! Section BaseTest *)

Generalizable Variable E.

From DeepWeb.Free.Monad
     Require Import Free Common Verif.

From QuickChick Require Import Decidability.

From Custom Require Import List.
Import ListNotations.

Require Import DeepWeb.Spec.ServerDefs.
Require Import DeepWeb.Lib.Socket.
Require Import DeepWeb.Lib.NetworkInterface.

Require Import String.
Require Import ZArith.

Import SocketAPI.

From Custom Require Monad.
Import MonadNotations.

(** * Low-level "C-Like" Specification of the Swap Server *)

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

(* BCP: Belongs in /Lib? *)
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

(* BCP: Belongs in /Lib? *)
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
  M SocketE (option connection) :=
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

Definition is_complete (buffer_size : Z) (msg : string) :=
  Z.eqb (Z.of_nat (String.length msg)) buffer_size.

Definition conn_read (buffer_size : Z)
           (conn: connection) (last_full_msg : string)
  : M SocketE (connection * string) :=
  let req_len := Z.of_nat (String.length (conn_request conn)) in
  or (r <- recv (conn_id conn) (Z.to_nat (buffer_size - req_len)) ;;
      match r with
      | None => ret (upd_conn_state conn DELETED, last_full_msg)
      | Some msg =>
        let msg_len := Z.of_nat (String.length msg) in
        let msg' := (*!*) (conn_request conn ++ msg)%string (*! "BAD" *) in
        if is_complete buffer_size msg' then
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
           (conn: connection) : M SocketE connection :=
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

Definition process_conn (buffer_size : Z)
           (conn: connection) (last_full_msg : string)
  : M SocketE (connection * string) :=
  match conn_state conn with
  | RECVING => conn_read  buffer_size conn last_full_msg
  | SENDING =>
    conn' <- conn_write conn ;;
    ret (conn', last_full_msg)
  | _ => ret (conn, last_full_msg)
  end.

Definition select_loop_body
           (server_addr : endpoint_id)
           (buffer_size : Z)
           (server_st : list connection * string)
  : M SocketE (bool * (list connection * string)) :=
  let '(connections, last_full_msg) := server_st in
  or
    (r <- accept_connection server_addr ;;
       match r with
       | Some conn => ret (true, (conn :: connections, last_full_msg))
       | None =>
         ret (true, (connections, last_full_msg))
       end)
    (let waiting_to_recv := filter (has_conn_state RECVING) connections in
     let waiting_to_send := filter (has_conn_state SENDING) connections in
     conn <- choose (waiting_to_recv ++ waiting_to_send) ;;
          new_st <- process_conn buffer_size conn last_full_msg ;;
          let '(conn', last_full_msg') := new_st in
          let connections' :=
              replace_when
                (fun c =>
                   if (has_conn_state RECVING c
                       || has_conn_state SENDING c)%bool then 
                     (conn_id c = conn_id conn' ?)
                   else
                     false 
                )
                conn'
                connections in
          ret (true, (connections', last_full_msg'))
    ).

Definition select_loop (server_addr : endpoint_id) (buffer_size : Z)
  : (bool * (list connection * string))
    -> M SocketE (bool * (list connection * string)) :=
  while fst
        (fun '(_, server_st) =>
           select_loop_body server_addr buffer_size server_st).

(* TODO: Don't do [Z.to_nat port], just use the port as a binary constant. *)
Definition server_
           (endpoint : endpoint_id)
           (buffer_size : Z)
           (ini_msg : string) :=
  (or (listen endpoint ;;
       select_loop endpoint buffer_size (true, ([], ini_msg))
       ;; ret tt)
      (ret tt) ).

Definition server := server_ SERVER_PORT BUFFER_SIZE INIT_MSG.

(* Alternative instantiation with smaller constants for testing. *)

Module Def := DeepWeb.Lib.Util.TestDefault.

Definition test_server := server_
                            dummy_endpoint
                            (Z.of_nat Def.buffer_size)
                            Def.init_message.
