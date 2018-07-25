(*! Section BaseTest *)

Generalizable Variable E.

From DeepWeb.Free.Monad
     Require Import Free Common Verif.

From QuickChick Require Import Decidability.

From Custom Require Import List.
Import ListNotations.

From DeepWeb Require Import
     Lib.NetworkInterface
     Lib.NetworkAdapter
     Lib.SimpleSpec
     Lib.Socket
     Spec.ServerDefs.

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

Definition accept_connection (addr : endpoint_id):
  M socketE (option connection) :=
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

(* Wait for a message from connection [conn].
   [recv] can return a partial message, in which case we store the
   bytes we received to try receiving more in a late. iteration. *)
Definition conn_read (buffer_size : Z)
           (conn: connection) (last_full_msg : string)
  : M socketE (connection * string) :=
  let req_len := Z.of_nat (String.length (conn_request conn)) in
  or (r <- recv (conn_id conn) (Z.to_nat (buffer_size - req_len)) ;;
      match r with
        (* If [recv] returns [r = None], the connection was closed. *)
      | None => ret (upd_conn_state conn DELETED, last_full_msg)
        (* Otherwise, we append the received bytes to the other
           bytes previously received on that connection. *)
      | Some msg =>
        let msg_len := Z.of_nat (String.length msg) in
        let msg' := (*!*) (conn_request conn ++ msg)%string
                    (*!! Respond too quickly *)
                    (*! "BAD" *) in
        if is_complete buffer_size msg' then
          (* If the client's message is complete (i.e., of
             length [buffer_size]) we prepare to respond with
             [last_full_msg] and store the [msg'] for the next
             exchange. *)
          let conn' :=  {| conn_id := conn_id conn ;
                           conn_request := msg';
                           conn_response := last_full_msg;
                           conn_response_bytes_sent := 0;
                           conn_state := SENDING
                        |}
          in ret (conn', msg')
        else
          (* Otherwise we wait for more input from this connection. *)
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

(* Send a response on connection [conn].
   [send_any_prefix] (representing the [send] POSIX syscall)
   may send only a prefix of the message (it returns the length [r]
   of that prefix), in which case we will retry sending the rest
   in a later iteration. *)
Definition conn_write (conn: connection) : M socketE connection :=
  or (let num_bytes_sent := Z.to_nat (conn_response_bytes_sent conn) in
      r <- send_any_prefix
            (conn_id conn)
            (substring num_bytes_sent
                       (String.length (conn_response conn) - num_bytes_sent)
                       (conn_response conn)) ;;
      if (String.length (conn_response conn) <? r)%nat
      then
        (* The sent prefix [r] must be no longer than the actual
           message to send. *)
        fail "dead code"
      else
        let num_bytes_sent := conn_response_bytes_sent conn + Z.of_nat r in
        if (num_bytes_sent =? Z.of_nat (String.length (conn_response conn))) then
          (* The whole message got sent, we start waiting for another
             message on this connection. *)
          ret {| conn_id := conn_id conn;
                 conn_request := "";
                 conn_response := "";
                 conn_response_bytes_sent := 0;
                 conn_state := RECVING
              |}
        else
          (* Only part of the message was sent, retry. *)
          ret {| conn_id := conn_id conn;
                 conn_request := conn_request conn;
                 conn_response := conn_response conn;
                 conn_response_bytes_sent := num_bytes_sent;
                 conn_state := conn_state conn
              |}
     )
     (* Internal errors can happen, then we discard the connection. *)
     (ret (upd_conn_state conn DELETED)).

(* Call [conn_read] or [conn_write] depending on the state
   of the connection. *)
Definition process_conn 
             (buffer_size : Z) (conn: connection) (last_full_msg : string)
          : M socketE (connection * string) :=
  match conn_state conn with
  | RECVING => conn_read  buffer_size conn last_full_msg
  | SENDING =>
    conn' <- conn_write conn ;;
    ret (conn', last_full_msg)
  | _ => ret (conn, last_full_msg)
  end.

(* Choose one connection to run [process_conn] with. *)
(* The returned [bool] is always true and is just waiting to
   be removed in the next refactoring. *)
Definition select_loop_body
           (server_addr : endpoint_id)
           (buffer_size : Z)
           (server_st : list connection * string)
         : M socketE (bool * (list connection * string)) :=
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
                  || has_conn_state SENDING c)%bool
              then (conn_id c = conn_id conn' ?)
              else false)
           conn'
           connections in
     ret (true, (connections', last_full_msg'))
    ).

Definition select_loop 
                (server_addr : endpoint_id) (buffer_size : Z)
              : (bool * (list connection * string))
                  -> M socketE (bool * (list connection * string)) :=
  while fst (* The [while] condition is always true. *)
        (fun '(_, server_st) =>
           select_loop_body server_addr buffer_size server_st).

Definition server_
           (endpoint : endpoint_id)
           (buffer_size : Z)
           (ini_msg : string) :=
  (or (listen endpoint ;;
       select_loop endpoint buffer_size (true, ([], ini_msg)) ;;
       ret tt)
      (* The server can just fail to start during initialization. *)
      (ret tt) ).

Definition server := server_ SERVER_PORT BUFFER_SIZE INIT_MSG.

(* Alternative instantiation with smaller constants for testing,
   and using a simplified version of server effects.
 *)

Module Def := DeepWeb.Lib.Util.TestDefault.

Definition test_server : ServerM unit := simplify_network
    (server_
       dummy_endpoint
       (Z.of_nat Def.buffer_size)
       Def.init_message).
