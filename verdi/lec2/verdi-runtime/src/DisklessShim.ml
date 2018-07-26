open Printf
open Util

module type ARRANGEMENT = sig
  type name
  type state
  type input
  type output
  type msg
  type client_id
  type res = (output list * state) * ((name * msg) list)
  val system_name : string
  val init : name -> state
  val reboot : state -> state
  val handle_input : name -> input -> state -> res
  val handle_msg : name -> name -> msg -> state -> res
  val handle_timeout : name -> state -> res
  val set_timeout : name -> state -> float
  val deserialize_msg : bytes -> msg
  val serialize_msg : msg -> bytes
  val deserialize_input : bytes -> (client_id * input) option
  val serialize_output : output -> client_id * bytes
  val debug : bool
  val debug_input : state -> input -> unit
  val debug_recv : state -> (name * msg) -> unit
  val debug_send : state -> (name * msg) -> unit
  val debug_timeout : state -> unit
  val string_of_client_id : client_id -> string
end

module Shim (A: ARRANGEMENT) = struct
  type cfg =
      { cluster : (A.name * (string * int)) list
      ; me : A.name
      ; port : int
      }

  type env =
      { cfg : cfg
      ; nodes_fd : Unix.file_descr
      ; clients_fd : Unix.file_descr
      ; nodes : (A.name * Unix.sockaddr) list
      ; client_read_fds : (Unix.file_descr, Unix.sockaddr) Hashtbl.t
      ; client_write_fds : (A.client_id, Unix.file_descr) Hashtbl.t
      ; client_read_bufs : (Unix.file_descr, int * bytes) Hashtbl.t
      }

  (* Translate node name to UDP socket address. *)
  let denote_node (env : env) (name : A.name) : Unix.sockaddr =
    List.assoc name env.nodes

  (* Translate UDP socket address to node name. *)
  let undenote_node (env : env) (addr : Unix.sockaddr) : A.name =
    let flip = function (x, y) -> (y, x) in
    List.assoc addr (List.map flip env.nodes)

  (* Translate client id to TCP socket address *)
  let denote_client (env : env) (c : A.client_id) : Unix.file_descr =
    Hashtbl.find env.client_write_fds c

  (* Gets state from the most recent snapshot, or the initial state from the arrangement. *)
  let get_initial_state (cfg : cfg) : A.state =
      A.init (cfg.me)

  (* Load state from disk, initialize environment, and start server. *)
  let setup (cfg : cfg) : (env * A.state) =
    Random.self_init ();
    let addressify (name, (host, port)) =
      let entry = Unix.gethostbyname host in
      (name, Unix.ADDR_INET (entry.Unix.h_addr_list.(0), port))
    in
    let initial_state = get_initial_state cfg in
    let env =
      { cfg = cfg
      ; nodes_fd = Unix.socket Unix.PF_INET Unix.SOCK_DGRAM 0
      ; clients_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0
      ; nodes = List.map addressify cfg.cluster
      ; client_read_fds = Hashtbl.create 17
      ; client_write_fds = Hashtbl.create 17
      ; client_read_bufs = Hashtbl.create 17
      }
    in
    let (node_addr, node_port) =
      match List.assoc cfg.me env.nodes with
      | Unix.ADDR_INET (addr, port) -> (addr, port)
      | _ -> assert false in
    Unix.setsockopt env.clients_fd Unix.SO_REUSEADDR true;
    Unix.setsockopt env.nodes_fd Unix.SO_REUSEADDR true;
    Unix.bind env.nodes_fd (Unix.ADDR_INET (node_addr, node_port));
    Unix.bind env.clients_fd (Unix.ADDR_INET (node_addr, cfg.port));
    Unix.listen env.clients_fd 8;
    Unix.set_nonblock env.clients_fd;
    (env, initial_state)

  let disconnect_client env fd reason =
    let addr = Hashtbl.find env.client_read_fds fd in
    Hashtbl.remove env.client_read_fds fd;
    Unix.close fd;
    if A.debug then begin
      printf "client %s disconnected: %s" (string_of_sockaddr addr) reason;
      print_newline ()
    end

  let sendto sock buf addr =
    try
      ignore (Unix.sendto sock buf 0 (Bytes.length buf) [] addr)
    with Unix.Unix_error (err, fn, arg) ->
      eprintf "error in sendto: %s, dropping message" (Unix.error_message err);
      prerr_newline ()

  let send env ((nm : A.name), (msg : A.msg)) =
    sendto env.nodes_fd (A.serialize_msg msg) (denote_node env nm)

  let output env o =
    let (c, out) = A.serialize_output o in
    try send_chunk (denote_client env c) out
    with 
    | Not_found ->
      eprintf "output: failed to find socket for client %s" (A.string_of_client_id c);
      prerr_newline ()
    | Disconnect s ->
      disconnect_client env (denote_client env c)
        (sprintf "output: failed send to client %s: %s" (A.string_of_client_id c) s)
    | Unix.Unix_error (err, fn, _) ->
       disconnect_client env (denote_client env c)
         (sprintf "output: error %s" (Unix.error_message err))

  let respond env ((os, s), ps) =
    List.iter (output env) os;
    List.iter (fun p -> if A.debug then A.debug_send s p; send env p) ps;
    s

  let new_client_conn env =
    let (client_fd, client_addr) = Unix.accept env.clients_fd in
    Unix.set_nonblock client_fd;
    Hashtbl.add env.client_read_fds client_fd client_addr;
    if A.debug then begin
      printf "client %s connected" (string_of_sockaddr client_addr);
      print_newline ()
      end

  let record_client_id env client_id fd =
    try
      let fd' = Hashtbl.find env.client_write_fds client_id in
      if fd <> fd' then
        (printf "client %s connected on new socket" (A.string_of_client_id client_id);
         Hashtbl.replace env.client_write_fds client_id fd)
      else ()
    with
    | Not_found -> Hashtbl.add env.client_write_fds client_id fd


  let input_step (fd : Unix.file_descr) (env : env) (state : A.state) =
    try
      match recv_buf_chunk fd env.client_read_bufs with
      | None ->
	state
      | Some buf ->
	match A.deserialize_input buf with
	| Some (client_id, inp) ->
     record_client_id env client_id fd;
     let state' = respond env (A.handle_input env.cfg.me inp state) in
     if A.debug then A.debug_input state' inp;
     state'
	| None ->
	  disconnect_client env fd "input deserialization failed";
	  state
    with
    | Disconnect s ->
      disconnect_client env fd s;
      state
    | Unix.Unix_error (err, fn, _) ->
      disconnect_client env fd (sprintf "error in %s: %s" fn (Unix.error_message err));
      state

  let msg_step (env : env) (state : A.state) : A.state =
    let len = 65536 in
    let buf = Bytes.make len '\x00' in
    let (_, from) = Unix.recvfrom env.nodes_fd buf 0 len [] in
    let (src, msg) = (undenote_node env from, A.deserialize_msg buf) in
    let state' = respond env (A.handle_msg env.cfg.me src msg state) in
    if A.debug then A.debug_recv state' (src, msg);
    state'

  let timeout_step (env : env) (state : A.state) : A.state =
    if A.debug then A.debug_timeout state;
    let x = A.handle_timeout env.cfg.me state in
    respond env x

  let process_fd env state fd : A.state =
    if fd = env.clients_fd then
      (new_client_conn env; state)
    else if fd = env.nodes_fd then
      msg_step env state
    else
      input_step fd env state

  let rec eloop (env : env) (state : A.state) : unit =
    let all_fds = env.nodes_fd :: env.clients_fd :: keys_of_hashtbl env.client_read_fds in
    let (ready_fds, _, _) = select_unintr all_fds [] [] (A.set_timeout env.cfg.me state) in
    let state' =
      match ready_fds with
      | [] -> timeout_step env state
      | _ -> List.fold_left (process_fd env) state ready_fds in
    eloop env state'

  let main (cfg : cfg) : unit =
    printf "unordered shim running setup for %s" A.system_name;
    print_newline ();
    let (env, initial_state) = setup cfg in
    print_endline "unordered shim ready for action";
    eloop env initial_state
end
