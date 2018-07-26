open Printf
open Util
open Daemon

module type ARRANGEMENT = sig
  type name
  type state
  type input
  type output
  type msg
  type client_id
  type res = (output list * state) * ((name * msg) list)
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float option
  val system_name : string
  val init : name -> state
  val handle_input : name -> input -> state -> res
  val handle_msg : name -> name -> msg -> state -> res
  val deserialize_msg : bytes -> msg
  val serialize_msg : msg -> bytes
  val deserialize_input : bytes -> client_id -> input option
  val serialize_output : output -> client_id * bytes
  val debug : bool
  val debug_input : state -> input -> unit
  val debug_recv_msg : state -> (name * msg) -> unit
  val debug_send_msg : state -> (name * msg) -> unit
  val create_client_id : unit -> client_id
  val string_of_client_id : client_id -> string
  val timeout_tasks : (task_handler * timeout_setter) list
end

module Shim (A: ARRANGEMENT) = struct
  type cfg =
      { cluster : (A.name * (string * int)) list
      ; me : A.name
      ; port : int
      }

  type env =
      { me : A.name
      ; nodes_fd : Unix.file_descr
      ; clients_fd : Unix.file_descr
      ; nodes : (A.name * Unix.sockaddr) list
      ; client_read_fds : (Unix.file_descr, A.client_id) Hashtbl.t
      ; client_write_fds : (A.client_id, Unix.file_descr) Hashtbl.t
      ; tasks : (Unix.file_descr, (env, A.state) task) Hashtbl.t
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

  (* Translate TCP socket address to client id *)
  let undenote_client (env : env) (fd : Unix.file_descr) : A.client_id =
    Hashtbl.find env.client_read_fds fd

  (* Gets initial state from the arrangement *)
  let get_initial_state (cfg : cfg) : A.state =
    A.init cfg.me

  (* Initialize environment *)
  let setup (cfg : cfg) : (env * A.state) =
    let addressify (name, (hostname, port)) =
      let entry = Unix.gethostbyname hostname in
      (name, Unix.ADDR_INET (entry.Unix.h_addr_list.(0), port))
    in
    Random.self_init ();
    let initial_state = get_initial_state cfg in
    let env =
      { me = cfg.me
      ; nodes_fd = Unix.socket Unix.PF_INET Unix.SOCK_DGRAM 0
      ; clients_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0
      ; nodes = List.map addressify cfg.cluster
      ; client_read_fds = Hashtbl.create 17
      ; client_write_fds = Hashtbl.create 17
      ; tasks = Hashtbl.create 17
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

  (* throws nothing *)
  let output env o =
    let (c, out) = A.serialize_output o in
    try send_chunk (denote_client env c) out
    with
    | Not_found ->
      eprintf "output: failed to find socket for client %s" (A.string_of_client_id c);
      prerr_newline ()
    | Disconnect s ->
      eprintf "output: failed send to client %s: %s" (A.string_of_client_id c) s;
      prerr_newline ();
      schedule_finalize_task (Hashtbl.find env.tasks (denote_client env c)) 0.5
    | Unix.Unix_error (err, fn, _) ->
      eprintf "output: error %s" (Unix.error_message err);
      prerr_newline ();
      schedule_finalize_task (Hashtbl.find env.tasks (denote_client env c)) 0.5

  (* throws Unix_error *)
  let new_client_conn env =
    let (client_fd, client_addr) = Unix.accept env.clients_fd in
    let c = A.create_client_id () in
    Unix.set_nonblock client_fd;
    Hashtbl.replace env.client_read_fds client_fd c;
    Hashtbl.replace env.client_write_fds c client_fd;
    if A.debug then begin
      printf "[%s] client %s connected on %s" (timestamp ()) (A.string_of_client_id c) (string_of_sockaddr client_addr);
      print_newline ()
    end;
    client_fd

  let sendto sock buf addr =
    try
      ignore (Unix.sendto sock buf 0 (Bytes.length buf) [] addr)
    with Unix.Unix_error (err, fn, arg) ->
      eprintf "error in sendto: %s, dropping message" (Unix.error_message err);
      prerr_newline ()

  let send env ((nm : A.name), (msg : A.msg)) =
    sendto env.nodes_fd (A.serialize_msg msg) (denote_node env nm)

  let respond env ((os, s), ps) =
    List.iter (output env) os;
    List.iter (fun p -> if A.debug then A.debug_send_msg s p; send env p) ps;
    s

  (* throws Disconnect, Unix_error *)
  let input_step (env : env) (fd : Unix.file_descr) (state : A.state) =
    match recv_buf_chunk fd env.client_read_bufs with
    | None ->
      state
    | Some buf ->
      let c = undenote_client env fd in
      match A.deserialize_input buf c with
      | Some inp ->
	let state' = respond env (A.handle_input env.me inp state) in
	if A.debug then A.debug_input state' inp;
	state'
      | None ->
	raise (Disconnect (sprintf "input_step: could not deserialize %s" (Bytes.to_string buf)))

  (* throws Unix_error *)
  let msg_step (env : env) (fd : Unix.file_descr) (state : A.state) : A.state =
    let len = 65536 in
    let buf = Bytes.make len '\x00' in
    let (_, from) = Unix.recvfrom fd buf 0 len [] in
    let (src, msg) = (undenote_node env from, A.deserialize_msg buf) in
    let state' = respond env (A.handle_msg env.me src msg state) in
    if A.debug then A.debug_recv_msg state' (src, msg);
    state'

  let node_read_task env =
    { fd = env.nodes_fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let state' = msg_step env t.fd state in
	    (false, [], state')
	  with Unix.Unix_error (err, fn, _) ->
	    eprintf "error receiving message from node in %s: %s" fn (Unix.error_message err);
	    prerr_newline ();
	    (false, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize = (fun t env state -> Unix.close t.fd; state)
    }

  let client_read_task fd =
    { fd = fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let state' = input_step env t.fd state in
	    (false, [], state')
	  with 
	  | Disconnect s ->
	    eprintf "connection error for client %s: %s" (A.string_of_client_id (undenote_client env t.fd)) s;
	    prerr_newline ();
	    (true, [], state)
	  | Unix.Unix_error (err, fn, _) ->
	    eprintf "error for client %s: %s" (A.string_of_client_id (undenote_client env t.fd)) (Unix.error_message err);
	    prerr_newline ();
	    (true, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize =
	(fun t env state ->
	  let client_fd = t.fd in
	  let c = undenote_client env client_fd in
	  if A.debug then begin
	    printf "[%s] closing connection to client %s" (timestamp ()) (A.string_of_client_id c);
	    print_newline ();
	  end;
	  Hashtbl.remove env.client_read_fds client_fd;
	  Hashtbl.remove env.client_write_fds c;
	  Hashtbl.remove env.client_read_bufs client_fd;
	  Unix.close client_fd;
	  state)
    }

  let client_connections_task env =
    { fd = env.clients_fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let client_fd = new_client_conn env in
	    (false, [client_read_task client_fd], state)
	  with Unix.Unix_error (err, fn, _) ->
	    eprintf "incoming client connection error in %s: %s" fn (Unix.error_message err);
	    prerr_newline ();
	    (false, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize = (fun t env state -> Unix.close t.fd; state)
    }

  let timeout_task env handler setter time =
    { fd = Unix.dup env.clients_fd
    ; select_on = false
    ; wake_time = Some time
    ; process_read = (fun t env state -> (false, [], state))
    ; process_wake =
	(fun t env state ->
	  let state' = respond env (handler env.me state) in
	  match setter env.me state' with
	  | None -> (true, [], state')
	  | Some time' -> begin
	    t.wake_time <- Some time';
	    (false, [], state')
	  end)
    ; finalize = (fun t env state -> Unix.close t.fd; state)
    }

  let main (cfg : cfg) : unit =
    printf "daemonized unordered shim running setup for %s" A.system_name;
    print_newline ();
    let (env, initial_state) = setup cfg in
    let t_nd_conn = node_read_task env in
    let t_cl_conn = client_connections_task env in
    Hashtbl.add env.tasks t_nd_conn.fd t_nd_conn;
    Hashtbl.add env.tasks t_cl_conn.fd t_cl_conn;
    List.iter (fun (handler, setter) ->
      match setter env.me initial_state with
      | None -> ()
      | Some time ->
	let t = timeout_task env handler setter time in
	Hashtbl.add env.tasks t.fd t)
      A.timeout_tasks;
    printf "daemonized unordered shim ready for %s" A.system_name;
    print_newline ();
    eloop 2.0 (Unix.gettimeofday ()) env.tasks env initial_state
end
