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
  val serialize_name : name -> bytes
  val deserialize_name : bytes -> name option
  val init : name -> state
  val handle_input : name -> input -> state -> res
  val handle_msg : name -> name -> msg -> state -> res
  val deserialize_msg : bytes -> msg
  val serialize_msg : msg -> bytes
  val deserialize_input : bytes -> client_id -> input option
  val serialize_output : output -> client_id * bytes
  val fail_msg : msg option
  val new_msg : msg option
  val debug : bool
  val debug_input : state -> input -> unit
  val debug_recv : state -> (name * msg) -> unit
  val debug_send : state -> (name * msg) -> unit
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
      { cluster : (A.name, string * int) Hashtbl.t
      ; me : A.name
      ; nodes_fd : Unix.file_descr
      ; clients_fd : Unix.file_descr
      ; node_read_fds : (Unix.file_descr, A.name) Hashtbl.t
      ; node_fds_read : (A.name, Unix.file_descr) Hashtbl.t
      ; node_write_fds : (A.name, Unix.file_descr) Hashtbl.t
      ; client_read_fds : (Unix.file_descr, A.client_id) Hashtbl.t
      ; client_write_fds : (A.client_id, Unix.file_descr) Hashtbl.t
      ; tasks : (Unix.file_descr, (env, A.state) task) Hashtbl.t
      ; read_bufs : (Unix.file_descr, int * bytes) Hashtbl.t
      }

  let sock_of_name (env : env) (node_name : A.name) : string * int =
    Hashtbl.find env.cluster node_name

  (* Translate node name to TCP socket address *)
  let denote_node (env : env) (node_name : A.name) : Unix.file_descr =
    Hashtbl.find env.node_write_fds node_name

  (* Translate TCP socket address to node name *)
  let undenote_node (env : env) (fd : Unix.file_descr) : A.name =
    Hashtbl.find env.node_read_fds fd

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
    Random.self_init ();
    let initial_state = get_initial_state cfg in
    let env =
      { cluster = Hashtbl.create (List.length cfg.cluster)
      ; me = cfg.me
      ; nodes_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0
      ; clients_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0
      ; node_read_fds = Hashtbl.create 17
      ; node_fds_read = Hashtbl.create 17
      ; node_write_fds = Hashtbl.create 17
      ; client_read_fds = Hashtbl.create 17
      ; client_write_fds = Hashtbl.create 17
      ; tasks = Hashtbl.create 17
      ; read_bufs = Hashtbl.create 17
      } in
    List.iter (fun (n, s) -> Hashtbl.add env.cluster n s) cfg.cluster;
    let (hostname, port) = Hashtbl.find env.cluster env.me in
    let entry = Unix.gethostbyname hostname in
    let listen_addr = entry.Unix.h_addr_list.(0) in
    Unix.setsockopt env.nodes_fd Unix.SO_REUSEADDR true;
    Unix.setsockopt env.clients_fd Unix.SO_REUSEADDR true;
    Unix.bind env.nodes_fd (Unix.ADDR_INET (listen_addr, port));
    Unix.bind env.clients_fd (Unix.ADDR_INET (listen_addr, cfg.port));
    Unix.listen env.nodes_fd 8;
    Unix.listen env.clients_fd 8;
    Unix.set_nonblock env.nodes_fd;
    Unix.set_nonblock env.clients_fd;
    (env, initial_state)

  (* throws nothing *)
  let output env o =
    let (c, buf) = A.serialize_output o in
    try send_chunk (denote_client env c) buf
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

  (* throws Disconnect *)
  let add_write_node_fd env node_name node_addr =
    if A.debug then begin
      printf "[%s] connecting to %s for the first time..." (timestamp ()) (Bytes.to_string (A.serialize_name node_name));
      print_newline ()
    end;
    let write_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    try
      Unix.connect write_fd node_addr;
      let name_buf = A.serialize_name env.me in
      send_chunk write_fd name_buf;
      let (hostname, port) = sock_of_name env env.me in
      let addr_buf = Bytes.of_string (sprintf "%s:%d" hostname port) in
      send_chunk write_fd addr_buf;
      if A.debug then begin
	printf "[%s] ...connected!" (timestamp ());
	print_newline ()
      end;
      Hashtbl.replace env.node_write_fds node_name write_fd;
      write_fd
    with
    | Disconnect s ->
      Unix.close write_fd;
      raise (Disconnect s)
    | Unix.Unix_error (err, fn, _) ->
      Unix.close write_fd;
      raise (Disconnect (sprintf "add_write_fd: error in %s: %s" fn (Unix.error_message err)))

  (* throws Disconnect *)
  let get_write_node_fd env node_name =
    try denote_node env node_name
    with Not_found ->
      try
	let (hostname, port) = sock_of_name env node_name in
	let entry = Unix.gethostbyname hostname in
	let node_addr = Unix.ADDR_INET (entry.Unix.h_addr_list.(0), port) in
	add_write_node_fd env node_name node_addr
      with Not_found -> raise (Disconnect "get_write_node_fd: lookup error")

  (* throws Disconnect *)
  let new_node_conn env =
    if A.debug then begin
      printf "[%s] new incoming node connection" (timestamp ());
      print_newline ()
    end;
    (* TODO: catch Unix_error on accept *)
    let (node_read_fd, node_addr) = Unix.accept env.nodes_fd in
    let name_buf = 
      try recv_full_chunk node_read_fd
      with
      | Disconnect s ->
	Unix.close node_read_fd;
	raise (Disconnect s)
      | Unix.Unix_error (err, fn, _) ->
	Unix.close node_read_fd;
	raise (Disconnect (sprintf "new_node_conn: error in %s: %s" fn (Unix.error_message err)))
    in
    match A.deserialize_name name_buf with
    | None ->
      Unix.close node_read_fd;
      raise (Disconnect (sprintf "new_node_conn: failed to deserialize name %s" (Bytes.to_string name_buf)))
    | Some node_name ->
      let sock_buf =
	try recv_full_chunk node_read_fd
	with
	| Disconnect s ->
	  Unix.close node_read_fd;
	  raise (Disconnect s)
	| Unix.Unix_error (err, fn, _) ->
	  Unix.close node_read_fd;
	  raise (Disconnect (sprintf "new_node_conn: error in %s: %s" fn (Unix.error_message err)))
      in
      let sock_str = Bytes.to_string sock_buf in
      let sock =
	try Scanf.sscanf sock_str "%[^:]:%d" (fun i p -> (i, p))
	with _ ->
	  Unix.close node_read_fd;
	  raise (Disconnect (sprintf "new_node_conn: sscanf error %s" sock_str))
      in
      Hashtbl.replace env.cluster node_name sock;
      begin
	try ignore (get_write_node_fd env node_name)
	with Disconnect s ->
	  Unix.close node_read_fd;
	  raise (Disconnect s)
      end;
      Hashtbl.replace env.node_read_fds node_read_fd node_name;
      Hashtbl.replace env.node_fds_read node_name node_read_fd;
      Unix.set_nonblock node_read_fd;
      if A.debug then begin
	printf "[%s] done processing new connection from node %s" (timestamp ()) (Bytes.to_string (A.serialize_name node_name));
	print_newline ()
      end;
      node_read_fd

  (* throws nothing *)
  let connect_to_nodes env =
    let go node_name =
      try ignore (get_write_node_fd env node_name)
      with Disconnect s ->
	eprintf "connect_to_nodes: moving on after error for node %s: %s" (Bytes.to_string (A.serialize_name node_name)) s;
	prerr_newline ()
    in
    let ns = Hashtbl.fold (fun n _ acc -> if n != env.me then n :: acc else acc) env.cluster [] in
    List.iter go ns

  (* throws Disconnect, Unix_error *)
  let send_msg env node_name msg =
    let node_fd =
      try denote_node env node_name
      with Not_found -> raise (Disconnect "send_msg: message destination not found")
    in
    let buf = A.serialize_msg msg in
    send_chunk node_fd buf

  (* throws nothing *)
  let respond env ((os, s), ps) = (* assume outgoing message destinations have tasks *)
    let go ((node_name : A.name), (msg : A.msg)) =
      try
	if A.debug then A.debug_send s (node_name, msg);
	send_msg env node_name msg
      with
      | Disconnect s ->
	eprintf "respond: error for node %s: %s" (Bytes.to_string (A.serialize_name node_name)) s;
	prerr_newline ();
	let task_fd = Hashtbl.find env.node_fds_read node_name in
	schedule_finalize_task (Hashtbl.find env.tasks task_fd) 0.5
      | Unix.Unix_error (err, fn, _) ->
	eprintf "respond: error for node %s: %s" (Bytes.to_string (A.serialize_name node_name)) (Unix.error_message err);
	prerr_newline ();
	let task_fd = Hashtbl.find env.node_fds_read node_name in
	schedule_finalize_task (Hashtbl.find env.tasks task_fd) 0.5
    in
    List.iter (output env) os;
    List.iter go ps;
    s

  (* throws nothing *)
  let deliver_msg env state src msg : A.state =
    let state' = respond env (A.handle_msg env.me src msg state) in
    if A.debug then A.debug_recv state' (src, msg);
    state'

  (* throws Disconnect, Unix_error *)
  let msg_step (env : env) (fd : Unix.file_descr) (state : A.state) : A.state =
    match recv_buf_chunk fd env.read_bufs with
    | None ->
      state
    | Some buf ->
      let src =
	try undenote_node env fd
	with Not_found -> failwith "msg_step: failed to find source for message"
      in
      let msg = A.deserialize_msg buf in
      deliver_msg env state src msg

  (* throws Disconnect, Unix_error *)
  let input_step (env : env) (fd : Unix.file_descr) (state : A.state) =
    match recv_buf_chunk fd env.read_bufs with
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

  let node_read_task fd =
    { fd = fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let state' = msg_step env t.fd state in
	    (false, [], state')
	  with 
	  | Disconnect s ->
	    eprintf "connection error for node %s: %s" (Bytes.to_string (A.serialize_name (undenote_node env t.fd))) s;
	    prerr_newline ();
	    (true, [], state)
	  | Unix.Unix_error (err, fn, _) ->
	    eprintf "error for node %s: %s" (Bytes.to_string (A.serialize_name (undenote_node env t.fd))) (Unix.error_message err);
	    prerr_newline ();
	    (true, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize =
	(fun t env state ->
	  let read_fd = t.fd in
	  let node_name = undenote_node env read_fd in
	  let write_fd = denote_node env node_name in (* assumed to never throw Not_found *)
	  if A.debug then begin
	    printf "[%s] closing connections for node %s" (timestamp ()) (Bytes.to_string (A.serialize_name node_name));
	    print_newline ();
	  end;
	  Hashtbl.remove env.node_read_fds read_fd;
	  Hashtbl.remove env.node_fds_read node_name;
	  Hashtbl.remove env.node_write_fds node_name;
	  Hashtbl.remove env.read_bufs read_fd;
	  Hashtbl.remove env.cluster node_name;
	  Unix.close read_fd;
	  Unix.close write_fd;
	  match A.fail_msg with
          | None -> state
          | Some m -> deliver_msg env state node_name m)
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
	  Hashtbl.remove env.read_bufs client_fd;
	  Unix.close client_fd;
	  state)
    }

  let connect_to_nodes_task env =
    { fd = Unix.dup env.nodes_fd
      ; select_on = false
      ; wake_time = Some 1.0
      ; process_read = (fun t env state -> (false, [], state))
      ; process_wake =
	  (fun t env state ->
	    connect_to_nodes env;
	    t.wake_time <- Some 1.0;
	    (false, [], state))
      ; finalize = (fun t env state -> Unix.close t.fd; state)
      }

  let node_connections_task env =
    { fd = env.nodes_fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let node_fd = new_node_conn env in
	    let state' =
	      match A.new_msg with
	      | None -> state
              | Some m -> deliver_msg env state (Hashtbl.find env.node_read_fds node_fd) m
	    in
	    (false, [node_read_task node_fd], state')
	  with Disconnect s ->
	    eprintf "incoming node connection error: %s" s;
	    prerr_newline ();
	    (false, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize = (fun t env state -> Unix.close t.fd; state)
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
    printf "ordered shim running setup for %s" A.system_name;
    print_newline ();
    let (env, initial_state) = setup cfg in
    let t_conn_nd = connect_to_nodes_task env in
    let t_nd_conn = node_connections_task env in
    let t_cl_conn = client_connections_task env in
    Hashtbl.add env.tasks t_conn_nd.fd t_conn_nd;
    Hashtbl.add env.tasks t_nd_conn.fd t_nd_conn;
    Hashtbl.add env.tasks t_cl_conn.fd t_cl_conn;
    List.iter (fun (handler, setter) ->
      match setter env.me initial_state with
      | None -> ()
      | Some time ->
	let t = timeout_task env handler setter time in
	Hashtbl.add env.tasks t.fd t)
      A.timeout_tasks;
    printf "ordered shim ready for %s" A.system_name;
    print_newline ();
    eloop 2.0 (Unix.gettimeofday ()) env.tasks env initial_state
end
