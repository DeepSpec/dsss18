open Printf
open Util
open Daemon

module type ARRANGEMENT = sig
  type name
  type state
  type msg
  type timeout
  type addr = string
  type res = state * (name * msg) list * timeout list * timeout list
  val port : int
  val addr_of_name : name -> addr
  val name_of_addr : addr -> name
  val deserialize_msg : bytes -> msg
  val serialize_msg : msg -> bytes
  val start_handler : name -> name list -> state * (name * msg) list * timeout list
  val msg_handler : name -> name -> state -> msg -> res
  val timeout_handler : name -> state -> timeout -> res
  val set_timeout : timeout -> float
  val default_timeout : float
  val debug : bool
  val debug_recv : state -> (name * msg) -> unit
  val debug_send : state -> (name * msg) -> unit
  val debug_timeout : state -> timeout -> unit
end

module Shim (A: ARRANGEMENT) = struct
  type env =
    { me : A.name
    ; listen_fd : Unix.file_descr
    ; read_fds : (Unix.file_descr, A.name) Hashtbl.t
    ; write_fds : (A.name, Unix.file_descr) Hashtbl.t
    ; tasks : (Unix.file_descr, (env, A.state * (float * A.timeout) list) task) Hashtbl.t
    ; read_bufs : (Unix.file_descr, int * bytes) Hashtbl.t
    }

  let bind_sock sock name any_port =
    let hostname = A.addr_of_name name in
    let entry = Unix.gethostbyname hostname in
    let listen_addr = entry.Unix.h_addr_list.(0) in
    Unix.bind sock (Unix.ADDR_INET (listen_addr, if any_port then 0 else A.port))
    
  let setup me : env =
    Random.self_init ();
    let env =
      { me = me
      ; listen_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0
      ; read_fds = Hashtbl.create 17
      ; write_fds = Hashtbl.create 17
      ; tasks = Hashtbl.create 17
      ; read_bufs = Hashtbl.create 17
      } in
    Unix.setsockopt env.listen_fd Unix.SO_REUSEADDR true;
    bind_sock env.listen_fd env.me false;
    Unix.listen env.listen_fd 8;
    Unix.set_nonblock env.listen_fd;
    env

  let filter_cleared clearedts ts =
    let not_cleared (_, t) = not (List.mem t clearedts) in
    List.filter not_cleared ts

  let add_times ts =
    let now = Unix.gettimeofday () in
    let add_time t = (now +. A.set_timeout t, t) in
    List.map add_time ts

  (* throws Unix_error *)
  let connect_write_fd env nm =
    let hostname = A.addr_of_name nm in
    let entry = Unix.gethostbyname hostname in
    let addr = entry.Unix.h_addr_list.(0) in
    let write_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.setsockopt write_fd Unix.SO_REUSEADDR true;
    (* bind before connect *)
    bind_sock write_fd env.me true;
    Unix.connect write_fd (Unix.ADDR_INET (addr, A.port));
    Hashtbl.add env.write_fds nm write_fd;
    write_fd

  let send_msg env (dst, msg) =
    try
      let write_fd =
        try Hashtbl.find env.write_fds dst
        with Not_found -> connect_write_fd env dst
      in
      let buf = A.serialize_msg msg in
      send_chunk write_fd buf
    with
    | Disconnect s ->
      eprintf "connection error: %s" s;
      prerr_newline ()
    | Unix.Unix_error (err, fn, _) ->
      eprintf "connection error: %s" (Unix.error_message err);
      prerr_newline ()

  let respond env ts (s, ps, newts, clearedts) =
    let ts' = filter_cleared clearedts ts @ add_times newts in
    List.iter 
      (fun ms ->
	if A.debug then A.debug_send s ms;
	send_msg env ms) ps;
    (s, ts')

  let rec uniqappend l = function
    | [] -> l
    | h :: rest ->
       if List.mem h l
       then uniqappend l rest
       else uniqappend (l @ [h]) rest

  let do_timeout env (s, sends, newts, clearedts) (deadline, t) =
    if not (List.mem t clearedts)
    then
      let (s', sends', newts', clearedts') = A.timeout_handler env.me s t in
      A.debug_timeout s' t;
      (s', sends @ sends', newts @ newts', uniqappend clearedts clearedts')
    else (s, sends, newts, clearedts)   

  let timeout_step env s ts =
    let now = Unix.gettimeofday () in
    let active = List.filter (fun (deadline, _) -> now > deadline) ts in
    let do_t = do_timeout env in
    let res = (s, [], [], []) in
    let (s, sends, newts, clearedts) = List.fold_left do_t res active in
    let cts = uniqappend clearedts (List.map snd active) in
    respond env ts (s, sends, newts, cts)

  let min_of_list default l =
    List.fold_left (fun acc x -> min acc x) default l

  let free_time ts =
    let now = Unix.gettimeofday () in
    let min_deadline = min_of_list now (List.map fst ts) in
    max A.default_timeout (min_deadline -. now)

  (* to use instead of Hashtbl.filter_map_inplace (not in-place though) *)
  let filter_map f h =
    let size = Hashtbl.length h in
    let h' = Hashtbl.create size in
    let filter_map_step k v acc =
      match f k v with
      | Some v' -> Hashtbl.add acc k v'; acc
      | None -> acc
    in
    Hashtbl.fold filter_map_step h h'

  let init nm knowns =
    let (st, sends, nts) = A.start_handler nm knowns in
    (st, sends, nts, [])

  let new_conn env =
    if A.debug then begin
      printf "[%s] incoming connection" (timestamp ());
      print_newline ()
    end;
    let (read_fd, read_addr) = Unix.accept env.listen_fd in
    let nm =
      match read_addr with
      | Unix.ADDR_INET (addr, port) -> A.name_of_addr (Unix.string_of_inet_addr addr)
      | _ -> assert false
    in
    Unix.set_nonblock read_fd;
    Hashtbl.replace env.read_fds read_fd nm;
    if A.debug then begin
      printf "[%s] done processing new connection" (timestamp ());
      print_newline ()
    end;
    read_fd

  (* throws Disconnect, Unix_error *)
  let msg_step env fd s ts =
    match recv_buf_chunk fd env.read_bufs with
    | None ->
      (s, ts)
    | Some buf ->
      let m = A.deserialize_msg buf in
      let src = Hashtbl.find env.read_fds fd in
      let (s', ms, newts, clearedts) = A.msg_handler src env.me s m in
      if A.debug then A.debug_recv s' (src, m);
      respond env ts (s', ms, newts, clearedts)

  let read_task fd =
    { fd = fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env (state, ts) ->
	  try
	    let (state', ts') = msg_step env t.fd state ts in
	    (false, [], (state', ts'))
	  with 
	  | Disconnect s ->
	    eprintf "connection read error: %s" s;
	    prerr_newline ();
	    (true, [], (state, ts))
	  | Unix.Unix_error (err, fn, _) ->
	    eprintf "connection read error: %s" (Unix.error_message err);
	    prerr_newline ();
	    (true, [], (state, ts)))
    ; process_wake = (fun t env (state, ts) -> (false, [], (state, ts)))
    ; finalize =
	(fun t env (state, ts) ->
	  let read_fd = t.fd in
	  let nm = Hashtbl.find env.read_fds read_fd in
	  if A.debug then begin
	    printf "[%s] closing connections to %s" (timestamp ()) (A.addr_of_name nm);
	    print_newline ();
	  end;
	  Hashtbl.remove env.read_fds read_fd;
	  Hashtbl.remove env.read_bufs read_fd;
	  if Hashtbl.mem env.write_fds nm then begin
	    let write_fd = Hashtbl.find env.write_fds nm in
	    Hashtbl.remove env.write_fds nm;
	    Unix.close write_fd
	  end;
	  Unix.close read_fd;
	  (state, ts))
    }
      
  let connections_task env =
    { fd = env.listen_fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env (state, ts) ->
	  try
	    let read_fd = new_conn env in
	    (false, [read_task read_fd], (state, ts))
	  with Disconnect s ->
	    eprintf "incoming node connection error: %s" s;
	    prerr_newline ();
	    (false, [], (state, ts)))
    ; process_wake = (fun t env (state, ts) -> (false, [], (state, ts)))
    ; finalize = (fun t env (state, ts) -> Unix.close t.fd; (state, ts))
    }

  let timeout_step_task env time =
    { fd = Unix.dup env.listen_fd
    ; select_on = false
    ; wake_time = Some time
    ; process_read = (fun t env (state, ts) -> (false, [], (state, ts)))
    ; process_wake =
	(fun t env (state, ts) ->
	  let (state', ts') = timeout_step env state ts in
	  let time' = free_time ts' in
	  t.wake_time <- Some time';
	  (false, [], (state', ts')))
    ; finalize = (fun t env (state, ts) -> Unix.close t.fd; (state, ts))
    }

  let main me_addr known_addrs =
    printf "dynamic shim running setup";
    print_newline ();
    let me = A.name_of_addr me_addr in
    let env = setup me in
    let known_names = List.map A.name_of_addr known_addrs in
    let (init_state, init_ts) = respond env [] (init env.me known_names) in
    let t_timeout_step = timeout_step_task env (free_time init_ts) in
    let t_connections = connections_task env in
    Hashtbl.add env.tasks t_timeout_step.fd t_timeout_step;
    Hashtbl.add env.tasks t_connections.fd t_connections;
    printf "dynamic shim ready";
    print_newline ();
    eloop 2.0 (Unix.gettimeofday ()) env.tasks env (init_state, init_ts)
end
