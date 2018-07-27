let raw_bytes_of_int (x : int) : bytes =
  let buf = Bytes.make 4 '\x00' in
  Bytes.set buf 0 (char_of_int (x land 0xff));
  Bytes.set buf 1 (char_of_int ((x lsr 8) land 0xff));
  Bytes.set buf 2 (char_of_int ((x lsr 16) land 0xff));
  Bytes.set buf 3 (char_of_int ((x lsr 24) land 0xff));
  buf

let int_of_raw_bytes (buf : bytes) : int =
  (int_of_char (Bytes.get buf 0)) lor
    ((int_of_char (Bytes.get buf 1)) lsl 8) lor
    ((int_of_char (Bytes.get buf 2)) lsl 16) lor
    ((int_of_char (Bytes.get buf 3)) lsl 24)

let char_list_of_string s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let bytes_of_char_list l =
  let res = Bytes.create (List.length l) in
  let rec imp i = function
    | [] -> res
    | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l

let string_of_char_list l =
  Bytes.to_string (bytes_of_char_list l)

let rec select_unintr rs ws es t =
  try Unix.select rs ws es t
  with
  | Unix.Unix_error (Unix.EINTR, fn, arg) ->
    select_unintr rs ws es t
  | Unix.Unix_error (e, _, _) ->
    Printf.eprintf "select error: %s" (Unix.error_message e);
    prerr_newline ();
    select_unintr rs ws es t

let mk_addr_inet (ip, port) =
  Unix.ADDR_INET (Unix.inet_addr_of_string ip, port)

let mk_addr_inet_random_port ip =
  mk_addr_inet (ip, 0)

let string_of_sockaddr (saddr : Unix.sockaddr) : string =
  match saddr with
  | Unix.ADDR_UNIX path -> (Printf.sprintf "unix://%s" path)
  | Unix.ADDR_INET (addr, port) -> (Printf.sprintf "%s:%d" (Unix.string_of_inet_addr addr) port)

let octets_to_ip o1 o2 o3 o4 =
  o1 lsl 24 + o2 lsl 16 + o3 lsl 8 + o4

(* Matches four groups of at most three digits separated by dots *)
let weak_ip_regexp =
  Str.regexp "\\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)$"

(* Convert the string representation s of an ip, e.g., "10.14.122.04" to a
   32-bit integer.
   Throws Invalid_argument if s does not represent a valid IPv4 address. *)
let int_of_ip s =
  if Str.string_match weak_ip_regexp s 0
  then
    let int_of_kth_group k = int_of_string (Str.matched_group k s) in
    let numbers = List.map int_of_kth_group [1; 2; 3; 4] in
    match numbers with
    | [o1; o2; o3; o4] ->
       if List.for_all (fun x -> 0 <= x && x <= 255) numbers
       then octets_to_ip o1 o2 o3 o4
       else invalid_arg s
    | _ -> invalid_arg s
  else invalid_arg s

(* Convert a 32-bit integer to its dotted octet representation. *)
let ip_of_int i =
  if i > 1 lsl 32
  then invalid_arg (string_of_int i)
  else let octets = [(i land (1 lsl 32 - 1 lsl 24)) lsr 24;
                     (i land (1 lsl 24 - 1 lsl 16)) lsr 16;
                     (i land (1 lsl 16 - 1 lsl 8)) lsr 8;
                     i land (1 lsl 8 - 1)] in
       String.concat "." (List.map string_of_int octets)

let map_default f d = function
  | None -> d
  | Some v -> f v

let timestamp () =
  let (fr_sec, time) = modf (Unix.gettimeofday ()) in
  let tm = Unix.gmtime time in
  let frs = String.sub (string_of_float fr_sec) 2 3 in
  Printf.sprintf "%.4i-%.2i-%.2iT%.2i:%.2i:%.2i.%sZ"
    Unix.(tm.tm_year+1900) Unix.(tm.tm_mon+1) Unix.(tm.tm_mday)
    Unix.(tm.tm_hour) Unix.(tm.tm_min) Unix.(tm.tm_sec) frs

let log level s = Printf.printf "[%s] %s: %s\n" (timestamp ()) level s

let debug = log "DEBUG"

let info = log "INFO"

let keys_of_hashtbl h =
  let cons k _ l = k :: l in
  Hashtbl.fold cons h []

exception Disconnect of string

(* throws Unix_error, Disconnect *)
let rec send_all fd buf offset len =
  if offset < len then begin
    let n = Unix.send fd buf offset (len - offset) [] in
    if n = 0 then raise (Disconnect "send_all: other side closed connection");
    send_all fd buf (offset + n) len
  end

(* throws Unix_error, Disconnect *)
let send_chunk fd buf =
  let len = Bytes.length buf in
  let n = Unix.send fd (raw_bytes_of_int len) 0 4 [] in
  if n < 4 then raise (Disconnect "send_chunk: message header failed to send all at once");
  send_all fd buf 0 len

(* throws Unix_error, Disconnect *)
let recv_buf_chunk fd ht =
  if Hashtbl.mem ht fd then begin
    let (rem, buf) = Hashtbl.find ht fd in
    let len = Bytes.length buf in
    let offset = len - rem in
    let n = Unix.recv fd buf offset rem [] in
    if n = 0 then raise (Disconnect "recv_buf_chunk: other side closed connection");
    if n < rem then begin
      let rem' = rem - n in
      Hashtbl.replace ht fd (rem', buf);
      None
    end else begin
      Hashtbl.remove ht fd;
      Some buf
    end
  end else begin
    let buf = Bytes.make 4 '\x00' in
    let n = Unix.recv fd buf 0 4 [] in
    if n = 0 then raise (Disconnect "recv_buf_chunk: other side closed connection");
    if n < 4 then raise (Disconnect "recv_buf_chunk: message header did not arrive all at once");
    let len = int_of_raw_bytes buf in
    let buf = Bytes.make len '\x00' in
    try
      let n = Unix.recv fd buf 0 len [] in
      if n < len then begin
	let rem = len - n in
	Hashtbl.add ht fd (rem, buf);
	None
      end else Some buf
    with
    | Unix.Unix_error (Unix.EAGAIN, _, _)
    | Unix.Unix_error (Unix.EWOULDBLOCK, _, _) ->
      Hashtbl.add ht fd (len, buf);
      None
  end

(* throws Unix_error, Disconnect *)
let recv_full_chunk fd =
  let recv_check fd buf offs len flags =
    let n = Unix.recv fd buf offs len flags in
    if n = 0 then raise (Disconnect "recv_full_chunk: other side closed connection");
    n
  in
  let buf = Bytes.make 4 '\x00' in
  let n = recv_check fd buf 0 4 [] in
  if n < 4 then raise (Disconnect "recv_full_chunk: message header did not arrive all at once");
  let len = int_of_raw_bytes buf in
  let buf = Bytes.make len '\x00' in
  let n = recv_check fd buf 0 len [] in
  if n < len then raise (Disconnect (Printf.sprintf "recv_full_chunk: message of length %d did not arrive all at once" len));
  buf

let arr_of_string s =
  let listl = (Str.split (Str.regexp " ") s) in
  (Array.of_list listl)
