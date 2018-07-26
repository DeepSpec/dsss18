open List
open Printf
open Str

let cluster_default = []
let me_default = -1
let port_default = 8351
let dbpath_default = "/tmp/verdi"
let debug_default = false

let cluster = ref cluster_default
let me = ref me_default
let port = ref port_default
let dbpath = ref dbpath_default
let debug = ref debug_default

let node_spec arg nodes_ref doc =
  let parse opt =
    (* name,ip:port *)
    if string_match (regexp "\\([0-9]+\\),\\(.+\\):\\([0-9]+\\)") opt 0 then
      (int_of_string (matched_group 1 opt),
       (matched_group 2 opt, int_of_string (matched_group 3 opt)))
    else
      raise (Arg.Bad (sprintf "wrong argument: '%s'; option '%s' expects an entry in the form 'name,host:port'" arg opt))
  in (arg, Arg.String (fun opt -> nodes_ref := !nodes_ref @ [parse opt]), doc)

let parse inp =
  let opts =
    [ node_spec "-node" cluster "{name,host:port} one node in the cluster"
    ; ("-me", Arg.Set_int me, "{name} name for this node")
    ; ("-port", Arg.Set_int port, "{port} port for client commands")
    ; ("-dbpath", Arg.Set_string dbpath, "{path} directory for storing database files")
    ; ("-debug", Arg.Set debug, "run in debug mode")
    ] in
   Arg.parse_argv ?current:(Some (ref 0)) inp
    opts
    (fun x -> raise (Arg.Bad (sprintf "%s does not take position arguments" inp.(0))))
    "Try -help for help or one of the following."

let rec assoc_unique = function
  | [] -> true
  | (k, _) :: l -> if mem_assoc k l then false else assoc_unique l

let validate () =
  if length !cluster = 0 then
    raise (Arg.Bad "Please specify at least one -node");
  if !me = me_default then
    raise (Arg.Bad "Please specify the node name -me");
  if not (mem_assoc !me !cluster) then
    raise (Arg.Bad (sprintf "%d is not a member of this cluster" !me));
  if not (assoc_unique !cluster) then
    raise (Arg.Bad "Please remove duplicate -node name entries");
  if !port = snd (assoc !me !cluster) then
    raise (Arg.Bad "Can't use same port for client commands and messages")
