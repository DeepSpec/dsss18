let serialize_name : LockServ.name -> string = function
  | LockServ.Server -> "Server"
  | LockServ.Client i -> Printf.sprintf "Client-%d" i

let deserialize_name (s : string) : LockServ.name option =
  match s with
  | "Server" -> Some LockServ.Server
  | _ -> 
    try Scanf.sscanf s "Client-%d" (fun x -> Some (LockServ.Client (Obj.magic x)))
    with _ -> None

let deserialize_msg : bytes -> LockServ.msg = fun s ->
  Marshal.from_bytes s 0

let serialize_msg : LockServ.msg -> bytes = fun m ->
  Marshal.to_bytes m []

let deserialize_input inp c : LockServ.msg option =
  match Bytes.to_string inp with
  | "Unlock" -> Some LockServ.Unlock
  | "Lock" -> Some (LockServ.Lock c)
  | "Locked" -> Some (LockServ.Locked c)
  | _ -> None

let serialize_output : LockServ.msg -> int * bytes = function
  | LockServ.Locked c -> (c, Bytes.of_string "Locked")
  | _ -> failwith "wrong output"

let debug_msg : LockServ.msg -> string = function
  | LockServ.Lock c -> Printf.sprintf "Lock %d" c
  | LockServ.Unlock -> "Unlock"
  | LockServ.Locked c -> Printf.sprintf "Locked %d" c

let debug_input = debug_msg
