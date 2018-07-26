let serialize_name : LockServSerialized.name0 -> string = function
  | LockServSerialized.Server -> "Server"
  | LockServSerialized.Client i -> Printf.sprintf "Client-%d" i

let deserialize_name (s : string) : LockServSerialized.name0 option =
  match s with
  | "Server" -> Some LockServSerialized.Server
  | _ -> 
    try Scanf.sscanf s "Client-%d" (fun x -> Some (LockServSerialized.Client (Obj.magic x)))
    with _ -> None

let deserialize_input inp c : LockServSerialized.msg0 option =
  match Bytes.to_string inp with
  | "Unlock" -> Some LockServSerialized.Unlock
  | "Lock" -> Some (LockServSerialized.Lock c)
  | "Locked" -> Some (LockServSerialized.Locked c)
  | _ -> None

let serialize_output : LockServSerialized.msg0 -> int * bytes = function
  | LockServSerialized.Locked c -> (c, Bytes.of_string "Locked")
  | _ -> failwith "invalid output"

let debug_input : LockServSerialized.msg0 -> string = function
  | LockServSerialized.Lock c -> Printf.sprintf "Lock %d" c
  | LockServSerialized.Unlock -> "Unlock"
  | LockServSerialized.Locked c -> Printf.sprintf "Locked %d" c
