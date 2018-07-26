let serialize_name : LockServSeqNum.name0 -> string = function
  | LockServSeqNum.Server -> "Server"
  | LockServSeqNum.Client i -> Printf.sprintf "Client-%d" i

let deserialize_name (s : string) : LockServSeqNum.name0 option =
  match s with
  | "Server" -> Some LockServSeqNum.Server
  | _ -> 
    try Scanf.sscanf s "Client-%d" (fun x -> Some (LockServSeqNum.Client (Obj.magic x)))
    with _ -> None

let deserialize_msg : bytes -> LockServSeqNum.seq_num_msg = fun s ->
  Marshal.from_bytes s 0

let serialize_msg : LockServSeqNum.seq_num_msg -> bytes = fun m ->
  Marshal.to_bytes m []

let deserialize_input inp c : LockServSeqNum.msg0 option =
  match Bytes.to_string inp with
  | "Unlock" -> Some LockServSeqNum.Unlock
  | "Lock" -> Some (LockServSeqNum.Lock c)
  | "Locked" -> Some (LockServSeqNum.Locked c)
  | _ -> None

let serialize_output : LockServSeqNum.msg0 -> int * bytes = function
  | LockServSeqNum.Locked c -> (c, Bytes.of_string "Locked")
  | _ -> failwith "wrong output"

let debug_input : LockServSeqNum.msg0 -> string = function
  | LockServSeqNum.Lock c -> Printf.sprintf "Lock %d" c
  | LockServSeqNum.Unlock -> "Unlock"
  | LockServSeqNum.Locked c -> Printf.sprintf "Locked %d" c

let debug_msg : LockServSeqNum.seq_num_msg -> string = function
  | { LockServSeqNum.tmNum = n ; LockServSeqNum.tmMsg = m } ->
    Printf.sprintf "%d: %s" n (debug_input (Obj.magic m))
