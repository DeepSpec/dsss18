module type IntValue = sig
  val v : int
end

module type Params = sig
  val debug : bool
  val num_clients : int
end

module LockServArrangement (P : Params) = struct
  type name = LockServ.name
  type state = LockServ.data0
  type input = LockServ.msg
  type output = LockServ.msg
  type msg = LockServ.msg
  type client_id = int
  type res = (output list * state) * ((name * msg) list)
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float option

  let system_name = "Lock Server"

  let init = fun n ->
    let open LockServ in
    Obj.magic ((lockServ_MultiParams P.num_clients).init_handlers (Obj.magic n))

  let handle_input = fun n i s ->
    let open LockServ in
    Obj.magic ((lockServ_MultiParams P.num_clients).input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))

  let handle_msg = fun dst src m s ->
    let open LockServ in
    Obj.magic ((lockServ_MultiParams P.num_clients).net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))

  let deserialize_msg = LockServSerialization.deserialize_msg

  let serialize_msg = LockServSerialization.serialize_msg

  let deserialize_input = LockServSerialization.deserialize_input

  let serialize_output = LockServSerialization.serialize_output

  let debug = P.debug

  let debug_input = fun _ inp ->
    Printf.printf
      "[%s] got input %s"
      (Util.timestamp ())
      (LockServSerialization.debug_input inp);
    print_newline ()

  let debug_recv_msg = fun _ (nm, msg) ->
    Printf.printf
      "[%s] receiving message %s from %s" 
      (Util.timestamp ()) 
      (LockServSerialization.debug_msg msg)
      (LockServSerialization.serialize_name nm);
    print_newline ()

  let debug_send_msg = fun _ (nm, msg) ->
    Printf.printf
      "[%s] sending message %s to %s"
      (Util.timestamp ())
      (LockServSerialization.debug_msg msg)
      (LockServSerialization.serialize_name nm);
    print_newline ()

  let create_client_id () =
    let upper_bound = 1073741823 in
    Random.int upper_bound

  let string_of_client_id = string_of_int

  let timeout_tasks = []
end
