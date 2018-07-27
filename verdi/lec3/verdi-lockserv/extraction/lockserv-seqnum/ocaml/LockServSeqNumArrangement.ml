module type IntValue = sig
  val v : int
end

module type Params = sig
  val debug : bool
  val num_clients : int
end

module LockServSeqNumArrangement (P : Params) = struct
  type name = LockServSeqNum.name0
  type state = LockServSeqNum.seq_num_data
  type input = LockServSeqNum.msg0
  type output = LockServSeqNum.msg0
  type msg = LockServSeqNum.seq_num_msg
  type client_id = int
  type res = (output list * state) * ((name * msg) list)
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float option

  let system_name = "Lock Server with Sequence Numbering"

  let init = fun n ->
    let open LockServSeqNum in
    Obj.magic ((transformed_multi_params P.num_clients).init_handlers (Obj.magic n))

  let handle_input = fun n i s ->
    let open LockServSeqNum in
    Obj.magic ((transformed_multi_params P.num_clients).input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))

  let handle_msg = fun dst src m s ->
    let open LockServSeqNum in
    Obj.magic ((transformed_multi_params P.num_clients).net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))
    
  let deserialize_msg = LockServSeqNumSerialization.deserialize_msg

  let serialize_msg = LockServSeqNumSerialization.serialize_msg

  let deserialize_input = LockServSeqNumSerialization.deserialize_input

  let serialize_output = LockServSeqNumSerialization.serialize_output

  let debug = P.debug

  let debug_input = fun _ inp ->
    Printf.printf
      "[%s] got input %s"
      (Util.timestamp ())
      (LockServSeqNumSerialization.debug_input inp);
    print_newline ()

  let debug_recv_msg = fun _ (nm, msg) ->
    Printf.printf
      "[%s] receiving message %s from %s"
      (Util.timestamp ())
      (LockServSeqNumSerialization.debug_msg msg)
      (LockServSeqNumSerialization.serialize_name nm);
    print_newline ()

  let debug_send_msg = fun _ (nm, msg) ->
    Printf.printf
      "[%s] sending message %s to %s"
      (Util.timestamp ())
      (LockServSeqNumSerialization.debug_msg msg)
      (LockServSeqNumSerialization.serialize_name nm);
    print_newline ()

  let create_client_id () =
    let upper_bound = 1073741823 in
    Random.int upper_bound

  let string_of_client_id = string_of_int

  let timeout_tasks = []
end
