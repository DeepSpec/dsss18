module type IntValue = sig
  val v : int
end

module type Params = sig
  val debug : bool
  val num_clients : int
end

module LockServSerializedArrangement (P : Params) = struct
  type name = LockServSerialized.name0
  type state = LockServSerialized.data0
  type input = LockServSerialized.msg0
  type output = LockServSerialized.msg0
  type msg = Serializer_primitives.wire
  type client_id = int
  type res = (output list * state) * ((name * msg) list)
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float option

  let system_name = "Lock Server with serialization"

  let init = fun n ->
    let open LockServSerialized in
    Obj.magic ((transformed_multi_params P.num_clients).init_handlers (Obj.magic n))

  let handle_input = fun n i s ->
    let open LockServSerialized in
    Obj.magic ((transformed_multi_params P.num_clients).input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))

  let handle_msg = fun dst src m s ->
    let open LockServSerialized in
    Obj.magic ((transformed_multi_params P.num_clients).net_handlers (Obj.magic dst) (Obj.magic src) (Obj.magic m) (Obj.magic s))
    
  let deserialize_msg = fun s -> s

  let serialize_msg = fun s -> s

  let deserialize_input = LockServSerializedSerialization.deserialize_input

  let serialize_output = LockServSerializedSerialization.serialize_output

  let debug = P.debug

  let debug_input = fun _ inp ->
    Printf.printf
      "[%s] got input %s"
      (Util.timestamp ())
      (LockServSerializedSerialization.debug_input inp);
    print_newline ()

  let debug_recv_msg = fun _ (nm, msg) ->
    Printf.printf
      "[%s] receiving message from %s"
      (Util.timestamp ())
      (LockServSerializedSerialization.serialize_name nm);
    print_newline ()

  let debug_send_msg = fun _ (nm, msg) ->
    Printf.printf
      "[%s] sending message to %s"
      (Util.timestamp ())
      (LockServSerializedSerialization.serialize_name nm);
    print_newline ()

  let create_client_id () =
    let upper_bound = 1073741823 in
    Random.int upper_bound

  let string_of_client_id = string_of_int

  let timeout_tasks = []
end
