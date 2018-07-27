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
  val init : name -> state
  val handle_input : name -> input -> state -> res
  val handle_msg : name -> name -> msg -> state -> res
  val deserialize_msg : bytes -> msg
  val serialize_msg : msg -> bytes
  val deserialize_input : bytes -> client_id -> input option
  val serialize_output : output -> client_id * bytes
  val debug : bool
  val debug_input : state -> input -> unit
  val debug_recv_msg : state -> (name * msg) -> unit
  val debug_send_msg : state -> (name * msg) -> unit
  val create_client_id : unit -> client_id
  val string_of_client_id : client_id -> string
  val timeout_tasks : (task_handler * timeout_setter) list
end

module Shim :
  functor (A : ARRANGEMENT) ->
    sig
      type cfg = 
	{ cluster : (A.name * (string * int)) list
	; me : A.name
	; port : int
	}
      val main : cfg -> unit
    end
