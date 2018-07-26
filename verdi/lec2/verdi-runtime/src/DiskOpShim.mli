type 'a disk_op =
| Append of 'a * Serializer_primitives.serializer
| Write of 'a * Serializer_primitives.serializer
| Delete of 'a

module type ARRANGEMENT = sig
  type name
  type file_name
  type state
  type input
  type output
  type msg
  type client_id
  type res = ((file_name disk_op list * output list) * state) * ((name * msg) list)
  type disk = file_name -> in_channel option
  val system_name : string
  val reboot : name -> disk -> state * file_name disk_op list
  val handle_input : name -> input -> state -> res
  val handle_msg : name -> name -> msg -> state -> res
  val handle_timeout : name -> state -> res
  val set_timeout : name -> state -> float
  val deserialize_msg : bytes -> msg
  val serialize_msg : msg -> bytes
  val deserialize_input : bytes -> client_id -> input option
  val serialize_output : output -> client_id * bytes
  val debug : bool
  val debug_input : state -> input -> unit
  val debug_recv : state -> (name * msg) -> unit
  val debug_send : state -> (name * msg) -> unit
  val debug_timeout : state -> unit
  val deserialize_client_id : bytes -> client_id option
  val string_of_client_id : client_id -> string
  val string_of_file_name : file_name -> string
  val files : file_name list
end

module Shim :
  functor (A : ARRANGEMENT) ->
    sig
      type cfg =
        { cluster : (A.name * (string * int)) list
        ; me : A.name
        ; port : int
        ; fspath : string
        }
      val main : cfg -> unit
    end
