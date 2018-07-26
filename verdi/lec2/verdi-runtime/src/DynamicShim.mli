module type ARRANGEMENT = sig
  type name
  type state
  type msg
  type timeout
  type addr = string
  type res = state * (name * msg) list * timeout list * timeout list
  val port : int
  val addr_of_name : name -> addr
  val name_of_addr : addr -> name
  val deserialize_msg : bytes -> msg
  val serialize_msg : msg -> bytes
  val start_handler : name -> name list -> state * (name * msg) list * timeout list
  val msg_handler : name -> name -> state -> msg -> res
  val timeout_handler : name -> state -> timeout -> res
  val set_timeout : timeout -> float
  val default_timeout : float
  val debug : bool
  val debug_recv : state -> (name * msg) -> unit
  val debug_send : state -> (name * msg) -> unit
  val debug_timeout : state -> timeout -> unit
end

module Shim :
  functor (A : ARRANGEMENT) ->
    sig
      val main : A.addr -> A.addr list -> unit
    end
