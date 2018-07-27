val cluster_default : (int * (string * int)) list

val me_default : int

val port_default : int

val dbpath_default : string

val debug_default : bool

val cluster : (int * (string * int)) list ref

val me : int ref

val port : int ref

val dbpath : string ref

val debug : bool ref

val parse : string array -> unit

val validate : unit -> unit
