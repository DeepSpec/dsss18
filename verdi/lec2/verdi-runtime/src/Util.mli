val raw_bytes_of_int : int -> bytes

val int_of_raw_bytes : bytes -> int

val char_list_of_string : string -> char list

val bytes_of_char_list : char list -> bytes

val string_of_char_list : char list -> string

val select_unintr :
  Unix.file_descr list ->
  Unix.file_descr list ->
  Unix.file_descr list ->
  float -> Unix.file_descr list * Unix.file_descr list * Unix.file_descr list

val mk_addr_inet : string * int -> Unix.sockaddr

val mk_addr_inet_random_port : string -> Unix.sockaddr

val string_of_sockaddr : Unix.sockaddr -> string

val octets_to_ip : int -> int -> int -> int -> int

val weak_ip_regexp : Str.regexp

val int_of_ip : string -> int

val ip_of_int : int -> string

val map_default : ('a -> 'b) -> 'b -> 'a option -> 'b

val timestamp : unit -> string

val log : string -> string -> unit

val debug : string -> unit

val info : string -> unit

val keys_of_hashtbl : ('a, 'b) Hashtbl.t -> 'a list

exception Disconnect of string

val send_chunk : Unix.file_descr -> bytes -> unit

val recv_buf_chunk : Unix.file_descr -> (Unix.file_descr, int * bytes) Hashtbl.t -> bytes option

val recv_full_chunk : Unix.file_descr -> bytes

val arr_of_string : string -> string array
