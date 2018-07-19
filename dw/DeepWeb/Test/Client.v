From Coq Require Import
     Extraction
     String.
From DeepWeb Require Import ByteType.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter file_descr : Type.

Parameter close  : file_descr -> unit.
Parameter init   : forall {A}, A -> A.
Parameter recvb  : file_descr -> option byte.
Parameter sendb  : file_descr -> byte -> unit.
Parameter socket : unit -> file_descr.

Extract Constant file_descr => "Unix.file_descr".

Extract Constant close  => "fun sock ->
  Unix.shutdown sock Unix.SHUTDOWN_ALL".
Extract Constant init => "fun x ->
  ignore (Unix.system ""make server"");
  Unix.sleep 1;
  x".
Extract Constant recvb  => "fun sock ->
  let bs = Bytes.create 1 in
  match Unix.recv sock bs 0 1 [] with
  | exception Unix.Unix_error(Unix.EAGAIN, _, _) ->
     None
  | 0 -> None
  | k ->
     if k = 1 then
       Some (Bytes.get bs 0)
     else
       None".
Extract Constant sendb  => "fun sock c ->
  ignore (Unix.send sock (Bytes.make 1 c) 0 1)".
Extract Constant socket => "fun _ ->
  let open Unix in
  let sock = socket PF_INET SOCK_STREAM 0 in
  connect sock (ADDR_INET (inet_addr_loopback, 8000));
  setsockopt_float sock SO_RCVTIMEO 0.;
  sock".
