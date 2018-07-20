From Coq Require Import
     Extraction
     String.

From DeepWeb Require Import
     Lib.Util.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter file_descr : Type.

Parameter close  : file_descr -> unit.
Parameter init   : forall {A}, A -> A.
Parameter log    : string -> unit.
Parameter recvb  : file_descr -> option byte.
Parameter sendb  : file_descr -> byte -> nat.
Parameter socket : unit -> file_descr.

Extract Constant file_descr => "Unix.file_descr".

Extract Constant close  => "fun sock ->
  Unix.shutdown sock Unix.SHUTDOWN_ALL".
Extract Constant init => "fun x ->
  ignore (Unix.system ""make server"");
  Unix.sleep 1;
  x".
Extract Constant log => "fun cl ->
  let str =
    Bytes.to_string (
      let s = Bytes.create (List.length cl) in
      let rec copy i = function
      | [] -> s
      | c :: l -> Bytes.set s i c; copy (i+1) l
      in copy 0 cl) in
  let out = open_out_gen [Open_wronly; Open_append; Open_creat; Open_text]
                0o666 ""/tmp/client_log"" in
  output_string out (str ^ ""\n"");
  close_out out".
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
  Unix.send sock (Bytes.make 1 c) 0 1 []".
Extract Constant socket => "fun _ ->
  let open Unix in
  let sock = socket PF_INET SOCK_STREAM 0 in
  connect sock (ADDR_INET (inet_addr_loopback, 8000));
  setsockopt_float sock SO_RCVTIMEO 0.;
  sock".
