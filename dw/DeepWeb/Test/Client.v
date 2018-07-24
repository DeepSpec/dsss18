(* IO monad for Coq. *)

From Coq Require Import
     Extraction
     String.

From ExtLib Require Import
     Monad.

From DeepWeb Require Import
     Lib.Util.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

Parameter file_descr : Type.
Parameter ocaml_unit : Type.
(* Opaque type in case Coq tries to be too smart about [unit]. *)

Parameter out_channel : Type.
Parameter error_handle : out_channel.

Parameter IO     : Type -> Type.
Parameter retIO  : forall A, A -> IO A.
Parameter bindIO : forall A B, IO A -> (A -> IO B) -> IO B.

Instance Monad_IO : Monad IO :=
  { ret := retIO;
    bind := bindIO;
  }.

Parameter runIO_with_server' : forall A, out_channel -> IO A -> option A.
Definition runIO_with_server A := runIO_with_server' A error_handle.
Parameter log    : string -> IO unit.
Parameter close  : file_descr -> IO unit.
Parameter recvb  : file_descr -> IO (option byte).
Parameter sendb  : file_descr -> byte -> IO nat.
Parameter socket : IO (option file_descr).

Arguments runIO_with_server {A}.

Extract Constant IO "'a" => "unit -> 'a".

Extract Constant file_descr => "Unix.file_descr".
Extract Constant ocaml_unit => "unit".

Extract Inlined Constant out_channel => "out_channel".
Extract Constant error_handle => "open_out ""/tmp/client_error""".

Extract Constant retIO => "fun a () -> a".
Extract Constant bindIO =>
  "fun ioa to_iob () -> to_iob (ioa ()) ()".

Extract Constant runIO_with_server' => "fun err io ->
  ignore (Unix.system ""make server --quiet"");
  Unix.sleepf 1e-3;
  let a =
    try Some (io ())
    with e ->
      output_string err (Printexc.to_string e);
      output_char err '\n';
      flush err;
      None in
  ignore (Unix.system ""make stop --quiet"");
  a".

Extract Constant close => "fun fd () -> Unix.close fd".

Extract Constant log => "
  let out = open_out_gen [Open_wronly; Open_append; Open_creat; Open_text]
                0o666 ""/tmp/client_log"" in
  fun cl () ->
    let str =
      Bytes.to_string (
        let s = Bytes.create (List.length cl) in
        let rec copy i = function
        | [] -> s
        | c :: l -> Bytes.set s i c; copy (i+1) l
        in copy 0 cl) in
    output_string out (str ^ ""\n"")".

Extract Constant recvb  => "fun sock () ->
  let bs = Bytes.create 1 in
  match Unix.recv sock bs 0 1 [] with
  | exception Unix.Unix_error((Unix.EAGAIN | Unix.EWOULDBLOCK), _, _) ->
     None
  | k ->
     if k = 1 then
       Some (Bytes.get bs 0)
     else
       None".

Extract Constant sendb  => "fun sock c () ->
  Unix.send sock (Bytes.make 1 c) 0 1 []".

Extract Constant socket => "fun () ->
  let open Unix in
  let sock = socket PF_INET SOCK_STREAM 0 in
  try
    connect sock (ADDR_INET (inet_addr_loopback, 8000));
    set_nonblock sock;
    Some sock
  with
  | Unix.Unix_error(Unix.ECONNREFUSED, _, _) ->
    close sock;
    None".

Parameter flip : IO bool.
Parameter rand : nat -> IO nat.

Extract Constant flip => "Random.bool".
Extract Constant rand => "fun n () -> Random.int n".
