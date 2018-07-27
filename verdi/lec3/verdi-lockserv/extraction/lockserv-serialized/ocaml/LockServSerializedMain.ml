open LockServSerializedOpts
open LockServSerializedArrangement

let () =
  let () =
    try
      parse Sys.argv
    with
    | Arg.Help msg ->
      Printf.printf "%s: %s" Sys.argv.(0) msg;
      exit 2
    | Arg.Bad msg ->
      Printf.eprintf "%s" msg;
      exit 2
  in
  let () =
    try
      validate ()
    with Arg.Bad msg ->
      Printf.eprintf "%s: %s." Sys.argv.(0) msg;
      prerr_newline ();
      exit 2
  in
  let module Pms = struct
    let debug = !debug
    let num_clients = List.length !cluster - 1
  end in
  let module Arrangement = LockServSerializedArrangement (Pms) in
  let module Shim = UnorderedShim.Shim (Arrangement) in
  let open Shim in
  main { cluster = !cluster
       ; me = !me
       ; port = !port
       }
