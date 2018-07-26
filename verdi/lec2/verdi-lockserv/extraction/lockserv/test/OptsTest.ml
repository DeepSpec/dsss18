open OUnit2
open ListLabels
open Util

let tear_down () test_ctxt =
  LockServOpts.cluster := LockServOpts.cluster_default;
  LockServOpts.me := LockServOpts.me_default;
  LockServOpts.port := LockServOpts.port_default;
  LockServOpts.debug := LockServOpts.debug_default

let test_parse_correct_line test_ctxt =
  LockServOpts.parse (arr_of_string "./LockServMain.native -me Server -port 8000 -node Server,localhost:9000 -node Client-0,localhost:9001 -node Client-1,localhost:9002");
  assert_equal LockServ.Server !LockServOpts.me;
  assert_equal 8000 !LockServOpts.port;
  assert_equal [(LockServ.Server, ("localhost", 9000)); (LockServ.Client 0, ("localhost", 9001)); (LockServ.Client 1, ("localhost", 9002))] !LockServOpts.cluster;
  assert_equal false !LockServOpts.debug

let test_parse_correct_line_with_debug test_ctxt =
  LockServOpts.parse (arr_of_string "./LockServMain.native -debug -me Client-0 -port 8000 -node Server,localhost:9000 -node Client-0,localhost:9001");
  assert_equal (LockServ.Client 0) !LockServOpts.me;
  assert_equal 8000 !LockServOpts.port;
  assert_equal [(LockServ.Server, ("localhost", 9000)); (LockServ.Client 0, ("localhost", 9001))] !LockServOpts.cluster;
  assert_equal true !LockServOpts.debug

let test_validate_correct_line test_ctxt =
  LockServOpts.parse (arr_of_string "./LockServMain.native -me Server -port 8000 -node Server,localhost:9000 -node Client-0,localhost:9001 -node Client-1,localhost:9002");
  assert_equal () (LockServOpts.validate ())

let test_validate_empty_cluster test_ctxt =
  LockServOpts.parse (arr_of_string "./LockServMain.native -me Server -port 8000");
  assert_raises (Arg.Bad "Please specify at least one -node") LockServOpts.validate

let test_validate_me_not_cluster_member test_ctxt =
  LockServOpts.parse (arr_of_string "./LockServMain.native -me Server -port 8000 -node Client-0,localhost:9001 -node Client-1,localhost:9002");
  assert_raises (Arg.Bad "Server is not a member of this cluster") LockServOpts.validate

let test_validate_duplicate_node_entry test_ctxt =
  LockServOpts.parse (arr_of_string "./LockServMain.native -me Server -port 8000 -node Server,localhost:9000 -node Server,localhost:9001");
  assert_raises (Arg.Bad "Please remove duplicate -node name entries") LockServOpts.validate

let test_validate_same_client_msg_port test_ctxt =
  LockServOpts.parse (arr_of_string "./LockServMain.native -me Server -port 8000 -node Server,localhost:8000 -node Client-0,localhost:9001");
  assert_raises (Arg.Bad "Can't use same port for client commands and messages") LockServOpts.validate

let test_list =
  ["parse correct line", test_parse_correct_line;
   "parse correct line with debug", test_parse_correct_line_with_debug;
   "validate correct line", test_validate_correct_line;
   "validate empty cluster", test_validate_empty_cluster;
   "validate me not member of cluster", test_validate_me_not_cluster_member;
   "validate duplicate node entry", test_validate_duplicate_node_entry;
   "validate same client/msg port", test_validate_same_client_msg_port;
  ]
  
let tests =
  "Opts" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))
