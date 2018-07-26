open OUnit2
open ListLabels

let tear_down () test_ctxt = ()

let test_deserialize_server_name test_ctxt =
  assert_equal (Some LockServ.Server) (LockServSerialization.deserialize_name "Server")

let test_deserialize_client_name test_ctxt =
  assert_equal (Some (LockServ.Client 5)) (LockServSerialization.deserialize_name "Client-5")

let test_serialize_server_name test_ctxt =
  assert_equal "Server" (LockServSerialization.serialize_name LockServ.Server)

let test_serialize_client_name test_ctxt =
  assert_equal "Client-0" (LockServSerialization.serialize_name (LockServ.Client 0))

let test_list =
  [
    "deserialize server name", test_deserialize_server_name;
    "deserialize client name", test_deserialize_client_name;
    "serialize server name", test_serialize_server_name;
    "serialize client name", test_serialize_client_name;
  ]

let tests =
  "Serialization" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))
