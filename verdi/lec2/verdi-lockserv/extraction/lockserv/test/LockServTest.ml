open OUnit2

let () =
  run_test_tt_main 
    ~exit
    ("Lock Serv" >:::
	[
          SerializationTest.tests;
	  OptsTest.tests
	])
