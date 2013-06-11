open OUnit;;
open Subprover;;
open Str;;

let rec create_dummy_prover str =
  match Str.split (regexp " ")  str with
  | cmd :: args ->
    {
      Subprover.sp_type = Subprover.Folprover;
      path = cmd;
      name = "Dummyprover(" ^ str ^  ")";
      options = args
    }
  | [] ->
    create_dummy_prover "echo dummyProver"
;;


let test_prover_simple () =
  assert_equal "test"
    ( Subprover.subprover_wait_result
        ( Subprover.subprover_call
            ( create_dummy_prover "echo test" ) "input" ))
;;


let test_prover_long () =
  assert_equal "test"
    ( Subprover.subprover_wait_result
        ( Subprover.subprover_call
            ( create_dummy_prover "./helpers/test.sh 0.1 test" ) "input" ))
;;


let test_prover_checking () =
  let sp = Subprover.subprover_call ( create_dummy_prover "./helpers/test.sh 0.1 test" ) "input" in
  let rec wait_for_done called sp =
    if sp.Subprover.finished == true then (
        assert called;
        assert_equal (Subprover.subprover_fetch_result sp) "test"
      )
    else
      wait_for_done true (Subprover.subprover_update sp)
  in
  wait_for_done false sp

let suite =

  " tests" >:::
    [
      "simple prover call" >:: test_prover_simple;
      "longrunning prover call" >:: test_prover_long;
      "multiplem checks on subprover call" >:: test_prover_checking;
    ]
;;

let _ =
  run_test_tt_main suite
;;
