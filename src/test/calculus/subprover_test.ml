open OUnit;;
open Str;;
open Subprover;;

let rec create_dummy_prover str =
  match Str.split (regexp " ")  str with
  | cmd :: args ->
    {
      sp_type = Folprover;
      path = cmd;
      name = "Dummyprover(" ^ str ^  ")";
      options = args
    }
  | [] ->
    create_dummy_prover "echo dummyProver"
;;


let test_prover_simple () =
  assert_equal "test"
    ( wait
        ( start
            ( create_dummy_prover "echo test" ) "input" ))
;;


let test_prover_long () =
  assert_equal "test"
    ( wait
        ( start
            ( create_dummy_prover "./helpers/test.sh 0.1 test" ) "input" ))
;;


let test_prover_checking () =
  let sp = start ( create_dummy_prover "./helpers/test.sh 0.1 test" ) "input" in
  let rec wait_for_done called sp =
    if is_finished (sp) then (
        assert called;
        assert_equal (fetch_result sp) "test"
      )
    else
      wait_for_done true (update sp)
  in
  wait_for_done false sp


let fake_prover_wrapper (secs:int) (msg:string) : subprover =
  let secs_str = string_of_int(secs) in
  {
    sp_type = Folprover;
    path = "helpers/test.sh";
    name = "Dummyprover(" ^ secs_str ^ ", \"" ^ msg ^ "\")";
    options = [ secs_str; msg ]
  }


let fake_controller =
  init ~parrallel:2 [
    fake_prover_wrapper 3 "% SZS status Error for SYN075+1";
    fake_prover_wrapper 1 "# SZS status Success";
    fake_prover_wrapper 4 "% SZS status Success for SYN075+1"
  ]
;;


let controller_assert sc (a,b,c,d) =
  assert_equal
    ~printer: string_of_int
    ~msg: "Invalid number of waiting processes"
    a (List.length (sc.waiting));

  assert_equal
    ~printer: string_of_int
    ~msg: "Invalid number of running processes"
    b (List.length (sc.running));

  assert_equal
    ~printer: string_of_int
    ~msg: "Invalid number of finished processes"
    c (List.length (sc.finished));

  assert_equal
    ~printer: string_of_int
    ~msg: "Invalid number of solutions"
    d (List.length (get_solutions sc))


let test_controller_one_result () =
  let sc_started = perform_update ((add_problem "asdds") fake_controller) in
  Unix.sleep 2;
  let sc_next = perform_update sc_started in
  controller_assert sc_next (0,2,1,1);
  ignore (kill_all_provers sc_next)
;;

let test_controller_all_done () =
  let sc_started = perform_update ((add_problem "asdds") fake_controller) in
  Unix.sleep 2;
  let sc_next = perform_update sc_started in
  Unix.sleep 5;
  let sc_next = perform_update sc_next in
  controller_assert sc_next (0,0,3,2)
;;

let suite =
  "tests" >:::
    [
(*      "simple prover call" >:: test_prover_simple;
      "longrunning prover call" >:: test_prover_long;
      "multiplem checks on subprover call" >:: test_prover_checking; *)
      "test controller until one result" >:: test_controller_one_result;
      "test controller wait for all" >:: test_controller_all_done
  ]
;;

let _ =
  run_test_tt_main suite
;;
