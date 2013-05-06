(* open Kaputt.Abbreviations 
open Szs


let () = 
  Test.add_simple_test
    ~title:"szs_read_status"
    ( fun () ->
      Assert.equal
        ( szs_read_status "% SZS status Unsatisfiable for SYN075+1" )
        Szs.UNS;
     
      Assert.equal
        ( szs_read_status "% SZS status GaveUp for SYN075+1" )
        Szs.CEQ
    )
*)

open OUnit;;
open Szs;;


let test_succ_status () =
  assert_equal Szs.UNS ( szs_read_status "% SZS status Unsatisfiable for SYN075+1" );
   assert_equal Szs.GUP ( szs_read_status "% SZS status GaveUp for SYN075+1" )
;;

let test_invalid_status () =
  assert_raises ~msg:"No InvalidSzsStatus exception thrown"
    (InvalidSzsStatus "No valid szs status")
    (fun () -> szs_read_status "% SZS status InvalidStatus for SYN004+1")

let test_empty_string () =
  assert_raises ~msg:"No InvalidSzsStatus exception thrown"
    (InvalidSzsStatus "No szs status line found")
    (fun () -> szs_read_status "")

let test_long_string () =
  let longstring = "some text, and even proof output might be here\r\n" ^
    "even more text\r\n" ^
    "% SZS status NoConsequence for this problem\r\n" ^
    "And even more proofoutput\r\n"
  in
  assert_equal Szs.NOC ( szs_read_status longstring ) 

let read_suite =

  "reading szs status form strings" >:::
    [
      "read sucessfull" >:: test_succ_status;
      "read invalid status" >:: test_invalid_status;
      "read emtpy string" >:: test_empty_string;
      "read from long string" >:: test_long_string;
    ]
;;


let test_deduct () =
  assert_bool "TAC is not a SAP" (szs_is_a TAC SAP)
;;

let test_deduct_fail () =
  assert_bool "TAC is not a FSA" (not (szs_is_a TAC FSA))
;;

let deduction_suite =

  "deducting with in the szs ontology" >:::
    [
      "deduct sucessfull" >:: test_deduct;
      "deduct uncessfull" >:: test_deduct_fail;
    ]
;;

let suite = 
   
  "all szs tests" >:::
    [
     read_suite; 
      deduction_suite;
    ]
    

let _ = 
  run_test_tt_main suite
;;
