let e =

  let e_init (st:State.state) (p:Subprover.prover) : Subporver.prover =
    p
  in

(*      Util.sysout 1 ("[E:"^(string_of_int st.flags.atp_timeout)^"s");
        let prover = try List.assoc "e" (!atp_cmds) with
        Not_found ->
	(
        set_current_success_status None Error;
	Util.sysout 0 "\n\nNO EXECUTABLE FOR PROVER E FOUND\n";
	raise (Termination (Some st));
	)
        in
        (* let epclextract = try List.assoc "epclextract" (!atp_cmds) with
        Not_found -> ""
        in *)
        let file_in = "PIPE" in
        let file_out_used_leoclauses = atp_outfile st ^ "_used_clauses" in
        Util.register_tmpfiles [file_out_used_leoclauses];
        IFDEF DEBUG THEN
        Util.sysout 1 ("E(" ^ file_in ^ ")")
        END;
        flush stdout;
        let output_options = (*E should not produce a proof if it's not needed*)
        if st.flags.proof_output > 1 then
        "-l 4 --tstp-format"
        else "-l 0" in
        let unix_options = if Sys.os_type = "Unix" then "--memory-limit=Auto" else "" in
        let options = "--tstp-in -xAuto -tAuto --cpu-limit=" ^
        string_of_int st.flags.atp_timeout ^ " " ^ unix_options in
        let call_string = (prover ^ " " ^ options ^ " " ^ output_options) in *)


  (* preprocessing for the e prover *)
  let e_pre (fo_formulars:string) : string =
    fo_formulars
  in

  (* post processing for the e prover *)
  let e_porduce_proof (szs:SZS.status, output:string) =
    Util.sysout 0 ("\n Trying to integrate the Proof Object of E into the LEO-II proof; this may take a while ...");
    let rec adjust_e_clause_identifiers num protocol_string =
      Util.sysout 3 ("\n Num :" ^ string_of_int num); Util.sysout 3 ("\n Hallo1 :" ^ protocol_string);
      let test =
        try let _ = search_forward (regexp "\\(c_[0-9]*_\\)\\([0-9]*\\)") protocol_string 0 in true
        with Not_found -> false in
      if test
      then
        let found1 = matched_group 1 protocol_string and
	    found2 = matched_group 2 protocol_string in
        adjust_e_clause_identifiers num
	  (replace_first (regexp_string (found1 ^ found2)) (string_of_int (num + (int_of_string found2)))
	     protocol_string)
      else protocol_string in
    let adjust_e_empty_clause_num num stringnum = string_of_int (num + (int_of_string stringnum)) in
    let _ = search_forward (regexp "[cnfo]*(.*,.*,.*, *c_[0-9]*_\\([0-9]*\\),.*proof.*") res_string 0 in
    let e_empty_clause = adjust_e_empty_clause_num st.clause_count (matched_group 1 res_string) in
    let res_string_modified =
      global_replace (regexp "[cnfo]*([c_0]*\\([0-9]*\\).*proof.*\n") ""
        (global_replace (regexp "\\(;\\[[,0-9]*\\), *theory(.*)\\([,0-9]*\\];\\)") "\\1\\2"
	   (global_replace (regexp "\\([cnfo]*(\\)\\([0-9]*\\)\\(.*,\\)\\(\\[[0-9]+.*\\]\\)\\())\\.\n\\)") "\\2;\\4;\\1\\2\\3\\4\\5"
	      (adjust_e_clause_identifiers st.clause_count
	         (global_replace (regexp "^ *\n\\|#.*\n") ""
		    (global_replace (regexp "\\(.*\\)file(.*, *\\([0-9]*\\))\\(.*\n\\)") "\\1inference(fof_translation, [status(thm)],[\\2])\\3"
		       res_string))))) in
    Util.sysout 1 ("\n res_string_modified: ");
    Util.sysout 1 res_string_modified;
    let protocolinfo_list =
      List.map (fun x ->
        (match x with
	  [numstr; numliststr; str] ->
	    (let _ = Util.sysout 1 ("\n hallo: " ^ numstr ^ " " ^ numliststr ^ " " ^ str) in
	     let helplist =
	       List.map (fun x -> let _ = Util.sysout 1 (" ns:" ^ x) in (int_of_string x, ""))
	         (split (regexp_string ",")
		    (global_replace (regexp_string "[") ""
		       (global_replace (regexp_string "]") "" numliststr))) in
	     ((int_of_string numstr), ("e", helplist, ""), str))
        | _ ->  let _ = Util.sysout 1 "E protocol failure 2" in raise (Failure "E protocol failure")))
        (List.map
	   (fun str -> split (regexp_string ";") str)
	   (split (regexp "\n") res_string_modified)) in
    let _ = List.map (fun p -> add_to_protocol p st) protocolinfo_list in
    let _ = set_clause_count st (int_of_string e_empty_clause) in
    ([e_empty_clause], res_string_modified) in
  (e_init, e_pre, e_porduce_proof)
in () ;;





