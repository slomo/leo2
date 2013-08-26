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
  let e_porduce_proof (szs:SZS.status) (output:string) =
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



let atp_mains =
  [("dummy", fun (st:state) ->
      IFDEF DEBUG THEN
        if !Util.debuglevel > 0 then
          begin
            let file_in = atp_infile st in
              Util.sysout 1 "*** The FO part:\n";
              ignore(Util.command("cat " ^ file_in));
              Util.sysout 1 "\n*** End of FO part\n";
          end;
      END;
      (false,[],"")
   );
   ("e",fun (st:state) ->
      Util.sysout 1 ("[E:"^(string_of_int st.flags.atp_timeout)^"s");
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
       let call_string = (prover ^ " " ^ options ^ " " ^ output_options) in
       let fo_clauses = get_fo_clauses st in
       IFDEF DEBUG THEN
         Util.sysout 5 ("\nCall string:"^call_string^"\n");
       END;
       (*FIXME replacing "ignore(Util.waitfor_spawn call_string);"
               with Sys.command below, due to issues on MacOSX*)
       IFDEF DEBUG THEN
         Util.sysout 1 ("\n**Sent to E**\n" ^ fo_clauses ^ "**(End of input to E)**\n");
       END;
       let res_string =
         let (inchan, outchan) = Unix.open_process call_string in
         let rev_content : string list ref = ref [] in
         let read_all () =
           try
             while true do
               rev_content := input_line inchan :: !rev_content
             done
           with
               End_of_file -> ()
         in
           output_string outchan fo_clauses;
           close_out_noerr outchan;
           read_all ();
           ignore(Unix.close_process (inchan, outchan));
           String.concat "\n" (List.rev !rev_content) ^ "\n"
       in
       IFDEF DEBUG THEN
         Util.sysout 1 ("]");
         Util.sysout 1 ("\n*** Result of calling first order ATP E on " ^ file_in ^ " for " ^
                          string_of_int st.flags.atp_timeout ^ " sec ***\n ");
         Util.sysout 1 res_string;
         Util.sysout 1 ("\n*** End of output from first-order ATP ***\n");
       END;
       Util.try_delete_file file_out_used_leoclauses;
       let result =
         Str.string_match (Str.regexp ".*SZS status Unsatisfiable.*") (eliminate_newlines res_string) 0 in
       (*
        let used_clauses =
         split (regexp "\n")
           (global_replace (regexp "[cnfo]*(.*\n") ""
            (global_replace (regexp "\\(.*\\)file(.*, *\\([0-9]*\\))\\(.*\\)") "\\2"
             res_string))
         in
       *)
       if result & (st.flags.proof_output > 1) then
        (
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
              (result, [e_empty_clause], res_string_modified)
        )
       else (result, [], "")
    );
    (*If run locally, use the CASC version of Princess because of the difference in semantics.*)
    ("casc_princess", fun st -> oracle_atp_call "casc_princess" ".*SZS status Unsatisfiable.*" "(CASC)Princess"
       ("-logo -timeout=" ^ string_of_int st.flags.atp_timeout ^ " -inputFormat=tptp +multiStrategy") true st);
    ("r_tofof", remote_atp_call "r_ToFoF" "ToFoF---0.1" ".*says Unsatisfiable.*" false);
    ("r_princess", remote_atp_call "r_(CASC)Princess" "Princess---120604" ".*says Unsatisfiable.*" false);
    ("r_vampire", remote_atp_call "r_Vampire" "Vampire---2.6" ".*says Unsatisfiable.*" false);
    ("r_tptp_isabelle_hot", remote_atp_call "r_tptp_isabelle HOT" "Isabelle-HOT---2012" ".*says Unsatisfiable.*" true);
    ("spass", fun (st:state) ->
       Util.sysout 1 ("[SPASS:"^(string_of_int st.flags.atp_timeout)^"s");
       let prover = try List.assoc "spass" !atp_cmds with
                    Not_found -> 
                      (
            set_current_success_status None Error;
                        Util.sysout 0 "\n\nNO EXECUTABLE FOR PROVER SPASS FOUND\n";
                        raise (Termination (Some st))
                      )
       in
       let file_in = atp_infile st in
       let file_out = atp_outfile st in
       let file_out_used_leoclauses = (atp_outfile st ^ "_used_clauses") in
       Util.register_tmpfiles [file_out; file_out_used_leoclauses];
       Util.sysout 1 ("SPASS(" ^ file_in ^ ")");
       flush stdout;
       let options = "-TPTP -PGiven=0 -PProblem=0 -DocProof -TimeLimit=" ^ string_of_int st.flags.atp_timeout in
       ignore(Util.command (prover ^ " " ^ options ^ " " ^ file_in ^ " > " ^ file_out));
       Util.sysout 1 ("]");
       Util.sysout 3 ("\n*** Result of calling first order ATP SPASS on " ^ file_in ^ " for " ^ string_of_int st.flags.atp_timeout ^ " sec ***\n ");
       let res_string = read_file file_out in
       let res =
         Str.string_match (Str.regexp ".*Proof found.*") (eliminate_newlines res_string) 0 in
       let used_clauses = [] in
       Util.sysout 3 res_string;
       Util.sysout 3 ("\n*** End of file " ^ file_out ^ " ***\n");
       Util.try_delete_file file_out;
       Util.try_delete_file file_out_used_leoclauses;
       (res, used_clauses, if res then res_string else "")
    );
    ("tptp_isabelle", fun st -> oracle_atp_call "tptp_isabelle"
       ".*SZS status Unsatisfiable.*" "tptp_isabelle"
       (string_of_int st.flags.atp_timeout) false st);
 (*FIXME is Gandalf still supported?
    ("gandalf", fun (st:state) ->
       Util.sysout 1 ("[Gandalf:"^(string_of_int st.flags.atp_timeout)^"s");
       let prover = try List.assoc "gandalf" !atp_cmds with
                    Not_found -> 
                      (
            set_current_success_status None Error;
                        Util.sysout 0 "\n\NO EXECUTABLE FOR PROVER GANDALF FOUND\n";
                        raise (Termination (Some st))
                      )
       in
       let file_in = atp_infile st in
       let file_out = atp_outfile st in
       Util.register_tmpfile file_out;
       Util.sysout 1 ("Gandalf(" ^ file_in ^ ")");
       flush stdout;
       let _ = Util.command (prover ^ " " ^ file_in ^ " > " ^ file_out) in
       Util.sysout 1 ("]");
       Util.sysout 2 ("\n*** Result of calling first order ATP Gandalf on  "^file_in^" ***\n ");
       let res_string = read_file file_out in
       Util.sysout 2 res_string;
       Util.sysout 2 ("\n*** End of file " ^ file_out ^ " ***\n");
       Util.try_delete_file file_out;
       let res =
         Str.string_match (Str.regexp ".*START OF PROOF.*") (eliminate_newlines res_string) 0 in
         (res, [], if res then res_string else ""));
 *)
    ("vampire", fun (st:state) ->
       Util.sysout 1 ("[Vampire:"^(string_of_int st.flags.atp_timeout)^"s");
       let prover = try List.assoc "vampire" !atp_cmds with
                    Not_found -> 
                      (
            set_current_success_status None Error;
                        Util.sysout 0 "\n\nWARNING: NO EXECUTABLE FOR PROVER VAMPIRE FOUND\n\n  SZS Error";
                        raise (Termination (Some st))
                      )
       in
       let file_in = atp_infile st in
       let file_out = atp_outfile st in
       Util.register_tmpfile file_out;
       Util.sysout 1 ("Vampire(" ^ file_in ^ ")");
       flush stdout;
       let _ = Util.command (prover ^ " --mode casc -t " ^ string_of_int st.flags.atp_timeout ^ " " ^ file_in ^ " > " ^ file_out) in
       Util.sysout 1 ("]");
       Util.sysout 2 ("\n*** Result of calling first order ATP Vampire on  " ^ file_in ^ " ***\n ");
       let res_string = read_file file_out in
       Util.sysout 2 res_string;
       Util.sysout 2 ("\n*** End of file " ^ file_out ^ " ***\n");
       Util.try_delete_file file_out;
       let res =
         Str.string_match (Str.regexp ".*Refutation found.*") (eliminate_newlines res_string) 0 in
         (res, [], if res then res_string else ""));
 (**
    ("spass",fun (st:state) ->
       let prover = try List.assoc "spass" (!atp_cmds) with
                    Not_found -> raise (Failure "SPASS Prover not configured yet")
       in
       let file_in = atp_infile st in
       let file_out = atp_outfile st in
       let file_in_2 = (!tmp_directory)^"/donotmoveme+rm_eq_rstfp.dfg" in
       Util.tmpfiles := file_out::(!Util.tmpfiles);
       Util.tmpfiles := ((!tmp_directory)^"/donotmoveme")::(!Util.tmpfiles);
       Util.tmpfiles := file_in_2::(!Util.tmpfiles);
       let tptp2x = try List.assoc "tptp2x" (!atp_cmds) with
                    Not_found -> raise (Failure "TPTP2X not configured yet")
       in
       Util.sysout 1 ("\n*** Using TPTP2X to translate "^file_in^" ***\n ");
 (*      Util.sysout 1 ("infile: "^file_in^"\noutfile: "^file_out^"\n"); *)
       flush stdout;
 (* This is a bad hack to avoid free variables: *)
       let _ = Sys.command ("sed -e 's/\\(.*\\)/\\L\\1/g' < "^file_in^" > "^file_in^"clean && mv "^file_in^"clean "^file_in) in


       let _ = Sys.command ("cp "^file_in^" "^(!tmp_directory)^"/donotmoveme") in
       let _ = Sys.command (tptp2x^" -f dfg -t rm_equality:rstfp -d "^(!tmp_directory)^" "^(!tmp_directory)^"/donotmoveme") in

       (* let filenamestart = try String.rindex st.origproblem_filename '/' with Not_found -> 0 in
       let filenamelength = (String.length st.origproblem_filename)-filenamestart in *)

       Util.sysout 1 ("\n*** TPTP2X translation written to file  "^file_in_2^" ***\n ");
       let _ = Sys.command ("cat "^file_in_2) in
       flush stdout;
       Util.sysout 1 ("[SPASS("^file_in_2^")");
       flush stdout;
       let _ = Sys.command ("sed -e 's/$false/false/g' < "^file_in_2^" > "^file_in_2^"clean && mv "^file_in_2^"clean "^file_in_2) in
       let _ = Sys.command (prover^" -DocProof "^file_in_2^" > "^file_out) in
       Util.sysout 2 ("\n*** Result of calling first order ATP SPASS on  "^file_in_2^" ***\n ");
       flush stdout;
       let res_string = read_file file_out in
       Util.sysout 2 res_string;
       Util.sysout 2 ("\n*** End of file "^file_out^" ***\n");
       flush stdout;
       Util.try_delete_file file_out;
       Util.try_delete_file ((!tmp_directory)^"/donotmoveme");
       Util.try_delete_file file_in_2;
       let res =
         Str.string_match (Str.regexp ".*Proof found.*") (eliminate_newlines res_string) 0 in
         (res,[])
    )
 **)
    ]

