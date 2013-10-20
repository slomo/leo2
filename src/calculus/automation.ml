(* ========================================================================= *)
(* Automation                                                                *)
(* ========================================================================= *)

(** Module Automation implements the main reasoning loop of LEO-II
    -- Strongly Preliminary Version --
    @author Chris
    @since 07-03-07*)

open Literal
open Clause
open Clauseset
open State
open Main
open Calculus
open Str

let rec compose (rl:(cl_clause list -> state -> cl_clause list) list) =
  match rl with
     [] -> (fun (cll:cl_clause list) (st:state) -> cll)
   | hd::tl -> (fun (cll:cl_clause list) (st:state) -> ((compose tl) (hd cll st) st))

let raise_to_list (r:(cl_clause -> state -> cl_clause list)) (cll:cl_clause list) (st:state) =
  List.flatten
    (List.map
       (fun cl ->
	 let res = r cl st in
	 (* output st (fun () -> ("\n Step: "^(cl_clauselist_to_protocol res))); *)
	 res)
       cll)


let combine (r1:(cl_clause -> state -> cl_clause list)) (r2:(cl_clause -> state -> cl_clause list)) =
  fun (cl:cl_clause) ->
    fun (st:state) -> ((r1 cl st)@(r2 cl st))


let exhaustive_to_bound (bound:int) (r:(cl_clause list -> state -> cl_clause list)) (cll:cl_clause list) (st:state) =
  let rec exhaustive_to_bound' r cll st bound depth =
    try
      let cl_count_before = st.clause_count in
      let res = (r cll st) in
      if cl_count_before = st.clause_count || (depth > bound)
      then res
      else exhaustive_to_bound' r res st  bound (depth + 1)
    with
    | Failure str -> Util.sysout 0 ("***** Failure "^str^" *****"); raise (Failure str)
  in
  exhaustive_to_bound' r cll st bound 1

let rec exhaustive (r:(cl_clause list -> state -> cl_clause list)) (cll:cl_clause list) (st:state) =
  try
    State.check_timeout ();
    let cl_count_before = st.clause_count in
    let result = (r cll st) in
    if cl_count_before = st.clause_count
    then result
    else exhaustive r result st
  with
  | Failure str -> Util.sysout 0 ("***** Failure "^str^" *****"); raise (Failure str)



(** Extensional Pre-Unification *)


(*
let unify_alt (cl:cl_clause) (st:state) =
  compose
    [exhaustive_to_bound st.flags.max_uni_depth
       (compose
	  [(exhaustive_to_bound st.flags.max_uni_depth
	      (compose
		 [exhaustive (raise_to_list trivial);
       		  exhaustive (raise_to_list flex_rigid);
		  exhaustive_to_bound st.flags.max_uni_depth
		    (raise_to_list functional_ext);
		  exhaustive (raise_to_list decompose)]));
	   (exhaustive (raise_to_list subst_or_clash))]);
     exhaustive (raise_to_list boolean_ext)]
    [cl] st
*)


(*
  match
  let proc_2 = exhaustive (raise_to_list boolean_ext) proc_1 st in
  let proc_3 = exhaustive (raise_to_list decompose) proc_1 st in
  let proc_4 = exhaustive (raise_to_list boolean_ext) proc_3 st in
  (proc_2@proc_4@(func_bool_neg proc_4 st))
*)


(*
let unify_not_so_alt (cl:cl_clause) (st:state) =
  output st (fun () -> ("\n\  UNI: "^(cl_clause_to_protocol cl)));
  let result =
    (func_bool_neg [cl] st)
    @(compose
	[exhaustive_to_bound st.flags.max_uni_depth  (*needed?*)
	   (compose
	      [exhaustive (raise_to_list trivial);
	       exhaustive_to_bound st.flags.max_uni_depth
		 (raise_to_list flex_rigid);
	       exhaustive (raise_to_list functional_ext);
	       exhaustive (raise_to_list decompose)]);
	 exhaustive (raise_to_list subst_or_clash)]
	[cl] st)
  in
  output st (fun () -> ("  UNI-RESULT: "^(cl_clauselist_to_protocol result)^"\n"));
  result
*)


(*
let unify (cl:cl_clause) (st:state) =
   (compose
     [exhaustive
	(compose
	   [exhaustive (raise_to_list trivial);
	    exhaustive (raise_to_list flex_rigid);
	    exhaustive (raise_to_list functional_ext);
	    exhaustive (raise_to_list decompose);
	    exhaustive (raise_to_list subst_or_clash)]);

    [cl] st
*)

(*
let unify_pre (cl:cl_clause) (st:state) =
  output st (fun () -> ("\n\  UNI-PRE: "^(cl_clause_to_protocol cl)));
  let result =
    (compose
       [exhaustive_to_bound st.flags.max_uni_depth  (*needed?*)
	  (compose
	     [exhaustive (raise_to_list trivial);
	      exhaustive_to_bound st.flags.max_uni_depth (raise_to_list flex_rigid);
	      exhaustive (raise_to_list func_uni);
	      exhaustive (raise_to_list decompose)]);
	exhaustive (raise_to_list (combine subst_or_clash boolean_ext))]
       [cl] st)
  in
  output st (fun () -> ("  UNI-PRE-RESULT: "^(cl_clauselist_to_protocol result)^"\n"));
  result
*)

(*
let unify_pre_ext (cl:cl_clause) (st:state) =
  let remove_duplicates (cll:cl_clause list) =
    match cll with
       [] -> []
     | hd::tl -> (hd::(List.filter (fun cl -> (not (cl.cl_number = hd.cl_number))) tl))
  in
  output st (fun () -> ("\n\  UNI-PRE: "^(cl_clause_to_protocol cl)));
  let result =
    remove_duplicates
      (exhaustive_to_bound st.flags.max_uni_depth  (*needed?*)
	 (raise_to_list
	    (combine
	       (combine
		  (combine
		     (combine
			trivial
			functional_ext)
		     decompose)
	       boolean_ext)))
	 [cl] st)
  in
  output st (fun () -> ("  UNI-PRE-RESULT: "^(cl_clauselist_to_protocol result)^"\n"));
  result
*)



let unify_pre_ext_old (cl:cl_clause) (st:state) =
  Util.sysout 2 ("\n\  UNI-PRE: "^(cl_clause_to_protocol cl));
  let result =
    exhaustive_to_bound st.flags.max_uni_depth  (*needed?*)
      (raise_to_list
	 (combine
	    (combine
	       (combine
		  (combine
		     trivial
		     functional_ext)
		  decompose)
	       subst_or_clash)
	    boolean_ext))
      [cl] st
  in
  Util.sysout 2 ("  UNI-PRE-RESULT: "^(cl_clauselist_to_protocol result)^"\n");
  result



(* version from 25.7.2007 *)

let unify_pre_ext (cl:cl_clause) (st:state) =
  Util.sysout 3 ("\n\  UNIFY_PRE_EXT: "^(cl_clause_to_protocol cl));
  let result = pre_unify cl st in
    Util.sysout 3 ("  UNI_PRE_EXT_RESULT: "^(cl_clauselist_to_protocol result)^"\n");
    result


(** Subsumption *)

type subsumption_mode =
    Trivial
  | FO_match

let is_subsumed_by (cl : cl_clause) (cll : cl_clause list) (st : state) (flag : subsumption_mode) =
  let subsumption_check_fn =
    match flag with
        Trivial -> (fun c -> triv_subsumes c cl)
      | FO_match -> (fun c -> fo_match_subsumes c cl st) in
  let result = List.exists subsumption_check_fn cll
  in
    Util.sysout 3 ("\n   " ^ cl_clause_to_protocol cl ^ " is_subsumed_by " ^
                     cl_clauselist_to_protocol cll ^ ": " ^ string_of_bool result);
    result



let delete_subsumed_clauses (cll : cl_clause list) (cl : cl_clause) (st : state) (flag : subsumption_mode) =
    let subsumption_check_fn =
      match flag with
          Trivial -> (fun c -> (not (triv_subsumes cl c)))
	| FO_match -> (fun c -> (not (fo_match_subsumes cl c st)))
    in List.filter subsumption_check_fn cll


let merge_lists_with_subsumption (cll1 : cl_clause list) (cll2 : cl_clause list) (st : state) (flag : subsumption_mode) =
  let rec help (cll1 : cl_clause list) (cll2 : cl_clause list) (st : state) (flag : subsumption_mode) =
    match cll1 with
	[] -> cll2
      | hd :: tl ->
          if is_subsumed_by hd cll2 st flag then
            help tl cll2 st flag
          else
            help tl (hd :: delete_subsumed_clauses cll2 hd st flag) st flag in
    Util.sysout 3 ("\nmerge_lists_with_subsumption: \n list1: "^(cl_clauselist_to_protocol cll1)^"\n list2: "^(cl_clauselist_to_protocol cll2));
    let result = help cll1 cll2 st flag in
      Util.sysout 3 ("\n result: "^(cl_clauselist_to_protocol result));
      result

(** FO ATP Config **)
(* maybe to be exported to a file "atpconfig.ml" *)

let tmp_directory = Util.tmp_path

let atp_infile (st: state) =
  let fn =
    if Sys.file_exists st.origproblem_filename
    then !tmp_directory ^ "/" ^ Filename.basename st.origproblem_filename ^ ".atp_in"
    else !tmp_directory ^ "/atp_in" in
  (* Util.sysout 0 ("\n ATP-IN-FILE: "^fn^"\n"); *)
  fn

let atp_outfile (st: state) =
  let fn =
    if Sys.file_exists st.origproblem_filename
    then !tmp_directory ^ "/" ^ Filename.basename st.origproblem_filename ^ ".atp_out"
    else !tmp_directory ^ "/atp_out" in
  (* Util.sysout 0 ("\n ATP-OUT-FILE: "^fn^"\n"); *)
  fn

let atp_default_cmds =
  [("tptp2x", "tptp2X");
   ("e", "eprover");
   ("epclextract", "epclextract");
   ("spass", "SPASS");
   ("vampire", "vampire")]

let atp_version_parameters =
  [("e", "--version")]

let atp_config_file =
  ref (try (Sys.getenv "HOME" ^ "/.leoatprc")
       with Not_found -> !Util.tmp_path ^ "/.leoatprc")


(* FIXME: make tis avaible somewhere else
let read_atp_config () =
  if not !atp_configured then
    begin
      Util.sysout 1 "*** Reading ATP config file...";
      try
        let commands = Hashtbl.create 5 in
        let file = open_in !atp_config_file in
        let eof = ref false in
          while not !eof do
            try
              let next = input_line file in
              let matched = Str.string_match (Str.regexp "^\\([a-z_]+\\)[ ]*=[ ]*\\(.+\\)\\([ ]*#.*\\)?$") next 0
              in
                if matched then
                  let name = Str.matched_group 1 next in
                  let path = Str.matched_group 2 next
                  in Hashtbl.replace commands name path
            with End_of_file -> eof := true
          done;
          Hashtbl.iter (fun x y -> (Util.sysout 1 ("  Configured: " ^ x ^ " = " ^ y ^ "\n"))) commands;
          atp_cmds := Hashtbl.fold (fun a b c -> (a, b) :: c) commands [];
          close_in file;
          atp_configured := true;
          Util.sysout 1 "*** ATPs configured."
      with Sys_error s ->
        Util.sysout 1 ("\n *** Could not open configuration file:" ^ s ^ "\n")
    end
  else Util.sysout 1 "\n *** ATPs already configured.\n"
*)

(* FIXME: implement this in subprover
let atp_versions () =
  let ask_version (prover_name, prover_path) =
    try
      let version_param = List.assoc prover_name atp_version_parameters
      in
        Util.sysout 0 (prover_name ^ ": ");
        ignore(Util.command(prover_path ^ " " ^ version_param));
    with
      Not_found ->
        Util.sysout 0 (prover_name ^
         ": (Don't know how to get version information)\n")
  in
    read_atp_config ();
    List.iter ask_version !atp_cmds *)

let read_file name =
  let file = open_in name in
  let size = in_channel_length file in
  let buf = String.create size in
    begin
      try really_input file buf 0 size
      with exc ->
        begin try close_in file with _ -> () end;
        raise exc
    end;
    close_in file;
    buf

(*Eliminates \n to facilitate searching using regex*)
let eliminate_newlines s =
  Str.global_replace (Str.regexp "\n") " " s

(*Runs an ATP and trusts its (positive) output, by relying on a spotted string.
  The parameters consist of:
         desired_prover : prover who's binary to look up
      friendly_atp_name : ATP name to use in logging (could be same as desired_prover)
         success_string : which string signals success
                   args : argument string to pass to the prover
            null_stderr : whether prover's STDERR output should be ignored
                          (some provers print status information to STDERR)
                     st : Leo's state*)
(*let oracle_atp_call desired_prover success_string friendly_atp_name args null_stderr st =
  Util.sysout 1 ("[" ^ friendly_atp_name ^ ":"^ string_of_int st.flags.atp_timeout ^"s");
  let prover = try List.assoc desired_prover !atp_cmds with
      Not_found ->
        begin
          set_current_success_status (Some st) Error;
          Util.sysout 0 ("\n\nNO EXECUTABLE FOR PROVER " ^ desired_prover ^ " FOUND\n");
          raise (Termination (Some st))
        end in
  let file_in = atp_infile st in
  let file_out = atp_outfile st in
  let drop_stderr = if null_stderr then " 2> /dev/null" else "" in
  let file_out_used_leoclauses = (atp_outfile st ^ "_used_clauses") in
    Util.register_tmpfiles [file_out; file_out_used_leoclauses];
    Util.sysout 1 ("(" ^ file_in ^ ")");
    flush stdout;
    ignore(Util.command (prover ^ " " ^ args ^ " " ^ file_in ^ " > " ^ file_out ^ drop_stderr));
    Util.sysout 1 ("]");
    Util.sysout 3 ("\n*** Result of calling " ^ desired_prover ^ " on " ^ file_in ^
                     " for " ^ string_of_int st.flags.atp_timeout ^ " sec ***\n ");
    let result_contents = read_file file_out in
    let result =
      Str.string_match (Str.regexp success_string) (eliminate_newlines result_contents) 0 in
    let used_clauses = []
    in
      Util.sysout 3 result_contents;
      Util.sysout 3 ("\n*** End of file " ^ file_out ^ " ***\n");
      Util.try_delete_file file_out;
      Util.try_delete_file file_out_used_leoclauses;
      (result, used_clauses, if result then result_contents else "")
*)
(*Runs an ATP on SystemOnTPTP via RemoteSOT script.
  The parameters consist of:
               atp_name : friendly name of ATP
    system_on_tptp_name : the name of the ATP as recognised by SystemOnTPTP
         success_string : which string signals success
                  force : force "inadequate" prover (i.e. where we know that
                           the prover might support certain features)
                     st : Leo's state*)
(*
let remote_atp_call atp_name system_on_tptp_name success_string force (st : state) =
  let args =
    let pre_args = "-s" ^ system_on_tptp_name ^ " -t" ^ string_of_int st.flags.atp_timeout
    in if force then pre_args ^ " -f" else pre_args
  in oracle_atp_call "remote_sot" success_string atp_name args false st
*)


let supported_atps = List.map fst Parallel.default_subprovers ;;

(*let get_atp_main prover = try List.assoc prover atp_mains with
     Not_found -> raise (Failure ("There is no ATP named " ^ prover ^ ".\n" ^
                   "Currently the following provers are available:\n" ^
                   (match atp_mains with
                        (p1, _) :: (p2 :: pr) -> List.fold_left (fun a (b, _) -> b ^ ", " ^ a) p1 (p2 :: pr)
                      | [(p1, _)] -> p1
                      | _ -> "")))
*)

 (** Call FO ATP *)

 let atp_times = ref []

 let add_atp_time (fl:float) (str:string) =
   (* Util.sysout 1 ("\n Adding entry ("^(string_of_float fl)^","^str^"\n");*)
   atp_times := (fl, str) :: !atp_times;
   ()

 let get_atp_times () = !atp_times

 let memorize_execution_time (name:string) (prover:string) (loop:int) (fn: state -> (bool * ('a list) * string)) (st:state) =
   let tm1 = Unix.gettimeofday () in
   let res = fn st in
   let tm2 = Unix.gettimeofday () in
   let exec_time = (tm2 -. tm1) in
   let proc_string = (name ^ "(" ^ prover ^ "-loop-" ^ string_of_int loop ^ ")") in
   (* Util.sysout 0 ("\n Process time for "^proc_string^": "^(string_of_float exec_time)^"\n"); *)
   add_atp_time exec_time proc_string;
   res


 (*Calls an FO ATP on the translated formulas, and interprets the
   ATP's output.*)

 (* FIXME:

    * here goes the very ugly hack
    * later the subprover manager should be given here from state
    * for now i am setting a subprover controller here

 *)


 let call_fo_atp_help (st:state) (prover:string) 
     (candidate_clauses:cl_clause list) : unit =

   (*  *)
   let candidate_clauses_numbers_and_strings =
     List.map (fun cl -> (cl.cl_number, "")) candidate_clauses
   in
   
   begin

     Translation.tr_add_fo_clauses candidate_clauses st;
     
     st.foatp_calls <- st.foatp_calls + 1;

       (* if there are new fo-formulars add them *)
     if not !Translation.next_atp_call_is_redundant then
       Parallel.submit_problem st;

     let (result, used_clauses, protocol) =
       Parallel.tick st;
       Parallel.collect_solution st

       (*                 memorize_execution_time st.origproblem_filename
                          "atp" st.loop_count apply_prover st *)
     in
       (* Util.try_delete_file file_in; *)
     match (result, used_clauses) with
       (true, []) ->
           (*The external prover didn't require to use any specific clauses to
             prove the result*)
         ignore(mk_clause [] (inc_clause_count st) []
                  ("fo_atp_" ^ prover, candidate_clauses_numbers_and_strings, "")
                  DERIVED st)
     | (true, cl_list) ->
         (*Link the specific clauses used by the external prover with the
           conclusion it derived*)
       let clauses_number_and_strings =
         List.map (fun intstr -> (int_of_string intstr, "")) cl_list
       in
       ignore(mk_clause [] (inc_clause_count st) []
                ("fo_atp_" ^ prover, clauses_number_and_strings, "") DERIVED st)
     | (false, _) -> ()
   end

let call_fo_atp_early (st:state) (prover:string) =
  match st.problem_stack with
      [cl] ->
	let candidate_clauses = ([cl]@st.problem_axioms) in
       (* let _ = index_clauselist_with_role candidate_clauses st in *)
       (* let expanded_candidate_clauses = (raise_to_list expand_nonlogical_defs) candidate_clauses st in *)
       (* let _ = index_clauselist_with_role expanded_candidate_clauses st in *)
	let remember = st.flags.fo_translation in
	let _ = set_flag_fo_translation st "simple" in
	let res = call_fo_atp_help st prover candidate_clauses in
	let _ = set_flag_fo_translation st remember in
	  res
    | _ -> ()

let call_fo_atp (st:state) (provers:string list) =
  let prover = List.hd(provers) in
  let candidate_clauses =
    Set_of_clauses.elements (Set_of_clauses.union st.active st.passive) in
  let time_left =
    (*if we've forced an ATP timeout then regard it*)
    match State.global_conf.atp_timeout_forced with
        None -> int_of_float (State.time_remaining_of_schedule ())
      | Some x -> x in
  let start_time = Unix.gettimeofday () in
    if time_left > 0 then (*otherwise ATP will be given negative time!*)
      (*shrink ATP timeout in case it would exceed this schedule's duration*)
      if State.state_initialize.flags.atp_timeout > time_left then
        ignore(State.set_flag_atp_timeout State.state_initialize time_left);

      call_fo_atp_help st prover candidate_clauses;
      State.child_time := !State.child_time +. (Unix.gettimeofday () -. start_time)

let call_fo_atp_according_to_frequency_flag (st:state) (prover:string) =
  if
    let test =
      st.loop_count > 0 &
      (not (st.flags.atp_provers = [])) &
      (Int32.rem (Int32.of_int st.loop_count) (Int32.of_int st.flags.atp_calls_frequency)) = Int32.of_int 0
    in
      Util.sysout 2 ("\n\n\nREM: " ^ string_of_int st.loop_count ^ " " ^ string_of_int st.flags.atp_calls_frequency ^
        " : " ^ string_of_bool test ^ "\n\n\n");
      test
  then call_fo_atp st [prover]
  else ()



(** Pre-Processing **)

(*
let clause_derived_from_clause_by_unfold (cl1:cl_clause) (cl2:cl_clause) =
  match cl1.cl_info with
      ("unfold_def",([num,_]),"") -> num = cl2.cl_number
    | _ -> false

let unfold_defs_stack (st:state) =
  let replace_unfolded_clauses_in_clauselist  (list:cl_clause list) (unfolded:cl_clause list) =
    List.map
      (fun cl ->
        let unfolded_from_cl = (List.find_all (fun unfold_cl -> clause_derived_from_clause_by_unfold unfold_cl cl) unfolded) in
          match unfolded_from_cl with
              [] -> cl
            | [u_cl] -> u_cl
            | _ -> raise (Failure "unfold_defs_stack"))  (* ecactly one unfold clause is asssumed for cl *)
      list in
  let (_,_,unfold_clauses) = unfold_defs_exhaustively st
  in
    set_problem_axioms st (replace_unfolded_clauses_in_clauselist st.problem_axioms unfold_clauses);
    set_problem_stack st (replace_unfolded_clauses_in_clauselist st.problem_axioms unfold_clauses);
    set_active st Set_of_clauses.empty;
    set_passive st Set_of_clauses.empty;
    st
*)

(*
 let replace_unfolded_clauses_in_clauselist  (list:cl_clause list) (unfolded:cl_clause list) =
   let clause_derived_from_clause_by_unfold (cl1:cl_clause) (cl2:cl_clause) =
     match cl1.cl_info with
         ("unfold_def",([num,_]),"") -> num = cl2.cl_number
       | _ -> false
   in
     List.map
       (fun cl ->
         let unfolded_from_cl = (List.find_all (fun unfold_cl -> clause_derived_from_clause_by_unfold unfold_cl cl) unfolded) in
           match unfolded_from_cl with
               [] -> cl
             | [u_cl] -> u_cl
             | _ -> raise (Failure "unfold_defs_stack"))  (* ecactly one unfold clause is asssumed for cl *)
       list
*)

(*
 let pre_process_1_with_stack (st:state) =
   let (_,oldclauses,unfold_clauses) = unfold_defs_exhaustively st in
     output st (fun () -> ("\n0a. Defs: "^(cl_clauselist_to_protocol unfold_clauses)));
     let res_unfold_problem_stack =
       replace_unfolded_clauses_in_clauselist st.problem_stack unfold_clauses
     and res_unfold_problem_axioms =
       replace_unfolded_clauses_in_clauselist st.problem_axioms unfold_clauses
     in
       set_problem_stack st res_unfold_problem_stack;
       set_problem_axioms st res_unfold_problem_axioms;
       set_active st Set_of_clauses.empty;
       set_passive st Set_of_clauses.empty;
       st
*)

let pre_process_1 (st:state) =
  let (_,oldclauses,unfold_clauses) = unfold_defs_exhaustively st in
  output st (fun () -> ("\n0a. Defs: "^(cl_clauselist_to_protocol unfold_clauses)));
  let res_init_unfold =
    (Set_of_clauses.elements
       (Set_of_clauses.union (list_to_set unfold_clauses)
    (Set_of_clauses.diff (Set_of_clauses.union st.active st.passive) (list_to_set oldclauses)))) in
  List.iter (fun cl -> remove_from_active st cl) oldclauses;
  List.iter (fun cl -> remove_from_passive st cl) oldclauses;
  let res_init =
    exhaustive (raise_to_list cnf_normalize_step) res_init_unfold st in
  index_clear_all_roles st;
  index_clauselist_with_role res_init st;
  set_active st (list_to_set res_init);
  set_passive st Set_of_clauses.empty;
  res_init


(*
let pre_process_2_bla (st:state) =
  let clauses = (Set_of_clauses.elements  st.active) in
  let primsubst_clauses = (raise_to_list prim_subst) clauses st in
  let processed =
    exhaustive
      (compose
         [
          (raise_to_list simplify);
          (raise_to_list unify_pre_ext);
          (raise_to_list factorize_restricted);
          (raise_to_list functional_ext_pos);
          (raise_to_list boolean_ext_pos);
          exhaustive (raise_to_list cnf_normalize_step);
        ]) (primsubst_clauses@clauses) st in
  index_clauselist_with_role processed st;
  set_active st (list_to_set processed);
  set_passive st Set_of_clauses.empty;
  processed
*)


let pre_process_2 (st:state) =
  let pre_clauses1 = (Set_of_clauses.elements  st.active) in
  let pre_clauses2 = if st.flags.use_choice then (raise_to_list detect_choice) pre_clauses1 st else pre_clauses1 in
  let pre_clauses3 = if st.flags.use_choice then  exhaustive (raise_to_list cnf_normalize_step) ((raise_to_list apply_choice) pre_clauses2 st) st else pre_clauses2 in
  let pre_clauses4 = if st.flags.replace_leibnizEQ then (raise_to_list replace_leibniz_lits) pre_clauses3 st else pre_clauses3 in
  let clauses      = if st.flags.replace_andrewsEQ then (raise_to_list replace_andrews_lits) pre_clauses4 st else pre_clauses4 in
  (*let primsubst_clauses = (raise_to_list prim_subst) clauses st in *)
  let primsubst_clauses = primsubst_new clauses st in
  let factorized_clauses = (raise_to_list factorize_restricted) clauses st in
  let processed_a =
    compose
      [
        exhaustive
          (compose
             [
              (raise_to_list functional_ext_pos);
              (raise_to_list boolean_ext_pos);
              exhaustive (raise_to_list cnf_normalize_step)
            ]);
        (raise_to_list unify_pre_ext);
        exhaustive (raise_to_list cnf_normalize_step)
      ]
      (factorized_clauses@clauses) st in
    Util.sysout 2 ("\n PROCESSED_A: " ^ cl_clauselist_to_protocol processed_a);
    if (not (st.flags.atp_provers == [])) then call_fo_atp st st.flags.atp_provers else ();
  let processed_b =
    compose
      [
        exhaustive
          (compose
             [
               (raise_to_list functional_ext_pos);
               (raise_to_list boolean_ext_pos);
               exhaustive (raise_to_list cnf_normalize_step)
             ]);
        (raise_to_list unify_pre_ext)
      ]
      (primsubst_clauses) st in
  let processed = processed_a@processed_b
  in

  let simplified = ((raise_to_list simplify) (clauses@processed) st) in
    index_clauselist_with_role simplified st;
    set_active st (list_to_set simplified);
    set_passive st Set_of_clauses.empty;
    processed

(*
    index_clauselist_with_role processed st;
    set_active st (list_to_set ((raise_to_list simplify) (clauses@processed) st));
    set_passive st Set_of_clauses.empty;
    processed
*)

(*
let pre_process_2_alt (st:state) =
  let clauses = (Set_of_clauses.elements  st.active) in
  let ext_clauses =
    let cll1 = (raise_to_list functional_ext_pos) clauses st in
    let cll2 = (raise_to_list boolean_ext_pos) clauses st in
    let cll3 = exhaustive (raise_to_list cnf_normalize_step) (cll1@cll2) st in
    let cll4 = (raise_to_list simplify) cll3 st in
    cll4 in
  let prim_subst_clauses =
    let cll1 = (raise_to_list prim_subst) clauses st in
    let cll2 = exhaustive (raise_to_list cnf_normalize_step) cll1 st in
    let cll3 = (raise_to_list simplify) cll2 st in
    cll3 in
  let factorized_clauses =
    let cll1 = (raise_to_list factorize_restricted) (clauses@ext_clauses@prim_subst_clauses) st in
    let cll2 = (raise_to_list unify_pre_ext) cll1 st in
    let cll3 = (raise_to_list simplify) cll2 st in
    cll3 in
  let res_clauses = (clauses@ext_clauses@prim_subst_clauses@factorized_clauses) in

(*    compose
      [
       (raise_to_list unify_pre_ext);
       exhaustive (raise_to_list cnf_normalize_step);
       exhaustive (raise_to_list simplify)
     ]
      (clauses@prim_subst_clauses@factorized_clauses) st in *)

  index_clauselist_with_role res_clauses st;
  set_active st (list_to_set res_clauses);
  set_passive st Set_of_clauses.empty;
  res_clauses
*)


let pre_process (st:state) =
  let _ = pre_process_1 st in
    if (not (st.flags.atp_provers == [])) then call_fo_atp st st.flags.atp_provers else ();
    let _ = pre_process_2 st in
      if (not (st.flags.atp_provers == [])) then call_fo_atp st st.flags.atp_provers else ();
      let result = (Set_of_clauses.elements st.active) in
  (* List.iter (fun cl -> set_clause_weight cl 1) result; *)
  result

(*The Main Loop*)
let loop (st:state) =
  IFDEF DEBUG THEN Util.sysout 1 ("<StartLooping>") ENDIF;
  try
    while not (check_local_max_time st) do
      let lc = inc_loop_count st
      in
        State.check_timeout ();
        IFDEF DEBUG THEN output st (fun () -> "\n\n *** NEW LOOP: " ^ string_of_int lc ^ " ***\n") ENDIF;
        if st.flags.max_loop_count > 0 && st.loop_count >= st.flags.max_loop_count then
          begin
            (*FIXME could elaborate the reason why GaveUp*)
            set_current_success_status (Some st) GaveUp;
            raise MAX_LOOPS
          end;
        if not (st.flags.atp_provers == []) then call_fo_atp_according_to_frequency_flag st (List.hd st.flags.atp_provers);
        let lightest' =
          let lightest = choose_and_remove_lightest_from_active st in
            IFDEF DEBUG THEN
              output st
              (fun () ->
                 "\n1. LIGHTEST: " ^ cl_clause_to_protocol lightest ^
                   "\n1  ACTIVE: " ^ cl_clauselist_to_protocol (Set_of_clauses.elements st.active));
              Util.sysout 2 ("[" ^ string_of_int lc ^ "-" ^ string_of_int lightest.cl_number ^ "] ");
            ENDIF;
            rename_free_variables lightest st
        in
          if not (is_subsumed_by lightest' (Set_of_clauses.elements st.passive) st FO_match)
            & (if st.flags.use_choice then (match detect_choice lightest' st with [] -> false | _ -> true) else true)
          then
            begin
              set_passive st (list_to_set (delete_subsumed_clauses (Set_of_clauses.elements st.passive) lightest' st FO_match));
	      add_to_passive st lightest';
              (* set_passive st (list_to_set (merge_lists_with_subsumption [lightest'] (Set_of_clauses.elements st.passive) st FO_match)); *)
              (* add_to_passive st lightest'; *)
              IFDEF DEBUG THEN
                output st (fun () -> "\n2. PASSIVE: " ^ cl_clauselist_to_protocol (Set_of_clauses.elements st.passive));
              ENDIF;

              let res_resolve =
                List.fold_right
                  (fun cl cll -> resolve lightest' cl st @cll) (Set_of_clauses.elements st.passive) [] in
              IFDEF DEBUG THEN
                output st (fun () -> "\n3. RES: " ^ cl_clauselist_to_protocol res_resolve);
              ENDIF;

              let res_prim_subst = (raise_to_list prim_subst) [lightest'] st
              and res_pos_bool = (raise_to_list boolean_ext_pos_main_loop) [lightest'] st
              and res_fac_restr = (raise_to_list factorize_restricted) [lightest'] st
              and res_choice = if st.flags.use_choice then (exhaustive (raise_to_list cnf_normalize_step) ((raise_to_list apply_choice) [lightest'] st) st) else [] in
              IFDEF DEBUG THEN
                output st (fun () -> "\n4. PRIM_SUBST: " ^ cl_clauselist_to_protocol res_prim_subst);
                output st (fun () -> "\n5. BOOL_POS: " ^ cl_clauselist_to_protocol res_pos_bool);
                output st (fun () -> "\n6. FAC_RESTR: " ^ cl_clauselist_to_protocol res_fac_restr);
                output st (fun () -> "\n7. CHOICE: " ^ cl_clauselist_to_protocol res_choice);
              ENDIF;
              
              let res_processed_pre_pre =  (res_resolve @ res_prim_subst @ res_pos_bool @ res_fac_restr @ res_choice) in

              let res_processed_pre =
                compose
                  [raise_to_list unify_pre_ext;
                   exhaustive (raise_to_list cnf_normalize_step);
                   exhaustive (raise_to_list simplify)]
                   res_processed_pre_pre st in
              IFDEF DEBUG THEN
                output st (fun () -> "\n8. PROCESSED_PRE: " ^ cl_clauselist_to_protocol res_processed_pre);
              ENDIF;

            let res_processed_pre_leibniz =
              if st.flags.replace_leibnizEQ then exhaustive (raise_to_list replace_leibniz_lits) res_processed_pre st else res_processed_pre in
            let res_processed_pre_andrews =
              if st.flags.replace_andrewsEQ then exhaustive (raise_to_list replace_andrews_lits) res_processed_pre_leibniz st else res_processed_pre_leibniz in
            let res_processed = res_processed_pre_andrews in
                
            IFDEF DEBUG THEN
              output st (fun () -> "\n9. PROCESSED (replacement of LeibnizEQ and AndrewsEQ eventually applied): " ^ cl_clauselist_to_protocol res_processed);
            ENDIF;

            let new_active = (res_processed @ Set_of_clauses.elements st.active) in
              (* merge_lists_with_subsumption (res_processed) (Set_of_clauses.elements st.active) st FO_match in *)

            index_clauselist_with_role new_active st;
            set_active st (list_to_set new_active);
            IFDEF DEBUG THEN
              output st (fun () -> "\n10. ACTIVE: " ^ cl_clauselist_to_protocol (Set_of_clauses.elements st.active));
            ENDIF;
          end
    done;
    Parallel.final_tick st
  with
      Sys.Break ->
        Parallel.final_tick st;
        set_current_success_status (Some st) User;
        raise (Termination (Some st))
