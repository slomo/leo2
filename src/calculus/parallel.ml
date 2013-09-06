open Subprover

(*
   Implements subprovers and thier execution.
   @author Yves Müller

   There exists two ways in using this module. Either can each subprover
   run be managed by hand. This is done via the "lowlevel". Or a strategy can
   be given, which only must be sheduled at a regular base, and therefore takes
   care of almost everything.

   {3 Low-Level API }

    For the lowlevel functions the following workflow is expected:

    {v
    start
    |
    v
    wait <-
    |    |
    |  false
    v    |
    is_finished
    |
    true
    |
    v
    fetch_result
    v}

*)


(** helpers *)

let rec read_until f fallback channel =  
  try
    let line = input_line channel in
    match f line with
    | Some value -> (value, [line])
    | None ->
      let (value, fragments) = read_until f fallback channel in
      (value, line::fragments)
  with
  | End_of_file -> (fallback, [])
;;

(**
   Lowlevel function to start a subprover on a given input string.
*)
let start (prover : subprover) (input : string) : run =

  (* This creates a pipe backed, through an non existing file. This
     results in a pipe with infinit buffer, which might get slow if
     the disk cache is running full *)
  let file_pipe () =
    let tmp_file = "./leo_file_pipe" in
    let write_end = Unix.openfile tmp_file
      [ Unix.O_CREAT; Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
    let read_end = Unix.openfile tmp_file
      [ Unix.O_RDONLY ] 0o006 in
    if not prover.debug then Unix.unlink (tmp_file);
    (read_end, write_end)
  in

  let (from_caller, to_cmd) = Unix.pipe() in
  let (from_cmd, to_caller) = file_pipe() in

  (* viewed from the perspective of leo *)
  let in_chan = Unix.in_channel_of_descr from_cmd in
  let out_chan = Unix.out_channel_of_descr to_cmd in

  (* write problem to stdin of subprover *)
  output_string out_chan input;
  flush out_chan;
  close_out out_chan;

  match prover with
  | { path = cmd; options = args} ->

    (* set argv[0] for subprover *)
    let args = cmd :: args in
    let prover_run =
      {
        subprover =  prover;
        pid = Unix.create_process cmd (Array.of_list args) from_caller to_caller Unix.stderr;
        channels = ( out_chan, in_chan );
      }
    in

    (* post start handle debugging *)
    if prover.debug then
      begin
        let fdin = Unix.openfile ( prover.name ^ "." ^ string_of_int prover_run.pid ^ ".in" )
          [ Unix.O_CREAT; Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
        let outchan = Unix.out_channel_of_descr fdin in
        output_string outchan input;
        flush outchan;
        close_out outchan;
        Unix.rename
          "./leo_file_pipe"
          ( prover.name ^ "." ^ string_of_int prover_run.pid ^ ".out")
      end;
    prover_run
;;


let kill pr = Unix.kill pr.pid Sys.sigterm ;;

(** transform a run to a result *)
let result_from_run (pr:run) (status:Unix.process_status) : result =

  (* fixme: this is not tail recursiv *)
  let read_until_szs(channel: in_channel) =
    read_until Szs.read_status Szs.ERR channel 
  in

  (* fixme: generate proof if requested *)
  (* check if run was successfull *)

  let error = {
    from = pr.subprover;
    channel = snd pr.channels;
    fragments = [];
    szs = Szs.ERR
  } in

  match status with
  | Unix.WEXITED n when n == 0 ->
    let (szs, fragments) = read_until_szs (snd pr.channels) in
    {
      from = pr.subprover;
      channel = snd pr.channels;
      fragments = fragments;
      szs = szs
    }
  | Unix.WSIGNALED n -> print_string ("signaled: " ^ string_of_int n); error
  | Unix.WSTOPPED n -> print_string ("stopped: " ^ string_of_int n); error
  | Unix.WEXITED n -> print_string ("exited: " ^ string_of_int n); error
;;



(* Handling of binary paths *)
let executable_paths :  (string * string) list ref = ref [];;

let get_subprover_path (atp:string) : string =
  try
    List.assoc atp !executable_paths
  with
  | Not_found ->
    ( print_string ("unable to find path for prover \"" ^ atp ^ "\"");
      exit 1)
(* FIXME: add function for unrecoverable errors *)
;;


(* from here on subprover speific code *)


let default_subprovers =

  let e_init (st:State.state) (name:string) : subprover =
    {
      sp_type = Folprover;
      path = get_subprover_path("e");
      name = name;
      options = [
        "-xAuto";
        "-tAuto";
        "--memory-limit=Auto";
        "--tptp3-format";
          (* limit execution time FIXME: might be seensless *)
        "--cpu-limit=" ^ string_of_int st.State.flags.State.atp_timeout; 
          (* only output proof if needed *)
        "-l " ^ if st.State.flags.State.proof_output > 1 then "4" else "0" 
      ];
      debug = name == "e_debug"
    }
  in

  let e_proof (lines:string list) =
    
    let comment_prefix = '#' in
    let regex = Str.regexp
      "^\\(cnf\\|fof\\)(\\(.*\\),\\(.*\\),\\(.*\\)\\(,\\(.*\\)\\)?)\\.$"
    in
    
      (* filter empty lines *)
    let formula_lines = List.filter 
      (fun line -> String.get line 0 != comment_prefix && String.length line > 0)
      lines
    in

      (* fof or cnf * name * role * logical formel * source * usefull info (optinal) *)
    let tuples : (string * string * string * string * string option) list =
      List.map
        (fun line ->
          ignore(Str.string_match regex line 0);
          (
            Str.matched_group 1 line,
            Str.matched_group 2 line,
            Str.matched_group 3 line,
            Str.matched_group 4 line,
            try  Some (Str.matched_group 6 line)
            with Not_found -> None
          )
        )
        formula_lines
    in
    print_string(
      String.concat "\n" (
        List.map (fun (a,b,_,d,_) -> String.concat "\t" [a;b;d]  )  tuples
      )
    );
    (0,"")
    
  in

  let dummy_proof a = (0,"") in

  [
    ("e", (
       e_init, e_proof));
    ("e_debug", (
       e_init, e_proof));
    ("spass", (
      (fun st name -> {
        sp_type = Folprover;
        path = get_subprover_path("spass");
        name = "SPASS";
        options = [
          "-TPTP"; "-PGiven=0"; "-PProblem=0";
          "-DocProof"; "-TimeLimit=10"];
        debug = false;
      }), dummy_proof));
    ("none", (
      (fun st name -> {
        sp_type = Folprover;
        path = "/bin/true";
        name = "none";
        options = [];
        debug = false;
      }), dummy_proof))
  ]
;;

(** {3 High-Level API } *)

(** Polls if any child process as finished. This might be dangerous to do,
    if there exists other subprozesses than those managed by this module. But
    it safes a lot of syscalls in comparrison to just poll for each subporver
    pid.
*)

let init (st: State.state) =

  let (provers: subprover list) = List.map
      (fun (prover_name) ->
        (fst (List.assoc prover_name default_subprovers)) st prover_name
      )
      st.State.flags.State.atp_provers
  in

  let parrallel = st.State.flags.State.atp_jobs in

  let sc = {
    max_parrallel = parrallel;
    running = [];
    provers = provers;
    waiting = [];
    results = [];
  } in
  sc
;;

let bind (f : controller -> controller) st =
  let obj = match st.State.subprover_controller with
    | None -> init st
    | Some controller -> controller
  in
  st.State.subprover_controller <- Some (f obj)
;;

let perform_update sc =
  (** Tests if any subprocess has terminated  *)
  let rec poll_terminations () =
    try
      let (pid, status) = Unix.waitpid [Unix.WNOHANG] (-1) in
      if pid == 0 then [] (* no child returned *)
      else (pid, status) :: poll_terminations ()
    with (* when no process has been started an exception is raised *)
      Unix.Unix_error (Unix.ECHILD,_,_) -> []
  in

  (** Tries to fetch result of specified process, and frees it space in controller
    datastructure *)
  let handle_termination pid status (sc:controller) =
    let now_finished = List.find
      (fun run -> pid == run.pid) sc.running in
    let still_running = List.filter
      (fun run -> pid != run.pid) sc.running in
    { sc with
      running = still_running;
      results = (result_from_run now_finished status) :: sc.results
    }
  in

  (** start as many new subprovers as possible *)
  let start_subprovers (sc:controller) =

  (*FIXME: may be replaced with batterie version of split_at *)
    let rec split (n:int) list =
      match list with
      | h :: tl when n > 0 -> let (hs,xs) = split (n-1) tl in (h::hs,xs)
      | rem -> ([],rem)
    in

    let capacity = sc.max_parrallel -  (List.length sc.running) in
    let (run_cand,  still_waiting) = split capacity sc.waiting in
    let now_running =  List.map
      (fun(problem, prover) -> start prover problem)
      run_cand in
    { sc with
      running = List.append sc.running now_running;
      waiting = still_waiting }
  in

  let terminated = if List.length(sc.running) == 0
    then []
    else poll_terminations ()
  in

  start_subprovers (
    List.fold_right
      (fun (pid,status) sc -> handle_termination pid status sc)
      (terminated) sc
  )
;;

(** helpers *)

let add_problem (fo_clauses:string) : controller -> controller =
  fun (sp_con) ->
    let waiting = List.map
      (fun (prover:subprover) -> fo_clauses, prover)
      sp_con.provers in
    { sp_con with waiting = waiting } ;;

let get_solutions (sc:controller) : controller * result list =
  (* remove all unsucessfull *)
  let successfull = List.filter
    (fun run -> Szs.is_a Szs.UNS run.szs)
    sc.results in
  ({sc with results = []}, successfull)
;;

(** Kill all subprovers that haven't terminating by them self *)
(*let kill_all_provers (sc:controller) : controller  =
  let now_finished = List.map (fun prover_run ->
    if is_active(prover_run)
    then prover_run
    else begin kill(prover_run); prover_run end ) sc.running in

  let all_finished = List.append sc.finished now_finished in
  { sc with finished = all_finished } ;;

*)
(** api functions *)

(** This function can be used to collect results of subprovers 

    @return information wether proof was succefull and used clauses

*)
let collect_solution (st:State.state) : (bool * string list * string) =

  let generate_proof result =
    let handler = (snd (List.assoc result.from.name default_subprovers)) in
    let (_, output) = read_until (fun _ -> None) () result.channel in
    let output = output @ results.fragments in
    handler output
  in

  match st.State.subprover_controller with
  | Some sc ->
    (* get sucessfull results *)
    let (sc, results) = get_solutions sc  in
    st.State.subprover_controller <- Some sc;
    
    if results != [] then (* proof found *)
      if st.flags.proof_output > 1 then (* give porve *)
        generate proof (List.hd results) 
      else (true, [], "") (* proof with out evidence *)
      else (false, [], "") (* no proof found *)
          
  (* no subprover has been started yet *)
  | None ->
    (false, [])
;;



(** Intended usage:

    start

    submit_problem

    collect_solutions

    tick

    tick_final
*)

let submit_problem (st:State.state) : unit =
  let fo_clauses:string = Main.get_fo_clauses st in
  bind (add_problem fo_clauses) st
;;

let tick (st:State.state) =
  bind perform_update st
;;

let debug (st) =
  bind (fun (sc) -> print_string (string_of_controller sc); sc) st
;;

let detect_cpu_count () =
  try
    let close chan = ignore (Unix.close_process_in chan) in
    let i = Unix.open_process_in "getconf _NPROCESSORS_ONLN" in
    try Scanf.fscanf i "%d" (fun n -> close i; n) with e -> close i; raise e
  with
  | e -> 1
;;
