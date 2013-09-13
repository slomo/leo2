(* parrallel part *)


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

open Subprover


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
let start (prover: subprover) (inputId: int) (input: string) : run =

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
        inputId = inputId;
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

(** kill a prover run
 *
 *  May be applied to any prover run, regardless wether the encapsulated process
 *  has already finished or not. It does not check, if the prover has really
 *  finished.
 *)

let kill pr =
  try Unix.kill pr.pid Sys.sigterm; pr
  with
      Unix.Unix_error (Unix.ESRCH,_,_) -> pr;
;;

(** transform a run to a result *)
let result_from_run (pr:run) (status:Unix.process_status) : result =

  (* fixme: this is not tail recursiv *)
  let read_until_szs(channel: in_channel) =
    read_until Szs.read_status Szs.ERR channel 
  in

  (* fixme: generate proof if requested *)
  (* check if run was successfull *)

  let error = {
    from = pr;
    channel = snd pr.channels;
    fragments = [];
    szs = Szs.ERR
  } in

  match status with
  | Unix.WEXITED n when n == 0 ->
    let (szs, fragments) = read_until_szs (snd pr.channels) in
    {
      from = pr;
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
(* fixe me hide more implemention here *)
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
      debug = name = "e_debug"
    }
  in

  let e_proof (lines:string list) =
    
    let comment_prefix = '#' in
    let regex = Str.regexp
      (* fof           (3          ,axiom       ,formel     ,file...).  *)
      "^\\(cnf\\|fof\\)(\\([^,]+\\), *\\(axiom\\|plain\\),\\(.+\\)).$" (*", \\(\\(file|inference\\).+\\),\\(.*\\)?).$"*)
    in
    
      (* filter empty lines *)
    let formula_lines = List.filter 
      (fun line ->  String.length line > 0 && String.get line 0 != comment_prefix )
      lines
    in

    
    (** this is essentally a little stack automaton that, can get the first of
        comma sperated list of wf prolog terms **)
    let split_formula str : (string * string) =

      let pos = ref 0 in
      let escaped_literal = ref false in
      let escape_slash = ref false in
      let brs = ref [] in
      let len =  String.length str in

      while !brs <> [] || (!pos < len && (String.get str !pos) <> ',') do
        ( match String.get str !pos with
          (* count brackets if  where are not in a escaped leteral *)
            '(' when not !escaped_literal -> brs := ')' :: !brs
          | '[' when not !escaped_literal -> brs := ']' :: !brs 
          | (')' | ']') as br  ->
            ( match !brs with
                bre :: rem when bre = br -> brs := rem
              | _ -> raise (
                Invalid_argument ( "Expected " ^  Char.escaped (List.hd !brs) 
                                   ^ "got " ^ Char.escaped br ))
            )
          (* toogle escaped literal, if we are not in a literal and an escape slash has preceeded*) 
          | '\'' when not (!escaped_literal && !escape_slash) ->
            escaped_literal := not !escaped_literal
          | '\'' when (!escaped_literal && !escape_slash) ->
            escape_slash := false
          (* when an slash within a escaped literal is encountared toggle slash escape *)
          | '\\' when !escaped_literal -> escape_slash := not !escape_slash
          (* other wise do nothinh *)
          | _ -> ()
        );
        pos := !pos + 1
      done;
      if !pos = len
      then ( str, "")
      else (
        String.sub str 0 (!pos),
        String.sub str (!pos+1) ((String.length str) - (!pos+1)))
    in
        
    let source_regex = Str.regexp " *file([^,]*, *\\([a-z0-9]+\\))" in


    (* fof or cnf * name * role * logical formel * source * usefull info (optinal) *)
    let tuples : (string * string * string * string * string) list =
      List.map
        (fun line ->
          if not (Str.string_match regex line 0) then
            print_string ("!" ^ line ^ "!\n")
          ;
          let ftype, name, role =
            Str.matched_group 1 line,
            Str.matched_group 2 line,
            Str.matched_group 3 line in
          let (formula, rem) = split_formula  (Str.matched_group 4 line) in
          let (source, info) = split_formula rem in

          (* rewrite file source *)
          let source =
            if Str.string_match source_regex source 0
            then "inference(fof_translation, [status(thm)],[" ^ (Str.matched_group 1 source) ^ "])"
            else source
          in
          
          


          (
            ftype,
            name,
            role,
            formula,
            source
          )
        )
        formula_lines
    in
    


    print_string "-------------------------------------------------\n";
    print_string(
      String.concat "\n" (
        List.map (fun (ftype, name, role, _, source) -> 
          ftype ^ "(" ^  name ^ ", " ^ role ^ ", *formel*, " ^ source ^ ")."
        ) tuples
      )
    );
    print_string "\n-------------------------------------------------\n";
    (0,[""])
    
  in

  let dummy_proof a = (0,[""]) in

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

let bind (f : state -> state) st =
  let obj = match st.State.subprover_state with
    | None -> init st
    | Some state -> state
  in
  st.State.subprover_state <- Some (f obj)
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

  (** Tries to fetch result of specified process, and frees it space in state
    datastructure *)
  let handle_termination pid status (sc:state) =
    let (termprocess, others) = List.partition
      (fun run -> pid == run.pid) sc.running in

    (* the process was killed, because of  a strategy decission (see below) *)
    if termprocess = [] then
      sc
    else
      let result = result_from_run (List.hd termprocess) status in
      (* strategic decisions based on szs value *)
      (* if Ax => true holds, for one model no refutation can be given, therefore
         terminate all other provers with the same input *)
      if Szs.is_a result.szs Szs.SAT then
        let (to_kill, others) = List.partition
          (fun run -> run.inputId == result.from.inputId) others in
        let killed = (List.map (fun(pr) -> result_from_run (kill pr) (Unix.WSIGNALED 15)) to_kill) in
          { sc with
            waiting = List.filter (fun ((id, _), _) -> id = result.from.inputId) sc.waiting;
            results = result :: killed @ sc.results
          }
      else
        { sc with
          running = others;
          results = result :: sc.results
        }
  in

  (** start as many new subprovers as possible *)
  let start_subprovers (sc:state) =

  (*FIXME: may be replaced with batterie version of split_at *)
    let rec split (n:int) list =
      match list with
      | h :: tl when n > 0 -> let (hs,xs) = split (n-1) tl in (h::hs,xs)
      | rem -> ([],rem)
    in

    let capacity = sc.max_parrallel -  (List.length sc.running) in
    let (run_cand,  still_waiting) = split capacity sc.waiting in
    let now_running =  List.map
      (fun((inputId, problem), prover) -> start prover inputId problem)
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

let add_problem ((fo_id, fo_clauses):(int * string)) : state -> state =
  fun (sp_con) ->
    let waiting = List.map
      (fun (prover:subprover) -> (fo_id, fo_clauses), prover)
      sp_con.provers in
    { sp_con with waiting = waiting } ;;

let get_solutions (sc:state) : state * result list =
  (* remove all unsucessfull *)
  let successfull = List.filter
    (fun run -> Szs.is_a Szs.UNS run.szs)
    sc.results in
  ({sc with results = []}, successfull)
;;

(** Kill all subprovers that haven't terminating by them self *)
(*let kill_all_provers (sc:state) : state  =
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
    let handler = (snd (List.assoc result.from.subprover.name default_subprovers)) in
    let (_, output) = read_until (fun _ -> None) () result.channel in
    let output = output @ result.fragments in
    (true, snd (handler output), "")
  in

  match st.State.subprover_state with
  | Some sc ->
    (* get sucessfull results *)
    let (sc, results) = get_solutions sc  in
    st.State.subprover_state <- Some sc;
    
    (* proof found *)
    if results != [] then 
      (* give porve *)
      if st.State.flags.State.proof_output >= 1 then 
        generate_proof (List.hd results) 
      (* proof without evidence *)
      else (true, [], "") 
    (* no proof found *)
    else (false, [], "") 
          
  (* no subprover has been started yet *)
  | None ->
    (false, [], "")
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
  let inputId = st.State.foatp_calls in
  bind (add_problem (inputId, fo_clauses)) st
;;

let tick (st:State.state) =
  bind perform_update st
;;

let debug (st) =
  bind (fun (sc) -> print_string (string_of_state sc); sc) st
;;

let detect_cpu_count () =
  try
    let close chan = ignore (Unix.close_process_in chan) in
    let i = Unix.open_process_in "getconf _NPROCESSORS_ONLN" in
    try Scanf.fscanf i "%d" (fun n -> close i; n) with e -> close i; raise e
  with
  | e -> 1
;;
