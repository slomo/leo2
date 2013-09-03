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

let (|-) f g = fun (x) -> f (g x);;

(** Modles the various types of subprover:
    {ul
    {- Modelfinder }
    {- First Order Prover (E, Vampire ... ) }
    {- Incremental ( Z3 ) }
    ul}

*)
type subprover_type = Modelfinder | Folprover | Incremental ;;

let string_of_kind (kind:subprover_type) = match kind with
  | Folprover -> "atp"
  | Modelfinder -> "mf"
  | Incremental -> "itp"
;;


(** Instances of that type a concrete subprovers. *)
type subprover = {
  sp_type: subprover_type;
  path: string; (* abs or rel path to executable *)
  name: string; (* humanreadale name of the prover *)
  options : string list; (* list of standard options *)
  debug: bool
};;

let string_of_prover (prover:subprover) : string =
  prover.path ^ "[" ^ string_of_kind prover.sp_type ^ "]"
;;

(** Every call to a subprover results in a subprover run. *)
type subprover_run = {
  subprover: subprover;
  pid: int;
  channels: out_channel * in_channel;
};;

let string_of_run (run:subprover_run) = match run with
  | { subprover =  prover; pid = pid } ->
   string_of_prover(prover) ^ "@" ^ string_of_int pid
;;

type subprover_result = {
  channel: in_channel;
  fragments: string list;
  szs: Szs.status
}

let string_of_result ({szs= szs}:subprover_result) =
  "result(" ^ Szs.string_of_szs szs ^ ")"

type controller = {
  max_parrallel: int;
  provers:  subprover list;
  running: subprover_run list;
  waiting: ( string * subprover) list;
  results: subprover_result list;
};;

let string_of_controller (controller:controller) = match controller with
  | { max_parrallel = mp; provers = provers;
      running = running; waiting =  waiting;
      results = finished } ->
    "{ running: " ^ String.concat "\n           " (List.map string_of_run running) ^ "\n" ^
    "  waiting: " ^ String.concat "\n           " (List.map (string_of_prover |- snd) waiting) ^ "\n" ^
    "  results: " ^ String.concat "\n           " (List.map string_of_result finished)  ^ "}"
;;

exception Subprover_failed

(**
   Lowlevel function to start a subprover on a given input string.
*)
let start (prover : subprover) (input : string) : subprover_run =

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
let result_from_run (pr:subprover_run) (status:Unix.process_status) : subprover_result =

  (* fixme: this is not tail recursiv *)
  let rec read_until_szs(channel: in_channel) =
    try
      let line = input_line channel in
      match Szs.read_status line with
      | Some szs_status -> ([line], szs_status)
      | None -> let (fragments, status) = read_until_szs(channel) in
                (line::fragments, status)
    with
    | End_of_file -> ([],Szs.ERR)
  in

  (* fixme: generate proof if requested *)
  (* check if run was successfull *)

  let error = {
      channel = snd pr.channels;
      fragments = [];
      szs = Szs.ERR
  } in

  match status with
  | Unix.WEXITED n when n == 0 ->
    let (fragments,szs) = read_until_szs (snd pr.channels) in
    {
      channel = snd pr.channels;
      fragments = fragments;
      szs = szs
    }
  | Unix.WSIGNALED n -> print_string ("signaled: " ^ string_of_int n); error
  | Unix.WSTOPPED n -> print_string ("stopped: " ^ string_of_int n); error
  | Unix.WEXITED n -> print_string ("exited: " ^ string_of_int n); error
;;


let executable_paths = ref []
;;


let get_subprover_path atp =
  try
    List.assoc atp !executable_paths
  with
  | Not_found ->
    ( print_string ("unable to find path for prover \"" ^ atp ^ "\"");
      exit 1)
    (* FIXME: add function for unrecoverable errors *)
;;

let default_subprovers =
  let construct_e debug = fun () ->
    { sp_type = Folprover;
      path = get_subprover_path("e");
      name = "E";
      options = [
        "-xAuto"; "-tAuto"; "--memory-limit=Auto";
        "--tptp3-format"; "--cpu-limit=10"; "-l 4"];
      debug = debug
    }

  in

  [
    ( "e", construct_e false);
    ( "e_debug", construct_e true);
    ( "spass",
      fun () ->
        { sp_type = Folprover;
          path = get_subprover_path("spass");
          name = "SPASS";
          options = [
            "-TPTP"; "-PGiven=0"; "-PProblem=0";
            "-DocProof"; "-TimeLimit=10"];
          debug = false;
        });
    ( "none",
      fun () -> {
        sp_type = Folprover;
        path = "/bin/true";
        name = "none";
        options = [];
        debug = false;
      })

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
        (List.assoc prover_name default_subprovers)()
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


(* FIXME: move to state *)
let sp_controller:controller option ref = ref None;;

let perform_update sc =

  let rec poll_terminations () =
    try
      let (return_pid, status) = Unix.waitpid [Unix.WNOHANG] (-1) in
      if return_pid == 0 (* no child as returned *)
      then []
      else (return_pid, status) :: (poll_terminations ())
    with
      Unix.Unix_error (Unix.ECHILD,_,_) -> []
  in

  (** Tries to fetch result of specified process, and frees it space in controller
    datastructure *)
  let handle_termination pid status (sc:controller) =
    let now_finished = List.find
      (fun ({pid = thisPid}) -> pid == thisPid) sc.running in
    let still_running = List.filter
      (fun ({pid = thisPid}) -> pid != thisPid) sc.running in
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
let with_ref_do (refa :  controller option ref) (f : controller -> controller) (st : State.state) : unit =
  let obj = match !refa with
    | None -> init st
    | Some controller -> controller
  in
  refa := Some (f obj)
;;

let add_problem (fo_clauses:string) : controller -> controller =
  fun (sp_con) ->
    let waiting = List.map
      (fun (prover:subprover) -> fo_clauses, prover)
      sp_con.provers in
    { sp_con with waiting = waiting } ;;

let get_solutions (sc:controller) : controller * subprover_result list =

  (* remove all unsucessfull *)
  let successfull = List.filter
    (fun (pr) -> match pr with
    | {szs = szs} ->
      Szs.is_a Szs.UNS szs)
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

let collect_solution (st:State.state) : (bool * string list * string) =
  let results =
    match !sp_controller with
    | Some sc ->
      let (sc, results) = get_solutions sc  in
      sp_controller := Some sc;
      results
    | _ ->
      []
  in
  if (List.length results) >= 0
  then (false, [], "")
  else (true, [], "")
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
  with_ref_do sp_controller (add_problem fo_clauses) st
;;

let tick (st:State.state) =
  with_ref_do sp_controller perform_update st
;;

(*let tick_final (st:State.state) =
   with_ref_do sp_controller kill_all_provers
;;*)

let debug (st) =
  with_ref_do sp_controller (fun (sc) -> print_string (string_of_controller sc); sc) st
;;

let detect_cpu_count () =
  try
    let close chan = ignore (Unix.close_process_in chan) in
    let i = Unix.open_process_in "getconf _NPROCESSORS_ONLN" in
    try Scanf.fscanf i "%d" (fun n -> close i; n) with e -> close i; raise e
  with
  | e -> 1
;;

