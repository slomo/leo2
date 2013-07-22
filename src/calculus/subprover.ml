(**
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


(** Modles the various types of subprover:
    {ul
    {- Modelfinder }
    {- First Order Prover (E, Vampire ... ) }
    {- Incremental ( Z3 ) }
    ul}

*)
type subprover_type = Modelfinder | Folprover | Incremental

(** Instances of that type a concrete subprovers. *)
type subprover = {
  sp_type: subprover_type;
  path: string; (* abs or rel path to executable *)
  name: string; (* humanreadale name of the prover *)
  options : string list; (* list of standard options *)
}


(** Every call to a subprover results in a subprover run. *)
type subprover_run = {
  subprover: subprover;
  pid: int;
  channels: out_channel * in_channel;
  finished: bool;
  killed: bool;
  value: int;
}

type subprover_result = {
  channel: in_channel;
  fragments: string list;
  szs: Szs.status
}

exception Subprover_failed

(**
   Lowlevel function to start a subprover on a given input string.
*)
let start (prover : subprover) (input : string) : subprover_run =

  (* This implements the behaviour of Unix.open_process, but returns
     pid in additon to in and out channels. *)
  let my_fork cmd args  =

    let ( from_caller, to_cmd ) = Unix.pipe() in
    let ( from_cmd, to_caller ) = Unix.pipe() in

    let cmd_pipe_setup () =
      Unix.close to_cmd; Unix.close from_cmd;

      Unix.dup2 from_caller Unix.stdin;
      Unix.dup2 to_caller Unix.stdout;

      Unix.close to_caller; Unix.close from_caller;
    in

    let caller_pipe_setup () =
      Unix.close from_caller; Unix.close to_caller;
    in

    match  Unix.fork() with
    | 0 -> cmd_pipe_setup(); Unix.execvp cmd ( Array.of_list ( cmd :: args))
    | cmd_pid -> caller_pipe_setup(); (
      cmd_pid,
      Unix.in_channel_of_descr from_cmd,
      Unix.out_channel_of_descr to_cmd
    )

  in


  match prover with
  | {  path = path; options = options } ->

    let (pid, in_chan, out_chan) = my_fork path options in
    {
      subprover =  prover;
      pid = pid;
      channels = ( out_chan, in_chan );
      finished = false;
      killed = false;
      value = 0;
    }

;;

(**
   Tries to gather information, wether the specified subprover run finished
   and what it resulted in.

   @param blocking if set to true the call blocks until the subprover terminates
   @param sr information about running subprover
   @return indormation about subprover updated with possible termination info and return value
*)
let check_for_termination blocking sr =  match sr with
    ({pid = pid} as sr) ->
      let waitpid_opts = if blocking then [] else  [ Unix.WNOHANG  ] in
      let ( return_pid, status ) = Unix.waitpid waitpid_opts pid in

      if return_pid == pid then
        match status with
        | Unix.WEXITED n   -> { sr with finished = true; value = n }
        | Unix.WSIGNALED n
        | Unix.WSTOPPED n -> { sr with finished = true; killed = true; value = n }
      else
        sr
;;

(** Fetches the result from a sucessfully terminated suprover, throws an exception otherwiese *)
let fetch_result finished_pr =

  (* TODO: read only as long as needed, we might aort if an undesired szs status is met *)
  let read_all_in chan =
    let lines = ref [] in
    try
      while true; do
        lines := input_line chan :: !lines
      done; []
    with End_of_file ->
      close_in chan;
      List.rev !lines
  in

  if (not finished_pr.killed && finished_pr.value == 0) then
    String.concat "\n" (read_all_in (snd finished_pr.channels))
  else
    raise Subprover_failed
;;

(** transform a run to a result *)
let to_result (pr:subprover_run) : subprover_result =

  let rec get_szs(channel: in_channel) =
    try
      let line = input_line channel in
      match Szs.read_status line with
      | Some szs_status -> ([line], szs_status)
      | None -> let (fragments, status) = get_szs(channel) in
                (line::fragments, status)
    with
    | End_of_file -> ([],Szs.ERR)
  in

  let (fragments,szs) = get_szs (snd pr.channels) in

  {
    channel = snd pr.channels;
    fragments = fragments;
    szs = szs
  }




(** Waits blocking until thesuprover is done and returns its result(see {! fetch_result }) *)
let wait pr =
  let finished_pr = check_for_termination true pr in
  fetch_result finished_pr

(** Updates the status of the given subprover structure, to that of the suprover *)
let update pr = check_for_termination false pr;;

let kill pr = Unix.kill pr.pid Sys.sigterm

(** Checks wether the given subprover_run structure has been set to finished *)
let is_finished (pr : subprover_run) = pr.finished ;;

(** Opposite of is_finished *)
let is_active (pr : subprover_run) = not pr.finished ;;

(** Checks wather the given prover run was successfull *)
let is_success (pr: subprover_run) (ret:Szs.status) =  Szs.is_a ret Szs.SUC ;;

let default_subprovers = [
   {
     sp_type = Folprover; path = "eprover";
     name = "E"; options = ["--auto"; "--tptp3-format"] }
];;




(** {3 High-Level API } *)

type controller = {
  max_parrallel: int;
  provers:  subprover list;
  running: subprover_run list;
  waiting: ( string * subprover) list;
  finished: subprover_run list;
};;

let init ?(parrallel = 0) (provers: subprover list) =

  let detect_cpu_count () =
    try
      let close chan = ignore (Unix.close_process_in chan) in
      let i = Unix.open_process_in "getconf _NPROCESSORS_ONLN" in
      try Scanf.fscanf i "%d" (fun n -> close i; n) with e -> close i; raise e
    with
    | e -> 1
  in

  let parrallel = if parrallel >= 1 then parrallel else detect_cpu_count() in
  {
    max_parrallel = parrallel;
    running = [];
    provers = provers;
    waiting = [];
    finished = [];
  }

;;

(** helpers *)
let with_ref_do (refa :  'a ref) (f : 'a -> 'a) : unit =
  refa :=  f !refa ;;

let add_problem (fo_clauses:string) : controller -> controller =
  fun (sp_con) ->
    let waiting = List.map
      (fun (prover:subprover) -> fo_clauses, prover)
      sp_con.provers in
    { sp_con with waiting = waiting } ;;

(* fixme: update status, ugly side effects *)
let get_solutions (sc:controller) : (bool * string list * string) list =

  (* get szs_codes  *)
  let prover_results = List.map
    (fun (prover_run) -> to_result prover_run)
    sc.finished
  in

  (* remove all unsucessfull *)
  let successfull = List.filter
    (fun (pr) -> match pr with
    | {szs= szs} ->  Szs.is_a Szs.SUC szs)
    prover_results in

  (* fixme: check if prove is needed *)
  (* fixme: rething leagcy format *)
  List.map (fun(pr) -> (true,[],""))  successfull
;;

let tick (st:State.state) =

  (* may be replaced with batterie version of split_at *)
  let rec split (n:int) list =
    match list with
    | h :: tl when n > 0 -> let (hs,xs) = split (n-1) tl in (h::hs,xs)
    | rem -> ([],rem)
  in

  (* update status *)
  let updated_runs = List.map update sc.running in

  (* remove finished *)
  let now_finished =  List.filter is_finished updated_runs in
  let still_running = List.filter is_active updated_runs in

  (* start as many new as possible *)
  let capacity = sc.max_parrallel -  (List.length still_running) in
  let (run_cand,  still_waiting) = split capacity sc.waiting in
  let now_running =  List.map
    (fun(problem, prover) -> start prover problem)
    run_cand in

  { sc with
    running = List.append still_running now_running;
    waiting = still_waiting;
    finished = List.append now_finished sc.finished }
;;

(** Kill all subprovers that haven't terminating by them self *)
let kill_all_provers (sc:controller) : controller  =
  let now_finished = List.map (fun prover_run ->
    if is_active(prover_run)
    then prover_run
    else begin kill(prover_run); prover_run end ) sc.running in

  let all_finished = List.append sc.finished now_finished in
  { sc with finished = all_finished } ;;


(** api functions *)

(* FIXME: move to state *)
let sp_controller = ref (init ~parrallel:2 default_subprovers);;

(** Intended usage:

    start

    submit_problem

    collect_solutions

    tick

    tick_final
*)

let submit_problem (st:State.state) =
  let fo_clauses:string = Main.get_fo_clauses st in
  with_ref_do sp_controller (add_problem fo_clauses)
;;

let collect_solutions (st:State.state) : (bool * string list * string) list =
  get_solutions !sp_controller
;;

let tick (st:State.state) =
  with_ref_do sp_controller perform_update
;;

let tick_final (st:State.state) =
   with_ref_do sp_controller kill_all_provers
;;

  let sc = !sp_controller in
  sp_controller := kill_all_provers !sp_controller
;;
