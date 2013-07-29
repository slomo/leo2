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
  | Folprover -> "first order prover"
  | Modelfinder -> "modelfinder"
  | Incremental -> "incremental prover"
;;


(** Instances of that type a concrete subprovers. *)
type subprover = {
  sp_type: subprover_type;
  path: string; (* abs or rel path to executable *)
  name: string; (* humanreadale name of the prover *)
  options : string list; (* list of standard options *)
};;

let string_of_prover (prover:subprover) : string =
  match prover with
  | { sp_type = kind; name = name } -> name ^ ":" ^ string_of_kind kind
;;

(** Every call to a subprover results in a subprover run. *)
type subprover_run = {
  subprover: subprover;
  pid: int;
  channels: out_channel * in_channel;
  killed: bool;
  value: int;
};;

let string_of_run (run:subprover_run) = match run with
  | { subprover =  prover; pid = pid } ->
   string_of_prover(prover) ^ "[" ^ string_of_int pid ^ "]"
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
  finished: subprover_result list;
};;


exception Subprover_failed

(**
   Lowlevel function to start a subprover on a given input string.
*)
let start (prover : subprover) (input : string) : subprover_run =

  (* This creates a pipe backed, through an non existing file. This
     results in a pipe with infinit buffer, which might get slow if
     the disk cache is running full *)
  let file_pipe () =
    let tmp_file = "/tmp/leo_file_pipe" in
    let write_end = Unix.openfile tmp_file
      [ Unix.O_CREAT; Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
    let read_end = Unix.openfile tmp_file
      [ Unix.O_RDONLY ] 0o006 in
    Unix.unlink (tmp_file);
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
    {
      subprover =  prover;
      pid = Unix.create_process cmd (Array.of_list args) from_caller to_caller Unix.stderr;
      channels = ( out_chan, in_chan );
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
        | Unix.WEXITED n   -> { sr with value = n }
        | Unix.WSIGNALED n
        | Unix.WSTOPPED n -> { sr with killed = true; value = n }
      else
        sr
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

;;


let result_from_run pr status =
  let res = match status with
  | Unix.WEXITED n -> { pr with value = n }
  | Unix.WSIGNALED n
  | Unix.WSTOPPED n -> { pr with killed = true; value = n }
  in to_result res
;;

let set_terminated pid status ({ running =  running; finished = finished} as sc) =
  let now_finished = List.find
    (fun ({pid = thisPid}) -> pid == thisPid) running in
  let still_running = List.filter
    (fun ({pid = thisPid}) -> pid != thisPid) running in
  { sc with
    running = running;
    finished = (result_from_run now_finished status) :: finished
  }
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




(** Waits blocking until thesuprover is done and returns its result(see {! fetch_result }) *)
let wait pr =
  let finished_pr = check_for_termination true pr in
  fetch_result finished_pr

(** Updates the status of the given subprover structure, to that of the suprover *)
let update pr = check_for_termination false pr;;

let kill pr = Unix.kill pr.pid Sys.sigterm

(** Checks wather the given prover run was successfull *)
let is_success (pr: subprover_run) (ret:Szs.status) =  Szs.is_a ret Szs.SUC ;;

let default_subprovers = [
   { sp_type = Folprover;
     path = "/home/yves/uni/ma/E/PROVER/eprover";
     name = "E";
     options = [
       "-xAuto"; "-tAuto"; "--memory-limit=Auto";
       "--tptp3-format"; "--cpu-limit=10"]}
];;




(** {3 High-Level API } *)


let string_of_controller (controller:controller) = match controller with
  | { max_parrallel = mp; provers = provers;
      running = running; waiting =  waiting;
      finished = finished } ->
    "{ running: " ^ String.concat "\n           " (List.map string_of_run running) ^ "\n" ^
    "  waiting: " ^ String.concat "\n           " (List.map (string_of_prover |- snd) waiting) ^ "\n" ^
    "  finishd: " ^ String.concat "\n           " (List.map string_of_result finished)  ^ "}"
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
  let prover_results = sc.finished in

  (* remove all unsucessfull *)
  let successfull = List.filter
    (fun (pr) -> match pr with
    | {szs= szs} ->
      Szs.is_a Szs.UNS szs)
    prover_results in


  (* fixme: check if prove is needed *)
  (* fixme: rething leagcy format *)
  List.map (fun(pr) -> (true,[],""))  successfull
;;

let perform_update sc =
  (* may be replaced with batterie version of split_at *)
  let rec split (n:int) list =
    match list with
    | h :: tl when n > 0 -> let (hs,xs) = split (n-1) tl in (h::hs,xs)
    | rem -> ([],rem)
  in

  let still_running = sc.running in

  (* start as many new as possible *)
  let capacity = sc.max_parrallel -  (List.length still_running) in
  let (run_cand,  still_waiting) = split capacity sc.waiting in
  let now_running =  List.map
    (fun(problem, prover) -> start prover problem)
    run_cand in

  { sc with
    running = List.append still_running now_running;
    waiting = still_waiting }
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

type message =
  Terminated of int * Unix.process_status
| Problem of string

type result_message =
  FofSuccess of string list

let channel : message Event.channel = Event.new_channel ();;

let result_channel : result_message Event.channel = Event.new_channel();;

let collect_solutions (st:State.state) : (bool * string list * string) list =
  match Event.poll (Event.receive result_channel) with
  | None -> [(false, [], "")]
  | Some (FofSuccess formulars) -> [(true, formulars, "")]
;;


(* let poll_termination () =
  Unix.waitpid [ Unix.WNOHANG  ] pid
*)


let rec notify_termination_loop () =
  let (pid, status) = Unix.wait () in
  Event.sync (Event.send channel (Terminated (pid, status)));
  notify_termination_loop ()
;;

let rec main_loop sc =
  let event = Event.receive channel in
  let new_state = match Event.sync event with
    | Terminated (pid, status) -> set_terminated pid status sc
    | Problem fo_str -> (add_problem fo_str) sc
  in
  if List.exists (fun ({szs = szs}) -> Szs.is_a szs Szs.UNS) sc.finished
  then Event.sync (Event.send result_channel (FofSuccess []) );
  main_loop (perform_update sc)
;;

let init ?(parrallel = 0) (provers: subprover list) =
  let detect_cpu_count () =
    try
      let close chan = ignore (Unix.close_process_in chan) in
      let i = Unix.open_process_in "getconf _NPROCESSORS_ONLN" in
      try Scanf.fscanf i "%d" (fun n -> close i; n) with e -> close i; raise e
    with
    | e -> 1
  in

  let parrallel = if parrallel >= 1
    then parrallel else detect_cpu_count() in
  let sc = {
    max_parrallel = parrallel;
    running = [];
    provers = provers;
    waiting = [];
    finished = [];
  } in

  ignore (Thread.create notify_termination_loop ());
  ignore (Thread.create main_loop sc);
  sc
;;


(* FIXME: move to state *)
let sp_controller = ref (init ~parrallel:1 default_subprovers);;

(** Intended usage:

    start

    submit_problem

    collect_solutions

    tick

    tick_final
*)

let submit_problem (st:State.state) =
  let fo_clauses:string = Main.get_fo_clauses st in
  print_string "submitted";
  Event.sync (Event.send channel (Problem fo_clauses));
  Thread.yield ()
(*  with_ref_do sp_controller (add_problem fo_clauses) *)
;;


let tick (st:State.state) =
  with_ref_do sp_controller perform_update
;;

(*let tick_final (st:State.state) =
   with_ref_do sp_controller kill_all_provers
;;*)

let debug () =
  print_string (string_of_controller !sp_controller);
;;


