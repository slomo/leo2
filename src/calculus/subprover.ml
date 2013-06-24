(**
   Implements subprovers and thier execution


   for the lowlevel functions the following workflow is expected:

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

   @author Yves Müller
*)

open Unix;;

module Subprover = struct

  (* Modles the various types of subprover:
      * Modelfinder
      * Folprover (E, Vampire ... )
      * Incremental ( Z3 )

  *)
  type subprover_type = Modelfinder | Folprover | Incremental

  (* Instances of that type a concrete subprovers. *)
  type subprover = {
    sp_type: subprover_type;
    path: string;
    name: string;
    options : string list;
  }


 (* Every call to a subprover results in a subprover run. *)
  type subprover_run = {
    subprover: subprover;
    pid: int;
    channels: out_channel * in_channel;
    finished: bool;
    killed: bool;
    value: int;
  }

  exception Subprover_failed

  (**
     Lowlevel function to start a subprover on a given input string.
  *)
  let start prover input =

    (* This implements the behaviour of Unix.open_process, but returns
       pid in additon to in and out channels. *)
    let my_fork cmd args =

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

  (** Waits blocking until thesuprover is done and returns its result (see fetch_result) *)
  let wait pr =
    let finished_pr = check_for_termination true pr in
    fetch_result finished_pr

  (** Updates the status of the given subprover structure, to that of the suprover *)
  let update pr = check_for_termination false pr;;

  (** Checks wether the given subprover_run structure has been set to finished *)
  let is_finished (pr : subprover_run) = pr.finished ;;

  let default_subprover =
   { sp_type = Folprover; path = "eprover"; name = "E"; options = [] }
  ;;








end
