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

  let subprover_call prover input =

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

  (*  TODO doku *)
  let subprover_update_status blocking sr =  match sr with
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
  
  (* This functions fetches a result as string from a subprover run in a blocking manner *)
  let subprover_fetch_result finished_pr =
    if (not finished_pr.killed && finished_pr.value == 0) then
      input_line (snd finished_pr.channels) (* TODO read whole channel *)
    else
      raise Subprover_failed
  ;;

  (* TODO doku *)
  let subprover_wait_result pr =
    let finished_pr = subprover_update_status true pr in
    subprover_fetch_result finished_pr
    
  (* TODO doku *)
  let subprover_update pr = subprover_update_status false pr;;

  let default_subprover =
   { sp_type = Folprover; path = "eprover"; name = "E"; options = [] }
  ;;

end
