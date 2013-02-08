module ProcessManager = 
  struct
    let detect_cpu_count_unix () =
      let getconfpipe = Unix.open_process_in "getconf _NPROCESSORS_ONLN" in
      let close() = ignore (Unix.close_process_in getconfpipe) in
      try 
        Scanf.fscanf getconfpipe "%d" (fun n -> close (); n) 
      with 
        e -> close() ; raise e
      
    let detect_cpu_count () = 
      try match Sys.os_type with
      | "Win32" -> int_of_string (Sys.getenv "NUMBER_OF_PROCESSORS")
      | _ -> detect_cpu_count_unix ()
      with
      | Not_found | Sys_error _ | Failure _ | Scanf.Scan_failure _


      | End_of_file | Unix.Unix_error (_, _, _) -> 1

    type process_state = {
      name : string;
      command : string list;
      pid : int;
      channels : out_channel * in_channel
    }

    type manager_state = process_state list

    let start prog_list handler state = match prog_list with
        (cmd :: args)  ->
          let (to_child_exit, to_child_entry) = Unix.pipe() in
          let (from_child_exit, from_child_entry) = Unix.pipe() in

          let child_start() =
            (* close parents pipes *)
            Unix.close to_child_entry;
            Unix.close from_child_exit;

            (* redirect sdtout and stdin *)
            Unix.dup2  from_child_entry Unix.stdout;
            Unix.close from_child_entry;

            Unix.dup2 to_child_exit Unix.stdin;
            Unix.close to_child_exit;
        
            Unix.execvp cmd ( Array.of_list ( cmd :: args)) in

          let parent_start child_pid =
            Unix.close from_child_entry;
            Unix.close to_child_exit;
            let child = { name = cmd;
                          command = cmd :: args;
                          pid = child_pid;
                          channels = ( 
                            ( Unix.out_channel_of_descr to_child_entry) ,
                            ( Unix.in_channel_of_descr from_child_exit) )
                
                        } in
            handler child;
            (child :: state)
          in 
          let fork_pid = Unix.fork() in
          if fork_pid == 0 then 
            child_start()
          else
            parent_start fork_pid

      | [] ->
        state


    let handle_finished state handler =

      let process_alive { pid = pid } = match Unix.waitpid [ Unix.WNOHANG ] pid with
        | ( 0, _ ) -> false
        | ( pid, Unix.WEXITED code ) | (pid, Unix.WSTOPPED code ) | (pid, Unix.WSIGNALED code )-> true
      in

      let finished = List.filter process_alive state in
      let running = List.filter (
        fun x -> not (
          List.exists ( fun y -> x == y ) finished
        ) ) state in


      (  List.map handler finished, running )


    let state_channel chan v = 
      let string_of_ps state = match state with
        | {name = name; pid = pid } -> 
          "[" ^ name  ^ " => " ^ (string_of_int pid) ^ "]" in
      output_string chan (String.concat ""
                            (List.map string_of_ps v))
     
  end
;;
