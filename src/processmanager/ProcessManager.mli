module ProcessManager :
  sig
    val detect_cpu_count_unix : unit -> int
    val detect_cpu_count : unit -> int
    type process_state = {
      name : string;
      command : string list;
      pid : int;
      channels : out_channel * in_channel;
    }
    type manager_state = process_state list
    val start : string list -> ( process_state -> 'a)   ->  process_state list -> process_state list
    val handle_finished :
      process_state list ->
      (process_state -> 'a) -> 'a list * process_state list
    val state_channel : out_channel -> process_state list -> unit
  end
