val ( |- ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
type subprover_type = Modelfinder | Folprover | Incremental
val string_of_kind : subprover_type -> string
type subprover = {
  sp_type : subprover_type;
  path : string;
  name : string;
  options : string list;
  debug : bool;
}
val string_of_prover : subprover -> string
type subprover_run = {
  subprover : subprover;
  pid : int;
  channels : out_channel * in_channel;
}
val string_of_run : subprover_run -> string
type subprover_result = {
  channel : in_channel;
  fragments : string list;
  szs : Szs.status;
}
val string_of_result : subprover_result -> string
type controller = {
  max_parrallel : int;
  provers : subprover list;
  running : subprover_run list;
  waiting : (string * subprover) list;
  results : subprover_result list;
}

val executable_paths : (string * string) list ref
val string_of_controller : controller -> string
exception Subprover_failed
val start : subprover -> string -> subprover_run
val kill : subprover_run -> unit
val result_from_run :
  subprover_run -> Unix.process_status -> subprover_result

val default_subprovers : (string * ( unit -> subprover )) list
val collect_solution : State.state -> bool * string list * string
val submit_problem : State.state -> unit
val tick : State.state -> unit
val debug : State.state -> unit
val detect_cpu_count : unit -> int
