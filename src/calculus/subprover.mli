type subprover_type = Modelfinder | Folprover | Incremental
type subprover = {
  sp_type : subprover_type;
  path : string;
  name : string;
  options : string list;
}
type subprover_run = {
  subprover : subprover;
  pid : int;
  channels : out_channel * in_channel;
  finished : bool;
  killed : bool;
  value : int;
}
type subprover_result = {
  channel : in_channel;
  fragments : string list;
  szs : Szs.status;
}
exception Subprover_failed
val start : subprover -> string -> subprover_run
val check_for_termination : bool -> subprover_run -> subprover_run
val fetch_result : subprover_run -> string
val to_result : subprover_run -> subprover_result
val wait : subprover_run -> string
val update : subprover_run -> subprover_run
val kill : subprover_run -> unit
val is_finished : subprover_run -> bool
val is_active : subprover_run -> bool
val is_success : subprover_run -> Szs.status -> bool
val default_subprovers : subprover list
type controller = {
  max_parrallel : int;
  provers : subprover list;
  running : subprover_run list;
  waiting : (string * subprover) list;
  finished : subprover_run list;
}
val init : ?parrallel:int -> subprover list -> controller
val sp_controller : controller ref
val submit_problem : State.state -> unit
val collect_solutions : State.state -> (bool * string list * string) list
val tick : State.state -> unit
val tick_final : State.state -> unit
