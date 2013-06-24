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
exception Subprover_failed
val start : subprover -> string -> subprover_run
val check_for_termination : bool -> subprover_run -> subprover_run
val fetch_result : subprover_run -> string
val wait : subprover_run -> string
val update : subprover_run -> subprover_run
val is_finished : subprover_run -> bool
val default_subprover : subprover
