val ( |- ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
type subprover_type = Modelfinder | Folprover | Incremental
val string_of_kind : subprover_type -> string
type subprover = {
  sp_type : subprover_type;
  path : string;
  name : string;
  options : string list;
}
val string_of_prover : subprover -> string
type subprover_run = {
  subprover : subprover;
  pid : int;
  channels : out_channel * in_channel;
  killed : bool;
  value : int;
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
  finished : subprover_result list;
}
exception Subprover_failed
val start : subprover -> string -> subprover_run
val check_for_termination : bool -> subprover_run -> subprover_run
val to_result : subprover_run -> subprover_result
val result_from_run :
  subprover_run -> Unix.process_status -> subprover_result
val set_terminated : int -> Unix.process_status -> controller -> controller
val fetch_result : subprover_run -> string
val wait : subprover_run -> string
val update : subprover_run -> subprover_run
val kill : subprover_run -> unit
val is_success : subprover_run -> Szs.status -> bool
val default_subprovers : subprover list
val string_of_controller : controller -> string
val init : ?parrallel:int -> subprover list -> controller
val with_ref_do : 'a ref -> ('a -> 'a) -> unit
val add_problem : string -> controller -> controller
val get_solutions : controller -> (bool * string list * string) list
val perform_update : controller -> controller
val sp_controller : controller ref
val submit_problem : State.state -> unit
val collect_solutions : State.state -> (bool * string list * string) list
val tick : State.state -> unit
val debug : unit -> unit
type message = Terminated of int * Unix.process_status | Problem of string
val channel : message Event.channel
val notify_termination_loop : unit -> 'a
val main_loop : controller -> 'a
