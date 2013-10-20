open Subprover
open State

val executable_paths : (string * string) list ref
val start : subprover -> int -> string -> run
val kill : run -> run
val result_from_run :
  run -> Unix.process_status -> result

val default_subprovers : 
  (string * 
     ( (state -> string -> subprover) *
         (state -> string list -> int * string list))) list


val collect_solution : state -> bool * string list * string
val submit_problem : state -> unit
val tick : state -> unit
val final_tick : state -> unit
val debug : state -> unit
val detect_cpu_count : unit -> int
