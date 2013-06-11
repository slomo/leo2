module Subprover :
  sig
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
    val subprover_call : subprover -> 'a -> subprover_run
    val subprover_update_status : bool -> subprover_run -> subprover_run
    val subprover_fetch_result : subprover_run -> string
    val subprover_wait_result : subprover_run -> string
    val subprover_update : subprover_run -> subprover_run
    val default_subprover : subprover
  end
