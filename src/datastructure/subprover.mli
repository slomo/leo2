val ( |- ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
type kind = Modelfinder | Folprover | Incremental
val string_of_kind : kind -> string
type subprover = {
  sp_type : kind;
  path : string;
  name : string;
  options : string list;
  debug : bool;
}
val string_of_prover : subprover -> string
type run = {
  inputId :  int;
  subprover : subprover;
  pid : int;
  channels : out_channel * in_channel;
}
val string_of_run : run -> string
type result = {
  from : run;
  channel : in_channel;
  fragments : string list;
  szs : Szs.status;
}
val string_of_result : result -> string
type state = {
  max_parrallel : int;
  provers : subprover list;
  running : run list;
  waiting : ((int * string) * subprover) list;
  results : result list;
}
val string_of_state : state -> string
