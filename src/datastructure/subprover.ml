let (|-) f g = fun (x) -> f (g x ) ;;

(** Modles the various types of subprover:
    {ul
*)
type kind = 
  Modelfinder (** {- Modelfinder } *)
| Folprover (** {- First Order Prover (E, Vampire ... ) } *)
| Incremental (**  {- Incremental ( Z3 ) } *)
;;
(** ul} *)

let string_of_kind (kind: kind) = match kind with
  | Folprover -> "atp"
  | Modelfinder -> "mf"
  | Incremental -> "itp"
;;

(** Instances of that type a concrete subprovers. *)
type subprover = {
  sp_type: kind;
  path: string; (* abs or rel path to executable *)
  name: string; (* humanreadale name of the prover *)
  options : string list; (* list of standard options *)
  debug: bool
};;

let string_of_prover (prover:subprover) : string =
  prover.path ^ "[" ^ string_of_kind prover.sp_type ^ "]"
;;

(** Every call to a subprover results in a subprover run. *)
type run = {
  subprover: subprover;
  pid: int;
  channels: out_channel * in_channel;
};;

let string_of_run (run:run) = match run with
  | { subprover =  prover; pid = pid } ->
   string_of_prover(prover) ^ "@" ^ string_of_int pid
;;

type result = {
  from: subprover;
  channel: in_channel;
  fragments: string list;
  szs: Szs.status
}

let string_of_result (res: result) =
  "result(" ^ Szs.string_of_szs res.szs ^ ")"

type controller = {
  max_parrallel: int;
  provers:  subprover list;
  running: run list;
  waiting: ( string * subprover) list;
  results: result list;
};;

let string_of_controller (con:controller) =
  "{ running: " ^ String.concat "\n           "
    (List.map string_of_run con.running) ^ "\n" ^
  "  waiting: " ^ String.concat "\n           "
    (List.map (string_of_prover |- snd) con.waiting) ^ "\n" ^
  "  results: " ^ String.concat "\n           "
    (List.map string_of_result con.results)  ^ "}"
;;
