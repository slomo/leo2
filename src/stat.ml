(* Simple stats module *)

module StringMap = Map.Make (String)

let string_of_StringMap (f: 'a -> string) (map: 'a StringMap.t) : string =
  let cstrs = StringMap.fold
    (fun k v rem -> (k ^ ":" ^ (f v)) :: rem )
    map
    []
  in
  String.concat "|" cstrs


(* counters *)
let counters = ref StringMap.empty ;;

let count_step (counter: string) (value: int) =
  counters :=
    if StringMap.mem counter !counters
    then StringMap.add counter ((StringMap.find counter !counters) + value) !counters
    else StringMap.add counter value !counters
;;
  
let count counter =
  count_step counter 1
;; 

let string_of_counters =
  string_of_StringMap string_of_int
;;

(* timers *)
let timers : (float * float) StringMap.t ref = ref StringMap.empty ;;    

let start_timer timer = 
  (* we need realtime not processer ticks as in Sys.time ()*)
  let current_time = Unix.gettimeofday() in
  timers :=
    if StringMap.mem timer !timers
    then StringMap.add timer
      (fst (StringMap.find timer !timers), current_time)
      !timers
    else
      StringMap.add timer (0.0, current_time) !timers
;;

let stop_timer timer =
  let current_time =  Unix.gettimeofday() in
  let (acc, start_time) = StringMap.find timer !timers in
  timers := StringMap.add timer (acc +. (current_time -. start_time), (-1.0)) !timers
;;

(* also stops all timers *)
let string_of_timers =
  string_of_StringMap (fun (acc, start_time) ->
    let current_time =  Unix.gettimeofday() in
    if start_time = -1.0 then
      string_of_float acc
    else
      let value = acc +. (current_time -. start_time) in
      string_of_float value)
;;


let stats_string () =
  "% LEO-II counters: " ^ string_of_counters !counters ^
  "\n% LEO-II timers: " ^ string_of_timers !timers




