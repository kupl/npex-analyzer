open! IStd
module F = Format
module L = Logging
module StringMap = PrettyPrintable.MakePPMap (String)

type profiler = (int * float) StringMap.t

type events = float StringMap.t

let profiler : profiler ref = ref StringMap.empty

let events : events ref = ref StringMap.empty

let start_time = ref 0.0

let pp fmt x =
  let tot_time = Unix.gettimeofday () -. !start_time in
  let pp_item fmt (event, (cnt, time)) =
    let percentage = time /. tot_time *. 100.0 in
    F.fprintf fmt "%s --> (%d times, %f sec. (%f%%))@." event cnt time percentage
  in
  PrettyPrintable.pp_collection ~pp_item fmt (StringMap.bindings x)


let path = ref (Config.results_dir ^/ "profiler.log")

let init ?(log = "profiler.log") () =
  profiler := StringMap.empty ;
  path := Config.results_dir ^/ log ;
  start_time := Unix.gettimeofday ()


let start_event event =
  let st = Unix.gettimeofday () in
  events := StringMap.add event st !events


let finish_event event =
  let ft = Unix.gettimeofday () in
  let st = StringMap.find event !events in
  let elapsed_time = ft -. st in
  let cnt, time = try StringMap.find event !profiler with _ -> (0, 0.0) in
  profiler := StringMap.add event (cnt + 1, time +. elapsed_time) !profiler


let pick (event : string) (f : 'a -> 'b) (arg : 'a) : 'b =
  start_event event ;
  let value = f arg in
  finish_event event ; value


let report () =
  Utils.with_file_out !path ~f:(fun oc -> F.fprintf (F.formatter_of_out_channel oc) "%a@." pp !profiler)
