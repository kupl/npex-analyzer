open! IStd
open! Vocab
module L = Logging
module F = Format

let from_alarm_json program =
  L.progress " - Localize NPE by alarm.json@." ;
  let nullpoint = NullPoint.from_alarm_report program "alarm.json" in
  L.progress "NullPoint : %a@." NullPoint.pp nullpoint ;
  let trace = ErrInfo.from_alarm_report "alarm.json" in
  CallTrace.from_alarm program trace ;
  let traces = ErrTrace.from_call_trace program nullpoint in
  (nullpoint, traces)


let from_npe_json program =
  L.progress " - Localize NPE by npe.json and trace.json...@." ;
  let nullpoint = NullPoint.from_error_report program "npe.json" in
  L.progress " - NullPoint : %a@." NullPoint.pp nullpoint ;
  let trace = ErrInfo.from_report "trace.json" in
  print_endline " - generating callgraph from trace.json..." ;
  CallTrace.from_alarm program trace ;
  print_endline " - generating callgraph from trace.json... done!" ;
  print_endline " - analyzing paths..." ;
  let traces = ErrTrace.from_call_trace program nullpoint in
  print_endline " - analyzing paths... done!" ;
  (nullpoint, traces)


let launch () = ()
