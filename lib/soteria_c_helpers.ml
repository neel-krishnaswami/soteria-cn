open Soteria_c_vendor

let not_impl desc =
  let open Csymex.Syntax in
  let* loc = Csymex.get_loc () in
  let open Soteria.Terminal in
  let call_trace = Call_trace.singleton ~loc ~msg:desc () in
  let labels =
    Diagnostic.call_trace_to_labels ~as_ranges:Error.Diagnostic.as_ranges
      call_trace
  in
  let severity = Grace.Diagnostic.Severity.Warning in
  let diag = Grace.Diagnostic.createf ~labels severity "%s" desc in
  let msg = (Fmt.to_to_string Diagnostic.pp) diag in
  Csymex.not_impl msg

let of_opt_not_impl ~msg = function
  | Some x -> Csymex.return x
  | None -> not_impl msg
