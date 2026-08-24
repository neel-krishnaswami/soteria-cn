module Csymex = Soteria_c_vendor.Csymex
module Diagnostic = Soteria.Terminal.Diagnostic

type t =
  [ Soteria_c_vendor.Error.t | Csymex.cons_fail | `Missing_resource | `No_spec ]

type with_trace = t * Cerb_location.t Soteria.Terminal.Call_trace.t

let error_with_loc ?(msg = "Triggering operation") (err : [< t ]) =
  let open Csymex.Syntax in
  let* loc = Csymex.get_loc () in
  let err = (err, Soteria.Terminal.Call_trace.singleton ~loc ~msg ()) in
  Csymex.Result.error err

(* Render a single [error] (either a soteria-c memory error or a logical
   consumption failure coming from the symex engine). *)
let pp ft : t -> unit = function
  | #Soteria_c_vendor.Error.t as e -> Soteria_c_vendor.Error.pp ft e
  | #Csymex.cons_fail as e -> Csymex.pp_cons_fail ft e
  | `Missing_resource -> Fmt.pf ft "Missing resource (under-specified)"
  | `No_spec -> Fmt.pf ft "Calling a function with no body or specification"

let severity : t -> Diagnostic.severity = function
  | #Soteria_c_vendor.Error.t as e -> Soteria_c_vendor.Error.severity e
  | #Csymex.cons_fail | `Missing_resource -> Diagnostic.Error
  | `No_spec -> Diagnostic.Error
