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

(* ───────────────────────── ADT helpers ───────────────────────── *)

module Adt = struct
  module Adt_ext = Soteria_c_vendor.Adt_ext

  (* CN datatype and constructor names are unique at top level, so the
     human-readable name is a valid mangling. *)
  let adt_name (sym : Symbol_std.t) : string =
    Fmt.str "%a" Symbol_std.pp_hum sym

  let rec desc_of_bt (bt : Cn.BaseTypes.t) : Adt_ext.sort_desc option =
    match bt with
    | Bool -> Some DBool
    | Bits (_, n) -> Some (DBits n)
    | Loc () -> Some (DPtr Typed.ptr_bits)
    | Datatype s -> Some (DAdt (adt_name s))
    | Map (k, v) -> (
        match (desc_of_bt k, desc_of_bt v) with
        | Some k, Some v -> Some (DMap (k, v))
        | _ -> None)
    | _ -> None

  (** Register every datatype of the program in the extension registry. *)
  let register_datatypes (datatypes : (Symbol_std.t * 'a) list)
      ~(cases : 'a -> (Symbol_std.t * (Cn.Id.t * Cn.BaseTypes.t) list) list) :
      unit =
    Adt_ext.reset ();
    List.iter
      (fun (adt_sym, dt) ->
        let adt = adt_name adt_sym in
        let cons =
          List.map
            (fun (con_sym, fields) ->
              let fields =
                List.map
                  (fun (id, bt) ->
                    match desc_of_bt bt with
                    | Some d -> (Cn.Id.get_string id, d)
                    | None ->
                        Soteria.Logs.Import.L.failwith
                          "Unsupported field type in datatype %s" adt)
                  fields
              in
              ({ con = adt_name con_sym; fields } : Adt_ext.con_def))
            (cases dt)
        in
        Adt_ext.register { adt; cons })
      datatypes

  (* Register solver signatures for the functions that stay uninterpreted
     ([Rec_Def]/[Uninterp]); non-recursive [Def]s are always inlined. *)
  let register_functions
      (functions : (Symbol_std.t * Cn.Definition.Function.t) list) : unit =
    List.iter
      (fun ((fsym, def) : _ * Cn.Definition.Function.t) ->
        match def.body with
        | Def _ -> ()
        | Rec_Def _ | Uninterp ->
            let fn = adt_name fsym in
            let desc bt =
              match desc_of_bt bt with
              | Some d -> d
              | None ->
                  Soteria.Logs.Import.L.failwith
                    "Unsupported sort in logical function %s" fn
            in
            Adt_ext.register_fun
              {
                fn;
                arg_sorts = List.map (fun (_, bt) -> desc bt) def.args;
                ret_sort = desc def.return_bt;
              })
      functions
end
