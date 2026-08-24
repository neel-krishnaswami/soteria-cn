open Soteria_c_vendor
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Core_value.Syntax
open Csymex
module Mu = Usable_mucore
open Mu
module Predicates = Predicates.M (Csymex)

module SState = struct
  include Soteria_c_vendor.State_variants.Lazy

  let consume_owned ptr ty : (Core_value.t, _, _) SM.Result.t =
    let open SM.Syntax in
    let ty = Sctypes.to_ctype ty in
    let++ v = consume_aggregate' ptr ty in
    Core_value.of_agv ~ty v

  let consume_uninit ptr ty =
    let open SM.Syntax in
    let*^ len = Layout.size_of_s (Sctypes.to_ctype ty) in
    let loc = Typed.Ptr.loc ptr in
    let ofs = Typed.Ptr.ofs ptr in
    let++ () = consume_uninit' loc ofs len in
    Core_value.Loaded Unspec

  let consume_any ptr ty =
    let open SM.Syntax in
    let*^ len = Layout.size_of_s (Sctypes.to_ctype ty) in
    let loc = Typed.Ptr.loc ptr in
    let ofs = Typed.Ptr.ofs ptr in
    let++ () = consume_any' loc ofs len in
    Core_value.Loaded Unspec

  let produce_owned (ptr : Typed.(T.sptr t)) (ty : Sctypes.t) (v : Core_value.t)
      (t : t option) : t option Csymex.t =
    let ty = Sctypes.to_ctype ty in
    let agv = Core_value.to_agv v in
    produce_aggregate' ptr ty agv t

  let leaks (state : t option) : Cerb_location.t option list =
    let result =
      match state with
      | None | Some { heap = None; _ } -> []
      | Some { heap = Some heap; _ } ->
          Seq.filter_map
            (fun (_, (block : Block.t)) ->
              if not (Block.is_freed block) then Some block.info else None)
            (Heap.syntactic_bindings heap)
          |> List.of_seq
    in
    List.sort_uniq Stdlib.compare result
end

module PState =
  Predicates.With_preds
    (struct
      include Symbol_std

      let pp = pp_hum
    end)
    (Core_value)
    (SState)

include PState

let with_miss_as_error (m : (_, _, _) SM.Result.t) =
  let open SM.Syntax in
  let* res = m in
  match res with
  | Compo_res.Ok x -> SM.return (Compo_res.Ok x)
  | Error e -> SM.return (Compo_res.Error e)
  | Missing _ ->
      let*^ loc = Csymex.get_loc () in
      let trace =
        Soteria.Terminal.Call_trace.singleton ~loc
          ~msg:
            "Memory operation requires additional resource (it may be hidden \
             in predicates?)"
          ()
      in
      SM.return (Compo_res.Error (`Missing_resource, trace))

let lift_produce (f : SState.t option -> SState.t option Csymex.t) :
    t option -> t option Csymex.t =
  let open Csymex.Syntax in
  fun state ->
    let { preds; base } = PState.of_opt state in
    let+ base = f base in
    PState.to_opt { preds; base }

let pp_pretty ~ignore_freed ft { base; preds } =
  Fmt.pf ft "@[<v 2>State:@ %a@]@ @[<v 2>Predicates:@ %a@]"
    (Fmt.option ~none:(Fmt.any "Empty Heap") @@ SState.pp_pretty ~ignore_freed)
    base
    (Fmt.option @@ Uninterpreted.pp)
    preds

(* HACK: until I make the signature of consumers and producers prettier in Soteria *)
let lift_produce (f : SState.t option -> SState.t option Csymex.t) : unit SM.t =
  let open Csymex.Syntax in
  fun st ->
    let+ st = lift_produce f st in
    ((), st)

let produce_owned ptr cty v = lift_produce (SState.produce_owned ptr cty v)
let produce_any' loc ofs len = lift_produce (SState.produce_any' loc ofs len)

let produce_uninit' loc ofs len =
  lift_produce (SState.produce_uninit' loc ofs len)

let lift_consumer_error (m : ('a, [< Cn_error.t ], 's) SM.Result.t) :
    ('a, Cn_error.with_trace, 's) SM.Result.t =
  let open SM.Syntax in
  let*^ loc = Csymex.get_loc () in
  let mk_trace msg = Soteria.Terminal.Call_trace.singleton ~loc ~msg () in
  let+ res = m in
  match res with
  | Compo_res.Ok x -> Compo_res.Ok x
  | Error e ->
      let trace = mk_trace "Could not consume resource" in
      Error (e, trace)
  | Missing _ ->
      let trace =
        mk_trace "Missing resource (could be hidden under a predicate?)"
      in
      Error (`Missing_resource, trace)

let consume_owned ptr ty =
  lift_consumer_error @@ with_base (SState.consume_owned ptr ty)

let consume_any ptr ty =
  lift_consumer_error @@ with_base (SState.consume_any ptr ty)

let consume_uninit ptr ty =
  lift_consumer_error @@ with_base (SState.consume_uninit ptr ty)

let consume_pred name ins = lift_consumer_error @@ PState.consume_pred name ins
let alloc_ty ty = with_miss_as_error @@ with_base (SState.alloc_ty ty)
let alloc size = with_miss_as_error @@ with_base (SState.alloc size)
let store ptr ty v = with_miss_as_error @@ with_base (SState.store ptr ty v)
let load ptr ty = with_miss_as_error @@ with_base (SState.load ptr ty)
let free ptr = with_miss_as_error @@ with_base (SState.free ptr)

let leaks state =
  let { base; preds } = of_opt state in
  (* FIXME: we can do better! *)
  let pred_leaks = if Option.is_none preds then [] else [ None ] in
  pred_leaks @ SState.leaks base
