module SState = State
open Soteria_c_vendor
open Soteria.Soteria_std
open Soteria.Logs.Import
open Core_value.Syntax
open Syntaxes.FunctionWrap
open Csymex
module Mu = Usable_mucore
open Mu
open SState.SM
include Result

type 'a t = ('a, Cn_error.with_trace, SState.syn list) Result.t

let lift (type a) (m : a Csymex.t) : a t =
  SState.SM.lift @@ Csymex.map Compo_res.ok m

let lift_symex_res (type a)
    (s : (a, Cn_error.with_trace, SState.syn list) Csymex.Result.t) : a t =
  SState.SM.lift s

let lift_sm x = SState.SM.map Compo_res.ok x

let with_extra_call_trace ~loc ~msg : 'a t -> 'a t =
  map_error @@ fun (e, trace) ->
  let elem = Soteria.Terminal.Call_trace.mk_element ~loc ~msg () in
  (e, elem :: trace)

let branches b = SState.SM.branches b

let[@inline] error (err : Cn_error.t) : 'a t =
  lift_symex_res @@ Cn_error.error_with_loc err

let not_impl fmt =
  Fmt.kstr (fun str -> SState.SM.lift @@ Soteria_c_helpers.not_impl str) fmt

let of_opt_not_impl ~msg = function Some x -> ok x | None -> not_impl "%s" msg

let with_loc ~loc (f : unit -> 'a t) =
 fun state -> Csymex.with_loc ~loc (f () state)

module CV = struct
  let cast_int v =
    Core_value.cast_int v
    |> of_opt_not_impl ~msg:"cast_int: value is not an integer"

  let cast_type v =
    Core_value.cast_type v
    |> of_opt_not_impl ~msg:"cast_type: value is not a type"

  let cast_ptr v =
    Core_value.cast_ptr v
    |> of_opt_not_impl ~msg:"cast_ptr: value is not a pointer"
end

module Syntax = struct
  let ( let* ) x f = bind f x
  let ( let+ ) x f = map f x
  let ( let*^ ) (x : 'a Csymex.t) (f : 'a -> 'b t) : 'b t = bind f (lift x)
  let ( let+^ ) (x : 'a Csymex.t) (f : 'a -> 'b) : 'b t = map f (lift x)

  module Symex_syntax = Syntax.Symex_syntax
end

let assert_or_error (b : Typed.(T.sbool t)) err : unit t =
  let open Syntax in
  let*^ loc = Csymex.get_loc () in
  let err =
    (err, Soteria.Terminal.Call_trace.singleton ~loc ~msg:"Assert failure" ())
  in
  SState.SM.assert_or_error b err

module State = struct
  open Syntax

  let alloc_ty ty = SState.alloc_ty (Cn.Sctypes.to_ctype ty)

  let alloc size =
    let* size = CV.cast_int size in
    SState.alloc size

  let store ptr ty v =
    let relevant_values =
     fun f ->
      f ptr;
      f v
    in
    let* ptr = CV.cast_ptr ptr in
    let ty = Cn.Sctypes.to_ctype ty in
    let v = Core_value.to_agv v in
    Cn_assert.with_recovery_attempt ~values:relevant_values
      (SState.store ptr ty v)

  let load ptr ty =
    let relevant_values = Iter.singleton ptr in
    let* ptr = CV.cast_ptr ptr in
    let ty = Cn.Sctypes.to_ctype ty in
    let+ v =
      Cn_assert.with_recovery_attempt ~values:relevant_values
        (SState.load ptr ty)
    in
    Core_value.of_agv ~ty v

  let free ptr =
    let relevant_values = Iter.singleton ptr in
    let* ptr = CV.cast_ptr ptr in
    Cn_assert.with_recovery_attempt ~values:relevant_values (SState.free ptr)

  let unfold_on_if_else guard =
    [%l.debug
      "If/else guard is %a, finding something to unfold." Core_value.pp guard];
    let+ could_unfold =
      lift_sm
      @@ Cn_assert.unfold_with_heuristics
           (Unfold_heuristics.if_else_heuristics guard)
    in
    if could_unfold then
      [%l.debug "Successfully unfolded something for the if/else guard."]
    else [%l.debug "Nothing to unfold for the if/else guard."]
end
