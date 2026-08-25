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
              (* CN's leak check is resource-emptiness: a block that owns no
                 bytes (freed, or its ownership consumed by e.g. a loop
                 invariant) is not a leak. *)
              if not (Block.owns_nothing block) then Some block.info else None)
            (Heap.syntactic_bindings heap)
          |> List.of_seq
    in
    List.sort_uniq Stdlib.compare result
end

module Uninterpreted =
  Predicates.Uninterpreted
    (struct
      include Symbol_std

      let pp = pp_hum
    end)
    (Core_value)

(* ─────────────── quantified facts, movable indices, Q chunks ─────────────── *)

type annot = Cn.(BaseTypes.t Terms.annot)

module Facts = struct
  (** A quantified assumption [forall (q : q_bt). body]. Never sent to the
      solver as a quantifier; used by [instantiate] (CN's QF discipline).
      [FIt] carries a spec term with [snapshot] closing its free variables;
      [FClosure] carries an already-closed body (e.g. the per-index value
      equalities of a merged [each] output). *)
  type fact =
    | FIt of {
        q : Symbol_std.t;
        q_bt : Cn.BaseTypes.t;
        body : annot;
        snapshot : Subst.t;
      }
    | FClosure of {
        q_bt : Cn.BaseTypes.t;
        body : Typed.T.sint Typed.t -> Typed.T.sbool Typed.t Csymex.t;
      }

  type t = fact list

  let pp_fact ft = function
    | FIt { q; body; _ } ->
        Fmt.pf ft "@[<2>forall %a.@ %a@]" Symbol_std.pp_hum q Mu.pp_it body
    | FClosure _ -> Fmt.pf ft "<closure fact>"

  let pp = Fmt.Dump.list pp_fact
end

module Movable = struct
  (** Indices registered by the [extract] statement. *)
  type target = MOwned of Cn.Sctypes.t | MPred of Symbol_std.t

  type t = (target * Typed.T.sint Typed.t) list

  let pp_target ft = function
    | MOwned ty -> Mu.pp_sct ft ty
    | MPred s -> Symbol_std.pp_hum ft s

  let pp = Fmt.Dump.list (Fmt.pair ~sep:(Fmt.any "@") pp_target Typed.ppa)

  let matches (target : target) (qname : Mu.Request.QPredicate.name) : bool =
    match (target, qname) with
    | MOwned ty, QOwned (ty', _) -> Cn.Sctypes.equal ty ty'
    | MPred s, QPName s' -> Symbol_std.equal s s'
    | _ -> false
end

module Qpreds = struct
  (** Permissions are closures over the index — this lets residual permissions
      mention evaluated symbolic values (e.g. exclusion of an extracted
      symbolic index), which an IT representation could not. Closures are pure
      and immutable, so the state stays persistent. *)
  type perm = Typed.T.sint Typed.t -> Typed.T.sbool Typed.t Csymex.t

  type iargs = Typed.T.sint Typed.t -> Core_value.t list Csymex.t
  (** The predicate's extra input arguments, as a function of the index
      (empty for [Owned] eaches). *)

  (** An [each] chunk: footprint at [pointer + q*step] for every index [q]
      satisfying [perm]; [out] is the map-valued output. *)
  type chunk = {
    qname : Mu.Request.QPredicate.name;
    pointer : Typed.T.sptr Typed.t;
    q_bt : Cn.BaseTypes.t;
    step : Cn.Sctypes.t;
    perm : perm;
    iargs : iargs;
    out : Core_value.t;
  }

  type t = chunk list

  let pp_chunk ft { qname; pointer; out; _ } =
    Fmt.pf ft "@[<2>each i.@ %a(%a + i*step) |-> %a@]" Mu.Request.pp_qname
      qname Typed.ppa pointer Core_value.pp out

  let pp = Fmt.Dump.list pp_chunk
end

type t = {
  base : SState.t option;
  preds : Uninterpreted.t option;
  facts : Facts.t; [@sym_state.ignore { empty = []; pp = Facts.pp }]
  movable : Movable.t; [@sym_state.ignore { empty = []; pp = Movable.pp }]
  qpreds : Qpreds.t; [@sym_state.ignore { empty = []; pp = Qpreds.pp }]
}
[@@deriving sym_state { symex = Csymex }]

(* ───────────── predicate combinators (moved from With_preds) ───────────── *)

let produce_pred name ins outs state =
  let open Csymex.Syntax in
  let st = of_opt state in
  let+ preds = Uninterpreted.produce' name ins outs st.preds in
  ((), to_opt { st with preds })

let consume_pred_inner name ins = with_preds (Uninterpreted.consume' name ins)

let unfold_with_heuristics ~produce_def ?can_unfold heuristics =
  let open SM in
  let open Syntax in
  let* state = get_state () in
  let st = of_opt state in
  match
    Uninterpreted.take_max_with_heurisitcs ?can_unfold heuristics st.preds
  with
  | None ->
      [%l.debug "Heuristics failed to find any predicate to unfold."];
      return false
  | Some (p, preds) ->
      [%l.debug "Heuristics is unfolding predicate %a" Uninterpreted.pp_pred p];
      let name, ins, outs = p in
      let state = to_opt { st with preds } in
      let*^ (), state = produce_def name ins outs state in
      let+ () = set_state state in
      true

let with_recovery_attempt ~produce_def ?can_unfold ~heuristics
    (f : ('a, 'err, syn list) SM.Result.t) : ('a, 'err, syn list) SM.Result.t =
  let open Csymex.Syntax in
  fun state ->
    let* first_res, first_state = f state in
    match first_res with
    | Compo_res.Ok _ -> Csymex.return (first_res, first_state)
    | Missing _ | Error _ -> (
        (* We give another attempt by finding a matching predicate to unfold *)
        let* could_unfold, state' =
          unfold_with_heuristics ~produce_def ?can_unfold heuristics first_state
        in
        if not could_unfold then Csymex.return (first_res, first_state)
        else
          (* We execute the operation a second time hoping for a better
             outcome. *)
          let* snd_res, snd_state = f state' in
          match snd_res with
          | Ok _ -> Csymex.return (snd_res, snd_state)
          | Missing _ | Error _ ->
              (* We failed even with our recovery tactic, we return the first
                 return before the attempt. *)
              Csymex.return (first_res, first_state))

(* ───────────────────────── lifted memory operations ───────────────────────── *)

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
    let st = of_opt state in
    let+ base = f st.base in
    to_opt { st with base }

let pp_pretty ~ignore_freed ft st =
  Fmt.pf ft
    "@[<v 2>State:@ %a@]@ @[<v 2>Predicates:@ %a@]@ @[<v 2>Each:@ %a@]@ @[<v \
     2>Facts:@ %a@]"
    (Fmt.option ~none:(Fmt.any "Empty Heap") @@ SState.pp_pretty ~ignore_freed)
    st.base
    (Fmt.option @@ Uninterpreted.pp)
    st.preds Qpreds.pp st.qpreds Facts.pp st.facts

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

let consume_pred name ins = lift_consumer_error @@ consume_pred_inner name ins

(** [Kill] of a stack variable: free the allocation when the pointer denotes a
    real block; otherwise (ownership produced from a spec — e.g. in a
    loop-label obligation — has no allocation bounds) consume the variable's
    footprint, which is what CN's [Kill] does. *)
let kill_static ptr ty : (unit, _, _) SM.Result.t =
 fun state ->
  let open Csymex.Syntax in
  let* res, state' = with_miss_as_error (with_base (SState.free ptr)) state in
  match res with
  | Compo_res.Ok () -> Csymex.return (res, state')
  | Error _ | Missing _ -> (
      let* res2, state2 =
        (lift_consumer_error @@ with_base (SState.consume_any ptr ty)) state
      in
      match res2 with
      | Compo_res.Ok _ -> Csymex.return (Compo_res.Ok (), state2)
      | Error _ | Missing _ ->
          (* Report the failure of the [free] attempt. *)
          Csymex.return (res, state'))

let alloc_ty ty = with_miss_as_error @@ with_base (SState.alloc_ty ty)
let alloc size = with_miss_as_error @@ with_base (SState.alloc size)
let store ptr ty v = with_miss_as_error @@ with_base (SState.store ptr ty v)
let load ptr ty = with_miss_as_error @@ with_base (SState.load ptr ty)
let free ptr = with_miss_as_error @@ with_base (SState.free ptr)

(* ─────────────── accessors for the plain-data components ─────────────── *)

let add_fact (fact : Facts.fact) : unit SM.t =
 fun state ->
  let st = of_opt state in
  Csymex.return ((), to_opt { st with facts = fact :: st.facts })

let get_facts : Facts.t SM.t =
 fun state -> Csymex.return ((of_opt state).facts, state)

let add_movable (m : Movable.target * Typed.T.sint Typed.t) : unit SM.t =
 fun state ->
  let st = of_opt state in
  Csymex.return ((), to_opt { st with movable = m :: st.movable })

let get_movable : Movable.t SM.t =
 fun state -> Csymex.return ((of_opt state).movable, state)

let add_qpred (c : Qpreds.chunk) : unit SM.t =
 fun state ->
  let st = of_opt state in
  Csymex.return ((), to_opt { st with qpreds = c :: st.qpreds })

let get_qpreds : Qpreds.t SM.t =
 fun state -> Csymex.return ((of_opt state).qpreds, state)

let set_qpreds (qpreds : Qpreds.t) : unit SM.t =
 fun state ->
  let st = of_opt state in
  Csymex.return ((), to_opt { st with qpreds })

let leaks state =
  let st = of_opt state in
  (* FIXME: we can do better! *)
  let pred_leaks = if Option.is_none st.preds then [] else [ None ] in
  let qpred_leaks = if List.is_empty st.qpreds then [] else [ None ] in
  pred_leaks @ qpred_leaks @ SState.leaks st.base
