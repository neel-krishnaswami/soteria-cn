open Soteria.Soteria_std
open Soteria.Logs.Import
module Mu = Usable_mucore
module Typed = Soteria_c_vendor.Typed
module Csymex = Soteria_c_vendor.Csymex
module Layout = Soteria_c_vendor.Layout
open Csymex
open Syntax
open Soteria_c_helpers
module Producer = Producer_monad
module Consumer = Consumer_monad
module Sym = Soteria_c_vendor.Symbol_std
module LSubst = Subst

type term = Cn.(BaseTypes.t Terms.term)
type annot = Cn.(BaseTypes.t Terms.annot)

let pp_okind ft = function
  | Mu.Request.Init -> Fmt.pf ft "Init"
  | Uninit -> Fmt.pf ft "Uninit"

(* ───────────────────────── each() helpers ───────────────────────── *)

module AE = Soteria_c_vendor.Adt_ext

let index_width (q_bt : Cn.BaseTypes.t) : int option =
  match q_bt with Bits (_, n) -> Some n | _ -> None

(** Close a permission IT into a {!State.Qpreds.perm} closure. *)
let perm_closure ~qsym ~(q_bt : Cn.BaseTypes.t) (it : annot) (close : Subst.t)
    : State.Qpreds.perm =
 fun i ->
  let open Csymex.Syntax in
  let* iv =
    match q_bt with
    | Cn.BaseTypes.Bits _ -> Csymex.return (Core_value.Obj (Int i))
    | _ -> Csymex.not_impl "each: non-bitvector index sort"
  in
  let* v = Subst.eval_annot (Subst.add qsym iv close) it in
  match Core_value.cast_bool v with
  | Some b -> Csymex.return b
  | None -> Csymex.not_impl "each: permission is not a boolean"

(** Close a quantified predicate's extra input arguments into an index-indexed
    closure. *)
let iargs_closure ~qsym ~(q_bt : Cn.BaseTypes.t) (iargs : annot list)
    (close : Subst.t) : State.Qpreds.iargs =
 fun i ->
  let open Csymex.Syntax in
  let* iv =
    match q_bt with
    | Cn.BaseTypes.Bits _ -> Csymex.return (Core_value.Obj (Int i))
    | _ -> Csymex.not_impl "each: non-bitvector index sort"
  in
  Csymex.map_list ~f:(Subst.eval_annot (Subst.add qsym iv close)) iargs

(** [true] iff [f i] is provable for an arbitrary (fresh, unconstrained) [i] —
    a sound forall-check by skolemization. *)
let csym_holds_forall ~width (f : State.Qpreds.perm) : bool Csymex.t =
  let open Csymex.Syntax in
  let* i = Csymex.nondet (Typed.t_int width) in
  let* b = f i in
  if%sure b then Csymex.return true else Csymex.return false

let qname_equal (a : Mu.Request.QPredicate.name)
    (b : Mu.Request.QPredicate.name) =
  match (a, b) with
  | QOwned (ty1, Mu.Request.Init), QOwned (ty2, Mu.Request.Init)
  | QOwned (ty1, Uninit), QOwned (ty2, Uninit) ->
      Cn.Sctypes.equal ty1 ty2
  | QPName s1, QPName s2 -> Sym.equal s1 s2
  | _ -> false

let cell_desc_of_qname (qname : Mu.Request.QPredicate.name) :
    AE.sort_desc option =
  match qname with
  | QOwned (ty, _) -> Soteria_c_helpers.Adt.desc_of_bt (Cn.Memory.bt_of_sct ty)
  | QPName name ->
      let def = Ctx.get_pred_def name in
      Soteria_c_helpers.Adt.desc_of_bt (snd def.oarg)

(** The permission [q < n] for an [n]-element array, built as an IT and
    evaluated through the standard evaluator so that array-form and each-form
    permissions can never diverge (e.g. on comparison signedness). *)
let array_perm ~(q_bt : Cn.BaseTypes.t) (n : int) : State.Qpreds.perm =
  let here = Cn.Locations.other "soteria-cn array permission" in
  let qsym = Cn.Sym.fresh "i" in
  let it =
    Cn.IndexTerms.lt_
      ( Cn.IndexTerms.sym_ (qsym, q_bt, here),
        Cn.IndexTerms.num_lit_ (Z.of_int n) q_bt here )
      here
  in
  perm_closure ~qsym ~q_bt it Subst.empty

(** The port of CN's [qpredicate_request]: consume an [each] footprint from the
    movable-index cells and the held Q chunks, and assemble the map output. *)
let consume_qpred ~consume_cell_pred ~(qname : Mu.Request.QPredicate.name)
    ~(ptr : Typed.T.sptr Typed.t) ~(q_bt : Cn.BaseTypes.t)
    ~(step : Cn.Sctypes.t) ~(req_iargs : State.Qpreds.iargs)
    ~(needed : State.Qpreds.perm) :
    (Core_value.t, _, State.syn list) State.SM.Result.t =
  let open State.SM in
  let open State.SM.Syntax in
  let*^ width =
    index_width q_bt |> Csymex.of_opt_not_impl ~msg:"each: index width"
  in
  let*^ step_size = Layout.size_of_s (Cn.Sctypes.to_ctype step) in
  let*^ cell_desc =
    cell_desc_of_qname qname
    |> Csymex.of_opt_not_impl ~msg:"each: unsupported cell sort"
  in
  let key_desc = AE.DBits width in
  let cell_ptr k =
    Typed.Ptr.add_ofs ptr (Typed.cast (Typed.BitVec.mul k step_size))
  in
  (* Phase 1: extraction at movable indices (CN's One cases). *)
  let* movable = State.get_movable in
  let rec extract_loop needed ones = function
    | [] -> Result.ok (needed, ones)
    | (target, k) :: rest ->
        if not (State.Movable.matches target qname) then
          extract_loop needed ones rest
        else
          let*^ take =
            let open Csymex.Syntax in
            let* b = needed k in
            if%sure b then Csymex.return true else Csymex.return false
          in
          if not take then extract_loop needed ones rest
          else
            let** v =
              match qname with
              | QOwned (ty, Mu.Request.Init) ->
                  State.with_base (State.SState.consume_owned (cell_ptr k) ty)
              | QOwned (ty, Uninit) ->
                  State.with_base (State.SState.consume_uninit (cell_ptr k) ty)
              | QPName name ->
                  (* Cells of a predicate [each] are folded instances. *)
                  let*^ extra = req_iargs k in
                  consume_cell_pred name
                    (Core_value.Obj (Ptr (cell_ptr k)) :: extra)
            in
            let*^ vsv =
              Subst.sv_of_cv cell_desc v
              |> Csymex.of_opt_not_impl ~msg:"each: cell sort mismatch"
            in
            let needed' i =
              let open Csymex.Syntax in
              let+ b = needed i in
              Typed.Bool.and_ b Typed.(not (Typed.Infix.( ==@ ) i k))
            in
            extract_loop needed' ((k, vsv) :: ones) rest
  in
  let** needed, ones = extract_loop needed [] movable in
  (* Phase 2: transfer from held Q chunks (CN's Many cases): take from each
     matching chunk the indices where both the (narrowed) request and the
     chunk's permission (and extra input arguments) coincide, with permission
     surgery on both sides. *)
  let* qpreds = State.get_qpreds in
  let*^ manys, needed, qpreds' =
    let open Csymex.Syntax in
    let rec loop manys needed acc = function
      | [] -> Csymex.return (List.rev manys, needed, List.rev acc)
      | (c : State.Qpreds.chunk) :: rest ->
          if
            not (qname_equal c.qname qname && Cn.Sctypes.equal c.step step)
          then loop manys needed (c :: acc) rest
          else
            let* peq =
              if%sure Typed.Infix.( ==@ ) ptr c.pointer then Csymex.return true
              else Csymex.return false
            in
            if not peq then loop manys needed (c :: acc) rest
            else
              (* CN's iarg_match: this chunk can only serve indices where its
                 extra input arguments coincide with the request's. *)
              let take i =
                let* nb = needed i in
                let* ab = c.perm i in
                let* ci = c.iargs i in
                let+ ri = req_iargs i in
                let iargs_eq =
                  try
                    List.fold_left2
                      (fun acc a b ->
                        Typed.Bool.and_ acc (Core_value.sem_eq a b))
                      Typed.v_true ci ri
                  with Invalid_argument _ -> Typed.v_false
                in
                Typed.Bool.and_ nb (Typed.Bool.and_ ab iargs_eq)
              in
              let* take_empty =
                csym_holds_forall ~width (fun i ->
                    let+ b = take i in
                    Typed.not b)
              in
              if take_empty then loop manys needed (c :: acc) rest
              else
                let needed' i =
                  let* nb = needed i in
                  let+ tb = take i in
                  Typed.Bool.and_ nb (Typed.not tb)
                in
                let residual i =
                  let* ab = c.perm i in
                  let+ tb = take i in
                  Typed.Bool.and_ ab (Typed.not tb)
                in
                let* res_empty =
                  csym_holds_forall ~width (fun i ->
                      let+ b = residual i in
                      Typed.not b)
                in
                let acc =
                  if res_empty then acc else { c with perm = residual } :: acc
                in
                loop ((take, c.out) :: manys) needed' acc rest
    in
    loop [] needed [] qpreds
  in
  let* () = State.set_qpreds qpreds' in
  (* Phase 3: remainder check. *)
  let*^ done_ =
    csym_holds_forall ~width (fun i ->
        let open Csymex.Syntax in
        let+ b = needed i in
        Typed.not b)
  in
  if not done_ then
    Result.miss_no_fix ~reason:"each: footprint not fully available" ()
  else
    (* Phase 4: assemble the output map (CN's cases_to_map). *)
    let cast_map_chunk out =
      match Core_value.cast_map out with
      | Some m -> Result.ok m
      | None -> lift @@ Csymex.not_impl "each: chunk output is not a map"
    in
    let** base_map =
      match manys with
      | [] -> Result.ok (Typed.map_default ~key:key_desc ~value:cell_desc)
      | [ (_take, out) ] ->
          (* A single source chunk: its map agrees with the request wherever
             the permission holds, and is arbitrary elsewhere — use it
             directly. *)
          cast_map_chunk out
      | _ :: _ :: _ ->
          (* Several source chunks: a fresh map, constrained per chunk by a
             quantified fact — as in CN, these facts are quantifier-free and
             only usable through [instantiate]. *)
          let*^ m = Csymex.nondet (Typed.t_map key_desc cell_desc) in
          let value_ty = Subst.ty_of_desc cell_desc in
          let** () =
            Result.fold_list manys ~init:() ~f:(fun () (take, out) ->
                let** out_m = cast_map_chunk out in
                let body i =
                  let open Csymex.Syntax in
                  let+ tb = take i in
                  Typed.Bool.or_ (Typed.not tb)
                    (Typed.Infix.( ==@ )
                       (Typed.map_get ~value_ty m i)
                       (Typed.map_get ~value_ty out_m i))
                in
                let* () =
                  State.add_fact (State.Facts.FClosure { q_bt; body })
                in
                Result.ok ())
          in
          Result.ok m
    in
    let out =
      List.fold_left
        (fun m (k, v) -> Typed.map_set ~key:key_desc ~value:cell_desc m k v)
        base_map ones
    in
    Result.ok (Core_value.Map out)

let subst_for_pred_def (def : Mu.predicate_def) iargs =
  (* Both [def.iargs] and [iargs] lead with the pointer, so they line up. *)
  Iter.of_list_combine def.iargs iargs
  |> Iter.map (fun ((sym, _), v) -> (sym, v))
  |> Subst.of_iter

let lift_pure_error ~v m =
  let open State.SM.Syntax in
  let*^ loc = Csymex.get_loc () in
  let mk_trace msg = Soteria.Terminal.Call_trace.singleton ~loc ~msg () in
  let+ res = m in
  match res with
  | Compo_res.Ok x -> Compo_res.Ok x
  | Missing _ -> L.failwith "Cannot miss on pure consumption"
  | Error e ->
      [%l.debug "Could not prove %a holds in the pc below" Typed.ppa v];
      Csymex.log_solver_state ~level:Debug ();
      let trace = mk_trace "Could not prove this holds" in
      Error (e, trace)

(* Sound only in OX mode, of course *)
let logic_assert v : unit Consumer.t =
  Consumer.lift_state @@ lift_pure_error ~v
  @@ State.SM.assert_or_error v (`Lfail v :> Cn_error.t)

let produce_computational_arg
    ((arg, loc) : Mu.computational_arg * Cn.Locations.info) : unit Producer.t =
  let open Producer.With_syntax in
  [%l.trace "Producing computational argument: %a" Mu.pp_computational_arg arg];
  let@ () = Producer.with_loc ~loc:(fst loc) in
  let (Computational (sym, ty) | Ghost (sym, ty)) = arg in
  let*^ v = Core_value.nondet_bt ty in
  Subst.add sym v

let produce_pure (annot : annot) : unit Producer.t =
  let open Producer.With_syntax in
  let* v = Subst.eval_annot annot in
  let*^ v =
    Core_value.cast_bool v |> of_opt_not_impl ~msg:"produce_pure: not a boolean"
  in
  lift @@ assume [ v ]

let rec produce_def_s name ins outs =
  let open State.SM.Syntax in
  let def = Ctx.get_pred_def name in
  let* res = produce_pred_def ~name def ins in
  let out = List.hd outs in
  State.SM.assume [ Core_value.sem_eq res out ]

(* Chunks of clause-less predicates (e.g. the built-in [Alloc] token) can
   never be unfolded; keep the heuristics from picking them. *)
and can_unfold name = Option.is_some (Ctx.get_pred_def name).clauses

and unfold_with_heuristics heuristics =
  State.unfold_with_heuristics ~produce_def:produce_def_s ~can_unfold
    heuristics

and with_recovery_attempt ~values f =
  State.with_recovery_attempt
    ~heuristics:(Unfold_heuristics.recovery_heuristics values)
    ~produce_def:produce_def_s ~can_unfold f

and produce_logical_constraint (lc : Cn.LogicalConstraints.t) : unit Producer.t
    =
  match lc with
  | T it -> produce_pure it
  | Forall ((q, q_bt), body) ->
      (* CN's quantifier-free discipline: quantified assumptions are never sent
         to the solver; they are stored (with the current substitution closing
         their free spec variables) and used by [instantiate]. *)
      let open Producer.With_syntax in
      let* snapshot = Producer.get_state () in
      Producer.lift_state
        (State.add_fact (State.Facts.FIt { q; q_bt; body; snapshot }))

and produce_clause (clause : Mu.clause) =
  let open Producer.With_syntax in
  let@ () = with_loc ~loc:clause.loc in
  let* guard = Subst.eval_annot clause.guard in
  let*^ guard =
    Core_value.cast_bool guard
    |> of_opt_not_impl ~msg:"clause guard isn't a boolean?"
  in
  let*^ () = Csymex.assume [ guard ] in
  let logical_args =
    List.map (fun arg -> (arg, (clause.loc, None))) clause.logical_args
  in
  let* () = iter_list ~f:produce_logical_arg logical_args in
  Subst.eval_annot clause.ret

and produce_pred_def ~name (def : Mu.predicate_def) (iargs : Core_value.t list)
    : Core_value.t State.SM.t =
  let open State.SM.Syntax in
  [%l.trace "Producing the definition of %a" Sym.pp_hum name];
  let+ v, _ =
    Producer.run_with_subst
      ~subst:(subst_for_pred_def def iargs)
      (let open Producer.With_syntax in
       let@ () = with_loc ~loc:def.loc in
       let*^ clauses =
         of_opt_not_impl ~msg:"produce_pred_def: no clauses" def.clauses
       in
       branches @@ List.map (fun clause () -> produce_clause clause) clauses)
  in
  v

and produce_owned_resource ~cty ~(kind : Mu.Request.init) ~ptr ty =
  let open Producer.With_syntax in
  let* ptr = Subst.eval_annot ptr in
  let*^ ptr =
    Core_value.cast_ptr ptr
    |> of_opt_not_impl ~msg:"produce_resource: not a pointer"
  in
  match cty with
  | Cn.Sctypes.Array (ict, Some n) ->
      (* Owned-array unfolds to an [each] chunk (CN's [unfolded_array]):
         footprint at every index in [0, n), map-valued output. *)
      let q_bt = Cn.Memory.uintptr_bt in
      let perm = array_perm ~q_bt n in
      let*^ out = Core_value.nondet_bt ty in
      let+ () =
        Producer.lift_state
          (State.add_qpred
             {
               qname = QOwned (ict, kind);
               pointer = ptr;
               q_bt;
               step = ict;
               perm;
               iargs = (fun _ -> Csymex.return []);
               out;
             })
      in
      out
  | Array (_, None) ->
      Producer.lift @@ not_impl "produce: array without a known length"
  | _ -> (
  match kind with
  | Init ->
      let*^ v = Core_value.nondet_bt ty in
      let+ () = lift_state @@ State.produce_owned ptr cty v in
      v
  | Uninit ->
      let loc = Typed.Ptr.loc ptr in
      let ofs = Typed.Ptr.ofs ptr in
      let*^ len = Layout.size_of_s (Cn.Sctypes.to_ctype cty) in
      let+ () = lift_state @@ State.produce_any' loc ofs len in
      Core_value.Loaded Unspec)

and produce_predicate (sym : Sym.t) (iargs : annot list) :
    Core_value.t Producer.t =
  let open Producer.With_syntax in
  let def = Ctx.get_pred_def sym in
  let ret_ty = snd def.oarg in
  let*^ v = Core_value.nondet_bt ret_ty in
  let* iargs = map_list ~f:Subst.eval_annot iargs in
  (* I think CN never produces non-recursive predicates?
     So let's just unfold them. Clause-less predicates (e.g. the built-in
     [Alloc] token) can only exist folded. *)
  if def.recursive || Option.is_none def.clauses then
    (* Cn predicates have a unique out-param. *)
    let+ () = lift_state @@ State.produce_pred sym iargs [ v ] in
    v
  else
    let+ v = lift_state @@ produce_pred_def ~name:sym def iargs in
    v

and produce_resource (req : Mu.Request.t) (ty : Cn.BaseTypes.t) :
    Core_value.t Producer.t =
  match req with
  | Owned { ty = cty; kind; ptr } -> produce_owned_resource ~cty ~kind ~ptr ty
  | P { name; iargs } -> produce_predicate name iargs
  | Q qp ->
      let open Producer.With_syntax in
      let* pv = Subst.eval_annot qp.pointer in
      let*^ ptr =
        Core_value.cast_ptr pv
        |> of_opt_not_impl ~msg:"each: pointer is not a pointer"
      in
      let* snapshot = Producer.get_state () in
      let qsym, q_bt = qp.q in
      let perm = perm_closure ~qsym ~q_bt qp.permission snapshot in
      let iargs = iargs_closure ~qsym ~q_bt qp.iargs snapshot in
      let*^ out = Core_value.nondet_bt ty in
      let+ () =
        Producer.lift_state
          (State.add_qpred
             {
               qname = qp.name;
               pointer = ptr;
               q_bt;
               step = qp.step;
               perm;
               iargs;
               out;
             })
      in
      out

and produce_logical_arg ((arg, loc) : Mu.logical_arg * Cn.Locations.info) :
    unit Producer.t =
  let open Producer.With_syntax in
  let@ () = with_loc ~loc:(fst loc) in
  match arg with
  | Define (sym, annot) ->
      let* v = Subst.eval_annot annot in
      Subst.add sym v
  | Resource (sym, (req, ty)) ->
      let* v = produce_resource req ty in
      Subst.add sym v
  | Constraint lc -> produce_logical_constraint lc

(** Like {!produce_logical_arg}, but resources only bind their output to a
    fresh value instead of adding footprint. Used to bring a function's
    binders and pure constraints into scope for label-body obligations, which
    (as in CN's [check_procedure]) see the function's context but not its
    resources. *)
let produce_logical_arg_ghost ((arg, loc) : Mu.logical_arg * _) :
    unit Producer.t =
  let open Producer.With_syntax in
  let@ () = with_loc ~loc:(fst loc) in
  match arg with
  | Define (sym, annot) ->
      let* v = Subst.eval_annot annot in
      Subst.add sym v
  | Resource (sym, (_req, ty)) ->
      let*^ v = Core_value.nondet_bt ty in
      Subst.add sym v
  | Constraint lc -> produce_logical_constraint lc

let produce_arguments ?(ghost_resources = false) ?(subst = Subst.empty)
    ?(state = State.empty) (args : Mu.arguments) :
    (Subst.t * State.t option) Csymex.t =
  (* [produce_computational_arg] threads [(subst, state)] over [Csymex] by hand;
     reshape it into a [Producer.t] (which threads [subst] over [State.SM]). *)
  let open Csymex.Syntax in
  let produce_logical =
    if ghost_resources then produce_logical_arg_ghost else produce_logical_arg
  in
  let producer =
    let open Producer.With_syntax in
    let* () = iter_list ~f:produce_computational_arg args.comp in
    iter_list ~f:produce_logical args.logic
  in
  let+ ((), subst), state = producer subst state in
  (subst, state)

(** Toplevel function made to be used in the interpreter *)
let produce_return_type ~subst (ret_ty : Mu.return_type) :
    (Subst.t, _, _) State.SM.Result.t =
  let producer =
    let open Producer.With_syntax in
    let@ () = with_loc ~loc:(fst ret_ty.ret_info) in
    [%l.trace "@[Producing post condition:@ %a@]" Mu.pp_return_type ret_ty];
    let rsym, bty = ret_ty.ret in
    let*^ r = Core_value.nondet_bt bty in
    let* () = Subst.add rsym r in
    Producer.iter_list ret_ty.logic ~f:produce_logical_arg
  in
  let open State.SM.Syntax in
  let+ (), subst = Producer.run_with_subst ~subst producer in
  Compo_res.Ok subst

(** Produce a lemma's [ensures] (a logical return type with no return
    binder). Mirror of {!produce_return_type}. *)
let produce_logical_return ~subst ~loc (lrt : Mu.logical_return) :
    (Subst.t, _, _) State.SM.Result.t =
  let producer =
    let open Producer.With_syntax in
    let@ () = with_loc ~loc in
    Producer.iter_list lrt ~f:produce_logical_arg
  in
  let open State.SM.Syntax in
  let+ (), subst = Producer.run_with_subst ~subst producer in
  Compo_res.Ok subst

let consume_pure (annot : annot) : unit Consumer.t =
  let open Consumer.With_syntax in
  let (IT (_, _, loc)) = annot in
  let@ () = Consumer.with_loc ~loc in
  let* v = Subst.eval_annot annot in
  let*^ v =
    Core_value.cast_bool v
    |> of_opt_not_impl ~msg:"consume_annot: not a boolean"
  in
  logic_assert v

let consume_logical_constraint (lc : Cn.LogicalConstraints.t) : unit Consumer.t
    =
  match lc with
  | T it -> consume_pure it
  | Forall ((q, q_bt), body) ->
      (* Sound forall-introduction: prove the body for a fresh, unconstrained
         skolem variable. *)
      let open Consumer.With_syntax in
      let (IT (_, _, loc)) = body in
      let@ () = Consumer.with_loc ~loc in
      let*^ skolem = Core_value.nondet_bt q_bt in
      let* subst = Consumer.get_subst () in
      let*^ v = LSubst.eval_annot (LSubst.add q skolem subst) body in
      let*^ v =
        Core_value.cast_bool v
        |> of_opt_not_impl ~msg:"forall body is not a boolean"
      in
      logic_assert v

let consume_owned_pred cty (kind : Mu.Request.init) ptr :
    Core_value.t Consumer.t =
  let open Consumer.With_syntax in
  let* ptr = Subst.eval_annot ptr in
  let*^ ptr =
    Core_value.cast_ptr ptr
    |> of_opt_not_impl ~msg:"consume_p_resource: not a pointer"
  in
  [%l.trace "@[Consuming Owned %a at %a@]" pp_okind kind Typed.ppa ptr];
  match cty with
  | Cn.Sctypes.Array (ict, Some n) ->
      (* Owned-array consumes as its [each] form. *)
      let q_bt = Cn.Memory.uintptr_bt in
      let needed = array_perm ~q_bt n in
      lift_state @@ State.lift_consumer_error
      @@ consume_qpred
           ~consume_cell_pred:(fun _ _ ->
             (* Unreachable: the qname is [QOwned]. *)
             State.SM.lift @@ Csymex.not_impl "array bridge: predicate cell")
           ~qname:(QOwned (ict, kind))
           ~ptr ~q_bt ~step:ict
           ~req_iargs:(fun _ -> Csymex.return [])
           ~needed
  | Array (_, None) -> Consumer.not_impl "consume: array without a known length"
  | _ -> (
      match kind with
      | Init -> lift_state @@ State.consume_owned ptr cty
      | Uninit -> lift_state @@ State.consume_any ptr cty)

let rec find_clause_consume ~subst (clauses : Mu.clause list) :
    (Core_value.t, _, _) State.SM.Result.t =
  let open State.SM in
  let open State.SM.Syntax in
  let*^ loc = Csymex.get_loc () in
  match clauses with
  | [] ->
      let trace =
        Soteria.Terminal.Call_trace.singleton ~loc ~msg:"No matching clause" ()
      in
      Result.error ((`Lfail Typed.v_false :> Cn_error.t), trace)
  | clause :: rest ->
      let*^ guard = Subst.eval_annot subst clause.guard in
      let*^ guard =
        Core_value.cast_bool guard
        |> of_opt_not_impl ~msg:"clause guard isn't a boolean?"
      in
      if%sure guard then
        let logical_args =
          List.map (fun arg -> (arg, (clause.loc, None))) clause.logical_args
        in
        let** (), subst =
          Consumer_monad.run_with_subst ~subst
            (Consumer_monad.iter_list ~f:consume_logical_arg logical_args)
        in
        let*^ ret = Subst.eval_annot subst clause.ret in
        Result.ok ret
      else find_clause_consume ~subst rest

and consume_pred_def ~name (def : Mu.predicate_def) (iargs : Core_value.t list)
    : (Core_value.t, _, _) State.SM.Result.t =
  let open State.SM.Syntax in
  [%l.trace "Consuming the definition of %a" Sym.pp_hum name];
  let subst = subst_for_pred_def def iargs in
  let*^ clauses =
    of_opt_not_impl ~msg:"consume_pred_def: no clauses" def.clauses
  in
  (* We consume at most one case if we are guaranteed it matches *)
  find_clause_consume ~subst clauses

and consume_predicate sym iargs : (Core_value.t, _, _) State.SM.Result.t =
  let open State.SM in
  let open Syntax in
  let* first_res =
    let** vs = State.consume_pred sym iargs in
    (* Cn predicates have a unique out-parameter *)
    Result.ok (List.hd vs)
  in
  (* If we failed to consume the predicate, we try to fold it instead *)
  match first_res with
  | Ok _ -> return first_res
  | Error _ | Missing _ when Option.is_none (Ctx.get_pred_def sym).clauses ->
      (* Clause-less predicates (e.g. [Alloc]) cannot be folded. *)
      return first_res
  | Error _ | Missing _ -> (
      [%l.trace
        "Auto-fold attempt for %a(%a, _)" Sym.pp_hum sym
          Fmt.(list ~sep:comma Core_value.pp)
          iargs];
      let def = Ctx.get_pred_def sym in
      let+ snd_res = consume_pred_def ~name:sym def iargs in
      match snd_res with
      | Compo_res.Ok v ->
          [%l.debug "Successfully auto-folded %a" Sym.pp_hum sym];
          Compo_res.Ok v
      | Error _ | Missing _ ->
          (* Otherwise, we give the error of the first attempt *)
          first_res)

and consume_resource (req : Mu.Request.t) : Core_value.t Consumer.t =
  let open Consumer.With_syntax in
  match req with
  | Owned { ty = cty; kind; ptr } -> consume_owned_pred cty kind ptr
  | P { name; iargs } ->
      let* (iargs : Core_value.t list) = map_list ~f:Subst.eval_annot iargs in
      lift_state @@ consume_predicate name iargs
  | Q qp ->
      let* pv = Subst.eval_annot qp.pointer in
      let*^ ptr =
        Core_value.cast_ptr pv
        |> of_opt_not_impl ~msg:"each: pointer is not a pointer"
      in
      let* subst = Consumer.get_subst () in
      let qsym, q_bt = qp.q in
      let needed = perm_closure ~qsym ~q_bt qp.permission subst in
      let consume_cell_pred name ins =
        (* [consume_predicate] returns traced errors; [consume_qpred] is
           itself wrapped in [lift_consumer_error], so drop the trace. *)
        State.SM.Result.map_error (fun (e, _trace) -> e)
          (consume_predicate name ins)
      in
      let req_iargs = iargs_closure ~qsym ~q_bt qp.iargs subst in
      lift_state @@ State.lift_consumer_error
      @@ consume_qpred ~consume_cell_pred ~qname:qp.name ~ptr ~q_bt
           ~step:qp.step ~req_iargs ~needed

and consume_logical_arg ((arg, (loc, _)) : Mu.logical_arg * Cn.Locations.info) :
    unit Consumer.t =
  let open Consumer.With_syntax in
  let@ () = Consumer.with_loc ~loc in
  match arg with
  | Define (sym, annot) ->
      let* v = Subst.eval_annot annot in
      Subst.add sym v
  | Resource (sym, (req, _ty)) ->
      let* v = consume_resource req in
      Subst.add sym v
  | Constraint lc -> consume_logical_constraint lc

let consume_arguments (args : Mu.arguments) : unit Consumer.t =
  (* I'm assuming the type Cn base type checker already went through code,
in which case there's nothing else to do about computational args. *)
  Consumer.iter_list ~f:consume_logical_arg args.logic

let consume_return_type ~subst (ty : Mu.return_type) (ret : Core_value.t) :
    (unit, Cn_error.with_trace, State.syn list) State.SM.Result.t =
  let open State.SM.Syntax in
  let* state = State.SM.get_state () in
  [%l.debug
    "@[<v 2>Consuming return type: %a@]@.@[<v 2>with state:@ %a@]@.@[<v 2>and \
     subst:@ %a@]"
    Mu.pp_return_type ty
      (Fmt.option @@ State.pp_pretty ~ignore_freed:true)
      state Subst.pp subst];
  let subst = Subst.add (fst ty.ret) ret subst in
  let++ v, _subst =
    Consumer.run_with_subst ~subst
      (Consumer.iter_list ~f:consume_logical_arg ty.logic)
  in
  v
