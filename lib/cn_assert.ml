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

type term = Cn.(BaseTypes.t Terms.term)
type annot = Cn.(BaseTypes.t Terms.annot)

let pp_okind ft = function
  | Mu.Request.Init -> Fmt.pf ft "Init"
  | Uninit -> Fmt.pf ft "Uninit"

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

and unfold_with_heuristics heuristics =
  State.unfold_with_heuristics ~produce_def:produce_def_s heuristics

and with_recovery_attempt ~values f =
  State.with_recovery_attempt
    ~heuristics:(Unfold_heuristics.recovery_heuristics values)
    ~produce_def:produce_def_s f

and produce_logical_constraint (lc : Cn.LogicalConstraints.t) : unit Producer.t
    =
  match lc with
  | T it -> produce_pure it
  | Forall _ -> Producer.lift @@ not_impl "consume_logical_constraint: Forall"

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
      Core_value.Loaded Unspec

and produce_predicate (sym : Sym.t) (iargs : annot list) :
    Core_value.t Producer.t =
  let open Producer.With_syntax in
  let def = Ctx.get_pred_def sym in
  let ret_ty = snd def.oarg in
  let*^ v = Core_value.nondet_bt ret_ty in
  let* iargs = map_list ~f:Subst.eval_annot iargs in
  (* I think CN never produces non-recursive predicates?
     So let's just unfold them *)
  if def.recursive then
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
  | Q _ -> Producer.lift @@ not_impl "produce_resource: Q"

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

let produce_arguments (args : Mu.arguments) :
    (Subst.t * State.t option) Csymex.t =
  (* [produce_computational_arg] threads [(subst, state)] over [Csymex] by hand;
     reshape it into a [Producer.t] (which threads [subst] over [State.SM]). *)
  let open Csymex.Syntax in
  let producer =
    let open Producer.With_syntax in
    let* () = iter_list ~f:produce_computational_arg args.comp in
    iter_list ~f:produce_logical_arg args.logic
  in
  let+ ((), subst), state = producer Subst.empty State.empty in
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
  | Forall _ -> Consumer.not_impl "consume_logical_constraint: Forall"

let consume_owned_pred cty (kind : Mu.Request.init) ptr :
    Core_value.t Consumer.t =
  let open Consumer.With_syntax in
  let* ptr = Subst.eval_annot ptr in
  let*^ ptr =
    Core_value.cast_ptr ptr
    |> of_opt_not_impl ~msg:"consume_p_resource: not a pointer"
  in
  [%l.trace "@[Consuming Owned %a at %a@]" pp_okind kind Typed.ppa ptr];
  match kind with
  | Init -> lift_state @@ State.consume_owned ptr cty
  | Uninit -> lift_state @@ State.consume_any ptr cty

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
  | Q _ -> Consumer.not_impl "consume_resource: Q"

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
