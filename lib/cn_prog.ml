module SState = State
open Soteria.Soteria_std
open Soteria.Logs.Import
open Soteria_c_vendor
module State = SState
module Mu = Usable_mucore
open Csymex
open Syntax
open Soteria_c_helpers
module InterpM = Interp_monad

let execute_load (subst : Subst.t) (load : Mu.cn_load) : Subst.t InterpM.t =
  let open InterpM.Syntax in
  let@ () = InterpM.with_loc ~loc:load.loc in
  let*^ ptr = Subst.eval_annot subst load.pointer in
  let* v = InterpM.State.load ptr load.ct in
  InterpM.ok (Subst.add load.sym v subst)

let eval_lc (subst : Subst.t) (lc : Cn.LogicalConstraints.t) :
    Typed.(T.sbool t) InterpM.t =
  let open InterpM.Syntax in
  match lc with
  | T it ->
      let*^ b = Subst.eval_annot subst it in
      Core_value.cast_bool b
      |> InterpM.of_opt_not_impl ~msg:"eval_lc: not a boolean"
  | Forall ((q, q_bt), body) ->
      let open InterpM.Syntax in
      let*^ skolem = Core_value.nondet_bt q_bt in
      let*^ b = Subst.eval_annot (Subst.add q skolem subst) body in
      Core_value.cast_bool b
      |> InterpM.of_opt_not_impl ~msg:"eval_lc: forall body is not a boolean"

let execute_statement (subst : Subst.t) (stmt : Mu.cn_statement) :
    unit InterpM.t =
  let open InterpM.Syntax in
  match stmt with
  | Mu.Split_case lc ->
      let* b = eval_lc subst lc in
      (* Weird code but really we eval both cases*)
      if%sat b then InterpM.ok () else InterpM.ok ()
  | Mu.Assert lc ->
      let* b = eval_lc subst lc in
      InterpM.assert_or_error b `FailedAssert
  | Mu.Pack_unpack _ -> InterpM.not_impl "cn statement: pack/unpack"
  | Mu.To_from_bytes _ -> InterpM.not_impl "cn statement: to/from bytes"
  | Mu.Have _ -> InterpM.not_impl "cn statement: have"
  | Mu.Instantiate (_filter, index_it) ->
      (* Assume [body[q := index]] for every stored quantified fact whose bound
         variable has the index's sort. CN filters which facts to instantiate
         ([I_Function]/[I_Good]); instantiating more facts than CN is sound
         (they are all assumptions), so the filter is ignored. *)
      let open InterpM.Syntax in
      let (Cn.Terms.IT (_, ibt, _)) = index_it in
      let*^ idx = Subst.eval_annot subst index_it in
      let* facts = InterpM.lift_sm State.get_facts in
      InterpM.fold_list facts ~init:() ~f:(fun () (f : State.Facts.fact) ->
          if not (Cn.BaseTypes.equal f.q_bt ibt) then InterpM.ok ()
          else
            let*^ b =
              Subst.eval_annot (Subst.add f.q idx f.snapshot) f.body
            in
            match Core_value.cast_bool b with
            | None -> InterpM.not_impl "instantiate: fact body is not a boolean"
            | Some b -> InterpM.lift (Csymex.assume [ b ]))
  | Mu.Extract (_attrs, to_extract, index_it) -> (
      let open InterpM.Syntax in
      let* target =
        match to_extract with
        | Cerb_frontend.Cn.E_Pred (CN_owned (Some ct))
        | Cerb_frontend.Cn.E_Pred (CN_block (Some ct)) ->
            InterpM.ok (State.Movable.MOwned ct)
        | E_Pred (CN_named pn) -> InterpM.ok (State.Movable.MPred pn)
        | _ -> InterpM.not_impl "extract: requires a C-type annotation"
      in
      let*^ idxv = Subst.eval_annot subst index_it in
      let* idx =
        Core_value.cast_int idxv
        |> InterpM.of_opt_not_impl ~msg:"extract: index is not an integer"
      in
      let* () = InterpM.lift_sm (State.add_movable (target, idx)) in
      (* Immediate extraction from held chunks (CN's add_movable_index ->
         do_unfold_resources sequence): move the cell at [idx] from a covering
         Q chunk into the heap, and weaken the chunk's permission. *)
      let* qpreds = InterpM.lift_sm State.get_qpreds in
      let rec extract_pass acc = function
        | [] -> InterpM.lift_sm (State.set_qpreds (List.rev acc))
        | (c : State.Qpreds.chunk) :: rest ->
            if not (State.Movable.matches target c.qname) then
              extract_pass (c :: acc) rest
            else
              let*^ covered =
                let open Csymex.Syntax in
                let* b = c.perm idx in
                if%sure b then Csymex.return true else Csymex.return false
              in
              if not covered then extract_pass (c :: acc) rest
              else
                let*^ cell_desc =
                  Cn_assert.cell_desc_of_qname c.qname
                  |> Csymex.of_opt_not_impl ~msg:"extract: cell sort"
                in
                let*^ step_size =
                  Soteria_c_vendor.Layout.size_of_s
                    (Cn.Sctypes.to_ctype c.step)
                in
                let cell_ptr =
                  Typed.Ptr.add_ofs c.pointer
                    (Typed.cast (Typed.BitVec.mul idx step_size))
                in
                let* () =
                  match c.qname with
                  | QOwned (ty, Mu.Request.Init) -> (
                      match Core_value.cast_map c.out with
                      | None -> InterpM.not_impl "extract: chunk out not a map"
                      | Some m ->
                          let cell_sv =
                            Typed.map_get
                              ~value_ty:(Subst.ty_of_desc cell_desc)
                              m idx
                          in
                          let v = Subst.cv_of_desc cell_desc cell_sv in
                          InterpM.lift_sm
                            (State.produce_owned cell_ptr ty v))
                  | QOwned (_, Uninit) ->
                      InterpM.not_impl "extract from W<> each"
                  | QPName _ ->
                      InterpM.not_impl "extract from predicate each"
                in
                let perm' i =
                  let open Csymex.Syntax in
                  let+ b = c.perm i in
                  Typed.Bool.and_ b Typed.(not (Typed.Infix.( ==@ ) i idx))
                in
                extract_pass ({ c with perm = perm' } :: acc) rest
      in
      extract_pass [] qpreds)
  | Mu.Unfold (fsym, arg_annots) -> (
      match Ctx.get_fun_def fsym with
      | None -> InterpM.not_impl "unfold: unknown function"
      | Some def -> (
          match def.body with
          | Def _ ->
              (* Non-recursive definitions are inlined at every application;
                 nothing to assert. *)
              InterpM.ok ()
          | Uninterp ->
              InterpM.not_impl
                "unfold: cannot unfold an uninterpreted function"
          | Rec_Def _ -> (
              let fn = Soteria_c_helpers.Adt.adt_name fsym in
              match Soteria_c_vendor.Adt_ext.find_fun fn with
              | None -> InterpM.not_impl "unfold: function not registered"
              | Some { arg_sorts; ret_sort; _ } ->
                  let open InterpM.Syntax in
                  (* One capture-avoiding unrolling, via CN's own machinery. *)
                  let rhs_it =
                    Cn.Definition.Function.unroll_once def arg_annots
                    |> Option.get
                  in
                  let*^ rhs = Subst.eval_annot subst rhs_it in
                  let*^ args =
                    Csymex.map_list
                      ~f:(fun (desc, a) ->
                        let open Csymex.Syntax in
                        let* v = Subst.eval_annot subst a in
                        Subst.sv_of_cv desc v
                        |> Soteria_c_helpers.of_opt_not_impl
                             ~msg:"unfold: argument sort mismatch")
                      (List.combine arg_sorts arg_annots)
                  in
                  let lhs =
                    Subst.cv_of_desc ret_sort
                      (Typed.fn_app ~fn
                         ~ret_ty:(Subst.ty_of_desc ret_sort)
                         args)
                  in
                  InterpM.lift
                    (Csymex.assume [ Core_value.sem_eq lhs rhs ]))))
  | Mu.Apply (lsym, arg_annots) -> (
      match Ctx.get_lemma lsym with
      | None -> InterpM.not_impl "apply: unknown lemma"
      | Some (loc, (args, ensures)) ->
          let open InterpM.Syntax in
          InterpM.with_extra_call_trace ~loc
            ~msg:(Fmt.str "Applying lemma %a" Symbol_std.pp_hum lsym)
          @@ (* Bind the lemma's computational/ghost binders to the evaluated
                argument terms, then run the spine: consume the requires,
                produce the ensures. *)
          let*^ lemma_subst =
            let open Csymex.Syntax in
            match List.combine args.comp arg_annots with
            | exception Invalid_argument _ ->
                Csymex.not_impl "apply: wrong number of arguments"
            | pairs ->
                Csymex.fold_list pairs ~init:Subst.empty
                  ~f:(fun acc ((barg, _info), annot) ->
                    let (Mu.Computational (bsym, _) | Mu.Ghost (bsym, _)) =
                      barg
                    in
                    let+ v = Subst.eval_annot subst annot in
                    Subst.add bsym v acc)
          in
          let* (), lemma_subst = Cn_assert.consume_arguments args lemma_subst in
          let+ _subst =
            Cn_assert.produce_logical_return ~subst:lemma_subst ~loc ensures
          in
          ())
  | Mu.Inline _ -> InterpM.not_impl "cn statement: inline"
  | Mu.Print _ -> InterpM.not_impl "cn statement: print"

let execute_one (subst : Subst.t) (prog : Mu.cn_prog) : unit InterpM.t =
  let open InterpM.Syntax in
  let@ () = InterpM.with_loc ~loc:prog.loc in
  let* subst = InterpM.fold_list ~init:subst ~f:execute_load prog.loads in
  execute_statement subst prog.stmt

let execute_cn_prog (progs : Mu.cn_prog list) (subst : Subst.t) : unit InterpM.t
    =
  InterpM.fold_list ~init:() ~f:(fun () prog -> execute_one subst prog) progs
