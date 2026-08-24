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
  | Forall _ -> InterpM.not_impl "eval_lc: Forall"

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
  | Mu.Instantiate _ -> InterpM.not_impl "cn statement: instantiate"
  | Mu.Extract _ -> InterpM.not_impl "cn statement: extract"
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
  | Mu.Apply _ -> InterpM.not_impl "cn statement: apply"
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
