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
  | Mu.Unfold _ -> InterpM.not_impl "cn statement: unfold"
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
