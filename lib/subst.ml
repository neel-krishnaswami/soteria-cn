open Soteria.Soteria_std
open Syntaxes.FunctionWrap
open Soteria.Logs.Import
open Soteria_c_vendor
open Csymex
module Mu = Usable_mucore
open Mu
include Symbol_std.Map

type nonrec t = Core_value.t t

let of_iter iter = Iter.fold (fun acc (k, v) -> add k v acc) empty iter

module Builtin_names = struct
  open Cn.Builtins

  let name_of (_, s, _) = s
  let ptr_eq = name_of ptr_eq_def
  let is_null = name_of is_null_def
end

let pp ft t =
  Fmt.iter_bindings ~sep:Fmt.cut iter
    (fun ft (k, v) -> Fmt.pf ft "%a -> %a" Symbol_std.pp_hum k Core_value.pp v)
    ft t

let rec assign_pattern subst (pat : pattern) (v : Core_value.t) : t Csymex.t =
  let@@ () = Csymex.with_loc ~loc:pat.loc in
  match pat.node with
  | CaseBase (Some sym, _) -> return (add sym v subst)
  | CaseBase (None, _) -> return subst
  | CaseCtor (ctor, pats) -> (
      match (ctor, v, pats) with
      | Cspecified, Loaded (Spec v'), [ p ] -> assign_pattern subst p (Obj v')
      | Ctuple, Tuple vs, pats' when List.compare_lengths vs pats' = 0 ->
          Csymex.fold_list (List.combine pats' vs) ~init:subst
            ~f:(fun acc (p, v) -> assign_pattern acc p v)
      | _ ->
          Fmt.kstr Csymex.not_impl
            "@[<v 2>assign_pattern: unsupported constructor pattern@ CTOR: %a@ \
             VALUE: %a@ PATTERNS: %a@]"
            Mu.pp_ctor ctor Core_value.pp v
            (Fmt.Dump.list Mu.pp_pattern)
            pats)

let from_args ?(init = empty) (args : Mu.arguments) (params : Core_value.t list)
    : t =
  List.fold_left2
    (fun acc ((arg, _) : Mu.computational_arg * _) param ->
      match arg with
      | Computational (sym, _) -> add sym param acc
      | Ghost _ -> L.failwith "Unsupported ghost arguments")
    init args.comp params

type term = Cn.(BaseTypes.t Terms.term)
type annot = Cn.(BaseTypes.t Terms.annot)

(* It's quite annoying but the printer for const isn't exposed, it's 
    inlined in the printer for annot for some reason. So we have to 
    retrieve the const when printing the error *)
exception Not_impl_const
exception Not_implemented of annot

let eval_tconst : Cn.Terms.const -> Core_value.t = function
  | Bits ((_sign, size), v) ->
      let i = Typed.BitVec.mk_masked size v in
      Obj (Core_value.Int i)
  | Z z ->
      (* FIXME: Not sure why Z is necessary here? We're adding integers with non-integers... *)
      (* I'll model those as i128 for now... *)
      let i = Typed.BitVec.mk_masked 128 z in
      Obj (Core_value.Int i)
  | Bool b -> Core_value.Bool.of_bool b
  | Null -> Obj (Core_value.Ptr Typed.Ptr.null)
  | _ -> raise Not_impl_const


(* ───────────────────────── ADT term helpers ───────────────────────── *)

module AE = Soteria_c_vendor.Adt_ext
module HAdt = Soteria_c_helpers.Adt

(* With the transparent [Typed], every ['a Typed.t] is an svalue, so these
   conversions are mere repackagings. *)
let sv_of_cv (desc : AE.sort_desc) (v : Core_value.t) : Typed.Svalue.t option =
  match desc with
  | DBool -> Core_value.cast_bool v
  | DBits _ -> Core_value.cast_int v
  | DPtr _ | DLoc _ -> Core_value.cast_ptr v
  | DAdt _ -> Core_value.cast_adt v
  | DMap _ -> Core_value.cast_map v

let cv_of_desc (desc : AE.sort_desc) (sv : Typed.Svalue.t) : Core_value.t =
  match desc with
  | DBool -> Bool sv
  | DBits _ -> Obj (Int sv)
  | DPtr _ | DLoc _ -> Obj (Ptr sv)
  | DAdt _ -> Adt sv
  | DMap _ -> Map sv

let ty_of_desc (desc : AE.sort_desc) : Typed.Svalue.ty =
  match desc with
  | DBool -> Soteria.Bv_values.Svalue.TBool
  | DBits n -> Soteria.Bv_values.Svalue.TBitVector n
  | DPtr n -> Soteria.Bv_values.Svalue.TPointer n
  | DLoc n -> Soteria.Bv_values.Svalue.TLoc n
  | DAdt a -> Typed.t_adt a
  | DMap (k, v) -> Typed.t_map k v

let ite_val ~of_opt_not_impl ~fail g (b1 : Core_value.t) (b2 : Core_value.t) :
    Core_value.t =
  match b1 with
  | Loaded (Spec (Int i1)) | Obj (Int i1) ->
      let i2 = Core_value.cast_int b2 |> of_opt_not_impl in
      Core_value.Obj (Int (Typed.ite g i1 i2))
  | Loaded (Spec (Ptr p1)) | Obj (Ptr p1) ->
      let p2 = Core_value.cast_ptr b2 |> of_opt_not_impl in
      Obj (Ptr (Typed.ite g p1 p2))
  | Bool o1 ->
      let o2 = Core_value.cast_bool b2 |> of_opt_not_impl in
      Bool (Typed.ite g o1 o2)
  | Adt a1 ->
      let a2 = Core_value.cast_adt b2 |> of_opt_not_impl in
      Adt (Typed.ite g a1 a2)
  | _ -> fail ()

let rec eval_annot (subst : t) (annot : annot) : Core_value.t =
  let not_impl () = raise (Not_implemented annot) in
  let of_opt_not_impl = function None -> not_impl () | Some x -> x in
  let open Typed.Infix in
  let (IT (it, _bt, _loc)) = annot in
  match it with
  | Sym s -> find s subst
  | Const c -> (
      try eval_tconst c
      with Not_impl_const ->
        [%l.debug "Unsupported const!"];
        not_impl ())
  | Tuple ts ->
      let vs = List.map (eval_annot subst) ts in
      Core_value.Tuple vs
  | Binop (op, t1, t2) -> (
      let v1 = eval_annot subst t1 in
      let v2 = eval_annot subst t2 in
      (* FIXME(signedness): this should come from the operand types
         ([Bits (Unsigned, _)] -> false), but the C-side interpreter
         ([Minterp.eval_op]) currently compares signed unconditionally; using
         the correct signedness here makes spec obligations and body path
         conditions disagree on unsigned programs (e.g. min3.c). Keep the two
         sides consistent until Minterp threads C types through comparisons. *)
      let signed = true in
      let ints () =
        ( Core_value.cast_int v1 |> of_opt_not_impl,
          Core_value.cast_int v2 |> of_opt_not_impl )
      in
      let int_op f =
        let i1, i2 = ints () in
        Core_value.Obj (Int (Typed.cast (f i1 i2)))
      in
      match op with
      | LE -> Core_value.leq ~signed v1 v2
      | LT -> Core_value.lt ~signed v1 v2
      | And -> Core_value.Bool.and_ v1 v2
      | Or -> Core_value.Bool.or_ v1 v2
      | Implies -> Core_value.Bool.or_ (Core_value.Bool.not v1) v2
      | EQ ->
          [%l.trace "Sem_eq? %a == %a" Core_value.pp v1 Core_value.pp v2];
          Bool (Core_value.sem_eq v1 v2)
      | Add -> int_op (fun a b -> a +!@ b)
      | Sub -> int_op (fun a b -> Typed.BitVec.sub a b)
      | Mul -> int_op (fun a b -> Typed.BitVec.mul a b)
      | Div -> int_op (fun a b -> Typed.BitVec.div ~signed a (Typed.cast b))
      | Rem -> int_op (fun a b -> Typed.BitVec.rem ~signed a (Typed.cast b))
      | Mod -> int_op (fun a b -> Typed.BitVec.mod_ a b)
      | Min ->
          let i1, i2 = ints () in
          Obj (Int (Typed.ite (Typed.BitVec.lt ~signed i1 i2) i1 i2))
      | Max ->
          let i1, i2 = ints () in
          Obj (Int (Typed.ite (Typed.BitVec.lt ~signed i1 i2) i2 i1))
      | _ ->
          [%l.trace "Not impl binop?"];
          not_impl ())
  | Unop (op, t') -> (
      let v = eval_annot subst t' in
      match op with
      | Not -> Core_value.Bool.not v
      | Negate ->
          let i = Core_value.cast_int v |> of_opt_not_impl in
          let zero = Typed.BitVec.zero (Typed.size_of_int i) in
          Obj (Int (Typed.cast (Typed.BitVec.sub zero i)))
      | _ ->
          [%l.trace "Not impl unop?"];
          not_impl ())
  | StructMember (t, memb) ->
      let v = eval_annot subst t in
      let v = Core_value.struct_field v memb |> of_opt_not_impl in
      Loaded v
  | Record members ->
      let membres =
        List.map (fun (id, t) -> (id, eval_annot subst t)) members
      in
      Core_value.Record membres
  | RecordMember (record, memb) ->
      let record =
        match eval_annot subst record with
        | Core_value.Record members -> members
        | _ -> not_impl ()
      in
      record
      |> List.find_map (fun (id, v) ->
          if Id.equal id memb then Some v else None)
      |> of_opt_not_impl
  | Apply (s, [ p1; p2 ]) when Sym.equal s Builtin_names.ptr_eq ->
      let p1 = eval_annot subst p1 in
      let p2 = eval_annot subst p2 in
      Bool (Core_value.sem_eq p1 p2)
  | Apply (s, [ p1 ]) when Sym.equal s Builtin_names.is_null ->
      let p1 = eval_annot subst p1 in
      let p1 = Core_value.cast_ptr p1 |> of_opt_not_impl in
      Bool (Typed.Ptr.is_null p1)
  | Apply (fsym, arg_annots) -> (
      match Ctx.get_fun_def fsym with
      | Some ({ body = Def _; _ } as def) ->
          (* Capture-avoiding IT-level inlining via CN's own substitution
             ([open_] -> [IT.subst]); the result's free vars are the spec's
             vars, so we evaluate it under the current subst. *)
          let body' =
            Cn.Definition.Function.try_open def arg_annots |> of_opt_not_impl
          in
          eval_annot subst body'
      | Some { body = Rec_Def _ | Uninterp; _ } -> (
          (* Uninterpreted at the solver; equations come from [unfold]. *)
          let fn = HAdt.adt_name fsym in
          match AE.find_fun fn with
          | None -> not_impl ()
          | Some { arg_sorts; ret_sort; _ } ->
              let args =
                List.map2
                  (fun desc a ->
                    eval_annot subst a |> sv_of_cv desc |> of_opt_not_impl)
                  arg_sorts arg_annots
              in
              cv_of_desc ret_sort
                (Typed.fn_app ~fn ~ret_ty:(ty_of_desc ret_sort) args))
      | None -> not_impl ())
  | ITE (g, b1, b2) -> (
      let g = eval_annot subst g in
      let b1 = eval_annot subst b1 in
      let b2 = eval_annot subst b2 in
      let g = Core_value.cast_bool g |> of_opt_not_impl in
      ite_val ~of_opt_not_impl ~fail:not_impl g b1 b2)
  | Good (_, _) ->
      (* Are those pointer invariants? I don't think it should be separate from the chunk? *)
      Core_value.true_
  | MapGet (m_t, k_t) -> (
      let (IT (_, mbt, _)) = m_t in
      match HAdt.desc_of_bt mbt with
      | Some (AE.DMap (kd, vd)) ->
          let m = eval_annot subst m_t |> Core_value.cast_map |> of_opt_not_impl in
          let k = eval_annot subst k_t |> sv_of_cv kd |> of_opt_not_impl in
          cv_of_desc vd (Typed.map_get ~value_ty:(ty_of_desc vd) m k)
      | _ -> not_impl ())
  | MapSet (m_t, k_t, v_t) -> (
      let (IT (_, mbt, _)) = m_t in
      match HAdt.desc_of_bt mbt with
      | Some (AE.DMap (kd, vd)) ->
          let m = eval_annot subst m_t |> Core_value.cast_map |> of_opt_not_impl in
          let k = eval_annot subst k_t |> sv_of_cv kd |> of_opt_not_impl in
          let v = eval_annot subst v_t |> sv_of_cv vd |> of_opt_not_impl in
          Core_value.Map (Typed.map_set ~key:kd ~value:vd m k v)
      | _ -> not_impl ())
  | MapConst (kbt, v_t) -> (
      let (IT (_, vbt, _)) = v_t in
      match (HAdt.desc_of_bt kbt, HAdt.desc_of_bt vbt) with
      | Some kd, Some vd ->
          let v = eval_annot subst v_t |> sv_of_cv vd |> of_opt_not_impl in
          Core_value.Map (Typed.map_const ~key:kd ~value:vd v)
      | _ -> not_impl ())
  | Constructor (con_sym, field_annots) -> (
      let adt =
        match _bt with
        | Cn.BaseTypes.Datatype s -> HAdt.adt_name s
        | _ -> not_impl ()
      in
      let con = HAdt.adt_name con_sym in
      match AE.find_con adt con with
      | None -> not_impl ()
      | Some cdef ->
          let arg_of (fname, desc) =
            field_annots
            |> List.find_map (fun (id, a) ->
                if String.equal (Id.get_string id) fname then Some a else None)
            |> of_opt_not_impl
            |> eval_annot subst
            |> sv_of_cv desc
            |> of_opt_not_impl
          in
          let args = List.map arg_of cdef.fields in
          Core_value.Adt (Typed.adt_constr ~adt ~con args))
  | Match (scrut, cases) -> (
      let (IT (_, sbt, _)) = scrut in
      let scrut_adt =
        match sbt with
        | Cn.BaseTypes.Datatype s -> HAdt.adt_name s
        | _ -> not_impl ()
      in
      let sv = eval_annot subst scrut |> Core_value.cast_adt |> of_opt_not_impl in
      (* Compile a pattern against value [v] of datatype [adt]: yields the
         match guard and the pattern-variable bindings (as selector chains). *)
      let rec compile_pat adt (v : Typed.Svalue.t) (Cn.Terms.Pat (p, pbt, _)) =
        match p with
        | Cn.Terms.PWild -> (Typed.v_true, [])
        | PSym s ->
            let desc = HAdt.desc_of_bt pbt |> of_opt_not_impl in
            (Typed.v_true, [ (s, cv_of_desc desc v) ])
        | PConstructor (con_sym, fpats) ->
            let con = HAdt.adt_name con_sym in
            let guard = Typed.adt_tester ~con v in
            List.fold_left
              (fun (g, binds) (fid, subpat) ->
                let field = Id.get_string fid in
                let desc = AE.field_sort adt con field |> of_opt_not_impl in
                let child =
                  Typed.adt_sel ~adt ~con ~field ~field_ty:(ty_of_desc desc) v
                in
                let adt' = match desc with AE.DAdt a -> a | _ -> adt in
                let g', binds' = compile_pat adt' child subpat in
                (Typed.Bool.and_ g g', binds @ binds'))
              (guard, []) fpats
      in
      let eval_case binds body =
        let subst =
          List.fold_left (fun s (sym, v) -> add sym v s) subst binds
        in
        eval_annot subst body
      in
      match List.rev cases with
      | [] -> not_impl ()
      | (last_pat, last_body) :: earlier_rev ->
          (* The last case is the default branch of the ite chain. *)
          let _, last_binds = compile_pat scrut_adt sv last_pat in
          let init = eval_case last_binds last_body in
          List.fold_left
            (fun acc (pat, body) ->
              let guard, binds = compile_pat scrut_adt sv pat in
              ite_val ~of_opt_not_impl ~fail:not_impl guard
                (eval_case binds body)
                acc)
            init earlier_rev)
  | _ -> raise (Not_implemented annot)

let eval_annot subst term =
  try
    [%l.trace "Evaluating annot: %a" Mu.pp_it term];
    let res = eval_annot subst term in
    [%l.trace "Evaluated to: %a" Core_value.pp res];
    Csymex.return res
  with Not_implemented annot ->
    Fmt.kstr Csymex.not_impl "eval_annot %a" Mu.pp_it annot
