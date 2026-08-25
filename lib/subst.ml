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
let rec sv_of_cv (desc : AE.sort_desc) (v : Core_value.t) :
    Typed.Svalue.t option =
  match desc with
  | DBool -> Core_value.cast_bool v
  | DBits _ -> Core_value.cast_int v
  | DPtr _ | DLoc _ -> Core_value.cast_ptr v
  | DAdt _ -> Core_value.cast_adt v
  | DMap _ -> Core_value.cast_map v
  | DRecord fields -> (
      match v with
      | Core_value.Adt sv -> Some sv
      | Core_value.Record members ->
          let name = AE.register_record fields in
          let rec go acc = function
            | [] -> Some (List.rev acc)
            | (f, d) :: rest -> (
                let mv =
                  List.find_map
                    (fun (id, mv) ->
                      if String.equal (Cn.Id.get_string id) f then Some mv
                      else None)
                    members
                in
                match mv with
                | None -> None
                | Some mv -> (
                    match sv_of_cv d mv with
                    | Some sv -> go (sv :: acc) rest
                    | None -> None))
          in
          Option.map
            (fun args ->
              (Typed.adt_constr ~adt:name ~con:(AE.record_con name) args
                :> Typed.Svalue.t))
            (go [] fields)
      | _ -> None)

let rec cv_of_desc (desc : AE.sort_desc) (sv : Typed.Svalue.t) : Core_value.t =
  match desc with
  | DBool -> Bool sv
  | DBits _ -> Obj (Int sv)
  | DPtr _ | DLoc _ -> Obj (Ptr sv)
  | DAdt _ -> Adt sv
  | DMap _ -> Map sv
  | DRecord fields ->
      (* Rebuild a concrete record of selector projections, so record
         operations ([RecordMember], equality) stay structural. *)
      let name = AE.register_record fields in
      let con = AE.record_con name in
      let here = Cerb_location.unknown in
      Core_value.Record
        (List.map
           (fun (f, d) ->
             let field_sv =
               Typed.adt_sel ~adt:name ~con ~field:f ~field_ty:(ty_of_desc d)
                 (Typed.cast sv)
             in
             (Cn.Id.make here f, cv_of_desc d field_sv))
           fields)

and ty_of_desc (desc : AE.sort_desc) : Typed.Svalue.ty =
  match desc with
  | DBool -> Soteria.Bv_values.Svalue.TBool
  | DBits n -> Soteria.Bv_values.Svalue.TBitVector n
  | DPtr n -> Soteria.Bv_values.Svalue.TPointer n
  | DLoc n -> Soteria.Bv_values.Svalue.TLoc n
  | DAdt a -> Typed.t_adt a
  | DMap (k, v) -> Typed.t_map k v
  | DRecord fields -> Typed.t_adt (AE.register_record fields)

(* CN struct layouts of the current program, for [Good]/[Representable]
   expansion and [OffsetOf]/[MemberShift]. *)
let struct_decls () : Cn.Memory.struct_decls =
  let prog = Ctx.get_prog () in
  Symbol_std.Map.fold
    (fun tag def acc ->
      match def with
      | Mu.StructDef layout -> Cn.Sym.Map.add tag layout acc
      | Mu.UnionDef -> acc)
    prog.tag_defs Cn.Sym.Map.empty

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
      (* Signedness comes from the operands' base type, as in CN. (The C-side
         interpreter is consistent: it compares Core mathematical integers,
         which embed C values order-preservingly.) *)
      let signed =
        let (IT (_, bt1, _)) = t1 in
        match bt1 with
        | Cn.BaseTypes.Bits (Unsigned, _) -> false
        | Cn.BaseTypes.Bits (Signed, _) -> true
        | Cn.BaseTypes.Loc _ -> false
        | _ -> true
      in
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
      | Div | DivNoSMT ->
          int_op (fun a b -> Typed.BitVec.div ~signed a (Typed.cast b))
      | Rem | RemNoSMT ->
          int_op (fun a b -> Typed.BitVec.rem ~signed a (Typed.cast b))
      | Mod | ModNoSMT -> int_op (fun a b -> Typed.BitVec.mod_ a b)
      | MulNoSMT -> int_op (fun a b -> Typed.cast (Typed.BitVec.mul a b))
      | BW_And -> int_op Typed.BitVec.and_
      | BW_Or -> int_op Typed.BitVec.or_
      | BW_Xor -> int_op Typed.BitVec.xor
      | ShiftLeft -> int_op Typed.BitVec.shl
      | ShiftRight ->
          int_op (if signed then Typed.BitVec.ashr else Typed.BitVec.lshr)
      | Exp | ExpNoSMT -> (
          (* Concrete exponent only, as in CN. *)
          let i1, i2 = ints () in
          match (Typed.BitVec.to_z i1, Typed.BitVec.to_z i2) with
          | Some b, Some e when Z.fits_int e && Z.geq e Z.zero ->
              let w = Typed.size_of_int i1 in
              Obj (Int (Typed.BitVec.mk_masked w (Z.pow b (Z.to_int e))))
          | _ -> not_impl ())
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
      | BW_Compl ->
          let i = Core_value.cast_int v |> of_opt_not_impl in
          Obj (Int (Typed.BitVec.not i))
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
  | EachI ((i1, (x, bt), i2), body) ->
      (* CN's solver expands [EachI] into a conjunction over the (concrete)
         range (solver.ml); mirror it, with a safety cap on the range size. *)
      if i2 - i1 > 10_000 then (
        [%l.warn "EachI range too large to expand (%d..%d)" i1 i2];
        not_impl ())
      else if i1 > i2 then Core_value.Bool Typed.v_true
      else
        (* The body types [x] as mathematical [integer] (CN re-types it via
           WellTyped before its solver expands); bind the index in the
           evaluation environment instead — capture-safe, since evaluation is
           environment-based. The index value is built at the quantifier's
           declared width. *)
        let width =
          match bt with
          | Cn.BaseTypes.Bits (_, n) -> n
          | _ -> Typed.math_bits
        in
        let conj =
          List.init
            (i2 - i1 + 1)
            (fun d ->
              let i = i1 + d in
              let iv =
                Core_value.Obj (Int (Typed.BitVec.mk_masked width (Z.of_int i)))
              in
              eval_annot (add x iv subst) body |> Core_value.cast_bool
              |> of_opt_not_impl)
        in
        Core_value.Bool
          (List.fold_left
             (fun acc b -> Typed.Bool.and_ acc b)
             Typed.v_true conj)
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
  | SizeOf ct -> (
      match _bt with
      | Cn.BaseTypes.Bits (_, w) ->
          Obj
            (Int
               (Typed.BitVec.mk_masked w
                  (Z.of_int (Cn.Memory.size_of_ctype ct))))
      | _ -> not_impl ())
  | OffsetOf (tag, member) -> (
      let layout =
        match Symbol_std.Map.find_opt tag (Ctx.get_prog ()).tag_defs with
        | Some (Mu.StructDef layout) -> layout
        | _ -> not_impl ()
      in
      match (Cn.Memory.member_offset layout member, _bt) with
      | Some off, Cn.BaseTypes.Bits (_, w) ->
          Obj (Int (Typed.BitVec.mk_masked w (Z.of_int off)))
      | _ -> not_impl ())
  | ArrayShift { base; ct; index } ->
      let bp = eval_annot subst base |> Core_value.cast_ptr |> of_opt_not_impl in
      let idx =
        eval_annot subst index |> Core_value.cast_int |> of_opt_not_impl
      in
      let signed =
        let (IT (_, ibt, _)) = index in
        match ibt with Cn.BaseTypes.Bits (Signed, _) -> true | _ -> false
      in
      let idx = Typed.BitVec.fit_to ~signed Typed.ptr_bits idx in
      let size =
        Typed.BitVec.mk_masked Typed.ptr_bits
          (Z.of_int (Cn.Memory.size_of_ctype ct))
      in
      Obj (Ptr (Typed.Ptr.add_ofs bp (Typed.cast (Typed.BitVec.mul idx size))))
  | MemberShift (t, tag, member) -> (
      let p = eval_annot subst t |> Core_value.cast_ptr |> of_opt_not_impl in
      let layout =
        match Symbol_std.Map.find_opt tag (Ctx.get_prog ()).tag_defs with
        | Some (Mu.StructDef layout) -> layout
        | _ -> not_impl ()
      in
      match Cn.Memory.member_offset layout member with
      | Some off ->
          Obj
            (Ptr
               (Typed.Ptr.add_ofs p
                  (Typed.BitVec.mk_masked Typed.ptr_bits (Z.of_int off))))
      | None -> not_impl ())
  | Cast (target_bt, t') -> (
      let (IT (_, src_bt, _)) = t' in
      match (target_bt, src_bt) with
      | Cn.BaseTypes.Bits (tsign, tw), Cn.BaseTypes.Bits (ssign, _) ->
          let _ = tsign in
          let i =
            eval_annot subst t' |> Core_value.cast_int |> of_opt_not_impl
          in
          let signed = match ssign with Cn.BaseTypes.Signed -> true | _ -> false in
          Obj (Int (Typed.BitVec.fit_to ~signed tw i))
      | Cn.BaseTypes.Alloc_id, Cn.BaseTypes.Loc _ ->
          (* An allocation id, represented as the pointer's location with a
             zeroed offset — only its equality is ever used (prov_eq). *)
          let p =
            eval_annot subst t' |> Core_value.cast_ptr |> of_opt_not_impl
          in
          Obj
            (Ptr
               (Typed.Ptr.mk (Typed.Ptr.loc p)
                  (Typed.BitVec.zero Typed.ptr_bits)))
      | _ -> not_impl ())
  | WrapI (ity, t') ->
      let i = eval_annot subst t' |> Core_value.cast_int |> of_opt_not_impl in
      let bits = Core_value.bits_of_ity ity in
      Obj (Int (Typed.BitVec.fit_to ~signed:false bits i))
  | HasAllocId t' ->
      let p = eval_annot subst t' |> Core_value.cast_ptr |> of_opt_not_impl in
      Bool (Typed.not (Typed.Ptr.is_null_loc (Typed.Ptr.loc p)))
  | Aligned _ ->
      (* The memory model does not track alignment (cf. soteria-c's
         [PtrWellAligned]); alignment facts are trivially true in it. *)
      Core_value.true_
  | Representable (ct, t') ->
      eval_annot subst (Cn.IndexTerms.representable (struct_decls ()) ct t' _loc)
  | Good (ct, t') ->
      (* CN expands [good]/[representable] into range/member/array
         constraints; reuse its expansion and evaluate the result. *)
      eval_annot subst (Cn.IndexTerms.good_value (struct_decls ()) ct t' _loc)
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
