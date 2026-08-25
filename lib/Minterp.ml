module SState = State
open Soteria_c_vendor
module State = SState
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
open Core_value.Syntax
open Csymex
module Mu = Usable_mucore
open Mu
module InterpM = Interp_monad

module ExprM = struct
  type 'a exec_r = Normal of 'a | Returned of Core_value.t | Jumped
  [@@deriving show { with_path = false }]

  let returned_value = function
    | Returned v -> v
    | Normal _ | Jumped -> Core_value.Unit

  type 'a t = 'a exec_r InterpM.t

  let bind (f : 'a -> 'b t) (m : 'a t) : 'b t =
    InterpM.bind
      (function
        | Normal x -> f x
        | Returned v -> InterpM.ok (Returned v)
        | Jumped -> InterpM.ok Jumped)
      m

  let map (f : 'a -> 'b) (m : 'a t) : 'b t =
    InterpM.map
      (function
        | Normal x -> Normal (f x)
        | Returned v -> Returned v
        | Jumped -> Jumped)
      m

  let ok (x : 'a) : 'a t = InterpM.ok (Normal x)
  let error e : 'a t = InterpM.error e
  let returned (v : Core_value.t) : 'a t = InterpM.ok (Returned v)

  let fold_list (xs : 'a list) ~(init : 'b) ~(f : 'b -> 'a -> 'b t) : 'b t =
    Monad.foldM (module List) ~init ~return:ok ~bind xs ~f

  let map_list (xs : 'a list) ~(f : 'a -> 'b t) : 'b list t =
    fold_list ~init:[] xs ~f:(fun acc a -> map (fun b -> b :: acc) (f a))
    |> map List.rev

  module Syntax = struct
    let ( let** ) m f = bind f m
    let ( let++ ) m f = map f m
  end
end

open InterpM
open Syntax

let error_of_ub (_ub : CF.Undefined.undefined_behaviour) : Cn_error.t =
  `UBPointerArithmetic

let eval_impl_call (i : CF.Implementation.implementation_constant)
    (args : Core_value.t list) : Core_value.t InterpM.t =
  match (i, args) with _ -> not_impl "unsupported impl call"

let malloc_failure_case () =
  if (Soteria_c_vendor.Config.current ()).alloc_cannot_fail then []
  else
    [
      (fun () ->
        let ptr = Typed.Ptr.null in
        ok (Core_value.Loaded (Spec (Ptr ptr))));
    ]

let int_ty_of_ctype ~what (ty : CF.Ctype.ctype) :
    CF.Ctype.integerType InterpM.t =
  match ty with
  | Ctype (_, Basic (Integer int_ty)) -> ok int_ty
  | _ ->
      not_impl "%s: type argument is not an integer type: %a" what Mu.pp_ctype
        ty

(* [v] is in the range of [ity], seen at [v]'s (signed) width. *)
let in_ity_range (ity : CF.Ctype.integerType) (v : Typed.(T.sint t)) :
    Typed.(T.sbool t) =
  let width =
    match Typed.get_ty v with
    | TBitVector s -> s
    | _ -> L.failwith "in_ity_range: not a bitvector"
  in
  let bits = Core_value.bits_of_ity ity in
  let signed = Layout.is_int_ty_signed ity in
  let lo = if signed then Z.neg (Z.shift_left Z.one (bits - 1)) else Z.zero in
  let hi =
    if signed then Z.pred (Z.shift_left Z.one (bits - 1))
    else Z.pred (Z.shift_left Z.one bits)
  in
  let lo = Typed.BitVec.mk_masked width lo in
  let hi = Typed.BitVec.mk_masked width hi in
  Typed.Bool.and_
    (Typed.BitVec.leq ~signed:true lo v)
    (Typed.BitVec.leq ~signed:true v hi)

(* Core's [conv_int]: embed a loaded C value of integer type [ty] into Core's
   mathematical integers ([math_bits] wide), order-preservingly. *)
let conv_int ~(ty : CF.Ctype.ctype) v : Typed.(T.sint t) InterpM.t =
  let open Typed.Infix in
  let* i = CV.cast_int v in
  let* int_ty = int_ty_of_ctype ~what:"conv_int" ty in
  let+ current_size =
    match Typed.get_ty i with
    | TBitVector s -> ok s
    | _ -> not_impl "conv_int: value is not a bitvector: %a" Core_value.pp v
  in
  match int_ty with
  | Bool ->
      Typed.ite
        (i ==@ Typed.BitVec.zero current_size)
        (Typed.BitVec.mk_masked Typed.math_bits Z.zero)
        (Typed.BitVec.mk_masked Typed.math_bits Z.one)
  | ity ->
      let signed = Layout.is_int_ty_signed ity in
      Typed.BitVec.fit_to ~signed Typed.math_bits i

(* Core's [conv_loaded_int]: convert a mathematical integer back to a loaded C
   value of type [ty]. Following CN's [check_conv_int]: _Bool tests against 0,
   unsigned types wrap, and a signed target must be provable in range. *)
let conv_loaded_int ~(ty : CF.Ctype.ctype) v : Typed.(T.sint t) InterpM.t =
  let open Typed.Infix in
  let* i = CV.cast_int v in
  let* int_ty = int_ty_of_ctype ~what:"conv_loaded_int" ty in
  let* current_size =
    match Typed.get_ty i with
    | TBitVector s -> ok s
    | _ ->
        not_impl "conv_loaded_int: value is not a bitvector: %a" Core_value.pp
          v
  in
  match int_ty with
  | Bool ->
      let bits = Core_value.bits_of_ity Bool in
      ok
        (Typed.ite
           (i ==@ Typed.BitVec.zero current_size)
           (Typed.BitVec.mk_masked bits Z.zero)
           (Typed.BitVec.mk_masked bits Z.one))
  | ity ->
      let bits = Core_value.bits_of_ity ity in
      let signed = Layout.is_int_ty_signed ity in
      if not signed then ok (Typed.BitVec.fit_to ~signed:false bits i)
      else
        if%sat Typed.Bool.not (in_ity_range ity i) then
          (* CN reports an unrepresentable-integer error here. *)
          error `Overflow
        else ok (Typed.BitVec.fit_to ~signed:true bits i)

let eval_ctor (ctor : CF.Core.ctor) (vs : Core_value.t list) :
    Core_value.t InterpM.t =
  let open Core_value in
  match (ctor, vs) with
  | Cspecified, [ Obj v ] -> ok (Loaded (Spec v))
  | Cunspecified, _ -> ok (Loaded Unspec)
  | Ctuple, vs -> ok (Tuple vs)
  | Civsizeof, [ Type ty ] ->
      let+^ size = Layout.size_of_s ty in
      Obj (Int (Typed.BitVec.fit_to ~signed:false Typed.math_bits size))
  | Civalignof, [ Type ty ] ->
      let+^ align = Layout.align_of_s ty in
      Obj (Int (Typed.BitVec.fit_to ~signed:false Typed.math_bits align))
  | Carray, vs ->
      let cells =
        List.map
          (function
            | Obj o -> Spec o
            | Loaded l -> l
            | v -> L.failwith "Carray: not an object value: %a" Core_value.pp v)
          vs
      in
      ok (Obj (Array cells))
  | (Civmax | Civmin), [ Type ty ] ->
      let* int_ty = int_ty_of_ctype ~what:"Civmax/Civmin" ty in
      let bits = Core_value.bits_of_ity int_ty in
      let signed = Layout.is_int_ty_signed int_ty in
      let z =
        match ctor with
        | Civmax ->
            if signed then Z.pred (Z.shift_left Z.one (bits - 1))
            else Z.pred (Z.shift_left Z.one bits)
        | _ -> if signed then Z.neg (Z.shift_left Z.one (bits - 1)) else Z.zero
      in
      ok (Obj (Int (Typed.BitVec.mk_masked Typed.math_bits z)))
  | CivCOMPL, [ Type ty; v ] ->
      (* Complement within the type's width, re-embedded as a mathematical
         integer. *)
      let* int_ty = int_ty_of_ctype ~what:"CivCOMPL" ty in
      let bits = Core_value.bits_of_ity int_ty in
      let signed = Layout.is_int_ty_signed int_ty in
      let* i = CV.cast_int v in
      let i = Typed.BitVec.fit_to ~signed:false bits i in
      let r = Typed.BitVec.not i in
      ok (Obj (Int (Typed.BitVec.fit_to ~signed Typed.math_bits r)))
  | (CivAND | CivOR | CivXOR), [ Type ty; a; b ] ->
      let* int_ty = int_ty_of_ctype ~what:"CivAND/OR/XOR" ty in
      let bits = Core_value.bits_of_ity int_ty in
      let signed = Layout.is_int_ty_signed int_ty in
      let* a = CV.cast_int a in
      let* b = CV.cast_int b in
      let a = Typed.BitVec.fit_to ~signed:false bits a in
      let b = Typed.BitVec.fit_to ~signed:false bits b in
      let r =
        match ctor with
        | CivAND -> Typed.BitVec.and_ a b
        | CivOR -> Typed.BitVec.or_ a b
        | _ -> Typed.BitVec.xor a b
      in
      ok (Obj (Int (Typed.BitVec.fit_to ~signed Typed.math_bits r)))
  | _ ->
      not_impl "Unsupported constructor: %a with args %a" Mu.pp_ctor ctor
        (Fmt.Dump.list Core_value.pp)
        vs

let exec_spec ~subst (arguments : arguments) (return_type : return_type) :
    Core_value.t InterpM.t =
  let open Cn_assert in
  let* state =
    (* We only retrieve this for debugging *)
    get_state ()
  in
  [%l.debug
    "@[<v 2>About to execute specification with state: %a@]@.@[<v 2>Subst:@ \
     %a@]"
      (Fmt.Dump.option @@ SState.pp_pretty ~ignore_freed:true)
      state Subst.pp subst];
  let* (), subst = consume_arguments arguments subst in
  let+ subst = produce_return_type ~subst return_type in
  let v = Subst.find (fst return_type.ret) subst in
  v

(* [PEwrapI]/[PEcatch_exceptional_condition]: mirror CN by computing in a
   width where the operation cannot wrap ([2*bits + 4], like CN's [large_bt]),
   then either wrapping to [int_ty] (wrapI) or erroring when the exact result
   is outside [int_ty]'s range (catch_exceptional_condition). Operands and
   result are mathematical integers ([math_bits] wide). *)
let eval_iop ~(int_ty : CF.Ctype.integerType) ~(wrapping : bool)
    (iop : CF.Core.iop) (lhs : Typed.(T.sint t)) (rhs : Typed.(T.sint t)) :
    Typed.(T.sint t) InterpM.t =
  let bits = Core_value.bits_of_ity int_ty in
  let signed = Layout.is_int_ty_signed int_ty in
  let big = max Typed.math_bits ((2 * bits) + 4) in
  let l = Typed.BitVec.fit_to ~signed:true big lhs in
  let r = Typed.BitVec.fit_to ~signed:true big rhs in
  let* res =
    match iop with
    | IOpAdd -> ok (Typed.cast (Typed.BitVec.add l r))
    | IOpSub -> ok (Typed.cast (Typed.BitVec.sub l r))
    | IOpMul -> ok (Typed.cast (Typed.BitVec.mul l r))
    | IOpDiv ->
        (* Division by zero is guarded by the elaboration. *)
        ok (Typed.cast (Typed.BitVec.div ~signed:true l (Typed.cast r)))
    | IOpRem_t ->
        ok (Typed.cast (Typed.BitVec.rem ~signed:true l (Typed.cast r)))
    | IOpShl -> ok (Typed.cast (Typed.BitVec.shl l r))
    | IOpShr ->
        ok
          (Typed.cast
             (if signed then Typed.BitVec.ashr l r
              else Typed.BitVec.lshr l r))
  in
  if wrapping then
    let wrapped = Typed.BitVec.fit_to ~signed:false bits res in
    ok (Typed.BitVec.fit_to ~signed Typed.math_bits wrapped)
  else
    if%sat Typed.Bool.not (in_ity_range int_ty res) then error `Overflow
    else ok (Typed.BitVec.fit_to ~signed:true Typed.math_bits res)

let cfunction (v : Core_value.t) =
  let* sym =
    match v with
    | Obj (Fn sym) | Loaded (Spec (Fn sym)) -> ok sym
    | _ -> not_impl "cfunction: value is not a function: %a" Core_value.pp v
  in
  let prog = Ctx.get_prog () in
  let* fn =
    Sym.Map.find_opt sym prog.call_funinfo
    |> InterpM.of_opt_not_impl ~msg:"cfunction: function not found in program"
  in
  ok (Core_value.cfunction fn)

let eval_memop (memop : Symbol_std.t CF.Mem_common.generic_memop)
    (args : Core_value.t list) : Core_value.t InterpM.t =
  let open Typed.Infix in
  match (memop, args) with
  | PtrEq, [ p1; p2 ] ->
      let* p1 = CV.cast_ptr p1 in
      let* p2 = CV.cast_ptr p2 in
      (* Is this correct? I forgot the semantics of pointer equality *)
      ok (Core_value.Bool (p1 ==@ p2))
  | PtrNe, [ p1; p2 ] ->
      let* p1 = CV.cast_ptr p1 in
      let* p2 = CV.cast_ptr p2 in
      ok (Core_value.Bool (Typed.Bool.not (p1 ==@ p2)))
  | ((PtrLt | PtrGt | PtrLe | PtrGe) as op), [ p1; p2 ] ->
      let* p1 = CV.cast_ptr p1 in
      let* p2 = CV.cast_ptr p2 in
      (* Relational comparison is only defined within one object. *)
      if%sat Typed.Ptr.loc p1 ==@ Typed.Ptr.loc p2 then
        let o1 = Typed.Ptr.ofs p1 in
        let o2 = Typed.Ptr.ofs p2 in
        let b =
          match op with
          | PtrLt -> Typed.BitVec.lt ~signed:false o1 o2
          | PtrGt -> Typed.BitVec.lt ~signed:false o2 o1
          | PtrLe -> Typed.BitVec.leq ~signed:false o1 o2
          | PtrGe -> Typed.BitVec.leq ~signed:false o2 o1
          | _ -> assert false
        in
        ok (Core_value.Bool b)
      else error `UBPointerComparison
  | Ptrdiff, ([ Type ty; p1; p2 ] | [ p1; Type ty; p2 ]) ->
      let* p1 = CV.cast_ptr p1 in
      let* p2 = CV.cast_ptr p2 in
      if%sat Typed.Ptr.loc p1 ==@ Typed.Ptr.loc p2 then
        let*^ size = Layout.size_of_s ty in
        let diff = Typed.BitVec.sub (Typed.Ptr.ofs p1) (Typed.Ptr.ofs p2) in
        let q =
          Typed.BitVec.div ~signed:true (Typed.cast diff) (Typed.cast size)
        in
        ok
          (Core_value.Obj
             (Int
                (Typed.BitVec.fit_to ~signed:true Typed.math_bits
                   (Typed.cast q))))
      else error `UBPointerArithmetic
  | PtrArrayShift, ([ p; Type ty; idx ] | [ Type ty; p; idx ]) ->
      let* p = CV.cast_ptr p in
      let* idx = CV.cast_int idx in
      let*^ size = Layout.size_of_s ty in
      let idx = Typed.BitVec.fit_to ~signed:true Typed.ptr_bits idx in
      ok
        (Core_value.Obj
           (Ptr (Typed.Ptr.add_ofs p (Typed.cast (Typed.BitVec.mul idx size)))))
  | PtrMemberShift (tag, member), [ p ] ->
      let* p = CV.cast_ptr p in
      let ty = CF.Ctype.(Ctype ([], Struct tag)) in
      let+^ mem_ofs = Layout.member_ofs member ty in
      Core_value.Obj (Ptr (Typed.Ptr.add_ofs p mem_ofs))
  | (PtrWellAligned | PtrValidForDeref), _args ->
      (* Pointer validity for dereference should be handled by the state.
         For alignment, we could also do the Soteria Rust trick of embedding the alignment in the pointer representation. *)
      ok Core_value.true_
  | _ -> not_impl "Unsupported memop: %a" Mu.pp_memop memop

let eval_op (op : CF.Core.binop) (lhs : Core_value.t) (rhs : Core_value.t) =
  let open Core_value in
  match op with
  | OpEq -> ok (Bool (sem_eq lhs rhs))
  | OpOr -> ok @@ Core_value.Bool.or_ lhs rhs
  | OpLt ->
      (* Operands are mathematical integers ([math_bits]-wide, order-preserving
         signed embedding), so a signed comparison is always correct. *)
      ok @@ Core_value.lt ~signed:true lhs rhs
  | OpLe -> ok @@ Core_value.leq ~signed:true lhs rhs
  | OpGt -> ok @@ Core_value.lt ~signed:true rhs lhs
  | OpGe -> ok @@ Core_value.leq ~signed:true rhs lhs
  | OpAdd | OpSub | OpMul | OpDiv | OpRem_t | OpRem_f -> (
      (* Arithmetic on Core mathematical integers ([math_bits]-wide). The
         elaboration guards division by zero separately. *)
      let* l = CV.cast_int lhs in
      let* r = CV.cast_int rhs in
      let res =
        match op with
        | OpAdd -> Typed.cast (Typed.BitVec.add l r)
        | OpSub -> Typed.cast (Typed.BitVec.sub l r)
        | OpMul -> Typed.cast (Typed.BitVec.mul l r)
        | OpDiv -> Typed.cast (Typed.BitVec.div ~signed:true l (Typed.cast r))
        | OpRem_t ->
            Typed.cast (Typed.BitVec.rem ~signed:true l (Typed.cast r))
        | _ -> Typed.cast (Typed.BitVec.mod_ l r)
      in
      ok (Obj (Int res)))
  | OpExp -> (
      let* l = CV.cast_int lhs in
      let* r = CV.cast_int rhs in
      match (Typed.BitVec.to_z l, Typed.BitVec.to_z r) with
      | Some b, Some e when Z.fits_int e && Z.geq e Z.zero ->
          ok
            (Obj
               (Int
                  (Typed.BitVec.mk_masked Typed.math_bits
                     (Z.pow b (Z.to_int e)))))
      | _ -> not_impl "OpExp: symbolic exponent")
  | _ -> not_impl "eval_op: unsupported operator: %a" Mu.pp_binop op

let rec eval_action (subst : Subst.t) (action : action) : Core_value.t InterpM.t
    =
  let@ () = with_loc ~loc:action.loc in
  match action.action with
  | Create { align = _; ty; prefix = _ } ->
      let* ptr = State.alloc_ty ty.node in
      let pv = Core_value.Obj (Ptr ptr) in
      (* CN's [Create] also yields an allocation token, consumed by [Kill] and
         by loop-invariant argument types. Its output (base/size record) is
         left unconstrained. *)
      let*^ out = Core_value.nondet_bt Cn.Alloc.History.value_bt in
      let+ () =
        lift_sm (SState.produce_pred Cn.Alloc.Predicate.sym [ pv ] [ out ])
      in
      pv
  | Store { ptr; value; ty; _ } ->
      let* ptr = eval_pexpr subst ptr in
      let* value = eval_pexpr subst value in
      let+ () = State.store ptr ty.node value in
      Core_value.Unit
  | Load { ptr; ty; _ } ->
      let* ptr = eval_pexpr subst ptr in
      State.load ptr ty.node
  | Kill (kind, ptr) ->
      let* ptr = eval_pexpr subst ptr in
      let* _out = SState.consume_pred Cn.Alloc.Predicate.sym [ ptr ] in
      let+ () =
        match kind with
        | Static ct ->
            let* tptr = CV.cast_ptr ptr in
            SState.kill_static tptr ct
        | Dynamic -> State.free ptr
      in
      Core_value.Unit
  | _ -> not_impl "Unsupported action: %a" Mu.pp_action action

and eval_call ~loc (sym : Sym.t) (args : Core_value.t list) :
    Core_value.t InterpM.t =
  match (sym, args) with
  | Symbol (_, _, SD_Id "conv_loaded_int"), [ ty; i ] -> (
      let* ty = CV.cast_type ty in
      match i with
      | Loaded (Spec _) | Obj (Int _) ->
          let+ i = conv_loaded_int ~ty i in
          Core_value.Loaded (Spec (Int i))
      | Loaded Unspec -> ok (Core_value.Loaded Unspec)
      | _ -> L.failwith "Invalid input to conv_loaded_int")
  | Symbol (_, _, SD_Id "conv_int"), [ ty; i ] -> (
      let* ty = CV.cast_type ty in
      match i with
      | Loaded (Spec _) | Obj (Int _) ->
          let+ i = conv_int ~ty i in
          Core_value.(Obj (Int i))
      | Loaded Unspec -> ok (Core_value.Loaded Unspec)
      | _ -> L.failwith "Invalid input to conv_int %a" Core_value.pp i)
  | Symbol (_, _, SD_Id "is_representable_integer"), [ a; b ] ->
      let v, ty =
        match Core_value.cast_type a with Some _ -> (b, a) | None -> (a, b)
      in
      let* i = CV.cast_int v in
      let* ty = CV.cast_type ty in
      let* int_ty = int_ty_of_ctype ~what:"is_representable_integer" ty in
      ok (Core_value.Bool (in_ity_range int_ty i))
  | Symbol (_, _, SD_Id "ctype_width"), [ ty ] ->
      let* ty = CV.cast_type ty in
      let* int_ty = int_ty_of_ctype ~what:"ctype_width" ty in
      let bits = Core_value.bits_of_ity int_ty in
      ok
        (Core_value.Obj
           (Int (Typed.BitVec.mk_masked Typed.math_bits (Z.of_int bits))))
  | Symbol (_, _, SD_Id "params_length"), [ List l ] ->
      ok @@ Core_value.c_int (List.length l)
  | ( Symbol (_, _, SD_Id "params_nth"),
      [ List l; (Obj (Int i) | Loaded (Spec (Int i))) ] ) ->
      let* i =
        Typed.BitVec.to_z i
        |> InterpM.of_opt_not_impl
             ~msg:"params_nth: index is not a concrete integer"
      in
      let i = Z.to_int i in
      ok @@ List.nth l i
  | Symbol (_, _, SD_Id "malloc_proxy"), [ size ] ->
      InterpM.branches
        ([
           (fun () ->
             let* ptr = State.alloc size in
             let pv = Core_value.Loaded (Spec (Ptr ptr)) in
             (* Like CN's malloc spec, yield an allocation token so a later
                [Kill Dyn] (free) stays balanced. *)
             let*^ out = Core_value.nondet_bt Cn.Alloc.History.value_bt in
             let+ () =
               lift_sm
                 (SState.produce_pred Cn.Alloc.Predicate.sym [ pv ] [ out ])
             in
             pv);
         ]
        @ malloc_failure_case ())
  | sym, args -> (
      match Sym.Map.find_opt sym (Ctx.get_prog ()).funs with
      | None -> not_impl "Couldn't resolve function: %a" Sym.pp_hum sym
      | Some fn ->
          with_extra_call_trace ~loc ~msg:"Called from here" @@ exec_fun fn args
      )

and eval_pexpr (subst : Subst.t) (pexpr : pexpr) =
  [%l.trace "Evaluating pexpr: %a" Mu.pp_pexpr pexpr];
  let@ () = with_loc ~loc:pexpr.loc in
  match pexpr.node with
  | PEsym sym -> ok (Subst.find sym subst)
  | PEval v -> ok (Core_value.of_mu v)
  | PEcfunction pe ->
      let* f = eval_pexpr subst pe in
      cfunction f
  | PEundef (_, ub) -> error (error_of_ub ub)
  | PEcall (generic_name, args) -> (
      let* args = map_list ~f:(eval_pexpr subst) args in
      match generic_name with
      | Sym s -> eval_call ~loc:pexpr.loc s args
      | Impl i -> eval_impl_call i args)
  | PEctor (ctor, pes) ->
      let* vs = map_list ~f:(eval_pexpr subst) pes in
      eval_ctor ctor vs
  | PElet { pat; value; body } ->
      let* v = eval_pexpr subst value in
      let*^ subst = Subst.assign_pattern subst pat v in
      eval_pexpr subst body
  | PEcatch_exceptional_condition { int_ty; iop; lhs; rhs } ->
      let* lhs = eval_pexpr subst lhs in
      let* rhs = eval_pexpr subst rhs in
      let* lhs = CV.cast_int lhs in
      let* rhs = CV.cast_int rhs in
      let+ res = eval_iop ~int_ty ~wrapping:false iop lhs rhs in
      Core_value.Obj (Core_value.Int res)
  | PEwrapI { int_ty; iop; lhs; rhs } ->
      let* lhs = eval_pexpr subst lhs in
      let* rhs = eval_pexpr subst rhs in
      let* lhs = CV.cast_int lhs in
      let* rhs = CV.cast_int rhs in
      let+ res = eval_iop ~int_ty ~wrapping:true iop lhs rhs in
      Core_value.Obj (Core_value.Int res)
  | PEnot e ->
      let+ b = eval_pexpr subst e in
      Core_value.Bool.not b
  | PEop { op; lhs; rhs } ->
      let* lhs = eval_pexpr subst lhs in
      let* rhs = eval_pexpr subst rhs in
      eval_op op lhs rhs
  | PEare_compatible { left; right } ->
      (* Deeply uninteresting but I guess we have to implement that... *)
      let* left = eval_pexpr subst left in
      let* left = CV.cast_type left in
      let* right = eval_pexpr subst right in
      let* right = CV.cast_type right in
      let res =
        CF.AilTypesAux.are_compatible
          (CF.Ctype.no_qualifiers, left)
          (CF.Ctype.no_qualifiers, right)
      in
      ok (Core_value.Bool.of_bool res)
  | PEif { cond; then_; else_ } ->
      let* guard = eval_pexpr subst cond in
      let* () = State.unfold_on_if_else guard in
      let guard = Core_value.Bool.to_sbool guard in
      if%sat guard then eval_pexpr subst then_ else eval_pexpr subst else_
  | PEconv_int { ty; arg } -> (
      let* ty = eval_pexpr subst ty in
      let* i = eval_pexpr subst arg in
      let* ty = CV.cast_type ty in
      match i with
      | Loaded (Spec _) | Obj (Int _) ->
          let+ i = conv_loaded_int ~ty i in
          Core_value.(Obj (Int i))
      | Loaded Unspec -> ok (Core_value.Loaded Unspec)
      | _ -> L.failwith "Invalid input to conv_int %a" Core_value.pp i)
  | PEmember_shift { ptr; tag; member } ->
      let* ptr = eval_pexpr subst ptr in
      let* ptr = CV.cast_ptr ptr in
      let ty = CF.Ctype.(Ctype ([], Struct tag)) in
      let+^ mem_ofs = Layout.member_ofs member ty in
      Core_value.Obj (Ptr (Typed.Ptr.add_ofs ptr mem_ofs))
  | PEmemop _ -> not_impl "PEmemop"
  | PEconstrained _ -> not_impl "PEconstrainted"
  | PEerror (msg, _) ->
      [%l.debug "Reached PEerror: %s" msg];
      error `FailedAssert
  | PEarray_shift { base; ty; index } ->
      let* base_v = eval_pexpr subst base in
      let* bptr = CV.cast_ptr base_v in
      let* idx_v = eval_pexpr subst index in
      let* idx = CV.cast_int idx_v in
      let*^ size = Layout.size_of_s (Cn.Sctypes.to_ctype ty) in
      let idx = Typed.BitVec.fit_to ~signed:true Typed.ptr_bits idx in
      ok
        (Core_value.Obj
           (Ptr (Typed.Ptr.add_ofs bptr (Typed.cast (Typed.BitVec.mul idx size)))))
  | PEstruct (tag, fields) ->
      let* fields =
        map_list fields ~f:(fun (id, pe) ->
            let+ v = eval_pexpr subst pe in
            (id, v))
      in
      let prog = Ctx.get_prog () in
      let* members =
        match Sym.Map.find_opt tag prog.tag_defs with
        | Some (StructDef layout) ->
            InterpM.ok
              (List.filter_map
                 (fun (piece : Cn.Memory.struct_piece) ->
                   match piece.member_or_padding with
                   | None -> None
                   | Some (id, _) ->
                       let v =
                         List.find_map
                           (fun (id', v) ->
                             if Cn.Id.equal id id' then Some v else None)
                           fields
                       in
                       Some
                         (match v with
                         | Some (Core_value.Obj o) -> Core_value.Spec o
                         | Some (Loaded l) -> l
                         | _ -> Core_value.Unspec))
                 layout)
        | _ -> not_impl "PEstruct: unknown struct tag"
      in
      ok (Core_value.Obj (Struct { tag; members }))
  | PEunion _ -> not_impl "PEunion"
  | PEmemberof { tag; member; value } -> (
      let* v = eval_pexpr subst value in
      let prog = Ctx.get_prog () in
      let* members =
        match v with
        | Obj (Struct { members; _ }) | Loaded (Spec (Struct { members; _ }))
          ->
            InterpM.ok members
        | _ -> not_impl "PEmemberof: not a struct value"
      in
      match Sym.Map.find_opt tag prog.tag_defs with
      | Some (StructDef layout) -> (
          let member_ids =
            List.filter_map
              (fun (piece : Cn.Memory.struct_piece) ->
                Option.map fst piece.member_or_padding)
              layout
          in
          match
            List.find_index (fun id -> Cn.Id.equal id member) member_ids
          with
          | Some i -> (
              match List.nth_opt members i with
              | Some (Core_value.Spec o) -> ok (Core_value.Obj o)
              | Some Unspec -> ok (Core_value.Loaded Unspec)
              | None -> not_impl "PEmemberof: member index out of range")
          | None -> not_impl "PEmemberof: unknown member")
      | _ -> not_impl "PEmemberof: unknown struct tag")

and eval_expr ~(labels : label_def Sym.Map.t) (subst : Subst.t) (body : expr) :
    Core_value.t ExprM.t =
  let open ExprM.Syntax in
  [%l.debug "@[<v 2>Evaluating expr:@ %a@]" Mu.pp_expr body];
  let@ () = with_loc ~loc:body.loc in
  [%l.trace "@[<v 4>Substitution:@ %a@]" Subst.pp subst];
  let* st = get_state () in
  [%l.trace
    "@[<v 4>Current state:@ %a@]"
      (Fmt.Dump.option @@ SState.pp_pretty ~ignore_freed:true)
      st];
  let*^ () = Csymex.consume_fuel_steps 1 in
  (* let* () =
    if List.is_empty body.annots then return ()
    else Fmt.kstr not_impl "annotations: %a" 
  in *)
  match body.node with
  | Elet { pat; value; body = body' } ->
      let* v = eval_pexpr subst value in
      let*^ subst = Subst.assign_pattern subst pat v in
      eval_expr ~labels subst body'
  | Esseq { pat; value; body } | Ewseq { pat; value; body } ->
      let** v = eval_expr ~labels subst value in
      let*^ subst = Subst.assign_pattern subst pat v in
      eval_expr ~labels subst body
  | Eunseq es ->
      let++ res = ExprM.map_list es ~f:(eval_expr ~labels subst) in
      Core_value.Tuple res
  | Ebound e -> eval_expr ~labels subst e
  | Epure e ->
      let+ r = eval_pexpr subst e in
      ExprM.Normal r
  | Erun (lab, pes) -> (
      [%l.trace "Running label: %a" Sym.pp_hum lab];
      let* vs = map_list ~f:(eval_pexpr subst) pes in
      match (Sym.Map.find lab labels, vs) with
      | Return _, [ v ] -> ExprM.returned v
      | Return _, _ ->
          not_impl "Return label with multiple values: %a" Sym.pp_hum lab
      | Non_inlined _, _ -> not_impl "Non-inlined label: %a" Sym.pp_hum lab
      | Loop { loc = lloc; args; body; annots = _; info = _ }, vs -> (
          match Soteria_c_vendor.Config.current_mode () with
          | Whole_program ->
              (* Concrete execution: unroll. *)
              eval_expr ~labels subst body
          | Compositional -> (
              (* CN discipline: jumping to a loop label consumes the label's
                 argument type (the invariant, incl. the auto-generated
                 ownership of locals), requires the remaining footprint to be
                 empty, and ends the path. The label body is verified as a
                 separate obligation (see [Verify.verify_fn]). *)
              let@ () = with_loc ~loc:lloc in
              (* Extend (not replace) the current substitution: the invariant
                 may mention enclosing-scope variables (CN checks the spine in
                 the full typing context). *)
              let lsubst = Subst.from_args ~init:subst args vs in
              let* (), _lsubst = Cn_assert.consume_arguments args lsubst in
              let* state = get_state () in
              match SState.leaks state with
              | [] -> InterpM.ok ExprM.Jumped
              | _ :: _ ->
                  [%l.debug
                    "Resources left over at loop back-edge (invariant must \
                     capture the whole footprint)"];
                  error `Memory_leak)))
  | Eif { cond; then_; else_ } ->
      let* guard = eval_pexpr subst cond in
      let* () = State.unfold_on_if_else guard in
      let guard = Core_value.Bool.to_sbool guard in
      if%sat guard then eval_expr ~labels subst then_
      else eval_expr ~labels subst else_
  | Eccall { ty = _; fn; args; specs = _ } -> (
      let* fn = eval_pexpr subst fn in
      let* args = map_list ~f:(eval_pexpr subst) args in
      match fn with
      | Obj (Fn sym) | Loaded (Spec (Fn sym)) ->
          let+ v = eval_call ~loc:body.loc sym args in
          ExprM.Normal v
      | _ -> not_impl "Dynamic call %a" Core_value.pp fn)
  | Eaction action ->
      let+ v = eval_action subst action in
      ExprM.Normal v
  | Ememop (memop, args) ->
      let* args = map_list ~f:(eval_pexpr subst) args in
      let+ res = eval_memop memop args in
      ExprM.Normal res
  | Eskip -> ExprM.ok Core_value.Unit
  | CN_progs progs ->
      let+ () = Cn_prog.execute_cn_prog progs subst in
      ExprM.Normal Core_value.Unit
  | _ -> not_impl "Unsupported expr: %a" Mu.pp_expr body

and exec_fun (fn : Mu.fun_map_decl) params =
  [%l.debug "@[Executing function:@ %a@]" Mu.pp_fun_map_decl fn];

  match fn with
  | ProcDecl (loc, spec) -> (
      let@ () = with_loc ~loc in
      match spec with
      | None -> InterpM.error `No_spec
      | Some (args, ret) ->
          exec_spec ~subst:(Subst.from_args args params) args ret)
  | Proc { loc; args; body; labels; return_type; trusted = _ } -> (
      let subst = Subst.from_args args params in
      let@ () = with_loc ~loc in
      if Mu.has_spec args return_type then exec_spec ~subst args return_type
      else
        let+ v = eval_expr ~labels subst body in
        [%l.debug "Function returned: %a" (ExprM.pp_exec_r Core_value.pp) v];
        match v with
        | Normal _ -> Core_value.Unit
        | Returned v -> v
        | Jumped ->
            (* Only possible for a spec-less inlined callee containing a loop;
               CN requires a spec for such functions. *)
            L.failwith "Inlined call ended at a loop back-edge")
