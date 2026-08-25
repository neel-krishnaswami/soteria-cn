open Soteria_c_vendor
open Soteria.Logs.Import
open Soteria.Soteria_std
open Typed
module Sym = Symbol_std
module Ctype = Cerb_frontend.Ctype
module Impl_mem = Cerb_frontend.Impl_mem
module Svalue = Soteria.Bv_values.Svalue
module Mu = Usable_mucore
module Id = Cn.Id

type 'a or_unspec = Spec of 'a | Unspec

type obj =
  | Int of T.sint Typed.t
  | Float of T.sfloat Typed.t
  | Ptr of T.sptr Typed.t
  | Array of obj or_unspec list
  | Struct of { tag : Sym.t; members : obj or_unspec list }
  | Fn of Sym.t

type t =
  | Obj of obj
  | Loaded of obj or_unspec
  | Type of Ctype.ctype
  | Unit
  | List of t list
  | Tuple of t list
  | Record of (Id.t * t) list
  | Bool of T.sbool Typed.t
  | Adt of Typed.T_adt.sadt Typed.t
  | Map of Typed.T_map.smap Typed.t

(* A specified value prints as [Spec(...)] and an unspecified one as [Unspec],
   so that a [Loaded] value stays distinguishable from a raw [Obj]. *)
let pp_or_unspec pp_elt ft = function
  | Spec a -> Fmt.pf ft "Spec(%a)" pp_elt a
  | Unspec -> Fmt.string ft "Unspec"

let rec pp_obj ft (o : obj) =
  let pp_members = Fmt.(list ~sep:semi (pp_or_unspec pp_obj)) in
  match o with
  | Int i -> Typed.ppa ft i
  | Float f -> Typed.ppa ft f
  | Ptr p -> Typed.ppa ft p
  | Array elems -> Fmt.pf ft "@[<hov 2>[%a]@]" pp_members elems
  | Struct { tag; members } ->
      Fmt.pf ft "@[<hov 2>%a {%a}@]" Sym.pp_hum tag pp_members members
  | Fn sym -> Fmt.pf ft "&%a" Sym.pp_hum sym

let rec pp ft (v : t) =
  match v with
  | Obj o -> pp_obj ft o
  | Loaded l -> pp_or_unspec pp_obj ft l
  | Type ct -> Fmt_ail.pp_ty ft ct
  | Unit -> Fmt.string ft "()"
  | List vs -> Fmt.pf ft "@[<hov 2>[%a]@]" Fmt.(list ~sep:semi pp) vs
  | Tuple vs -> Fmt.pf ft "@[<hov 1>(%a)@]" Fmt.(list ~sep:comma pp) vs
  | Record fields ->
      let pp_field ft (id, v) = Fmt.pf ft "%a: %a" Fmt_ail.pp_id id pp v in
      Fmt.pf ft "@[<hov 2>{%a}@]" Fmt.(list ~sep:semi pp_field) fields
  | Bool b -> Typed.ppa ft b
  | Adt v -> Typed.ppa ft v
  | Map v -> Typed.ppa ft v

let show = Fmt.to_to_string pp
let true_ = Bool Typed.v_true
let false_ = Bool Typed.v_false

(* Width (in bits) of a Cerberus integer type. *)
let bits_of_ity ity =
  match Layout.size_of_int_ty ity with
  | Some bytes -> 8 * bytes
  | None -> L.failwith "Core_value: integer type of unknown size"

(* [iv] is masked to [bits], so a (two's complement) negative value is kept as
   its bit pattern. *)
let int_of_ival ~bits iv : T.sint Typed.t =
  Impl_mem.case_integer_value iv
    (fun z -> Typed.BitVec.mk_masked bits z)
    (fun () -> L.failwith "Core_value: unspecified integer value")

let float_of_fval fv : T.sfloat Typed.t =
  Impl_mem.case_fval fv
    (fun () -> L.failwith "Core_value: unspecified float value")
    (fun f -> Typed.Float.f64 f)

let ptr_of_ptr_value ptr : obj =
  Impl_mem.case_ptrval ptr
    (* Null *)
    (fun _ -> Ptr Typed.Ptr.null) (* Funptr *)
    (function
      | Some sym -> Fn sym
      | None -> L.failwith "Core_value: unspecified pointer value")
    (* Loc *)
    (fun _ ->
      L.failwith
        "Core_value: pointer values with known location are not supported")

(* A struct member is stored as a [mem_value], which may be unspecified, hence
   [obj or_unspec]. *)
let rec obj_of_mem mv : obj or_unspec =
  Impl_mem.case_mem_value mv
    (fun _ct -> Unspec)
    (fun _ity _sym -> L.failwith "Core_value: concurrency-read mem value")
    (fun ity iv -> Spec (Int (int_of_ival ~bits:(bits_of_ity ity) iv)))
    (fun _fty fv -> Spec (Float (float_of_fval fv)))
    (fun _ct ptr -> Spec (ptr_of_ptr_value ptr))
    (fun mvs -> Spec (Array (List.map obj_of_mem mvs)))
    (fun tag members ->
      let members = List.map (fun (_, _, mv) -> obj_of_mem mv) members in
      Spec (Struct { tag; members }))
    (fun _tag _id _mv -> L.failwith "Core_value: union mem value")

(* [OVinteger] carries no type, so its width defaults to [int]. *)
let rec obj_of_mu (ov : Mu.object_value) : obj =
  let open Mu in
  match ov with
  | OVinteger iv -> Int (int_of_ival ~bits:Typed.c_int_bits iv)
  | OVfloating fv -> Float (float_of_fval fv)
  | OVarray lvs -> Array (List.map loaded_of_mu lvs)
  | OVstruct { tag; members } ->
      let members = List.map (fun (_, _, mv) -> obj_of_mem mv) members in
      Struct { tag; members }
  | OVpointer ptr -> ptr_of_ptr_value ptr
  | OVunion _ -> L.failwith "obj_of_mu: union values are not supported"

and loaded_of_mu (lv : Mu.loaded_value) : obj or_unspec =
  let open Mu in
  match lv with
  | LVspecified ov -> Spec (obj_of_mu ov)
  | LVunspecified _ -> Unspec

let rec of_mu (v : Mu.value) : t =
  let open Mu in
  match v with
  | Vobject ov -> Obj (obj_of_mu ov)
  | Vctype ct -> Type ct
  | Vunit -> Unit
  | Vtrue -> true_
  | Vfalse -> false_
  | Vtuple vs -> Tuple (List.map of_mu vs)
  | Vlist (_, vs) -> List (List.map of_mu vs)
  | Vloaded lv -> Loaded (loaded_of_mu lv)

let rec nondet_bt (bt : Cn.BaseTypes.t) : t Csymex.t =
  let open Csymex.Syntax in
  match bt with
  | Unit -> Csymex.return Unit
  | Bool ->
      let+ b = Csymex.nondet Typed.t_bool in
      Bool b
  | Bits (_sign, size_bits) ->
      let+ v = Csymex.nondet (Typed.t_int size_bits) in
      Loaded (Spec (Int v))
  | Loc _ ->
      let* loc = Csymex.nondet Typed.t_loc in
      let+ ofs = Csymex.nondet Typed.t_usize in
      let ptr = Typed.Ptr.mk loc ofs in
      Loaded (Spec (Ptr ptr))
  | Record fields ->
      let+ members =
        Csymex.map_list
          ~f:(fun (id, bt) ->
            let+ v = nondet_bt bt in
            (id, v))
          fields
      in
      Record members
  | Datatype sym ->
      let+ v =
        Csymex.nondet (Typed.t_adt (Soteria_c_helpers.Adt.adt_name sym))
      in
      Adt v
  | Map (kbt, vbt) -> (
      match
        ( Soteria_c_helpers.Adt.desc_of_bt kbt,
          Soteria_c_helpers.Adt.desc_of_bt vbt )
      with
      | Some k, Some v ->
          let+ m = Csymex.nondet (Typed.t_map k v) in
          Map m
      | _ ->
          Fmt.kstr Soteria_c_helpers.not_impl "nondet_bt: unsupported map %a"
            Mu.pp_bt bt)
  | Struct sym ->
      let prog = Ctx.get_prog () in
      let layout =
        match Symbol_std.Map.find sym prog.tag_defs with
        | StructDef layout -> layout
        | _ ->
            L.failwith "nondet_bt: expected struct definition for %a" Sym.pp_hum
              sym
      in
      let+ values =
        Csymex.map_list
          ~f:(fun { member_or_padding; _ } ->
            match member_or_padding with
            | None -> Csymex.return None
            | Some (_id, ty) -> (
                let bt = Cn.Memory.bt_of_sct ty in
                let+ v = nondet_bt bt in
                match v with
                | Loaded x -> Some x
                | Obj x -> Some (Spec x)
                | _ -> L.failwith "nondet_bt: expected loaded or obj value"))
          layout
      in
      let values = List.filter_map Fun.id values in
      Loaded (Spec (Struct { tag = sym; members = values }))
  | _ -> Fmt.kstr Soteria_c_helpers.not_impl "nondet_bt: %a" Mu.pp_bt bt

let struct_field (v : t) (memb : Cerb_frontend.Symbol.identifier) :
    obj or_unspec option =
  let open Syntaxes.Option in
  let* tag, members =
    match v with
    | Obj (Struct { tag; members }) | Loaded (Spec (Struct { tag; members })) ->
        Some (tag, members)
    | _ -> None
  in
  let tag_def = Symbol_std.Map.find tag (Ctx.get_prog ()).tag_defs in
  let struct_def =
    match tag_def with
    | StructDef layout -> layout
    | _ -> L.failwith "struct_field: not a struct"
  in
  let rec find struct_def members =
    match (struct_def, members) with
    | [], [] -> None
    | Cn.Memory.{ member_or_padding = None; _ } :: rest_def, members ->
        find rest_def members
    | { member_or_padding = Some (id, _); _ } :: _, member :: _
      when Cerb_frontend.Symbol.idEqual memb id ->
        Some member
    | _ :: rest_def, _ :: rest_members -> find rest_def rest_members
    | _ -> L.failwith "Invalid structure definition for %a" Sym.pp_hum tag
  in
  find struct_def members

(* A scalar [obj] coerces to a [Basic] aggregate value; arrays and structs map
   to their aggregate counterparts. Function values have no runtime
   representation. *)
let rec obj_to_agv (o : obj) : Aggregate_val.t =
  match o with
  | Int i -> Aggregate_val.Basic (i :> T.cval Typed.t)
  | Float f -> Aggregate_val.Basic (f :> T.cval Typed.t)
  | Ptr p -> Aggregate_val.Basic (p :> T.cval Typed.t)
  | Array objs -> Aggregate_val.Array (List.map loaded_to_agv objs)
  | Struct { members; _ } ->
      Aggregate_val.Struct (List.map loaded_to_agv members)
  | Fn _ ->
      L.failwith
        "Core_value.to_agv: function value is not an aggregate value: %a" pp_obj
        o

and loaded_to_agv (o : obj or_unspec) : Aggregate_val.t =
  match o with
  | Spec o -> obj_to_agv o
  | Unspec ->
      L.failwith
        "Core_value.to_agv: unspecified value is not an aggregate value"

let to_agv (v : t) : Aggregate_val.t =
  match v with
  | Obj o -> obj_to_agv o
  | Loaded o -> loaded_to_agv o
  | Type _ | Unit | List _ | Tuple _ | Bool _ | Record _ | Adt _ | Map _ ->
      L.failwith "Core_value.to_agv: not an aggregate value: %a" pp v

(* The runtime type of a [Basic] aggregate value tells us which scalar [obj] it
   denotes. *)
let obj_of_cval (v : T.cval Typed.t) : obj =
  match Typed.get_ty v with
  | Svalue.TBitVector _ -> Int (Typed.cast v)
  | Svalue.TPointer _ -> Ptr (Typed.cast v)
  | Svalue.TFloat _ -> Float (Typed.cast v)
  | ty ->
      L.failwith "Core_value.of_agv: unexpected basic value type: %a"
        Typed.Svalue.pp_ty ty

(* Aggregate values carry neither array element types nor struct tags/field
   types, so the expected C type [ty] is needed to rebuild them. *)
let rec obj_of_agv ~(ty : Ctype.ctype) (agv : Aggregate_val.t) : obj =
  match agv with
  | Aggregate_val.Basic v -> obj_of_cval v
  | Aggregate_val.Array elems ->
      let elem_ty =
        match Layout.get_array_info ty with
        | Some (elem_ty, _) -> elem_ty
        | None ->
            L.failwith "Core_value.of_agv: array value for non-array type: %a"
              Fmt_ail.pp_ty ty
      in
      Array (List.map (fun e -> Spec (obj_of_agv ~ty:elem_ty e)) elems)
  | Aggregate_val.Struct fields ->
      let tag =
        match Ctype.proj_ctype_ ty with
        | Ctype.Struct tag -> tag
        | _ ->
            L.failwith "Core_value.of_agv: struct value for non-struct type: %a"
              Fmt_ail.pp_ty ty
      in
      let field_tys =
        match Layout.get_struct_fields_ty ty with
        | Some (fs, _fam) -> List.map (fun (_, (_, _, _, fty)) -> fty) fs
        | None ->
            L.failwith "Core_value.of_agv: unknown struct definition: %a"
              Fmt_ail.pp_ty ty
      in
      let members =
        try
          List.map2 (fun fty f -> Spec (obj_of_agv ~ty:fty f)) field_tys fields
        with Invalid_argument _ ->
          L.failwith
            "Core_value.of_agv: struct value has %d fields but type %a expects \
             %d"
            (List.length fields) Fmt_ail.pp_ty ty (List.length field_tys)
      in
      Struct { tag; members }

(* A load yields a (specified) loaded value. *)
let of_agv ~(ty : Ctype.ctype) (agv : Aggregate_val.t) : t =
  Loaded (Spec (obj_of_agv ~ty agv))

let cast_int (v : t) : T.sint Typed.t option =
  match v with Obj (Int i) | Loaded (Spec (Int i)) -> Some i | _ -> None

let cast_type (v : t) : Ctype.ctype option =
  match v with Type ct -> Some ct | _ -> None

let cast_ptr (v : t) : T.sptr Typed.t option =
  match v with Obj (Ptr p) | Loaded (Spec (Ptr p)) -> Some p | _ -> None

let cast_bool (v : t) : T.sbool Typed.t option =
  match v with Bool b -> Some b | _ -> None

let cast_adt (v : t) : Typed.T_adt.sadt Typed.t option =
  match v with Adt a -> Some a | _ -> None

let cast_map (v : t) : Typed.T_map.smap Typed.t option =
  match v with Map m -> Some m | _ -> None

let c_int (i : int) : t =
  Obj (Int (Typed.BitVec.mk_masked Typed.c_int_bits (Z.of_int i)))

let c_int_of_bool b = if b then c_int 1 else c_int 0

let lt ~signed lhs rhs =
  match (lhs, rhs) with
  | ( (Obj (Int i1) | Loaded (Spec (Int i1))),
      (Obj (Int i2) | Loaded (Spec (Int i2))) ) ->
      Bool (Typed.BitVec.lt ~signed i1 i2)
  | ( (Obj (Float f1) | Loaded (Spec (Float f1))),
      (Obj (Float f2) | Loaded (Spec (Float f2))) ) ->
      Bool (Typed.Float.lt f1 f2)
  | _ -> L.failwith "Core_value.lt: not comparable: %a, %a" pp lhs pp rhs

let leq ~signed lhs rhs =
  match (lhs, rhs) with
  | ( (Obj (Int i1) | Loaded (Spec (Int i1))),
      (Obj (Int i2) | Loaded (Spec (Int i2))) ) ->
      Bool (Typed.BitVec.leq ~signed i1 i2)
  | ( (Obj (Float f1) | Loaded (Spec (Float f1))),
      (Obj (Float f2) | Loaded (Spec (Float f2))) ) ->
      Bool (Typed.Float.leq f1 f2)
  | _ -> L.failwith "Core_value.lt: not comparable: %a, %a" pp lhs pp rhs

module Bool = struct
  let not b =
    match b with
    | Bool b -> Bool (Typed.Bool.not b)
    | _ -> L.failwith "not: not a boolean %a" pp b

  let and_ b1 b2 =
    match (b1, b2) with
    | Bool b1, Bool b2 -> Bool (Typed.Bool.and_ b1 b2)
    | _ -> L.failwith "and_: not booleans: %a, %a" pp b1 pp b2

  let of_bool b = Bool (Typed.Bool.of_bool b)

  let to_sbool v =
    match v with
    | Bool b -> b
    | _ ->
        L.failwith "Core_value.Bool.to_sbool: value is not a boolean: %a" pp v

  let or_ b1 b2 =
    match (b1, b2) with
    | Bool b1, Bool b2 -> Bool (Typed.Bool.or_ b1 b2)
    | _ -> L.failwith "or_: not booleans: %a, %a" pp b1 pp b2
end

let cfunction (fn_sig : Cn.Sctypes.c_concrete_sig) : t =
  (* Cerberus implementation: *)
  (* ATtuple
       [Vctype ret;
        Vlist BTy_ctype (List.map (fun (_, ty) -> Vctype ty) params);
        if is_variadic then Vtrue else Vfalse;
        if has_proto then Vtrue else Vfalse; ]
  *)
  Tuple
    [
      Type fn_sig.sig_return_ty;
      List (List.map (fun t -> Type t) fn_sig.sig_arg_tys);
      Bool.of_bool fn_sig.sig_variadic;
      Bool.of_bool fn_sig.sig_has_proto;
    ]

let sem_eq_or_unspec (sem_eq_a : 'a -> 'a -> T.sbool Typed.t)
    (v1 : 'a or_unspec) (v2 : 'a or_unspec) : T.sbool Typed.t =
  match (v1, v2) with
  | Spec a1, Spec a2 -> sem_eq_a a1 a2
  | Unspec, Unspec -> Typed.v_true
  | _ -> Typed.v_false

let rec sem_eq_obj o1 o2 =
  let open Typed.Infix in
  let sem_eq_ooul l1 l2 =
    try
      List.fold_left2
        (fun acc v1 v2 -> acc &&@ sem_eq_or_unspec sem_eq_obj v1 v2)
        Typed.v_true l1 l2
    with Invalid_argument _ -> Typed.v_false
  in
  match (o1, o2) with
  | Int i1, Int i2 -> i1 ==@ i2
  | Float f1, Float f2 -> f1 ==@ f2
  | Ptr p1, Ptr p2 -> p1 ==@ p2
  | Array a1, Array a2 -> sem_eq_ooul a1 a2
  | Struct { tag = t1; members = m1 }, Struct { tag = t2; members = m2 } ->
      let tag_eq = Typed.Bool.of_bool @@ Sym.equal t1 t2 in
      tag_eq &&@ sem_eq_ooul m1 m2
  | Fn s1, Fn s2 -> Typed.Bool.of_bool @@ Sym.equal s1 s2
  | _ -> Typed.v_false

let rec sem_eq v1 v2 =
  let open Typed.Infix in
  let sem_eq_list l1 l2 =
    try
      List.fold_left2 (fun acc v1 v2 -> acc &&@ sem_eq v1 v2) Typed.v_true l1 l2
    with Invalid_argument _ -> Typed.v_false
  in
  (* FIXME: I have no idea why I get Loaded (Spec _) and just Obj _ sometimes?
            I'll just assume that equality holds for these things for now... *)
  match (v1, v2) with
  | (Loaded (Spec o1) | Obj o1), (Loaded (Spec o2) | Obj o2) -> sem_eq_obj o1 o2
  | Type t1, Type t2 -> Typed.Bool.of_bool @@ Ctype.ctypeEqual t1 t2
  | Unit, Unit -> Typed.v_true
  | List l1, List l2 -> sem_eq_list l1 l2
  | Tuple t1, Tuple t2 -> sem_eq_list t1 t2
  | Bool b1, Bool b2 -> b1 ==@ b2
  | Adt a1, Adt a2 -> a1 ==@ a2
  | Map m1, Map m2 -> m1 ==@ m2
  | _ -> Typed.v_false

module Syntax = struct
  module Sym_int_syntax = struct
    open Typed.Syntax

    let zero = Obj (Int CInt.(0s))
    let one = Obj (Int CInt.(1s))
    let nonzero i = Obj (Int (CInt.Sym_int_syntax.mk_nonzero i))
  end
end

module Syn = struct
  (* We don't care about Syn stuff. Soteria shouldn't require this by default
  anymore.*)

  type syn = | [@@deriving show { with_path = false }]

  let to_syn (_ : t) : syn = L.failwith "Core_value.to_syn: not implemented"
  let fresh _ : t Csymex.t = L.failwith "Core_value.fresh: not implemented"
  let subst _ _ = L.failwith "Core_value.subst: not implemented"
  let learn_eq _ _ = L.failwith "Core_value.learn_eq: not implemented"
  let exprs_syn _ = L.failwith "Core_value.exprs_syn: not implemented"

  (* This is mostly where variable iteration belongs, but suddenly when it come to reason about heuristics, we must iterate over variables. *)
  let rec iter_vars_obj o f =
    let open Typed in
    match o with
    | Int i -> Svalue.iter_vars (Expr.of_value i) f
    | Float fs -> Svalue.iter_vars (Expr.of_value fs) f
    | Ptr p -> Svalue.iter_vars (Expr.of_value p) f
    | Array elems -> List.iter (fun e -> iter_vars_loaded e f) elems
    | Struct { members; _ } -> List.iter (fun m -> iter_vars_loaded m f) members
    | Fn _ -> ()

  and iter_vars_loaded o f =
    match o with Spec o -> iter_vars_obj o f | Unspec -> ()

  and iter_vars v f =
    match v with
    | Obj o -> iter_vars_obj o f
    | Loaded l -> iter_vars_loaded l f
    | List vs | Tuple vs -> List.iter (fun v -> iter_vars v f) vs
    | Record fields -> List.iter (fun (_, v) -> iter_vars v f) fields
    | Bool b -> Typed.Svalue.iter_vars (Typed.Expr.of_value b) f
    | Adt v -> Typed.Svalue.iter_vars (Typed.Expr.of_value v) f
    | Map v -> Typed.Svalue.iter_vars (Typed.Expr.of_value v) f
    | Type _ | Unit -> ()
end

include Syn
