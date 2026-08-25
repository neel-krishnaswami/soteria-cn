(* Vendored from soteria-tools/soteria soteria-c/lib (mainline 4e9182b; ctree_block/state_variants/csymex/symbol_std/layout from cn-main-merge 7b89176). *)
include Soteria.Bv_values.Typed.Make_transparent (Adt_ext) ()

let ptr_bits =
  Option.get Cerb_frontend.Ocaml_implementation.DefaultImpl.impl.sizeof_pointer
  * 8

let c_int_bits =
  Option.get
    (Cerb_frontend.Ocaml_implementation.DefaultImpl.impl.sizeof_ity
       (Signed Int_))
  * 8

(* Width of the embedding of Core's mathematical integers: one sign bit more
   than the widest C integer type, so every C integer value embeds
   order-preservingly (signed) and no conversion loses information. *)
let math_bits = ptr_bits + 1

let t_loc = t_loc ptr_bits
let t_ptr = t_ptr ptr_bits
let t_usize = t_int ptr_bits

module BitVec = struct
  include BitVec

  let of_bool x =
    let byte_size =
      Option.get
        (Cerb_frontend.Ocaml_implementation.DefaultImpl.impl.sizeof_ity
           (Signed Int_))
    in
    let bit_size = byte_size * 8 in
    of_bool bit_size x

  let usize z = mk ptr_bits z
  let usizenz z = mk_nz ptr_bits z
  let usizei i = mki ptr_bits i
  let usizeinz i = mki_nz ptr_bits i
  let isize_max = usize (Z.pred (Z.shift_left Z.one (ptr_bits - 1)))

  let sure_is_zero bv =
    match to_z bv with Some z -> Z.equal z Z.zero | None -> false

  let fit_to ?(signed = false) size (bv : [< T.sint ] t) : [> T.sint ] t =
    let cur = size_of_int bv in
    if cur = size then bv
    else if cur < size then extend ~signed (size - cur) bv
    else extract 0 (size - 1) bv

  let cast_to_size_t bv =
    Option.map (fun (v, _) -> fit_to ~signed:false ptr_bits v) (cast_int bv)
end

module Ptr = struct
  include Ptr

  let null = null ptr_bits
  let null_loc = null_loc ptr_bits
  let loc_of_z = loc_of_z ptr_bits
  let loc_of_int = loc_of_int ptr_bits
end

module Syntax = struct
  module U8 = struct
    module Sym_int_syntax = struct
      let mk_nonzero = BitVec.mki_nz 8
      let zero () = BitVec.zero 8
      let one () = BitVec.mki_nz 8 1
    end
  end

  module CInt = struct
    module Sym_int_syntax = struct
      let mk_nonzero = BitVec.mki_nz c_int_bits
      let zero () = BitVec.zero c_int_bits
      let one () = BitVec.mki_nz c_int_bits 1
    end
  end

  module Usize = struct
    module Sym_int_syntax = struct
      let mk_nonzero = BitVec.mki_nz ptr_bits
      let zero () = BitVec.zero ptr_bits
      let one () = BitVec.one ptr_bits
    end
  end
end

(* ───────────────────────── ADT extension glue ───────────────────────── *)

module T_adt = struct
  type sadt = [ `Adt ]
end

let t_adt name : [> T_adt.sadt ] ty =
  Soteria.Bv_values.Svalue.TExtension (Adt_ext.TAdt name)

let mk_adt ty x : 'a t = Adt_ext.mk (fun k t -> Svalue.(k <| t)) ty x

let adt_constr ~adt ~con (args : Svalue.t list) : [> T_adt.sadt ] t =
  mk_adt (t_adt adt) (Adt_ext.Constr { adt; con; args })

let adt_tester ~con (v : [> T_adt.sadt ] t) : T.sbool t =
  mk_adt Soteria.Bv_values.Svalue.TBool (Adt_ext.Tester { con; v })

let adt_sel ~adt ~con ~field ~(field_ty : 'b ty) (v : [> T_adt.sadt ] t) : 'b t
    =
  mk_adt field_ty (Adt_ext.Sel { adt; con; field; v })

let fn_app ~fn ~(ret_ty : 'a ty) (args : Svalue.t list) : 'a t =
  mk_adt ret_ty (Adt_ext.App { fn; args })

module T_map = struct
  type smap = [ `Map ]
end

let t_map k v : [> T_map.smap ] ty =
  Soteria.Bv_values.Svalue.TExtension (Adt_ext.TMap (k, v))

(* [value_ty] is the sort of the map's values (result of a get); descs give
   the map's own sort. *)
let map_get ~(value_ty : 'a ty) (m : [> T_map.smap ] t) (k : Svalue.t) : 'a t =
  mk_adt value_ty (Adt_ext.MapGet { m; k })

let map_set ~key ~value (m : [> T_map.smap ] t) (k : Svalue.t) (v : Svalue.t) :
    [> T_map.smap ] t =
  mk_adt (t_map key value) (Adt_ext.MapSet { m; k; v })

let map_const ~key ~value (v : Svalue.t) : [> T_map.smap ] t =
  mk_adt (t_map key value) (Adt_ext.MapConst { key; value; v })

let map_default ~key ~value : [> T_map.smap ] t =
  mk_adt (t_map key value) (Adt_ext.MapDefault (key, value))
