open Soteria_c_vendor
open Soteria.Logs.Import

type _ Effect.t +=
  | Get_prog : Usable_mucore.file Effect.t
  | Get_pred_def : Symbol_std.t -> Usable_mucore.predicate_def Effect.t
  | Get_fun_def : Symbol_std.t -> Cn.Definition.Function.t option Effect.t
  | Get_lemma :
      Symbol_std.t
      -> (Cn.Locations.t * (Usable_mucore.arguments * Usable_mucore.logical_return))
         option
         Effect.t

let get_prog () = Effect.perform Get_prog
let get_pred_def name = Effect.perform (Get_pred_def name)
let get_fun_def name = Effect.perform (Get_fun_def name)
let get_lemma name = Effect.perform (Get_lemma name)

let cn_to_ctype_def (def : Usable_mucore.tag_definition) :
    Soteria_c_vendor.Layout.Tag_defs.def =
  let module CF = Cerb_frontend in
  (* CN does not keep track of the source location of tag definitions. *)
  let loc = Cerb_location.unknown in
  (* Turn a CN [struct_piece] into the cerberus member representation, dropping
     padding pieces. The attributes/alignment/qualifiers are not preserved by
     CN, so we use the defaults; the member [ctype]s are enough to recompute
     the layout downstream. *)
  let member_of_piece ({ member_or_padding; _ } : Cn.Memory.struct_piece) =
    Option.map
      (fun (id, sct) ->
        ( id,
          ( CF.Annot.no_attributes,
            None,
            CF.Ctype.no_qualifiers,
            Cn.Sctypes.to_ctype sct ) ))
      member_or_padding
  in
  let tag_def : CF.Ctype.tag_definition =
    match def with
    | Usable_mucore.StructDef layout ->
        (* CN does not record flexible array members separately. *)
        CF.Ctype.StructDef (List.filter_map member_of_piece layout, None)
    | Usable_mucore.UnionDef ->
        (* CN's mucore drops union member information entirely. *)
        L.failwith "CN does not preserve union member information"
  in
  (loc, tag_def)

(** TODO: optimise hash function for Symbol_std. *)

let add_umu_defs (umu : Usable_mucore.file) tbl : unit =
  let open Soteria_c_vendor.Layout.Tag_defs in
  Symbol_std.Map.fold
    (fun id def _ -> Hashtbl.add tbl id (cn_to_ctype_def def))
    umu.tag_defs ()

let add_pred_defs (umu : Usable_mucore.file) tbl : unit =
  let open Cn.Definition.Predicate in
  List.iter (fun (sym, def) -> Hashtbl.add tbl sym def) umu.resource_predicates

let add_fun_defs (umu : Usable_mucore.file) tbl : unit =
  List.iter (fun (sym, def) -> Hashtbl.add tbl sym def) umu.logical_predicates

let add_lemmas (umu : Usable_mucore.file) tbl : unit =
  List.iter (fun (sym, l) -> Hashtbl.add tbl sym l) umu.lemmata

let run_with_prog (prog : Usable_mucore.file) f =
  let open Effect.Deep in
  let open Layout.Tag_defs in
  let tag_defs = Hashtbl.create 1020 in
  let layouts = Hashtbl.create 1020 in
  let pred_defs = Hashtbl.create 64 in
  let fun_defs = Hashtbl.create 64 in
  let lemmas = Hashtbl.create 16 in
  add_pred_defs prog pred_defs;
  add_fun_defs prog fun_defs;
  add_lemmas prog lemmas;
  add_umu_defs prog tag_defs;
  Soteria_c_helpers.Adt.register_datatypes prog.datatypes
    ~cases:(fun (d : Usable_mucore.datatype) -> d.cases);
  Soteria_c_helpers.Adt.register_functions prog.logical_predicates;
  try f () with
  | effect Get_prog, k -> Effect.Deep.continue k prog
  | effect Get_pred_def name, k -> continue k (Hashtbl.find pred_defs name)
  | effect Get_fun_def name, k -> continue k (Hashtbl.find_opt fun_defs name)
  | effect Get_lemma name, k -> continue k (Hashtbl.find_opt lemmas name)
  | effect Find_tag id, k -> continue k (Hashtbl.find_opt tag_defs id)
  | effect Find_layout_cache ty, k -> continue k (Hashtbl.find_opt layouts ty)
  | effect Add_layout_cache (ty, l), k ->
      continue k (Hashtbl.replace layouts ty l)
