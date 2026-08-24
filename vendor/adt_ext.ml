(* Algebraic-datatype value extension for the Soteria bitvector value language.
   Generic over the client: datatypes are registered by (string) name before
   verification starts; CN symbols are mangled by the client. *)

module Svalue = Soteria.Bv_values.Svalue
module Smt = Soteria.Smt
module Decls = Soteria.Solvers.Decls

(* ─────────────────────────── registry ─────────────────────────── *)

(** Sorts a datatype field may have; mirrors the client base types we support.
    Widths are supplied at registration time. *)
type sort_desc =
  | DBool
  | DBits of int
  | DPtr of int  (** pointer sort of the given bit width *)
  | DLoc of int
  | DAdt of string

type con_def = { con : string; fields : (string * sort_desc) list }
type adt_def = { adt : string; cons : con_def list }

type fun_def = { fn : string; arg_sorts : sort_desc list; ret_sort : sort_desc }

let registry : (string, adt_def) Hashtbl.t = Hashtbl.create 16
let fun_registry : (string, fun_def) Hashtbl.t = Hashtbl.create 16
let register (def : adt_def) = Hashtbl.replace registry def.adt def
let register_fun (def : fun_def) = Hashtbl.replace fun_registry def.fn def
let find_fun fn = Hashtbl.find_opt fun_registry fn

let reset () =
  Hashtbl.reset registry;
  Hashtbl.reset fun_registry

let find_def adt = Hashtbl.find_opt registry adt

let find_con adt con =
  match find_def adt with
  | None -> None
  | Some def -> List.find_opt (fun c -> String.equal c.con con) def.cons

let field_index adt con field =
  match find_con adt con with
  | None -> None
  | Some c ->
      List.find_index (fun (f, _) -> String.equal f field) c.fields

let field_sort adt con field =
  match find_con adt con with
  | None -> None
  | Some c ->
      List.find_map
        (fun (f, d) -> if String.equal f field then Some d else None)
        c.fields

let sel_name adt con field = Printf.sprintf "%s.%s.%s" adt con field

(* ─────────────────────── the value extension ─────────────────────── *)

type 'g t =
  | Constr of {
      adt : string;
      con : string;
      args : ('g, 'g t, 'g ty) Svalue.t list;
    }
  | Tester of { con : string; v : ('g, 'g t, 'g ty) Svalue.t }
  | Sel of {
      adt : string;
      con : string;
      field : string;
      v : ('g, 'g t, 'g ty) Svalue.t;
    }

  | App of { fn : string; args : ('g, 'g t, 'g ty) Svalue.t list }

and 'g ty = TAdt of string

let equal_ty _ (TAdt a) (TAdt b) = String.equal a b
let compare_ty _ (TAdt a) (TAdt b) = String.compare a b
let hash_ty (TAdt a) = Hashtbl.hash a
let pp_ty ft (TAdt a) = Fmt.string ft a
let tag (sv : _ Svalue.t) = sv.Hc.tag

let equal _ x y =
  match (x, y) with
  | Constr a, Constr b ->
      String.equal a.adt b.adt && String.equal a.con b.con
      && List.equal (fun l r -> Int.equal (tag l) (tag r)) a.args b.args
  | Tester a, Tester b ->
      String.equal a.con b.con && Int.equal (tag a.v) (tag b.v)
  | Sel a, Sel b ->
      String.equal a.adt b.adt && String.equal a.con b.con
      && String.equal a.field b.field
      && Int.equal (tag a.v) (tag b.v)
  | App a, App b ->
      String.equal a.fn b.fn
      && List.equal (fun l r -> Int.equal (tag l) (tag r)) a.args b.args
  | _ -> false

let compare _ x y =
  let int_of = function Constr _ -> 0 | Tester _ -> 1 | Sel _ -> 2 | App _ -> 3 in
  match (x, y) with
  | Constr a, Constr b ->
      let c = String.compare a.adt b.adt in
      if c <> 0 then c
      else
        let c = String.compare a.con b.con in
        if c <> 0 then c
        else List.compare (fun l r -> Int.compare (tag l) (tag r)) a.args b.args
  | Tester a, Tester b ->
      let c = String.compare a.con b.con in
      if c <> 0 then c else Int.compare (tag a.v) (tag b.v)
  | Sel a, Sel b ->
      let c = String.compare a.adt b.adt in
      if c <> 0 then c
      else
        let c = String.compare a.con b.con in
        if c <> 0 then c
        else
          let c = String.compare a.field b.field in
          if c <> 0 then c else Int.compare (tag a.v) (tag b.v)
  | App a, App b ->
      let c = String.compare a.fn b.fn in
      if c <> 0 then c
      else List.compare (fun l r -> Int.compare (tag l) (tag r)) a.args b.args
  | _ -> Int.compare (int_of x) (int_of y)

let hash x =
  match x with
  | Constr { adt; con; args } ->
      Hashtbl.hash (0, adt, con, List.map tag args)
  | Tester { con; v } -> Hashtbl.hash (1, con, tag v)
  | Sel { adt; con; field; v } -> Hashtbl.hash (2, adt, con, field, tag v)
  | App { fn; args } -> Hashtbl.hash (3, fn, List.map tag args)

let pp pp_super ft x =
  match x with
  | Constr { con; args; _ } ->
      Fmt.pf ft "@[<2>%s(%a)@]" con (Fmt.list ~sep:Fmt.comma pp_super) args
  | Tester { con; v } -> Fmt.pf ft "@[<2>(is %s@ %a)@]" con pp_super v
  | Sel { con; field; v; _ } ->
      Fmt.pf ft "@[<2>%a.%s.%s@]" pp_super v con field
  | App { fn; args } ->
      Fmt.pf ft "@[<2>%s(%a)@]" fn (Fmt.list ~sep:Fmt.comma pp_super) args

let iter_vars f x =
  match x with
  | Constr { args; _ } | App { args; _ } -> List.iter f args
  | Tester { v; _ } | Sel { v; _ } -> f v

(** Smart constructor: selector-of-constructor projects; tester-of-constructor
    concretises. *)
let mk build ty x =
  match x with
  | Sel { adt; con; field; v } -> (
      match v.Hc.node.Svalue.kind with
      | Svalue.Extension (Constr { con = con'; args; _ })
        when String.equal con con' -> (
          match field_index adt con field with
          | Some i -> List.nth args i
          | None -> build (Svalue.Extension x) ty)
      | _ -> build (Svalue.Extension x) ty)
  | Tester { con; v } -> (
      match v.Hc.node.Svalue.kind with
      | Svalue.Extension (Constr { con = con'; _ }) ->
          build (Svalue.Bool (String.equal con con')) Svalue.TBool
      | _ -> build (Svalue.Extension x) ty)
  | Constr _ | App _ -> build (Svalue.Extension x) ty

let eval f x =
  let map_args args =
    List.fold_left
      (fun (acc, ch) a ->
        let a' = f a in
        (a' :: acc, ch || a' != a))
      ([], false) args
  in
  match x with
  | Constr c ->
      let args, changed = map_args c.args in
      if changed then Constr { c with args = List.rev args } else x
  | App a ->
      let args, changed = map_args a.args in
      if changed then App { a with args = List.rev args } else x
  | Tester t ->
      let v = f t.v in
      if v == t.v then x else Tester { t with v }
  | Sel s ->
      let v = f s.v in
      if v == s.v then x else Sel { s with v }

let apply_subst sub ~missing_var st x =
  let sub_args st args =
    let st, rev_args =
      List.fold_left
        (fun (st, acc) a ->
          let a, st = sub ~missing_var st a in
          (st, a :: acc))
        (st, []) args
    in
    (st, List.rev rev_args)
  in
  match x with
  | Constr c ->
      let st, args = sub_args st c.args in
      (Constr { c with args }, st)
  | App a ->
      let st, args = sub_args st a.args in
      (App { a with args }, st)
  | Tester t ->
      let v, st = sub ~missing_var st t.v in
      (Tester { t with v }, st)
  | Sel s ->
      let v, st = sub ~missing_var st s.v in
      (Sel { s with v }, st)

(* ─────────────────────────── SMT encoding ─────────────────────────── *)

let adts_key = "cn-adt-datatypes"

(** All registered datatypes, declared as a single (mutually recursive)
    [declare-datatypes] group; sidesteps SCC ordering. *)
let declare_group (enc_sort : sort_desc -> Smt.sexp) : Smt.sexp =
  let defs =
    Hashtbl.fold (fun _ d acc -> d :: acc) registry []
    |> List.sort (fun a b -> String.compare a.adt b.adt)
  in
  let sort_decl d = Smt.List [ Smt.Atom d.adt; Smt.Atom "0" ] in
  let con_decl adt (c : con_def) =
    Smt.List
      (Smt.Atom c.con
      :: List.map
           (fun (f, desc) ->
             Smt.List [ Smt.Atom (sel_name adt c.con f); enc_sort desc ])
           c.fields)
  in
  let per_adt d = Smt.List (List.map (con_decl d.adt) d.cons) in
  Smt.List
    [
      Smt.Atom "declare-datatypes";
      Smt.List (List.map sort_decl defs);
      Smt.List (List.map per_adt defs);
    ]

let enc_sort_with (enc : 'g ty Svalue.ty -> Smt.sexp) : sort_desc -> Smt.sexp =
  function
  | DBool -> enc Svalue.TBool
  | DBits n -> enc (Svalue.TBitVector n)
  | DPtr n -> enc (Svalue.TPointer n)
  | DLoc n -> enc (Svalue.TLoc n)
  | DAdt s -> Smt.Atom s

(* The datatype group must be declared before ANY use of an ADT sort or
   constructor/selector/tester/function symbol — including ground terms whose
   sorts never go through [encode_ty] (no ADT-sorted variable in the query). *)
let declare_adts (enc : 'g ty Svalue.ty -> Smt.sexp) : unit =
  if Hashtbl.length registry > 0 then
    Decls.declare ~key:adts_key (fun yield ->
        yield (declare_group (enc_sort_with enc)))

let encode_ty (enc : 'g ty Svalue.ty -> Smt.sexp) (TAdt name : 'g ty) :
    Smt.sexp =
  declare_adts enc;
  Smt.Atom name

let encode_value (enc_ty : 'g ty Svalue.ty -> Smt.sexp)
    (enc : ('g, 'g t, 'g ty) Svalue.t -> Smt.sexp) ~ty:_ (x : 'g t) : Smt.sexp
    =
  let open Smt in
  declare_adts enc_ty;
  match x with
  | Constr { con; args; _ } -> app_ con (List.map enc args)
  | Tester { con; v } -> app (fam "is" [ Atom con ]) [ enc v ]
  | Sel { adt; con; field; v } -> app_ (sel_name adt con field) [ enc v ]
  | App { fn; args } ->
      (match find_fun fn with
      | Some { arg_sorts; ret_sort; _ } ->
          let enc_sort = enc_sort_with enc_ty in
          Decls.declare ~key:("cn-fun-" ^ fn) (fun yield ->
              yield
                (declare_fun fn (List.map enc_sort arg_sorts)
                   (enc_sort ret_sort)))
      | None -> ());
      app_ fn (List.map enc args)
