(** A sane, OCaml-idiomatic re-implementation of CN's [Cn.Mucore] AST. *)

module CF = Cerb_frontend
module Sym = Soteria_c_vendor.Symbol_std
(* = Cerb_frontend.Symbol.sym, with Map/Set/pp *)

module Locations = Cn.Locations
module IndexTerms = Cn.IndexTerms
module BaseTypes = Cn.BaseTypes
module LogicalConstraints = Cn.LogicalConstraints
module Sctypes = Cn.Sctypes
module ReturnTypes = Cn.ReturnTypes
module LogicalReturnTypes = Cn.LogicalReturnTypes
module ArgumentTypes = Cn.ArgumentTypes
module LogicalArgumentTypes = Cn.LogicalArgumentTypes
module Definition = Cn.Definition
module Cnprog = Cn.Cnprog
module Cnstatement = Cn.Cnstatement
module Memory = Cn.Memory
module Id = Cn.Id

type ctor = CF.Core.ctor
type integer_type = CF.Ctype.integerType
type iop = CF.Core.iop
type memory_order = CF.Cmm_csem.memory_order
type linux_memory_order = CF.Linux.linux_memory_order

(* ──────────────────── resource requests ([Cn.Request]) ──────────────────── *)

(** CN's [Cn.Request], re-owned as part of the AST. As with {!predicate_def},
    the pointer a (non-quantified) predicate request is about is folded into the
    head of [iargs] rather than kept in a separate field. The translation from
    [Cn.Request] lives in {!Of_mucore.request}. *)
module Request = struct
  (* Bridge from Cerberus' PPrint leaf printers; mirrors the top-level [pp_pp]. *)
  let pprint pp ft x = Fmt.string ft (Cn.Pp.plain (pp x))
  let pp_it = pprint IndexTerms.pp
  let pp_sct = pprint Sctypes.pp

  type init = Init | Uninit

  module Predicate = struct
    type t = { name : Sym.t; iargs : IndexTerms.t list }
    (** A user-defined predicate request; [iargs] leads with the pointer. *)
  end

  module QPredicate = struct
    type name = QOwned of Sctypes.t * init | QPName of Sym.t

    type t = {
      name : name;
      pointer : IndexTerms.t;
      q : Sym.t * BaseTypes.t;  (** the bound index variable *)
      step : Sctypes.t;  (** element stride, as a C type *)
      permission : IndexTerms.t;  (** guard over the index variable *)
      iargs : IndexTerms.t list;
    }
  end

  (* [Owned] points-to resources are their own request kind, with the pointer
     and pointee type explicit, rather than an [Owned] resource name whose
     pointer is smuggled in as a lone argument. *)
  type t =
    | Owned of { ty : Sctypes.t; kind : init; ptr : IndexTerms.t }
    | P of Predicate.t
    | Q of QPredicate.t

  let pp_kind ft = function
    | Init -> Fmt.string ft "RW"
    | Uninit -> Fmt.string ft "W"

  let pp_psym ~no_nums = if no_nums then Sym.pp else Sym.pp_hum

  let pp_predicate ?(no_nums = false) ft (p : Predicate.t) =
    Fmt.pf ft "@[<2>%a(%a)@]" (pp_psym ~no_nums) p.name
      Fmt.(list ~sep:comma pp_it)
      p.iargs

  let pp_qname ft = function
    | QPredicate.QOwned (ty, Init) -> Fmt.pf ft "RW<%a>" pp_sct ty
    | QPredicate.QOwned (ty, Uninit) -> Fmt.pf ft "W<%a>" pp_sct ty
    | QPredicate.QPName s -> Sym.pp_hum ft s

  let pp ?no_nums ft = function
    | Owned { ty; kind; ptr } ->
        Fmt.pf ft "@[<2>%a<%a>(%a)@]" pp_kind kind pp_sct ty pp_it ptr
    | P p -> pp_predicate ?no_nums ft p
    | Q (q : QPredicate.t) ->
        Fmt.pf ft "@[<2>each (%a; %a)@ %a(%a + %a * step)@]" Sym.pp_hum
          (fst q.q) pp_it q.permission pp_qname q.name pp_it q.pointer
          Sym.pp_hum (fst q.q)
end

(* ───────────────────────────── AST ───────────────────────────── *)

type 'a located = { loc : Locations.t; annots : CF.Annot.annot list; node : 'a }
(** A node decorated with its source location and annotations. One parametric
    record reused by {!act}, {!pattern}, {!pexpr} and {!expr}. *)

type act = Sctypes.t located
(** The old [act] record [{ loc; annot; ct }] is just a located [Sctypes.t]. *)

type object_value =
  | OVinteger of CF.Impl_mem.integer_value
  | OVfloating of CF.Impl_mem.floating_value
  | OVpointer of CF.Impl_mem.pointer_value
  | OVarray of loaded_value list
  | OVstruct of {
      tag : Sym.t;
      members : (Id.t * Sctypes.t * CF.Impl_mem.mem_value) list;
    }
  | OVunion of { tag : Sym.t; member : Id.t; value : CF.Impl_mem.mem_value }

and loaded_value =
  | LVspecified of object_value
  | LVunspecified of CF.Ctype.ctype

and value =
  | Vobject of object_value
  | Vloaded of loaded_value
  | Vctype of CF.Ctype.ctype
  | Vunit
  | Vtrue
  | Vfalse
  | Vlist of CF.Core.core_base_type * value list
  | Vtuple of value list

type pattern = pattern_ located

and pattern_ =
  | CaseBase of Sym.t option * CF.Core.core_base_type
  | CaseCtor of ctor * pattern list

type pexpr = pexpr_ located

and pexpr_ =
  | PEsym of Sym.t
  | PEval of value
  | PEconstrained of (CF.Mem.mem_iv_constraint * pexpr) list
  | PEundef of Locations.t * CF.Undefined.undefined_behaviour
  | PEerror of string * pexpr
  | PEctor of ctor * pexpr list
  | PEmember_shift of { ptr : pexpr; tag : Sym.t; member : Id.t }
  | PEarray_shift of { base : pexpr; ty : Sctypes.t; index : pexpr }
  | PEcatch_exceptional_condition of {
      int_ty : integer_type;
      iop : iop;
      lhs : pexpr;
      rhs : pexpr;
    }
  | PEwrapI of { int_ty : integer_type; iop : iop; lhs : pexpr; rhs : pexpr }
  | PEmemop of CF.Mem_common.pure_memop * pexpr
  | PEnot of pexpr
  | PEop of { op : CF.Core.binop; lhs : pexpr; rhs : pexpr }
  | PEconv_int of { ty : pexpr; arg : pexpr }
  | PEstruct of Sym.t * (Id.t * pexpr) list
  | PEunion of { tag : Sym.t; member : Id.t; value : pexpr }
  | PEcfunction of pexpr
  | PEmemberof of { tag : Sym.t; member : Id.t; value : pexpr }
  | PEcall of Sym.t CF.Core.generic_name * pexpr list
  | PElet of { pat : pattern; value : pexpr; body : pexpr }
  | PEif of { cond : pexpr; then_ : pexpr; else_ : pexpr }
  | PEare_compatible of { left : pexpr; right : pexpr }

type m_kill_kind = Dynamic | Static of Sctypes.t

type action = {
  loc : Locations.t;
  polarity : CF.Core.polarity;
  action : action_;
}
(** A memory action. The [Paction] polarity wrapper is folded in here. *)

and action_ =
  | Create of { align : pexpr; ty : act; prefix : CF.Symbol.prefix }
  | CreateReadOnly of {
      align : pexpr;
      ty : act;
      init : pexpr;
      prefix : CF.Symbol.prefix;
    }
  | Alloc of { align : pexpr; size : pexpr; prefix : CF.Symbol.prefix }
  | Kill of m_kill_kind * pexpr
  | Store of {
      is_locking : bool;
      ty : act;
      ptr : pexpr;
      value : pexpr;
      mo : memory_order;
    }
  | Load of { ty : act; ptr : pexpr; mo : memory_order }
  | RMW of {
      ty : act;
      ptr : pexpr;
      expected : pexpr;
      desired : pexpr;
      mo_success : memory_order;
      mo_failure : memory_order;
    }
  | Fence of memory_order
  | CompareExchangeStrong of {
      ty : act;
      ptr : pexpr;
      expected : pexpr;
      desired : pexpr;
      mo_success : memory_order;
      mo_failure : memory_order;
    }
  | CompareExchangeWeak of {
      ty : act;
      ptr : pexpr;
      expected : pexpr;
      desired : pexpr;
      mo_success : memory_order;
      mo_failure : memory_order;
    }
  | LinuxFence of linux_memory_order
  | LinuxLoad of { ty : act; ptr : pexpr; mo : linux_memory_order }
  | LinuxStore of {
      ty : act;
      ptr : pexpr;
      value : pexpr;
      mo : linux_memory_order;
    }
  | LinuxRMW of {
      ty : act;
      ptr : pexpr;
      value : pexpr;
      mo : linux_memory_order;
    }

(* ─────────────── CN proof statements ([Cnprog] / [Cnstatement]) ───────────────

   A [Cnstatement.statement Cnprog.t] is the *compiled* form of the surface CN
   proof commands (pack/unpack, unfold, assert, …). Two things have already
   happened in CN's frontend: every surface [cn_expr] has been lowered to an
   [IndexTerms.t] — i.e. the very [annot]/[Term]s that {!Subst}/{!Cn_assert}
   already handle — and every memory dereference inside those expressions has
   been hoisted out into a preamble of [Let] bindings. So there is nothing here
   that needs separate [cn_expr] handling; we only re-own the statement
   structure, keeping CN's [Request]/[LogicalConstraints]/[IndexTerms] leaves
   as-is and flattening the [Let] spine into an ordered list. *)

type cn_load = {
  loc : Locations.t;  (** location of the binding *)
  sym : Sym.t;  (** name bound to the loaded value *)
  ct : Sctypes.t;  (** type read through the pointer *)
  pointer : IndexTerms.t;  (** the pointer being dereferenced *)
}
(** One hoisted memory load [let sym = *(pointer : ct)], lifted out of a CN
    expression because reading memory is a stateful operation. The flattening of
    [Cnprog.Let]. *)

type predicate_or_predicate_name =
  | Predicate of Request.t
  | PredicateName of Sym.t
      (** Only user predicates can be named: pack/unpack of an [Owned] resource
          is not a valid program. *)

type cn_statement =
  | Pack_unpack of CF.Cn.pack_unpack * predicate_or_predicate_name
  | To_from_bytes of CF.Cn.to_from * Request.t
  | Have of LogicalConstraints.t
  | Instantiate of (Sym.t, Sctypes.t) CF.Cn.cn_to_instantiate * IndexTerms.t
  | Split_case of LogicalConstraints.t
  | Extract of Id.t list * (Sym.t, Sctypes.t) CF.Cn.cn_to_extract * IndexTerms.t
  | Unfold of Sym.t * IndexTerms.t list
  | Apply of Sym.t * IndexTerms.t list
  | Assert of LogicalConstraints.t
  | Inline of Sym.t list
  | Print of IndexTerms.t
      (** A single CN proof command. Mirrors [Cnstatement.statement]; all its
          expressions are already [IndexTerms.t] ([annot]). *)

type cn_prog = {
  loads : cn_load list;  (** memory loads to perform, in order, before [stmt] *)
  loc : Locations.t;  (** location of the proof command *)
  stmt : cn_statement;  (** the proof command itself *)
}
(** The flattened [Cnstatement.statement Cnprog.t]: its [Let] spine of hoisted
    loads followed by the terminal [Pure] statement. *)

type expr = expr_ located

and expr_ =
  | Epure of pexpr
  | Ememop of Sym.t CF.Mem_common.generic_memop * pexpr list
  | Eaction of action
  | Eskip
  | Eccall of {
      ty : act;
      fn : pexpr;
      args : pexpr list;
      specs : (Locations.t * IndexTerms.t Cnprog.t list) option;
    }
  | Eproc of Sym.t CF.Core.generic_name * pexpr list
  | Elet of { pat : pattern; value : pexpr; body : expr }
  | Eunseq of expr list
  | Ewseq of { pat : pattern; value : expr; body : expr }
  | Esseq of { pat : pattern; value : expr; body : expr }
  | Eif of { cond : pexpr; then_ : expr; else_ : expr }
  | Ebound of expr
  | End of expr list
  | Erun of Sym.t * pexpr list
  | CN_progs of cn_prog list
      (** Compiled CN proof commands; see {!cn_prog}. The surface
          [cn_statement list] is dropped — it is the pre-compilation form of the
          same statements and carries no extra information. *)

(* Argument binders: a flat record of the two binder lists. The body is paired
   with [arguments] at each use site (see {!fun_map_decl} and {!label_def}). *)

type logical_arg =
  | Define of Sym.t * IndexTerms.t
  | Resource of Sym.t * (Request.t * BaseTypes.t)
  | Constraint of LogicalConstraints.t

type computational_arg =
  | Computational of Sym.t * BaseTypes.t
  | Ghost of Sym.t * BaseTypes.t

type arguments = {
  comp : (computational_arg * Locations.info) list;
  logic : (logical_arg * Locations.info) list;
}

type logical_return = (logical_arg * Locations.info) list
(** The flattened [Cn.LogicalReturnTypes.t]: a trailing list of logical bindings
    ([Define]/[Resource]/[Constraint]) whose [I] terminator carries no data.
    Also the tail of a lemma's old [ArgumentTypes.lemmat]. *)

type return_type = {
  ret : Sym.t * BaseTypes.t;  (** the returned value's name and base type *)
  ret_info : Locations.info;
  logic : logical_return;  (** trailing logical constraints on the result *)
}
(** The flattened [Cn.ReturnTypes.t]: a single [Computational] binder followed
    by a logical tail. The old [ArgumentTypes.ft] is just [arguments] paired
    with one of these (see {!Of_mucore.argument_types}). *)

type globs = GlobalDef of Sctypes.t * expr | GlobalDecl of Sctypes.t

type loop_info = {
  condition_loc : Locations.t;  (** location of the loop condition *)
  loop_loc : Locations.t;  (** location of the whole loop *)
  has_invariant : bool;  (** did the user supply a loop invariant? *)
}
(** Replaces the [`Aux_info of loc * loc * bool] polymorphic-variant blob. *)

type label_def =
  | Non_inlined of {
      loc : Locations.t;
      label : Sym.t;
      annot : CF.Annot.label_annot;
      args : arguments;
      body : expr;
    }
  | Return of Locations.t
  | Loop of {
      loc : Locations.t;
      args : arguments;
      body : expr;
      annots : CF.Annot.annot list;
      info : loop_info;
    }

type trusted = Trusted of Locations.t | Checked

type fun_map_decl =
  | Proc of {
      loc : Locations.t;
      args : arguments;
      body : expr;
      labels : label_def Sym.Map.t;
      return_type : return_type;
      trusted : trusted;
    }
  | ProcDecl of Locations.t * (arguments * return_type) option

type tag_definition = StructDef of Memory.struct_layout | UnionDef

type function_to_convert = {
  loc : Locations.t;
  c_fun_sym : Sym.t;
  l_fun_sym : Sym.t;
}

type datatype = {
  loc : Locations.t;
  cases : (Sym.t * (Id.t * BaseTypes.t) list) list;
}

type clause = {
  loc : Locations.t;
  guard : IndexTerms.t;
  logical_args : logical_arg list;
  ret : IndexTerms.t;
}

type predicate_def = {
  loc : Locations.t;
  iargs : (Sym.t * BaseTypes.t) list;
  oarg : Locations.t * BaseTypes.t;
  clauses : clause list option;
  recursive : bool;
  attrs : Id.t list;
}

type file = {
  main : Sym.t option;
  tag_defs : tag_definition Sym.Map.t;
  globs : (Sym.t * globs) list;
  funs : fun_map_decl Sym.Map.t;
  extern : CF.Core.extern_map;
  stdlib_syms : Sym.Set.t;
  mk_functions : function_to_convert list;
  resource_predicates : (Sym.t * predicate_def) list;
  logical_predicates : (Sym.t * Definition.Function.t) list;
  datatypes : (Sym.t * datatype) list;
  lemmata : (Sym.t * (Locations.t * (arguments * logical_return))) list;
  call_funinfo : Sctypes.c_concrete_sig Sym.Map.t;
}

(* ──────────────────────────── helpers ──────────────────────────── *)

let has_spec (args : arguments) (ret_ty : return_type) =
  not (List.is_empty args.logic && List.is_empty ret_ty.logic)

let loc_of_pexpr (pe : pexpr) = pe.loc
let loc_of_expr (e : expr) = e.loc
let loc_of_pattern (p : pattern) = p.loc

let is_undef_or_error_pexpr (pe : pexpr) =
  match pe.node with PEundef _ | PEerror _ -> true | _ -> false

let is_undef_or_error_expr (e : expr) =
  match e.node with Epure pe -> is_undef_or_error_pexpr pe | _ -> false

let is_ctype_const (pe : pexpr) =
  match pe.node with PEval (Vctype ct) -> Some ct | _ -> None

let empty_file : file =
  {
    main = None;
    tag_defs = Sym.Map.empty;
    globs = [];
    funs = Sym.Map.empty;
    extern = Pmap.empty Id.compare;
    stdlib_syms = Sym.Set.empty;
    mk_functions = [];
    resource_predicates = [];
    logical_predicates = [];
    datatypes = [];
    lemmata = [];
    call_funinfo = Sym.Map.empty;
  }

(* ─────────────────────── pretty-printing (Fmt) ─────────────────────── *)

(* Bridge from Cerberus' PPrint-based printers to [Fmt.t]. *)
let pp_pp pp ft x = Fmt.string ft (Cn.Pp.plain (pp x))
let pp_sym = Sym.pp_hum
let pp_id = pp_pp Id.pp
let pp_loc = pp_pp Locations.pp
let pp_it = pp_pp IndexTerms.pp
let pp_request ft r = Request.pp ft r
let pp_bt = pp_pp BaseTypes.pp
let pp_lc = pp_pp LogicalConstraints.pp
let pp_sct = pp_pp Sctypes.pp
let pp_ctype = pp_pp CF.Pp_core_ctype.pp_ctype
let pp_cbt = pp_pp CF.Pp_core.Basic.pp_core_base_type
let pp_ctor = pp_pp CF.Pp_core.Basic.pp_ctor
let pp_prefix = pp_pp CF.Pp_symbol.pp_prefix
let pp_pure_memop = pp_pp CF.Pp_mem.pp_pure_memop
let pp_memop = pp_pp CF.Pp_mem.pp_memop
let pp_integer_value = pp_pp CF.Impl_mem.pp_integer_value_for_core
let pp_pointer_value = pp_pp CF.Impl_mem.pp_pointer_value
let pp_mem_value = pp_pp CF.Impl_mem.pp_mem_value
let pp_ub = Fmt.of_to_string CF.Undefined.stringFromUndefined_behaviour

let pp_floating ft fv =
  Fmt.string ft
    (CF.Impl_mem.case_fval fv (fun () -> "<unspec>") string_of_float)

let pp_binop ft (op : CF.Core.binop) =
  Fmt.string ft
    (match op with
    | OpAdd -> "+"
    | OpSub -> "-"
    | OpMul -> "*"
    | OpDiv -> "/"
    | OpRem_t -> "rem_t"
    | OpRem_f -> "rem_f"
    | OpExp -> "^"
    | OpEq -> "=="
    | OpGt -> ">"
    | OpLt -> "<"
    | OpGe -> ">="
    | OpLe -> "<="
    | OpAnd -> "/\\"
    | OpOr -> "\\/")

let pp_iop ft (op : iop) =
  Fmt.string ft
    (match op with
    | IOpAdd -> "+"
    | IOpSub -> "-"
    | IOpMul -> "*"
    | IOpShl -> "<<"
    | IOpShr -> ">>"
    | IOpDiv -> "/"
    | IOpRem_t -> "rem_t")

let pp_memory_order ft (mo : memory_order) =
  Fmt.string ft
    (match mo with
    | NA -> "na"
    | Seq_cst -> "seq_cst"
    | Relaxed -> "relaxed"
    | Release -> "release"
    | Acquire -> "acquire"
    | Consume -> "consume"
    | Acq_rel -> "acq_rel")

let pp_linux_memory_order ft (mo : linux_memory_order) =
  Fmt.string ft
    (match mo with
    | Once -> "once"
    | LAcquire -> "acquire"
    | LRelease -> "release"
    | Rmb -> "rmb"
    | Wmb -> "wmb"
    | Mb -> "mb"
    | RbDep -> "rb_dep"
    | RcuLock -> "rcu_lock"
    | RcuUnlock -> "rcu_unlock"
    | SyncRcu -> "sync_rcu")

let pp_name ft : Sym.t CF.Core.generic_name -> unit = function
  | Sym s -> pp_sym ft s
  | Impl _ -> Fmt.string ft "<impl>"

(* doc_tree-only leaves are rendered through their [dtree]. *)
let pp_dtree dtree = pp_pp (fun x -> CF.Pp_ast.pp_doc_tree (dtree x))
let comma = Fmt.comma

(* A delimited, comma-separated sequence with a leading soft break. When the
   contents don't fit, they drop onto a line indented from the opening
   delimiter rather than aligning under it (which marches off to the right as
   nesting deepens); short sequences still print inline. The break attaches to
   the caller's box, so call sites wrap these in their own [@[<2>...@]]. *)
let pp_paren pp ft xs = Fmt.pf ft "(@,%a)" (Fmt.list ~sep:comma pp) xs
let pp_bracket pp ft xs = Fmt.pf ft "[@,%a]" (Fmt.list ~sep:comma pp) xs

let rec pp_value ft = function
  | Vobject ov -> pp_object_value ft ov
  | Vloaded lv -> pp_loaded_value ft lv
  | Vctype ct -> pp_ctype ft ct
  | Vunit -> Fmt.string ft "unit"
  | Vtrue -> Fmt.string ft "true"
  | Vfalse -> Fmt.string ft "false"
  | Vlist (_, vs) -> Fmt.pf ft "@[<2>%a@]" (pp_bracket pp_value) vs
  | Vtuple vs -> Fmt.pf ft "@[<2>%a@]" (pp_paren pp_value) vs

and pp_object_value ft = function
  | OVinteger iv -> pp_integer_value ft iv
  | OVfloating fv -> pp_floating ft fv
  | OVpointer pv -> pp_pointer_value ft pv
  | OVarray lvs -> Fmt.pf ft "@[<2>array%a@]" (pp_bracket pp_loaded_value) lvs
  | OVstruct { tag; members } ->
      let pp_member ft (id, _, mv) =
        Fmt.pf ft "@[<2>.%a =@ %a@]" pp_id id pp_mem_value mv
      in
      Fmt.pf ft "@[<2>struct %a {@,%a}@]" pp_sym tag
        (Fmt.list ~sep:comma pp_member)
        members
  | OVunion { tag; member; value } ->
      Fmt.pf ft "@[<2>union %a {@,.%a =@ %a}@]" pp_sym tag pp_id member
        pp_mem_value value

and pp_loaded_value ft = function
  | LVspecified ov -> pp_object_value ft ov
  | LVunspecified ct -> Fmt.pf ft "@[<2>unspecified(@,%a)@]" pp_ctype ct

let rec pp_pattern ft (p : pattern) = pp_pattern_ ft p.node

and pp_pattern_ ft = function
  | CaseBase (None, _) -> Fmt.string ft "_"
  | CaseBase (Some s, _) -> pp_sym ft s
  | CaseCtor (c, ps) ->
      Fmt.pf ft "@[<2>%a%a@]" pp_ctor c (pp_paren pp_pattern) ps

let rec pp_pexpr ft (pe : pexpr) =
  match pe.node with
  | PEsym s -> pp_sym ft s
  | PEval v -> pp_value ft v
  | PEconstrained l ->
      Fmt.pf ft "@[<2>constrained%a@]"
        (pp_paren (fun ft (_, pe) -> pp_pexpr ft pe))
        l
  | PEundef (_, ub) -> Fmt.pf ft "@[<2>undef(%a)@]" pp_ub ub
  | PEerror (s, pe) -> Fmt.pf ft "@[<2>error(@,%S,@ %a)@]" s pp_pexpr pe
  | PEctor (c, pes) -> Fmt.pf ft "@[<2>%a%a@]" pp_ctor c (pp_paren pp_pexpr) pes
  | PEmember_shift { ptr; tag; member } ->
      Fmt.pf ft "@[<2>member_shift(@,%a,@ %a.%a)@]" pp_pexpr ptr pp_sym tag
        pp_id member
  | PEarray_shift { base; ty; index } ->
      Fmt.pf ft "@[<2>array_shift(@,%a : %a,@ %a)@]" pp_pexpr base pp_sct ty
        pp_pexpr index
  | PEcatch_exceptional_condition { iop; lhs; rhs; _ } ->
      Fmt.pf ft "@[<2>catch(@,%a %a@ %a)@]" pp_pexpr lhs pp_iop iop pp_pexpr rhs
  | PEwrapI { iop; lhs; rhs; _ } ->
      Fmt.pf ft "@[<2>wrapI(@,%a %a@ %a)@]" pp_pexpr lhs pp_iop iop pp_pexpr rhs
  | PEmemop (m, pe) ->
      Fmt.pf ft "@[<2>memop(@,%a,@ %a)@]" pp_pure_memop m pp_pexpr pe
  | PEnot pe -> Fmt.pf ft "@[<2>not(@,%a)@]" pp_pexpr pe
  | PEop { op; lhs; rhs } ->
      Fmt.pf ft "@[<2>(%a %a@ %a)@]" pp_pexpr lhs pp_binop op pp_pexpr rhs
  | PEconv_int { ty; arg } ->
      Fmt.pf ft "@[<2>conv_int(@,%a,@ %a)@]" pp_pexpr ty pp_pexpr arg
  | PEstruct (tag, members) ->
      let pp_member ft (id, pe) =
        Fmt.pf ft "@[<2>.%a =@ %a@]" pp_id id pp_pexpr pe
      in
      Fmt.pf ft "@[<2>struct %a {@,%a}@]" pp_sym tag
        (Fmt.list ~sep:comma pp_member)
        members
  | PEunion { tag; member; value } ->
      Fmt.pf ft "@[<2>union %a {@,.%a =@ %a}@]" pp_sym tag pp_id member pp_pexpr
        value
  | PEcfunction pe -> Fmt.pf ft "@[<2>cfunction(@,%a)@]" pp_pexpr pe
  | PEmemberof { tag; member; value } ->
      Fmt.pf ft "@[<2>memberof(@,%a.%a,@ %a)@]" pp_sym tag pp_id member pp_pexpr
        value
  | PEcall (name, pes) ->
      Fmt.pf ft "@[<2>%a%a@]" pp_name name (pp_paren pp_pexpr) pes
  | PElet _ -> pp_plet ft pe
  | PEif { cond; then_; else_ } -> pp_pif ft cond then_ else_
  | PEare_compatible { left; right } ->
      Fmt.pf ft "@[<2>are_compatible(@,%a,@ %a)@]" pp_pexpr left pp_pexpr right

(* Flatten a chain of [PElet]s — including bindings nested inside a bound value
   — into a flat list of statements plus the final tail. Hoisting the value's
   own bindings out preserves evaluation order while keeping the indentation
   flat instead of marching to the right. *)
and flatten_plet (pe : pexpr) : (pattern * pexpr) list * pexpr =
  match pe.node with
  | PElet { pat; value; body } ->
      let vstmts, vtail = flatten_plet value in
      let bstmts, tail = flatten_plet body in
      (vstmts @ ((pat, vtail) :: bstmts), tail)
  | _ -> ([], pe)

and pp_plet ft pe =
  let stmts, tail = flatten_plet pe in
  let pp_stmt ft (pat, value) =
    Fmt.pf ft "@[<2>let %a =@ %a@] in" pp_pattern pat pp_pexpr value
  in
  Fmt.pf ft "@[<v>%a@,%a@]" (Fmt.list ~sep:Fmt.cut pp_stmt) stmts pp_pexpr tail

(* Render a conditional as an [else if] ladder rather than nesting each [else]
   branch one indentation level deeper. *)
and pp_pif ft cond then_ else_ =
  Fmt.pf ft "@[<v>@[<2>if %a then@ %a@]@ %a@]" pp_pexpr cond pp_pexpr then_
    pp_pelse else_

and pp_pelse ft (pe : pexpr) =
  match pe.node with
  | PEif { cond; then_; else_ } ->
      Fmt.pf ft "@[<2>else if %a then@ %a@]@ %a" pp_pexpr cond pp_pexpr then_
        pp_pelse else_
  | _ -> Fmt.pf ft "@[<2>else@ %a@]" pp_pexpr pe

let pp_act ft (a : act) = pp_sct ft a.node

let pp_action_ ft = function
  | Create { align; ty; _ } ->
      Fmt.pf ft "@[<2>create(@,%a,@ %a)@]" pp_pexpr align pp_act ty
  | CreateReadOnly { align; ty; init; _ } ->
      Fmt.pf ft "@[<2>create_readonly(@,%a,@ %a,@ %a)@]" pp_pexpr align pp_act
        ty pp_pexpr init
  | Alloc { align; size; _ } ->
      Fmt.pf ft "@[<2>alloc(@,%a,@ %a)@]" pp_pexpr align pp_pexpr size
  | Kill (Dynamic, pe) -> Fmt.pf ft "@[<2>kill(@,dynamic,@ %a)@]" pp_pexpr pe
  | Kill (Static ct, pe) ->
      Fmt.pf ft "@[<2>kill(@,%a,@ %a)@]" pp_sct ct pp_pexpr pe
  | Store { is_locking; ty; ptr; value; mo } ->
      Fmt.pf ft "@[<2>store%s(@,%a,@ %a,@ %a,@ %a)@]"
        (if is_locking then "_lock" else "")
        pp_act ty pp_pexpr ptr pp_pexpr value pp_memory_order mo
  | Load { ty; ptr; mo } ->
      Fmt.pf ft "@[<2>load(@,%a,@ %a,@ %a)@]" pp_act ty pp_pexpr ptr
        pp_memory_order mo
  | RMW { ty; ptr; expected; desired; mo_success; mo_failure } ->
      Fmt.pf ft "@[<2>rmw(@,%a,@ %a,@ %a,@ %a,@ %a,@ %a)@]" pp_act ty pp_pexpr
        ptr pp_pexpr expected pp_pexpr desired pp_memory_order mo_success
        pp_memory_order mo_failure
  | Fence mo -> Fmt.pf ft "@[<2>fence(@,%a)@]" pp_memory_order mo
  | CompareExchangeStrong { ty; ptr; expected; desired; mo_success; mo_failure }
    ->
      Fmt.pf ft "@[<2>cmpxchg_strong(@,%a,@ %a,@ %a,@ %a,@ %a,@ %a)@]" pp_act ty
        pp_pexpr ptr pp_pexpr expected pp_pexpr desired pp_memory_order
        mo_success pp_memory_order mo_failure
  | CompareExchangeWeak { ty; ptr; expected; desired; mo_success; mo_failure }
    ->
      Fmt.pf ft "@[<2>cmpxchg_weak(@,%a,@ %a,@ %a,@ %a,@ %a,@ %a)@]" pp_act ty
        pp_pexpr ptr pp_pexpr expected pp_pexpr desired pp_memory_order
        mo_success pp_memory_order mo_failure
  | LinuxFence mo ->
      Fmt.pf ft "@[<2>linux_fence(@,%a)@]" pp_linux_memory_order mo
  | LinuxLoad { ty; ptr; mo } ->
      Fmt.pf ft "@[<2>linux_load(@,%a,@ %a,@ %a)@]" pp_act ty pp_pexpr ptr
        pp_linux_memory_order mo
  | LinuxStore { ty; ptr; value; mo } ->
      Fmt.pf ft "@[<2>linux_store(@,%a,@ %a,@ %a,@ %a)@]" pp_act ty pp_pexpr ptr
        pp_pexpr value pp_linux_memory_order mo
  | LinuxRMW { ty; ptr; value; mo } ->
      Fmt.pf ft "@[<2>linux_rmw(@,%a,@ %a,@ %a,@ %a)@]" pp_act ty pp_pexpr ptr
        pp_pexpr value pp_linux_memory_order mo

let pp_action ft (a : action) =
  let prefix = match a.polarity with Pos -> "" | Neg -> "neg " in
  Fmt.pf ft "%s%a" prefix pp_action_ a.action

let pp_pack_unpack ft = function
  | CF.Cn.Pack -> Fmt.string ft "pack"
  | CF.Cn.Unpack -> Fmt.string ft "unpack"

let pp_to_from ft = function
  | CF.Cn.To -> Fmt.string ft "to_bytes"
  | CF.Cn.From -> Fmt.string ft "from_bytes"

let pp_to_instantiate ft = function
  | CF.Cn.I_Function s -> Fmt.pf ft "function %a" pp_sym s
  | CF.Cn.I_Good ty -> Fmt.pf ft "good(%a)" pp_sct ty
  | CF.Cn.I_Everything -> Fmt.string ft "everything"

let pp_to_extract ft = function
  | CF.Cn.E_Everything -> Fmt.string ft "everything"
  | CF.Cn.E_Pred _ -> Fmt.string ft "pred"

let pp_pred ft (p : Request.t) = Request.pp ~no_nums:true ft p

let pp_pred_or_name ft = function
  | Predicate p -> pp_pred ft p
  | PredicateName n -> Sym.pp_hum ft n

let pp_cn_statement ft = function
  | Pack_unpack (pu, p) ->
      Fmt.pf ft "@[<2>%a %a@]" pp_pack_unpack pu pp_pred_or_name p
  | To_from_bytes (tf, p) -> Fmt.pf ft "@[<2>%a %a@]" pp_to_from tf pp_pred p
  | Have lc -> Fmt.pf ft "@[<2>have %a@]" pp_lc lc
  | Instantiate (i, it) ->
      Fmt.pf ft "@[<2>instantiate %a,@ %a@]" pp_to_instantiate i pp_it it
  | Split_case lc -> Fmt.pf ft "@[<2>split_case %a@]" pp_lc lc
  | Extract (attrs, e, it) ->
      Fmt.pf ft "@[<2>extract [%a] %a,@ %a@]"
        (Fmt.list ~sep:comma pp_id)
        attrs pp_to_extract e pp_it it
  | Unfold (s, args) ->
      Fmt.pf ft "@[<2>unfold %a%a@]" pp_sym s (pp_paren pp_it) args
  | Apply (s, args) ->
      Fmt.pf ft "@[<2>apply %a%a@]" pp_sym s (pp_paren pp_it) args
  | Assert lc -> Fmt.pf ft "@[<2>assert %a@]" pp_lc lc
  | Inline nms -> Fmt.pf ft "@[<2>inline %a@]" (Fmt.list ~sep:comma pp_sym) nms
  | Print it -> Fmt.pf ft "@[<2>print %a@]" pp_it it

let pp_cn_load ft (l : cn_load) =
  Fmt.pf ft "@[<2>let %a =@ load(%a : %a)@]" pp_sym l.sym pp_it l.pointer pp_sct
    l.ct

let pp_cn_prog ft (p : cn_prog) =
  match p.loads with
  | [] -> pp_cn_statement ft p.stmt
  | loads ->
      let pp_load ft l = Fmt.pf ft "%a in" pp_cn_load l in
      Fmt.pf ft "@[<v>%a@,%a@]"
        (Fmt.list ~sep:Fmt.cut pp_load)
        loads pp_cn_statement p.stmt

let rec pp_expr ft (e : expr) =
  match e.node with
  | Epure pe -> Fmt.pf ft "@[<2>pure(@,%a)@]" pp_pexpr pe
  | Ememop (m, pes) ->
      Fmt.pf ft "@[<2>memop(@,%a,@ %a)@]" pp_memop m
        (Fmt.list ~sep:comma pp_pexpr)
        pes
  | Eaction a -> pp_action ft a
  | Eskip -> Fmt.string ft "skip"
  | Eccall { ty; fn; args; _ } ->
      Fmt.pf ft "@[<2>ccall(%a : %a)%a@]" pp_pexpr fn pp_act ty
        (pp_paren pp_pexpr) args
  | Eproc (name, pes) ->
      Fmt.pf ft "@[<2>proc %a%a@]" pp_name name (pp_paren pp_pexpr) pes
  | Elet _ | Ewseq _ | Esseq _ -> pp_eseq ft e
  | Eunseq es -> Fmt.pf ft "@[<2>unseq%a@]" (pp_paren pp_expr) es
  | Eif { cond; then_; else_ } -> pp_eif ft cond then_ else_
  | Ebound e -> Fmt.pf ft "@[<2>bound(@,%a)@]" pp_expr e
  | End es -> Fmt.pf ft "@[<2>nd%a@]" (pp_paren pp_expr) es
  | Erun (s, pes) ->
      Fmt.pf ft "@[<2>run %a%a@]" pp_sym s (pp_paren pp_pexpr) pes
  | CN_progs progs ->
      Fmt.pf ft "@[<2>cn_progs%a@]" (pp_bracket pp_cn_prog) progs

(* Flatten a chain of sequenced bindings ([Elet]/[Ewseq]/[Esseq]) into a flat
   list of statements plus the final tail. Bindings nested in a bound value are
   hoisted out (faithful to the evaluation order, since the value must be fully
   evaluated before it is bound), so a deeply left-nested sequence prints as a
   flat block rather than a rightward staircase. [Eunseq] and other compound
   forms are kept intact and indented within their own value. *)
and flatten_eseq (e : expr) :
    (string * pattern * [ `P of pexpr | `E of expr ]) list * expr =
  match e.node with
  | Elet { pat; value; body } ->
      let bstmts, tail = flatten_eseq body in
      (("", pat, `P value) :: bstmts, tail)
  | Ewseq { pat; value; body } -> flatten_eseq_value "weak " pat value body
  | Esseq { pat; value; body } -> flatten_eseq_value "strong " pat value body
  | _ -> ([], e)

and flatten_eseq_value kw pat value body =
  let vstmts, vtail = flatten_eseq value in
  let bstmts, tail = flatten_eseq body in
  (vstmts @ ((kw, pat, `E vtail) :: bstmts), tail)

and pp_eseq ft e =
  let stmts, tail = flatten_eseq e in
  let pp_bound ft = function `P pe -> pp_pexpr ft pe | `E e -> pp_expr ft e in
  let pp_stmt ft (kw, pat, value) =
    Fmt.pf ft "@[<2>let %s%a =@ %a@] in" kw pp_pattern pat pp_bound value
  in
  Fmt.pf ft "@[<v>%a@,%a@]" (Fmt.list ~sep:Fmt.cut pp_stmt) stmts pp_expr tail

(* Render a conditional as an [else if] ladder rather than nesting each [else]
   branch one indentation level deeper. *)
and pp_eif ft cond then_ else_ =
  Fmt.pf ft "@[<v>@[<2>if %a then@ %a@]@ %a@]" pp_pexpr cond pp_expr then_
    pp_eelse else_

and pp_eelse ft (e : expr) =
  match e.node with
  | Eif { cond; then_; else_ } ->
      Fmt.pf ft "@[<2>else if %a then@ %a@]@ %a" pp_pexpr cond pp_expr then_
        pp_eelse else_
  | _ -> Fmt.pf ft "@[<2>else@ %a@]" pp_expr e

let pp_logical_arg ft = function
  | Define (s, it) -> Fmt.pf ft "@[<2>let %a =@ %a@]" pp_sym s pp_it it
  | Resource (s, (req, bt)) ->
      Fmt.pf ft "@[<2>take %a =@ %a : %a@]" pp_sym s pp_request req pp_bt bt
  | Constraint lc -> Fmt.pf ft "@[<2>assert %a@]" pp_lc lc

let pp_computational_arg ft = function
  | Computational (s, bt) -> Fmt.pf ft "@[<2>%a : %a@]" pp_sym s pp_bt bt
  | Ghost (s, bt) -> Fmt.pf ft "@[<2>ghost %a : %a@]" pp_sym s pp_bt bt

let pp_arguments ft { comp; logic } =
  let pp_c ft (x, _) = pp_computational_arg ft x in
  let pp_l ft (x, _) = pp_logical_arg ft x in
  match (comp, logic) with
  | [], [] -> Fmt.string ft "(no binders)"
  | _, [] -> Fmt.(list ~sep:cut pp_c) ft comp
  | [], _ -> Fmt.(list ~sep:cut pp_l) ft logic
  | _ ->
      Fmt.pf ft "@[<v>%a@ %a@]"
        Fmt.(list ~sep:cut pp_c)
        comp
        Fmt.(list ~sep:cut pp_l)
        logic

let pp_logical_return ft (logic : logical_return) =
  Fmt.(list ~sep:cut (fun ft (x, _) -> pp_logical_arg ft x)) ft logic

let pp_return_type ft { ret = s, bt; logic; _ } =
  match logic with
  | [] -> Fmt.pf ft "@[<2>return %a : %a@]" pp_sym s pp_bt bt
  | _ ->
      Fmt.pf ft "@[<v>@[<2>return %a : %a@]@ %a@]" pp_sym s pp_bt bt
        pp_logical_return logic

let pp_label_def ft = function
  | Non_inlined { label; args; body; _ } ->
      Fmt.pf ft "@[<v 2>label %a:@ %a@ %a@]" pp_sym label pp_arguments args
        pp_expr body
  | Return _ -> Fmt.string ft "return"
  | Loop { args; body; info; _ } ->
      Fmt.pf ft "@[<v 2>loop (invariant: %b):@ %a@ %a@]" info.has_invariant
        pp_arguments args pp_expr body

let pp_fun_map_decl ft = function
  | Proc { args; body; labels; return_type; trusted; _ } ->
      let tag =
        match trusted with Trusted _ -> " (trusted)" | Checked -> ""
      in
      let pp_label ft (s, l) =
        Fmt.pf ft "@[<v 2>%a:@ %a@]" pp_sym s pp_label_def l
      in
      Fmt.pf ft
        "@[<v 2>proc%s:@ @[<v 2>args:@ %a@]@ @[<2>returns:@ %a@]@ @[<v \
         2>body:@ %a@]@ @[<v 2>labels:@ %a@]@]"
        tag pp_arguments args pp_return_type return_type pp_expr body
        (Fmt.list ~sep:Fmt.cut pp_label)
        (Sym.Map.bindings labels)
  | ProcDecl (_, _) -> Fmt.string ft "<proc decl>"

let pp_globs ft = function
  | GlobalDef (ct, e) ->
      Fmt.pf ft "@[<v 2>global : %a =@ %a@]" pp_sct ct pp_expr e
  | GlobalDecl ct -> Fmt.pf ft "@[<2>global : %a@]" pp_sct ct

let pp_datatype ft (d : datatype) =
  let pp_field ft (id, bt) = Fmt.pf ft "@[<2>%a : %a@]" pp_id id pp_bt bt in
  let pp_case ft (s, fields) =
    Fmt.pf ft "@[<2>%a {%a}@]" pp_sym s (Fmt.list ~sep:comma pp_field) fields
  in
  Fmt.pf ft "@[<v 2>datatype:@ %a@]" (Fmt.list ~sep:Fmt.cut pp_case) d.cases

let pp_file ft (f : file) =
  let pp_binding pp ft (s, x) = Fmt.pf ft "@[<v 2>%a:@ %a@]" pp_sym s pp x in
  Fmt.pf ft
    "@[<v>main: %a@ @ @[<v 2>globs:@ %a@]@ @ @[<v 2>funs:@ %a@]@ @ @[<v \
     2>datatypes:@ %a@]@]"
    Fmt.(option ~none:(any "<none>") pp_sym)
    f.main
    (Fmt.list ~sep:Fmt.cut (pp_binding pp_globs))
    f.globs
    (Fmt.list ~sep:Fmt.cut (pp_binding pp_fun_map_decl))
    (Sym.Map.bindings f.funs)
    (Fmt.list ~sep:Fmt.cut (pp_binding pp_datatype))
    f.datatypes

(* ──────────────────── compile pass: Cn.Mucore → file ──────────────────── *)

module Of_mucore = struct
  module Mu = Cn.Mucore

  let rec object_value (Mu.OV (_, ov_)) : object_value =
    match ov_ with
    | Mu.OVinteger i -> OVinteger i
    | Mu.OVfloating f -> OVfloating f
    | Mu.OVpointer p -> OVpointer p
    | Mu.OVarray lvs -> OVarray (List.map loaded_value lvs)
    | Mu.OVstruct (tag, members) -> OVstruct { tag; members }
    | Mu.OVunion (tag, member, value) -> OVunion { tag; member; value }

  and loaded_value : 'a. 'a Mu.loaded_value -> loaded_value = function
    | Mu.LVspecified ov -> LVspecified (object_value ov)
    | Mu.LVunspecified ct -> LVunspecified ct

  and value (Mu.V (_, v_)) : value =
    match v_ with
    | Mu.Vobject ov -> Vobject (object_value ov)
    | Mu.Vloaded lv -> Vloaded (loaded_value lv)
    | Mu.Vctype ct -> Vctype ct
    | Mu.Vunit -> Vunit
    | Mu.Vtrue -> Vtrue
    | Mu.Vfalse -> Vfalse
    | Mu.Vlist (bt, vs) -> Vlist (bt, List.map value vs)
    | Mu.Vtuple vs -> Vtuple (List.map value vs)

  let rec pattern (Mu.Pattern (loc, annots, _, p_)) : pattern =
    { loc; annots; node = pattern_ p_ }

  and pattern_ = function
    | Mu.CaseBase (s, bt) -> CaseBase (s, bt)
    | Mu.CaseCtor (c, ps) -> CaseCtor (c, List.map pattern ps)

  let rec pexpr (Mu.Pexpr (loc, annots, _, pe_)) : pexpr =
    { loc; annots; node = pexpr_ pe_ }

  and pexpr_ = function
    | Mu.PEsym s -> PEsym s
    | Mu.PEval v -> PEval (value v)
    | Mu.PEconstrained l ->
        PEconstrained (List.map (fun (c, pe) -> (c, pexpr pe)) l)
    | Mu.PEundef (loc, ub) -> PEundef (loc, ub)
    | Mu.PEerror (s, pe) -> PEerror (s, pexpr pe)
    | Mu.PEctor (c, pes) -> PEctor (c, List.map pexpr pes)
    | Mu.PEmember_shift (pe, tag, member) ->
        PEmember_shift { ptr = pexpr pe; tag; member }
    | Mu.PEarray_shift (base, ty, index) ->
        PEarray_shift { base = pexpr base; ty; index = pexpr index }
    | Mu.PEcatch_exceptional_condition (int_ty, iop, l, r) ->
        PEcatch_exceptional_condition
          { int_ty; iop; lhs = pexpr l; rhs = pexpr r }
    | Mu.PEwrapI (int_ty, iop, l, r) ->
        PEwrapI { int_ty; iop; lhs = pexpr l; rhs = pexpr r }
    | Mu.PEmemop (m, pe) -> PEmemop (m, pexpr pe)
    | Mu.PEnot pe -> PEnot (pexpr pe)
    | Mu.PEop (op, l, r) -> PEop { op; lhs = pexpr l; rhs = pexpr r }
    | Mu.PEconv_int (ty, arg) -> PEconv_int { ty = pexpr ty; arg = pexpr arg }
    | Mu.PEstruct (tag, members) ->
        PEstruct (tag, List.map (fun (id, pe) -> (id, pexpr pe)) members)
    | Mu.PEunion (tag, member, pe) -> PEunion { tag; member; value = pexpr pe }
    | Mu.PEcfunction pe -> PEcfunction (pexpr pe)
    | Mu.PEmemberof (tag, member, pe) ->
        PEmemberof { tag; member; value = pexpr pe }
    | Mu.PEcall (name, pes) -> PEcall (name, List.map pexpr pes)
    | Mu.PElet (pat, v, b) ->
        PElet { pat = pattern pat; value = pexpr v; body = pexpr b }
    | Mu.PEif (c, t, e) ->
        PEif { cond = pexpr c; then_ = pexpr t; else_ = pexpr e }
    | Mu.PEare_compatible (a, b) ->
        PEare_compatible { left = pexpr a; right = pexpr b }

  let act ({ loc; annot; ct } : Mu.act) : act =
    { loc; annots = annot; node = ct }

  let m_kill_kind = function Mu.Dynamic -> Dynamic | Mu.Static ct -> Static ct

  let action_ = function
    | Mu.Create (align, a, prefix) ->
        Create { align = pexpr align; ty = act a; prefix }
    | Mu.CreateReadOnly (align, a, init, prefix) ->
        CreateReadOnly
          { align = pexpr align; ty = act a; init = pexpr init; prefix }
    | Mu.Alloc (align, size, prefix) ->
        Alloc { align = pexpr align; size = pexpr size; prefix }
    | Mu.Kill (k, pe) -> Kill (m_kill_kind k, pexpr pe)
    | Mu.Store (is_locking, a, ptr, value, mo) ->
        Store
          { is_locking; ty = act a; ptr = pexpr ptr; value = pexpr value; mo }
    | Mu.Load (a, ptr, mo) -> Load { ty = act a; ptr = pexpr ptr; mo }
    | Mu.RMW (a, ptr, e1, e2, mo1, mo2) ->
        RMW
          {
            ty = act a;
            ptr = pexpr ptr;
            expected = pexpr e1;
            desired = pexpr e2;
            mo_success = mo1;
            mo_failure = mo2;
          }
    | Mu.Fence mo -> Fence mo
    | Mu.CompareExchangeStrong (a, ptr, e1, e2, mo1, mo2) ->
        CompareExchangeStrong
          {
            ty = act a;
            ptr = pexpr ptr;
            expected = pexpr e1;
            desired = pexpr e2;
            mo_success = mo1;
            mo_failure = mo2;
          }
    | Mu.CompareExchangeWeak (a, ptr, e1, e2, mo1, mo2) ->
        CompareExchangeWeak
          {
            ty = act a;
            ptr = pexpr ptr;
            expected = pexpr e1;
            desired = pexpr e2;
            mo_success = mo1;
            mo_failure = mo2;
          }
    | Mu.LinuxFence mo -> LinuxFence mo
    | Mu.LinuxLoad (a, ptr, mo) -> LinuxLoad { ty = act a; ptr = pexpr ptr; mo }
    | Mu.LinuxStore (a, ptr, value, mo) ->
        LinuxStore { ty = act a; ptr = pexpr ptr; value = pexpr value; mo }
    | Mu.LinuxRMW (a, ptr, value, mo) ->
        LinuxRMW { ty = act a; ptr = pexpr ptr; value = pexpr value; mo }

  let paction (Mu.Paction (polarity, Mu.Action (loc, a_))) : action =
    { loc; polarity; action = action_ a_ }

  (* [Cn.Request] → our {!Request}. CN keeps [Owned] as a resource [name] whose
     pointer is a lone argument; we hoist [Owned] to its own request kind (which
     carries no iargs), and fold a user predicate's pointer into the head of its
     [iargs]. Quantified requests pass through. *)
  let request_init : Cn.Request.init -> Request.init = function
    | Init -> Init
    | Uninit -> Uninit

  let request_predicate (p : Cn.Request.Predicate.t) : Request.t =
    match p.name with
    | Owned (ty, init) ->
        if not (List.is_empty p.iargs) then
          failwith "Of_mucore.request: Owned resource with input arguments";
        Owned { ty; kind = request_init init; ptr = p.pointer }
    | PName name -> P { name; iargs = p.pointer :: p.iargs }

  let qpredicate (q : Cn.Request.QPredicate.t) : Request.QPredicate.t =
    let name =
      match q.name with
      | Owned (ty, init) -> Request.QPredicate.QOwned (ty, request_init init)
      | PName s -> QPName s
    in
    {
      name;
      pointer = q.pointer;
      q = q.q;
      step = q.step;
      permission = q.permission;
      iargs = q.iargs;
    }

  let request : Cn.Request.t -> Request.t = function
    | P p -> request_predicate p
    | Q q -> Q (qpredicate q)

  let request_resource ((req, bt) : Cn.Request.t * BaseTypes.t) :
      Request.t * BaseTypes.t =
    (request req, bt)

  (* pack/unpack only applies to user predicates; an [Owned] resource here — in
     either form — is an invalid program. *)
  let predicate_or_predicate_name :
      Cnstatement.predicate_or_predicate_name -> predicate_or_predicate_name =
    let invalid () =
      failwith "Of_mucore: pack/unpack of an Owned resource is not valid"
    in
    function
    | Cnstatement.Predicate p -> (
        match request_predicate p with
        | Owned _ -> invalid ()
        | req -> Predicate req)
    | Cnstatement.PredicateName (PName s) -> PredicateName s
    | Cnstatement.PredicateName (Owned _) -> invalid ()

  let cn_statement : Cnstatement.statement -> cn_statement = function
    | Cnstatement.Pack_unpack (pu, p) ->
        Pack_unpack (pu, predicate_or_predicate_name p)
    | Cnstatement.To_from_bytes (tf, p) ->
        To_from_bytes (tf, request_predicate p)
    | Cnstatement.Have lc -> Have lc
    | Cnstatement.Instantiate (i, it) -> Instantiate (i, it)
    | Cnstatement.Split_case lc -> Split_case lc
    | Cnstatement.Extract (attrs, e, it) -> Extract (attrs, e, it)
    | Cnstatement.Unfold (s, args) -> Unfold (s, args)
    | Cnstatement.Apply (s, args) -> Apply (s, args)
    | Cnstatement.Assert lc -> Assert lc
    | Cnstatement.Inline nms -> Inline nms
    | Cnstatement.Print it -> Print it

  (* Flatten the [Let] spine of hoisted loads, then translate the terminal
     [Pure] statement at the bottom. *)
  let cn_prog (p : Cnstatement.statement Cnprog.t) : cn_prog =
    let rec aux acc (p : Cnstatement.statement Cnprog.t) =
      match p with
      | Cnprog.Let (loc, (sym, load), rest) ->
          let ({ ct; pointer } : Cnprog.load) = load in
          aux ({ loc; sym; ct; pointer } :: acc) rest
      | Cnprog.Pure (loc, stmt) ->
          { loads = List.rev acc; loc; stmt = cn_statement stmt }
    in
    aux [] p

  (* Discarded [pure(unit)] sequencing steps are folded out as each [expr] is
     built, never constructed and then simplified — so these predicates inspect
     the source [Mu] AST directly, before conversion. *)
  let is_mu_wildcard (Mu.Pattern (_, _, _, p_)) =
    match p_ with Mu.CaseBase (None, _) -> true | _ -> false

  let mu_is_pure_unit (Mu.Expr (_, _, _, e_)) =
    match e_ with
    | Mu.Epure (Mu.Pexpr (_, _, _, Mu.PEval (Mu.V (_, Mu.Vunit)))) -> true
    | _ -> false

  (* [Esseq] is routed through {!build_sseq} so discarded units are elided at
     construction; every other form is the plain structural map of {!expr_}. *)
  let rec expr (Mu.Expr (loc, annots, _, e_)) : expr =
    match e_ with
    | Mu.Esseq (pat, e1, e2) -> build_sseq ~loc ~annots pat e1 (expr e2)
    | _ -> { loc; annots; node = expr_ e_ }

  (* Build the strong sequence [let strong pat = e1 in body], dropping a
     discarded trailing [pure(unit)]. CN emits these unit "results" of void
     statements everywhere; when [pat] is a wildcard, [e1]'s result is thrown
     away, so if [e1]'s sequence tail is [pure(unit)] we splice [body] straight
     into that slot ({!splice_unit_tail}) rather than bind a dead unit. The unit
     node is never built and no second pass runs. Evaluation order and result are
     unchanged; symbols being globally unique, extending an inner binder's scope
     over [body] captures nothing. *)
  and build_sseq ~loc ~annots pat e1 (body : expr) : expr =
    let plain () =
      { loc; annots; node = Esseq { pat = pattern pat; value = expr e1; body } }
    in
    if is_mu_wildcard pat then
      match splice_unit_tail e1 ~body with Some e -> e | None -> plain ()
    else plain ()

  (* [Some e]: [e1] converted with its trailing [pure(unit)] — found along the
     sequence's body spine — replaced by [body]. [None]: [e1] has no trailing
     unit, nothing to drop. The [Option.map] short-circuits, so when the spine
     does not bottom out in a unit, none of [e1]'s value sides are converted here
     (the caller converts [e1] once, plainly); when it does, the spine is rebuilt
     via {!build_sseq}, which re-elides any nested discards on the way. *)
  and splice_unit_tail e1 ~(body : expr) : expr option =
    if mu_is_pure_unit e1 then Some body
    else
      match e1 with
      | Mu.Expr (loc, annots, _, Mu.Esseq (pat, a, b)) ->
          Option.map
            (fun tail -> build_sseq ~loc ~annots pat a tail)
            (splice_unit_tail b ~body)
      | _ -> None

  (* [Esseq] never reaches here — {!expr} intercepts it — but the case is kept so
     this stays a total [Mu.expr_ -> expr_] map. *)
  and expr_ = function
    | Mu.Epure pe -> Epure (pexpr pe)
    | Mu.Ememop (m, pes) -> Ememop (m, List.map pexpr pes)
    | Mu.Eaction pa -> Eaction (paction pa)
    | Mu.Eskip -> Eskip
    | Mu.Eccall (a, fn, args, specs) ->
        Eccall { ty = act a; fn = pexpr fn; args = List.map pexpr args; specs }
    | Mu.Eproc (name, pes) -> Eproc (name, List.map pexpr pes)
    | Mu.Elet (pat, v, b) ->
        Elet { pat = pattern pat; value = pexpr v; body = expr b }
    | Mu.Eunseq es -> Eunseq (List.map expr es)
    | Mu.Ewseq (pat, e1, e2) ->
        Ewseq { pat = pattern pat; value = expr e1; body = expr e2 }
    | Mu.Esseq (pat, e1, e2) ->
        Esseq { pat = pattern pat; value = expr e1; body = expr e2 }
    | Mu.Eif (c, t, e) -> Eif { cond = pexpr c; then_ = expr t; else_ = expr e }
    | Mu.Ebound e -> Ebound (expr e)
    | Mu.End es -> End (List.map expr es)
    | Mu.Erun (s, pes) -> Erun (s, List.map pexpr pes)
    | Mu.CN_progs (_stmts, progs) -> CN_progs (List.map cn_prog progs)

  (* Flatten the cons-list argument types into [arguments] + the final body. *)
  let rec arguments_l :
      'i 'j.
      ('i -> 'j) ->
      'i Mu.arguments_l ->
      (logical_arg * Locations.info) list * 'j =
   fun f -> function
    | Mu.Define ((s, it), info, rest) ->
        let l, b = arguments_l f rest in
        ((Define (s, it), info) :: l, b)
    | Mu.Resource ((s, rbt), info, rest) ->
        let l, b = arguments_l f rest in
        ((Resource (s, request_resource rbt), info) :: l, b)
    | Mu.Constraint (lc, info, rest) ->
        let l, b = arguments_l f rest in
        ((Constraint lc, info) :: l, b)
    | Mu.I i -> ([], f i)

  let rec logical_argument_types_l :
      'i 'j.
      ('i -> 'j) ->
      'i LogicalArgumentTypes.t ->
      (logical_arg * Locations.info) list * 'j =
   fun f -> function
    | Define ((s, it), info, rest) ->
        let l, b = logical_argument_types_l f rest in
        ((Define (s, it), info) :: l, b)
    | Resource ((s, rbt), info, rest) ->
        let l, b = logical_argument_types_l f rest in
        ((Resource (s, request_resource rbt), info) :: l, b)
    | Constraint (lc, info, rest) ->
        let l, b = logical_argument_types_l f rest in
        ((Constraint lc, info) :: l, b)
    | I i -> ([], f i)

  let rec arguments : 'i 'j. ('i -> 'j) -> 'i Mu.arguments -> arguments * 'j =
   fun f -> function
    | Mu.Computational ((s, bt), info, rest) ->
        let a, b = arguments f rest in
        ({ a with comp = (Computational (s, bt), info) :: a.comp }, b)
    | Mu.Ghost ((s, bt), info, rest) ->
        let a, b = arguments f rest in
        ({ a with comp = (Ghost (s, bt), info) :: a.comp }, b)
    | Mu.L l ->
        let logic, b = arguments_l f l in
        ({ comp = []; logic }, b)

  (* The same flattening over [Cn.ArgumentTypes]/[Cn.LogicalArgumentTypes],
     which are structurally identical to [Mu.arguments] but nominally distinct.
     Used to turn [ArgumentTypes.ft]/[lemmat] into [arguments] + a tail. *)

  let logical_return_type : LogicalReturnTypes.t -> logical_return =
    let rec aux = function
      | LogicalReturnTypes.Define ((s, it), info, rest) ->
          (Define (s, it), info) :: aux rest
      | LogicalReturnTypes.Resource ((s, rbt), info, rest) ->
          (Resource (s, request_resource rbt), info) :: aux rest
      | LogicalReturnTypes.Constraint (lc, info, rest) ->
          (Constraint lc, info) :: aux rest
      | LogicalReturnTypes.I -> []
    in
    aux

  let return_type (ReturnTypes.Computational ((s, bt), info, lrt)) : return_type
      =
    { ret = (s, bt); ret_info = info; logic = logical_return_type lrt }

  let rec argument_types_l :
      'i 'j. ('i -> 'j) -> 'i LogicalArgumentTypes.t -> logical_return * 'j =
   fun f -> function
    | LogicalArgumentTypes.Define ((s, it), info, rest) ->
        let l, b = argument_types_l f rest in
        ((Define (s, it), info) :: l, b)
    | LogicalArgumentTypes.Resource ((s, rbt), info, rest) ->
        let l, b = argument_types_l f rest in
        ((Resource (s, request_resource rbt), info) :: l, b)
    | LogicalArgumentTypes.Constraint (lc, info, rest) ->
        let l, b = argument_types_l f rest in
        ((Constraint lc, info) :: l, b)
    | LogicalArgumentTypes.I i -> ([], f i)

  let rec argument_types :
      'i 'j. ('i -> 'j) -> 'i ArgumentTypes.t -> arguments * 'j =
   fun f -> function
    | ArgumentTypes.Computational ((s, bt), info, rest) ->
        let a, b = argument_types f rest in
        ({ a with comp = (Computational (s, bt), info) :: a.comp }, b)
    | ArgumentTypes.Ghost ((s, bt), info, rest) ->
        let a, b = argument_types f rest in
        ({ a with comp = (Ghost (s, bt), info) :: a.comp }, b)
    | ArgumentTypes.L l ->
        let logic, b = argument_types_l f l in
        ({ comp = []; logic }, b)

  let trusted = function Mu.Trusted loc -> Trusted loc | Mu.Checked -> Checked

  let pmap_to_symmap conv m =
    Pmap.fold (fun k v acc -> Sym.Map.add k (conv v) acc) m Sym.Map.empty

  let label_def = function
    | Mu.Non_inlined (loc, label, annot, mu_args) ->
        let args, body = arguments expr mu_args in
        Non_inlined { loc; label; annot; args; body }
    | Mu.Return loc -> Return loc
    | Mu.Loop (loc, mu_args, annots, `Aux_info (l1, l2, b)) ->
        let args, body = arguments expr mu_args in
        Loop
          {
            loc;
            args;
            body;
            annots;
            info = { condition_loc = l1; loop_loc = l2; has_invariant = b };
          }

  let fun_map_decl = function
    | Mu.Proc { loc; args_and_body = ab; trusted = tr } ->
        let args, (e, labels, rt) = arguments (fun x -> x) ab in
        Proc
          {
            loc;
            args;
            body = expr e;
            labels = pmap_to_symmap label_def labels;
            return_type = return_type rt;
            trusted = trusted tr;
          }
    | Mu.ProcDecl (loc, ft) ->
        ProcDecl (loc, Option.map (argument_types return_type) ft)

  let globs = function
    | Mu.GlobalDef (ct, e) -> GlobalDef (ct, expr e)
    | Mu.GlobalDecl ct -> GlobalDecl ct

  let tag_definition = function
    | Mu.StructDef sl -> StructDef sl
    | Mu.UnionDef -> UnionDef

  let datatype ({ loc; cases } : Mu.datatype) : datatype = { loc; cases }

  let function_to_convert
      ({ loc; c_fun_sym; l_fun_sym } : Mu.function_to_convert) :
      function_to_convert =
    { loc; c_fun_sym; l_fun_sym }

  let clause ({ loc; guard; packing_ft } : Definition.Clause.t) : clause =
    let logical_args, ret = logical_argument_types_l Fun.id packing_ft in
    let logical_args = List.map fst logical_args in
    { loc; guard; logical_args; ret }

  let predicate_def
      ({ loc; pointer; iargs; oarg; clauses; recursive; attrs } :
        Definition.Predicate.t) : predicate_def =
    let clauses = Option.map (List.map clause) clauses in
    (* CN keeps the predicate's pointer separate; we make it the first iarg. *)
    let iargs = (pointer, BaseTypes.Loc ()) :: iargs in
    { loc; iargs; oarg; clauses; recursive; attrs }

  let file (f : unit Mu.file) : file =
    {
      main = f.main;
      tag_defs = pmap_to_symmap tag_definition f.tagDefs;
      globs = List.map (fun (s, g) -> (s, globs g)) f.globs;
      funs = pmap_to_symmap fun_map_decl f.funs;
      extern = f.extern;
      stdlib_syms = Sym.Set.of_list (Cn.Sym.Set.elements f.stdlib_syms);
      mk_functions = List.map function_to_convert f.mk_functions;
      resource_predicates =
        List.map (fun (s, d) -> (s, predicate_def d)) f.resource_predicates;
      logical_predicates = f.logical_predicates;
      datatypes = List.map (fun (s, d) -> (s, datatype d)) f.datatypes;
      lemmata =
        List.map
          (fun (s, (loc, lemmat)) ->
            (s, (loc, argument_types logical_return_type lemmat)))
          f.lemmata;
      call_funinfo = pmap_to_symmap (fun x -> x) f.call_funinfo;
    }
end

let of_mucore : unit Cn.Mucore.file -> file = Of_mucore.file
