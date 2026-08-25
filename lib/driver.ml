open Soteria.Soteria_std
module CF = Cerb_frontend
module CB = Cerb_backend
open CB.Pipeline
open Cn
open Setup
open Syntaxes.FunctionWrap

module Frontend = struct
  (* Run Cerberus' C frontend and Core elaboration on [filename], then rewrite the
   resulting Core program down to the Milicore representation that
   [Core_to_mucore.normalise_file] expects. This is a trimmed-down copy of
   [cn/bin/common.ml]'s [frontend], keeping only what is needed to obtain the
   Mucore AST (no Coq export, CSV timing, etc.). The CLI knobs are fixed to the
   values CN uses by default. *)
  let frontend ~filename =
    Cerb_global.set_cerb_conf ~backend_name:"Cn" ~exec:false
      (* execution mode *) Random ~concurrency:false (* error verbosity *) Basic
      ~defacto:false ~permissive:false ~agnostic:false ~ignore_bitfields:false;
    CF.Ocaml_implementation.set CF.Ocaml_implementation.HafniumImpl.impl;
    CF.Switches.set [ "inner_arg_temps"; "at_magic_comments" ];
    let return = CF.Exception.except_return in
    let ( let@ ) = CF.Exception.except_bind in
    let@ stdlib = load_core_stdlib () in
    let@ impl = load_core_impl stdlib impl_name in
    let conf =
      Setup.conf "cc" [] [] [] (* disable_linemarkers *) false []
        (* save_cpp *) None
    in
    let cn_init_scope : CF.Cn_desugaring.init_scope =
      {
        predicates = [ Alloc.Predicate.(str, sym, Some loc) ];
        functions =
          List.map (fun (str, sym) -> (str, sym, None)) Builtins.fun_names;
        idents = [ Alloc.History.(str, sym, None) ];
      }
    in
    let@ _cabs_tunit_opt, ail_prog_opt, prog0 =
      c_frontend_and_elaboration ~cn_init_scope (conf, io) (stdlib, impl)
        ~filename
    in
    let@ () =
      if conf.typecheck_core then
        let@ _ = CF.Core_typing.typecheck_program prog0 in
        return ()
      else return ()
    in
    let markers_env, ail_prog = Option.get ail_prog_opt in
    CF.Tags.set_tagDefs prog0.CF.Core.tagDefs;
    (* Mandatory: [Core_to_mucore] has no case for [Ecase], which Core elaboration
     emits around possibly-unspecified values. This pass rewrites them away. *)
    let prog1 = CF.Remove_unspecs.rewrite_file prog0 in
    let prog2 = CF.Milicore.core_to_micore__file Locations.update prog1 in
    let prog3 = CF.Milicore_label_inline.rewrite_file prog2 in
    return (markers_env, ail_prog, prog3)

  let handle_frontend_error = function
    | CF.Exception.Exception err ->
        prerr_endline (CF.Pp_errors.to_string err);
        exit 2
    | CF.Exception.Result result -> result

  (* Load [file] and elaborate it all the way down to CN's Mucore AST, which
   carries the user's CN annotations (function specs, loop invariants, inline
   asserts, ...). *)
  let load_mucore_ast file : unit Mucore.file =
    let markers_env, ail_prog, prog2 =
      handle_frontend_error (frontend ~filename:file)
    in
    match
      Core_to_mucore.normalise_file ~inherit_loc:true
        (markers_env, snd ail_prog)
        prog2
    with
    | Ok prog3 -> prog3
    | Error err ->
        TypeErrors.report_pretty err;
        exit 1
end

(* Helper for all main entry points *)
let initialise ?soteria_config mode config f =
  Option.iter Soteria.Config.set_and_lock soteria_config;
  let@ () = Soteria_c_vendor.Config.with_config ~config ~mode in
  Soteria.Stats.As_ctx.with_dumped () f

(* Parse [file] down to the (Usable) Mucore AST and pretty-print it, without
   running any symbolic execution. *)
let show_mucore config c_config file =
  let open Soteria_c_vendor in
  let open Syntaxes.Result in
  let* file = Option.to_result ~none:"No input file provided" file in
  let@ () = initialise ~soteria_config:config Whole_program c_config in
  let mucore_file = Frontend.load_mucore_ast file in
  let umucore = Usable_mucore.of_mucore mucore_file in
  Fmt.pr "%a@.@?" Usable_mucore.pp_file umucore;
  Ok ()

(* ── Rocq lemma-obligation export (reuses CN's Lemmata module) ── *)

(* Build the slice of [Cn.Global.t] that [Cn.Lemmata.generate] reads
   (struct_decls, datatypes(+constrs), resource predicates, logical
   functions); the order fields and fun_decls are unused by it. *)
let build_global (mu : unit Mucore.file) : Global.t =
  let struct_decls =
    Pmap.fold
      (fun s (def : Mucore.tag_definition) acc ->
        match def with
        | StructDef l -> Sym.Map.add s l acc
        | UnionDef -> acc)
      mu.tagDefs Sym.Map.empty
  in
  let datatypes, datatype_constrs =
    List.fold_left
      (fun (dts, ctors) ((s, dt) : _ * Mucore.datatype) ->
        let dts =
          Sym.Map.add s
            BaseTypes.Datatype.
              {
                constrs = List.map fst dt.cases;
                all_params = List.concat_map snd dt.cases;
              }
            dts
        in
        let ctors =
          List.fold_left
            (fun ctors (c, params) ->
              Sym.Map.add c BaseTypes.Datatype.{ params; datatype_tag = s } ctors)
            ctors dt.cases
        in
        (dts, ctors))
      (Sym.Map.empty, Sym.Map.empty)
      mu.datatypes
  in
  let add_all xs m =
    List.fold_left (fun m (s, v) -> Sym.Map.add s v m) m xs
  in
  {
    Global.empty with
    struct_decls;
    datatypes;
    datatype_constrs;
    resource_predicates =
      add_all mu.resource_predicates Global.empty.resource_predicates;
    logical_functions = add_all mu.logical_predicates Sym.Map.empty;
    lemmata = add_all mu.lemmata Sym.Map.empty;
  }

let generate_lemmata ~out (mu : unit Mucore.file) : (unit, string) Result.t =
  (* [Lemmata.generate] raises [Failure] on lemmas whose coerced form it cannot
     translate (upstream CN crashes identically, e.g. on resource lemmas whose
     coercion introduces computational binders); fail cleanly instead. *)
  match Lemmata.generate (build_global mu) out mu.lemmata with
  | Ok () -> Ok ()
  | Error err ->
      TypeErrors.report_pretty err;
      Error "lemmata generation failed"
  | exception Failure msg -> Error ("lemmata generation failed: " ^ msg)

(* Compositionally verify CN function specifications. [functions] optionally
   restricts verification to the named functions; an empty list verifies all. *)
let verify (config : Soteria.Config.t) c_config fuel lemmata_out functions file
    =
  let open Syntaxes.Result in
  let functions = match functions with [] -> None | l -> Some l in
  let* file = Option.to_result ~none:"No input file provided" file in
  let fuel = Soteria.Symex.Fuel_gauge.Cli.validate_or_exit fuel in
  let@ () = initialise ~soteria_config:config Compositional c_config in
  let mucore_file =
    let@ () = Soteria.Stats.As_ctx.add_time_of_to "soteria-cn.parsing_time" in
    Frontend.load_mucore_ast file
  in
  let* () =
    match lemmata_out with
    | None -> Ok ()
    | Some out -> generate_lemmata ~out mucore_file
  in
  let umucore = Usable_mucore.of_mucore mucore_file in
  let@ () =
    Soteria.Stats.As_ctx.add_time_of_to "soteria-cn.verification_time"
  in
  let@ () = Ctx.run_with_prog umucore in
  Verify.verify_prog ~fuel ?only:functions umucore

let exec_main (config : Soteria.Config.t) c_config fuel file =
  let module SState = State in
  let open Soteria_c_vendor in
  let open Syntaxes.Result in
  let* file = Option.to_result ~none:"No input file provided" file in
  let fuel = Soteria.Symex.Fuel_gauge.Cli.validate_or_exit fuel in
  let@ () = initialise ~soteria_config:config Whole_program c_config in
  let mucore_file = Frontend.load_mucore_ast file in
  let umucore = Usable_mucore.of_mucore mucore_file in
  let* main = Option.to_result ~none:"No main function" umucore.main in
  let main = Symbol_std.Map.find main umucore.funs in
  let results =
    let@ () = Ctx.run_with_prog umucore in
    let computation = Minterp.exec_fun main [] in
    let computation =
      SState.SM.Result.run_with_state ~state:SState.empty computation
    in
    Csymex.Result.run ~stats:(Dump ()) ~fuel ~mode:OX computation
  in
  let has_errors = ref false in
  List.iter
    (function
      | Compo_res.Ok (v, _), _ ->
          Fmt.pr "Successfully finished with %a@\n@?" Core_value.pp v
      | Error (Soteria.Symex.Or_gave_up.E ((err, call_trace), _st)), _ ->
          has_errors := true;
          Verify.print_diagnostic ~fid:"main" ~call_trace ~error:err
      | Error (Gave_up msg), _ ->
          has_errors := true;
          Verify.print_diagnostic ~fid:"main"
            ~call_trace:Soteria.Terminal.Call_trace.empty ~error:(`Gave_up msg)
      | Missing _, _ -> Fmt.failwith "Can't miss at the moment")
    results;
  if !has_errors then Error "Didn't finish"
  else (
    Fmt.pr "Finished without errors!@?";
    Ok ())
