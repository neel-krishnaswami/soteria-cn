module State_here = State
open Soteria_c_vendor
module State = State_here
open Soteria.Soteria_std
open Soteria.Logs.Import
open Syntaxes.FunctionWrap
module Mu = Usable_mucore
open Mu
module Diagnostic = Soteria.Terminal.Diagnostic
module Or_gave_up = Soteria.Symex.Or_gave_up

let with_extra_call_trace ~loc ~msg : 'a Csymex.t -> 'a Csymex.t =
  Csymex.Result.map_error @@ fun (e, tr) ->
  let elem = Soteria.Terminal.Call_trace.mk_element ~loc ~msg () in
  (e, elem :: tr)

let verif_process ~loc ?ghost_args ~(args : Mu.arguments) ~return_type ~labels
    ~body () =
  let open Csymex in
  let open Syntax in
  let@@ () = with_extra_call_trace ~loc ~msg:"Verifying function" in
  [%l.debug "Producing pre-condition"];
  let* subst, state =
    (* For a label obligation, first bring the enclosing function's binders and
       pure constraints into scope (without its resources), as CN does. *)
    match ghost_args with
    | None -> Csymex.return (Subst.empty, State.empty)
    | Some fargs -> Cn_assert.produce_arguments ~ghost_resources:true fargs
  in
  let* subst, state = Cn_assert.produce_arguments ~subst ~state args in
  [%l.debug
    "@[<v 2>About to execute function body with:@ @[<v 2>subst: %a@]@ @[<v \
     2>state: %a@]@]"
    Subst.pp subst
      (Fmt.Dump.option @@ State.pp_pretty ~ignore_freed:true)
      state];
  Csymex.log_solver_state ~level:Trace ();
  let** result, state =
    State.SM.Result.run_with_state ~state
    @@ Minterp.eval_expr ~labels subst body
    |> Result.map_error (fun ((err, tr), _) -> ((err :> Cn_error.t), tr))
    |> Result.map_missing (fun x ->
        [%l.error "Missing resource during function execution"];
        x)
  in
  match result with
  | Minterp.ExprM.Jumped ->
      (* Invariant consumed and footprint checked empty at the jump. *)
      Result.ok ()
  | _ ->
  let ret = Minterp.ExprM.returned_value result in
  let** (), state =
    State.SM.Result.run_with_state ~state
      (Cn_assert.consume_return_type ~subst return_type ret)
    |> Result.map_error (fun ((err, tr), _) -> ((err :> Cn_error.t), tr))
    |> Result.map_missing (fun x ->
        [%l.error "Missing resource during postcondition consumption"];
        x)
  in
  let fn_call_trace elements =
    elements
    @ [
        Soteria.Terminal.Call_trace.mk_element ~loc
          ~msg:"Memory leftover after this function" ();
      ]
  in
  match State.leaks state with
  | [] -> Result.ok ()
  | leaks ->
      [%l.debug
        "@[<v 2>Memory leak in state:@ %a@]" (Fmt.Dump.option @@ State.pp) state];
      let elems =
        List.filter_map
          (Option.map (fun loc ->
               Soteria.Terminal.Call_trace.mk_element ~loc
                 ~msg:"Memory allocated here leaked" ()))
          leaks
      in
      Result.error (`Memory_leak, fn_call_trace elems)

let print_diagnostic ~fid ~call_trace ~error =
  let msg = Fmt.str "%a in %s" Cn_error.pp error fid in
  Soteria.Terminal.Diagnostic.print_diagnostic ~call_trace
    ~as_ranges:Error.Diagnostic.as_ranges ~msg
    ~severity:(Cn_error.severity error)

let print_errors ~entry_point (res : (_, _, _) Compo_res.t) =
  match res with
  | Compo_res.Ok () -> ()
  | Compo_res.Error (Or_gave_up.E (err, trace)) ->
      print_diagnostic ~fid:entry_point ~call_trace:trace ~error:err
  | Compo_res.Error (Or_gave_up.Gave_up msg) ->
      print_diagnostic ~fid:entry_point
        ~call_trace:Soteria.Terminal.Call_trace.empty ~error:(`Gave_up msg)
  | Compo_res.Missing _ ->
      Diagnostic.print_diagnostic_simple ~severity:Error
        "Missing resource (under-specified)"

(* Verify a single (non-trusted) function, returning every branch outcome. *)
let verify_fn ~fuel:_ ~loc (_name : Sym.t) args return_type labels body =
  [%l.debug
    "@[<v 2>verify_fn:@.arguments: %a@.return_type: %a@]" Mu.pp_arguments args
      Mu.pp_return_type return_type];
  [%l.debug
    "@[<v 2>Specifically within:@ ret: %a@ logic: %a@]" Mu.pp_bt
      (snd return_type.ret) Mu.pp_logical_return return_type.logic];
  let run process =
    Csymex.Result.run ~fail_fast:true ~mode:OX ~stats:Caller process
  in
  let main =
    run (verif_process ~loc ~args ~return_type ~labels ~body ())
  in
  (* Each loop label is its own obligation: produce its argument type (the
     invariant) and verify its body under the same label context. *)
  let label_obligations =
    Sym.Map.fold
      (fun _ def acc ->
        match def with
        | Mu.Loop { loc = lloc; args = largs; body = lbody; _ } ->
            acc
            @ run
                (verif_process ~loc:lloc ~ghost_args:args ~args:largs
                   ~return_type ~labels ~body:lbody ())
        | Non_inlined _ | Return _ -> acc)
      labels []
  in
  main @ label_obligations

let name_of Cerb_frontend.Symbol.(Symbol (_, _, sd)) =
  match sd with SD_Id name -> name | _ -> ""

let non_existing_functions (prog : Mu.file) (names : string list) : string list
    =
  Sym.Map.fold
    (fun name _ (acc : string list) ->
      List.filter (fun n -> name_of name <> n) acc)
    prog.funs names

let warn_non_existing prog fns =
  match fns with
  | None -> ()
  | Some names ->
      let non_existing = non_existing_functions prog names in
      List.iter
        (fun name ->
          [%l.warn
            "Function %s specified in the command line does not exist" name])
        non_existing

(* Verify every checked function of [prog], skipping the ones the user marked as
   trusted as well as the bare declarations (which have no body to check), and
   printing a diagnostic for each branch outcome. When [only] is non-empty, only
   the functions whose (human-readable) name appears in it are verified; a
   warning is emitted for any requested name that does not exist in [prog]. *)
let verify_prog ~fuel ?only (prog : Mu.file) : (unit, string) Result.t =
  let@ () = Soteria.Stats.As_ctx.with_dumped () in
  warn_non_existing prog only;
  let selected =
    match only with
    | None -> fun _ -> true
    | Some only -> fun n -> List.mem n only
  in
  Sym.Map.iter
    (fun name decl ->
      if not (selected (name_of name)) then ()
      else
        match decl with
        | Proc { trusted = Checked; args; return_type; body; labels; loc } ->
            Fmt.pr "Verifying function %a...\n@?" Sym.pp_hum name;
            let name_str = name_of name in
            let has_bugs = ref false in
            verify_fn ~fuel ~loc name args return_type labels body
            |> List.iter (fun (r, _pc) ->
                print_errors ~entry_point:name_str r;
                if not (Compo_res.is_ok r) then has_bugs := true);
            if not !has_bugs then
              Fmt.pr "%a\n" Soteria.Logs.Printers.pp_ok
                (Fmt.str "Successfully verified %a@?" Sym.pp_hum name)
        | Proc { trusted = Trusted loc; _ } ->
            L.info (fun m ->
                m "Skipping trusted function %a (%a)" Sym.pp_hum name pp_loc loc)
        | ProcDecl _ -> ())
    prog.funs;
  Ok ()
