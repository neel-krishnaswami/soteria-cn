open Cmdliner
open Soteria.Soteria_std.Cmdliner_helpers

let result_to_int (x : (_, _) result) : int =
  match x with Ok _ -> 0 | Error _ -> 1

module Exec_main = struct
  let file_arg = Arg.(value & pos 0 (some file) None & info ~docv:"FILE" [])

  let entry_point_arg =
    let doc = "Entry point of the program to execute" in
    let docv = "ENTRYPOINT" in
    Arg.(
      value & opt string "main"
      & info
          [ "entry"; "entry-point"; "harness" ]
          ~docs:Sections.frontend ~doc ~docv)

  let term =
    Term.(
      const Soteria_cn.Driver.exec_main
      $ Soteria.Config.cmdliner_term ()
      $ Soteria_c_vendor.Config.cmdliner_term ()
      $ Soteria.Symex.Fuel_gauge.Cli.term
          ~default:Soteria.Symex.Fuel_gauge.infinite ()
      $ file_arg)

  let cmd =
    Cmd.v
      (Cmd.info
         ~doc:"Symbolically execute a program starting from the main function."
         "exec")
      (Term.map result_to_int term)
end

module Verify = struct
  let file_arg = Arg.(value & pos 0 (some file) None & info ~docv:"FILE" [])

  let functions_arg =
    let doc =
      "Restrict verification to the function named $(docv). May be given \
       several times to verify a list of functions. If omitted, every \
       (non-trusted) function is verified."
    in
    Arg.(
      value & opt_all string [] & info [ "f"; "function" ] ~docv:"FUNCTION" ~doc)

  let term =
    Term.(
      const Soteria_cn.Driver.verify
      $ Soteria.Config.cmdliner_term ()
      $ Soteria_c_vendor.Config.cmdliner_term ()
      $ Soteria.Symex.Fuel_gauge.Cli.term
          ~default:Soteria.Symex.Fuel_gauge.infinite ()
      $ functions_arg $ file_arg)

  let cmd =
    Cmd.v
      (Cmd.info
         ~doc:
           "Verify each (non-trusted) function of a program against its CN \
            specification."
         "verify")
      (Term.map result_to_int term)
end

module Show_mucore = struct
  let file_arg = Arg.(value & pos 0 (some file) None & info ~docv:"FILE" [])

  let term =
    Term.(
      const Soteria_cn.Driver.show_mucore
      $ Soteria.Config.cmdliner_term ()
      $ Soteria_c_vendor.Config.cmdliner_term ()
      $ file_arg)

  let cmd =
    Cmd.v
      (Cmd.info ~doc:"Parse a program and display its Mucore representation."
         "show-mucore")
      (Term.map result_to_int term)
end

let arg = try Sys.argv.(1) with _ -> failwith "No argument provided"

let cmd =
  Cmd.group (Cmd.info "soteria-cn")
    [ Exec_main.cmd; Verify.cmd; Show_mucore.cmd ]

let () = exit @@ Cmd.eval' cmd
