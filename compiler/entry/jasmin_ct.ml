open Jasmin
open Cmdliner
open CommonCLI
open Utils

type model = 
  | CT
  | SCT_slh
  | SCT_dfence of bool (* true means patch *)

let parse_and_check arch call_conv =
  let module A = (val get_arch_module arch call_conv) in
  let check ~doit infer ct_list model outfile pass file =
    let prog = parse_and_compile (module A) pass file in
    match model with
    | CT ->
      let sigs, errs =
        Ct_checker_forward.ty_prog (A.is_ct_sopn ~doit) ~infer prog ct_list
      in
      Format.printf "/* Security types:\n@[<v>%a@]*/@."
        (pp_list "@ " (Ct_checker_forward.pp_signature prog))
        sigs;
      let on_err (loc, msg) =
        hierror ~loc:(Lone loc) ~kind:"constant type checker" "%t" msg
      in
      Stdlib.Option.iter on_err errs
    | SCT_slh ->
      begin match Sct_checker_forward.ty_prog (A.is_ct_sopn ~doit) prog ct_list with
      | exception Annot.AnnotationError (loc, code) ->
          hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | sigs ->
          Format.printf "/* Security types:\n@[<v>%a@]*/@."
            (pp_list "@ " Sct_checker_forward.pp_funty)
            sigs
      end
    | SCT_dfence false -> 
      begin match Dfence_checker_forward.ty_prog (A.is_ct_sopn ~doit) prog ct_list with
      | exception Annot.AnnotationError (loc, code) ->
          hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | sigs ->
          Format.printf "/* Security types:\n@[<v>%a@]*/@."
            (pp_list "@ " Dfence_checker_forward.pp_funty)
            sigs
      end
    | SCT_dfence true ->
      begin match Dfence_patch.patch_prog (A.is_ct_sopn ~doit) prog ct_list with
      | exception Annot.AnnotationError (loc, code) ->
          hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | prog, _ ->
        let fmt, close =
          match outfile with
          | None -> Format.std_formatter, fun () -> ()
          | Some f ->
              let out = open_out f in
              let fmt = Format.formatter_of_out_channel out in
              fmt, fun () -> close_out out
        in
        begin try
          BatPervasives.finally
            (fun () -> close ())
            (fun () -> Printer.pp_prog ~debug:false A.pointer_data A.asmOp fmt prog)
            ()
          with e ->
            BatPervasives.ignore_exceptions
              (fun() -> Option.map Unix.unlink outfile) ();
            raise e
        end
      end
  in
  fun infer ct_list model output compile file doit warn ->
    if not warn then nowarning ();
    let compile =
      if doit && compile < Compiler.PropagateInline then
        Compiler.PropagateInline
      else compile
    in
    match check ~doit infer ct_list model output compile file with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let infer =
  let doc = "Infer security contracts" in
  Arg.(value & flag & info [ "infer" ] ~doc)

let model =
  let alts = [ "normal", CT
             ; "speculative", SCT_slh
             ; "sct", SCT_slh
             ; "dfence", SCT_dfence false
             ; "dfence-patch", SCT_dfence true ] in
  let doc =
    "Constant time model.
    $(b,CT): constant time without speculation. 
    $(b,SCT_slh): speculative constant time (slh protection.
    $(b,SCT_dfence false): speculative constant time (dfence allowed).
    $(b,SCT_dfence true): speculative constant time (dfence allowed), try to patch the code."
  in
  Arg.(value & opt (Arg.enum alts) CT & info [ "m"; "model" ] ~doc)

let slice =
  let doc =
    "Only check the given function (and its dependencies). This argument may \
     be repeated to check many functions. If not given, all functions will be \
     checked."
  in
  Arg.(value & opt_all string [] & info [ "slice"; "only"; "on" ] ~doc)

let file =
  let doc = "The Jasmin source file to verify" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let output =
  let doc = "Output file. If not given, output will be printed on stdout." in
  Arg.(value & opt (some string) None & info [ "o"; "output" ] ~docv:"OUTPUT FILE" ~doc)

let doit =
  let doc = "Allow only DOIT instructions on secrets" in
  Arg.(value & flag & info [ "doit" ] ~doc)

let () =
  let doc = "Check Constant-Time security of Jasmin programs" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin-ct" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info
    Term.(
      const parse_and_check $ arch $ call_conv $ infer $ slice $ model $ output
      $ after_pass $ file $ doit $ warn)
  |> Cmd.eval |> exit
