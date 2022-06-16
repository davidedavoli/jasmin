open Utils
open Prog
open Glob_options

let preprocess reg_size asmOp p =
  let p =
    p |> Subst.remove_params |> Insert_copy_and_fix_length.doit reg_size
  in
  Typing.check_prog reg_size asmOp p;
  p

(* -------------------------------------------------------------------- *)

let parse_file reg_size asmOp_sopn fname =
  let env =
    List.fold_left Pretyping.Env.add_from Pretyping.Env.empty
      !Glob_options.idirs
  in
  Pretyping.tt_program reg_size asmOp_sopn env fname

(* -------------------------------------------------------------------- *)
let rec warn_extra_i pd asmOp i =
  match i.i_desc with
  | Cassgn (_, tag, _, _) | Copn (_, tag, _, _) -> (
      match tag with
      | AT_rename ->
          warning ExtraAssignment i.i_loc
            "@[<v>extra assignment introduced:@;<0 2>%a@]"
            (Printer.pp_instr ~debug:false pd asmOp)
            i
      | AT_inline ->
          hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
            "@[<v>AT_inline flag remains in instruction:@;<0 2>@[%a@]@]"
            (Printer.pp_instr ~debug:false pd asmOp)
            i
      | _ -> ())
  | Cif (_, c1, c2) | Cwhile (_, c1, _, c2) ->
      List.iter (warn_extra_i pd asmOp) c1;
      List.iter (warn_extra_i pd asmOp) c2
  | Cfor _ ->
      hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
        "for loop remains"
  | Ccall _ | Csyscall _ -> ()

let warn_extra_fd pd asmOp (_, fd) = List.iter (warn_extra_i pd asmOp) fd.f_body

(*--------------------------------------------------------------------- *)

let compile (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) visit_prog_after_pass prog cprog =
  let module Regalloc = Regalloc.Regalloc (Arch) in
  let module StackAlloc = StackAlloc.StackAlloc (Arch) in
  let fdef_of_cufdef fn cfd = Conv.fdef_of_cufdef (fn, cfd) in
  let cufdef_of_fdef fd = snd (Conv.cufdef_of_fdef fd) in

  let apply msg trans fn cfd =
    if !debug then Format.eprintf "START %s@." msg;
    let fd = fdef_of_cufdef fn cfd in
    if !debug then Format.eprintf "back to ocaml@.";
    let fd = trans fd in
    cufdef_of_fdef fd
  in

  let translate_var = Conv.var_of_cvar in

    let open Stack_alloc in
      let pp_pos fmt p =
        Z.pp_print fmt (Conv.z_of_pos p)
      in
      let rec pp_apexpr fmt e =
        let open Stack_alloc in
        let pp_btype fmt = function
          | Bool -> Format.fprintf fmt "bool"
          | U i  -> Format.fprintf fmt "u%i" (int_of_ws i)
          | Int  -> Format.fprintf fmt "int"
        in
        let pp_arr_access pp_gvar pp_expr pp_len fmt aa ws x e olen =
          let pp_len fmt = function
            | None -> ()
            | Some len -> Format.fprintf fmt " : %a" pp_len len in
          Format.fprintf fmt "%a%s[%a %a %a]"
            pp_gvar x
            (if aa = Warray_.AAdirect then "." else "")
            pp_btype (U ws) pp_expr e pp_len olen
        in
        let pp_pos_var fmt x =
          Format.fprintf fmt "#%a" pp_pos x
        in
        match e with
        | APconst i -> Z.pp_print fmt (Conv.z_of_cz i)
        | APbool b -> Format.fprintf fmt "%b" b
        | APvar v -> pp_pos_var fmt v
        | APget (aa, ws, x, e) -> pp_arr_access pp_apexpr pp_apexpr pp_pos fmt aa ws x e None
        | APsub (aa, ws, len, x, e) -> pp_arr_access pp_apexpr pp_apexpr pp_pos fmt aa ws x e (Some len)
        | APapp1 (op, e) -> Format.fprintf fmt "@[<h>(%s@ %a)@]" (PrintCommon.string_of_op1 op) pp_apexpr e
        | APapp2 (op, e1, e2)-> Format.fprintf fmt "@[(%a %s@ %a)@]" pp_apexpr e1 (PrintCommon.string_of_op2 op) pp_apexpr e2
        | APappN _ -> assert false
        | APif _ -> assert false
      in
        let pp_region fmt r =
          Format.fprintf fmt "{ slot = %a; wsize = %s; align = %b }"
            (Printer.pp_var ~debug:true) (Conv.var_of_cvar r.r_slot)
            (Prog.string_of_ws r.r_align)
            r.r_writable
        in
        let pp_abstract_slice fmt s =
          Format.fprintf fmt "[%a:%a]" pp_apexpr s.az_ofs pp_apexpr s.az_len
        in
        let pp_abstract_zone fmt z =
          Format.pp_print_list pp_abstract_slice fmt z
        in
        let _pp_zone fmt z =
          Format.fprintf fmt "{ z_ofs = %a; z_len = %a }"
            Z.pp_print (Conv.z_of_cz z.z_ofs)
            Z.pp_print (Conv.z_of_cz z.z_len)
        in
        let pp_sub_region fmt sr =
          Format.fprintf fmt "{ region = %a; zone = @[<h>%a@] }" pp_region sr.sr_region pp_abstract_zone sr.sr_zone
        in
        let print_trmap ii (trmap : Stack_alloc.table * Stack_alloc.Region.region_map) =
      let pp_tab fmt tab =
        let open Stack_alloc in
        let pp_bindings fmt bindings =
          Format.fprintf fmt "@[<v>";
          Var0.Mvar.fold (fun x ap () ->
            Format.fprintf fmt "@[<h>%a -> %a@]@,"
              (Printer.pp_var ~debug:true) (Conv.var_of_cvar (Obj.magic x))
              pp_apexpr ap) bindings ();
          Format.fprintf fmt "@]"
        in
        Format.fprintf fmt "@[<v>{ bindings:@;<2 4>%a@;<2 2>counter: %a@,}@]@." pp_bindings tab.bindings pp_pos tab.counter
      in
      let pp_rmap fmt rmap =
        let pp_region_var fmt vr =
          Format.fprintf fmt "@[<v>";
          Var0.Mvar.fold (fun x sr () ->
            Format.fprintf fmt "@[<h>%a -> %a@]@,"
              (Printer.pp_var ~debug:true) (Conv.var_of_cvar (Obj.magic x))
              pp_sub_region sr) vr ();
          Format.fprintf fmt "@]"
        in
        let pp_var_region fmt rv =
          let _pp_int fmt i =
            Z.pp_print fmt (Conv.z_of_cz i)
          in

          (*
          let pp_bytes fmt b =
            let pp_interval fmt i =
              Format.fprintf fmt "[%a, %a]" Z.pp_print (Conv.z_of_cz i.Byteset.imin) Z.pp_print (Conv.z_of_cz i.Byteset.imax)
            in
            Format.pp_print_list pp_interval fmt b
          in *)
          Format.fprintf fmt "@[<v>";
          Mr.fold (fun r bm () ->
            Var0.Mvar.fold (fun x s () ->
              let pp_status fmt s =
                let open Region in
                match s with
                | Valid -> Format.fprintf fmt "Valid"
                | Unknown -> Format.fprintf fmt "Unknown"
                | Borrowed z -> Format.fprintf fmt "Borrowed: @[<h>%a@]" (Format.pp_print_list pp_abstract_zone) z
              in
              Format.fprintf fmt "%a -> %a -> %a@,"
                (Printer.pp_var ~debug:true) (Conv.var_of_cvar (Obj.magic r).r_slot)
                (Printer.pp_var ~debug:true) (Conv.var_of_cvar (Obj.magic x))
                (* (Byteset.ByteSet.pp_bytes pp_int) b *)
                pp_status s
            ) bm ()
          ) rv ();
          Format.fprintf fmt "@]"
        in
        Format.fprintf fmt "@[<v>{ var_region:@;<2 4>%a@;<2 2>region_var:@;<2 4>%a@,}@]@." pp_region_var rmap.Region.var_region pp_var_region rmap.Region.region_var
      in
      Format.eprintf "@[<v>%a@,%a@,%a@]@." Location.pp_iloc (fst ii) pp_tab (fst trmap) pp_rmap (snd trmap)
    in

  let memory_analysis up : Compiler.stack_alloc_oracles =
    StackAlloc.memory_analysis
      (fun zs -> Conv.cstring_of_string (Format.asprintf "%a" (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp_abstract_zone) zs))
      (fun sr -> Conv.cstring_of_string (Format.asprintf "%a" pp_sub_region sr))
      (Printer.pp_err ~debug:!debug)
      ~debug:!debug
      (fun ii trmap -> print_trmap ii trmap; trmap)
      up
  in

  let global_regalloc fds =
    if !debug then Format.eprintf "START regalloc@.";
    let fds = List.map Conv.fdef_of_csfdef fds in

    CheckAnnot.check_stack_size fds;

    let fds =
      Regalloc.alloc_prog translate_var
        (fun _fd extra ->
          match extra.Expr.sf_save_stack with
          | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
          | Expr.SavedStackNone -> false)
        fds
    in
    let fds = List.map (fun (y, _, x) -> (y, x)) fds in
    let fds = List.map Conv.csfdef_of_fdef fds in
    fds
  in

  let pp_cuprog s cp =
    Conv.prog_of_cuprog cp |> visit_prog_after_pass ~debug:true s
  in

  let pp_csprog fmt cp =
    let p = Conv.prog_of_csprog cp in
    Printer.pp_sprog ~debug:true Arch.pointer_data Arch.asmOp fmt p
  in

  let pp_linear fmt lp = PrintLinear.pp_prog Arch.pointer_data Arch.asmOp fmt lp in

  let rename_fd ii fn cfd =
    let ii, _ = ii in
    let doit fd =
      let fd = Subst.clone_func fd in
      Subst.extend_iinfo ii fd
    in
    apply "rename_fd" doit fn cfd
  in

  let expand_fd fn cfd =
    let fd = Conv.fdef_of_cufdef (fn, cfd) in
    let vars, harrs = Array_expand.init_tbl fd in
    let cvar = Conv.cvar_of_var in
    let vars = List.map cvar (Sv.elements vars) in
    let arrs = ref [] in
    let doarr x (ws, xs) =
      arrs :=
        Array_expansion.
          {
            vi_v = cvar x;
            vi_s = ws;
            vi_n =
              List.map (fun x -> (cvar x).Var0.Var.vname) (Array.to_list xs);
          }
        :: !arrs
    in
    Hv.iter doarr harrs;

    let f_cc =
      match fd.f_cc with
      | Subroutine si ->
          (* Since some arguments/returns are expended we need to fix the info *)
          let tbl = Hashtbl.create 17 in
          let newpos = ref 0 in
          let mk_n x =
            match x.v_kind, x.v_ty with
            | Reg (_, Direct), Arr (_, n) -> n
            | _, _ -> 1
          in
          let doarg i x =
            Hashtbl.add tbl i !newpos;
            newpos := !newpos + mk_n x
          in
          List.iteri doarg fd.f_args;
          let doret o x =
            match o with
            | Some i -> [Some (Hashtbl.find tbl i)]
            | None -> List.init (mk_n (L.unloc x)) (fun _ -> None)
          in
          let returned_params =
            List.flatten (List.map2 doret si.returned_params fd.f_ret) in
          FInfo.Subroutine { returned_params }

      | _ -> fd.f_cc
    in
    let do_outannot x a =
      try
        let (_, va) = Hv.find harrs (L.unloc x) in
        List.init (Array.length va) (fun _ -> [])
      with Not_found -> [a] in
    let f_outannot = List.flatten (List.map2 do_outannot fd.f_ret fd.f_outannot) in
    let finfo = fd.f_loc, fd.f_annot, f_cc, f_outannot in
    { Array_expansion.vars; arrs = !arrs; finfo }
  in

  let refresh_instr_info fn f =
    (fn, f) |> Conv.fdef_of_cufdef |> refresh_i_loc_f |> Conv.cufdef_of_fdef |> snd
  in

  let warning ii msg =
    (if not !Glob_options.lea then
     let loc, _ = ii in
     warning UseLea loc "%a" Printer.pp_warning_msg msg);
    ii
  in

  let fresh_id _gd x =
    let x = Conv.var_of_cvar x in
    Prog.V.clone x
  in

  let split_live_ranges_fd fd = Regalloc.split_live_ranges fd in
  let renaming_fd fd = Regalloc.renaming fd in
  let remove_phi_nodes_fd fd = Regalloc.remove_phi_nodes fd in

  let removereturn sp =
    let fds, _data = Conv.prog_of_csprog sp in
    let tokeep = RemoveUnusedResults.analyse fds in
    tokeep
  in

  let is_reg_array x = is_reg_arr (Conv.var_of_cvar x) in

  let warn_extra s p =
    if s = Compiler.DeadCode_RegAllocation then
      let fds, _ = Conv.prog_of_csprog p in
      List.iter (warn_extra_fd Arch.pointer_data Arch.asmOp) fds
  in

  let slh_info up =
    let p = Conv.prog_of_cuprog up in
    let ttbl = Sct_checker_forward.compile_infer_msf p in
    fun fn ->
      try Hf.find ttbl fn with Not_found -> assert false
  in

  let cparams =
    {
      Compiler.string_of_sr =
        (fun sr -> Conv.cstring_of_string (Format.asprintf "%a" pp_sub_region sr));
      Compiler.string_of_borrowed = (fun zs -> Conv.cstring_of_string (Format.asprintf "%a" (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp_abstract_zone) zs));
      Compiler.rename_fd;
      Compiler.expand_fd;
      Compiler.split_live_ranges_fd =
        apply "split live ranges" split_live_ranges_fd;
      Compiler.renaming_fd = apply "alloc inline assgn" renaming_fd;
      Compiler.remove_phi_nodes_fd =
        apply "remove phi nodes" remove_phi_nodes_fd;
      Compiler.stack_register_symbol =
        Var0.Var.vname (Conv.cvar_of_var Arch.rsp_var);
      Compiler.global_static_data_symbol =
        Var0.Var.vname (Conv.cvar_of_var Arch.rip);
      Compiler.stackalloc = memory_analysis;
      Compiler.removereturn;
      Compiler.regalloc = global_regalloc;
      Compiler.print_uprog =
        (fun s p ->
          pp_cuprog s p;
          p);
      Compiler.print_sprog =
        (fun s p ->
          warn_extra s p;
          eprint s pp_csprog p;
          p);
      Compiler.print_linear =
        (fun s p ->
          eprint s pp_linear p;
          p);
      Compiler.refresh_instr_info;
      Compiler.warning;
      Compiler.lowering_opt = Arch.lowering_opt;
      Compiler.fresh_id;
      Compiler.fresh_var_ident = Conv.fresh_var_ident;
      Compiler.is_reg_array;
      Compiler.slh_info;
      Compiler.print_rmap = (fun ii trmap -> print_trmap ii trmap; trmap);
    }
  in

  let export_functions =
    let conv fd = fd.f_name in
    List.fold_right
      (fun fd acc ->
        match fd.f_cc with
        | Export -> conv fd :: acc
        | Internal | Subroutine _ -> acc)
      (snd prog) []
  in

  Compiler.compile_prog_to_asm Arch.asm_e Arch.call_conv Arch.aparams cparams
    export_functions
    (Expr.to_uprog Arch.asmOp cprog)
