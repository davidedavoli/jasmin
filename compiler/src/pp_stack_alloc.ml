open Stack_alloc

let pp_var fmt x =
  Printer.pp_var ~debug:true fmt (Conv.var_of_cvar x)

let pp_expr fmt x =
  Printer.pp_expr ~debug:true fmt (Conv.expr_of_cexpr x)

let pp_region fmt r =
  Format.fprintf fmt "{ slot = %a; wsize = %a; align = %b }"
    pp_var r.r_slot
    PrintCommon.pp_wsize r.r_align
    r.r_writable

let pp_symbolic_slice fmt s =
  Format.fprintf fmt "[%a:%a]" pp_expr s.ss_ofs pp_expr s.ss_len

let pp_symbolic_zone fmt z =
  Format.fprintf fmt "@[<h>%a@]" (Format.pp_print_list pp_symbolic_slice) z

let pp_sub_region fmt sr =
  Format.fprintf fmt "@[<v>{ region = %a;@;<2 2>zone = %a }@]" pp_region sr.sr_region pp_symbolic_zone sr.sr_zone

let pp_var_region fmt vr =
  Format.fprintf fmt "@[<v>";
  Var0.Mvar.fold (fun x sr () ->
    Format.fprintf fmt "@[<h>%a -> %a@]@," pp_var (Obj.magic x) pp_sub_region sr) vr ();
  Format.fprintf fmt "@]"

let rec pp_forest fmt f =
  let pp_pair fmt (s, f) =
    Format.fprintf fmt "%a ->@;<2 2>%a" pp_symbolic_slice s pp_forest f
  in
  let open Region in
  let Nodes l = f in
  Format.fprintf fmt "@[<v>%a@]" (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_pair) l

let pp_status fmt s =
  let open Region in
  match s with
  | Valid -> Format.fprintf fmt "Valid"
  | Unknown -> Format.fprintf fmt "Unknown"
  | Borrowed f -> Format.fprintf fmt "Borrowed: @[<v>%a@]" pp_forest f

let pp_region_var fmt rv =
  Format.fprintf fmt "@[<v>";
  Mr.fold (fun r sm () ->
    Var0.Mvar.fold (fun x s () ->
      Format.fprintf fmt "%a -> %a -> %a@,"
        pp_var (Obj.magic r).r_slot pp_var (Obj.magic x)
        pp_status s) sm ()) rv ();
  Format.fprintf fmt "@]"

let pp_rmap fmt rmap =
  let open Region in
  Format.fprintf fmt "@[<v>{ var_region:@;<2 4>%a@;<2 2>region_var:@;<2 4>%a@,}@]@." pp_var_region rmap.var_region pp_region_var rmap.region_var
