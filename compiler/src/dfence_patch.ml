open Utils
open Annotations
open Prog
open Constraints

module CT = Ct_checker_forward

module S = Syntax

open Dfence_checker_forward

type ('info,'asm) patch_fenv = {
    fenv : ('info,'asm) fenv;
    patchs : ('info, 'asm) func Hf.t;
  }

module FEnv = struct
  let get_fun_def fenv fn = FEnv.get_fun_def fenv.fenv fn 

  let get_fty fenv fn = FEnv.get_fty fenv.fenv fn 

  let get_patch fenv fn = 
    try Hf.find fenv.patchs fn with Not_found -> get_fun_def fenv fn

end

(* --------------------------------------------------------- *)

exception Insert_dfence of L.i_loc * expr 
exception Insert_dfence_ptr of L.i_loc * var_i 

(* --------------------------------------------------------- *)
(* Type checking of expressions                              *)

let ensure_add2 loc e ety ety' (n1, s1) (n2, s2) = 
  (try Lvl.add_le n1 n2 with Lvl.Unsat unsat -> error_unsat loc.L.base_loc unsat pp_expr e ety ety');
  try Lvl.add_le s1 s2 with Lvl.Unsat unsat -> raise (Insert_dfence (loc, e))

let rec ty_expr env venv loc (e:expr) : vty =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> Env.dpublic env

  | Pvar x -> Env.gget venv x

  | Pget (_, aa, ws, x, i) ->
      ensure_public_address env venv loc x.gv;
      ensure_public env venv loc i;
      let ty = Env.fresh2 env
      and xty = Env.gget venv x in
      if not (ssafe_test x.gv aa ws i) then VlPairs.add_le_speculative (Env.secret env) ty;
      VlPairs.add_le (content_ty xty) ty;
      Direct ty

    (* in the case of sub-arrays, no operation is performed, and there is now
       an alias on the values. Thus the type must be *equal* *)
  | Psub (_, _, _, x, i) ->
      ensure_public env venv loc i;
      Env.gget venv x

  | Pload (_, _, x, i) ->
      ensure_public env venv loc (Pvar (gkvar x));
      ensure_public env venv loc i;
      Env.dsecret env

  | Papp1(o, e)      ->
    let public = not (CT.is_ct_op1 o) in
    ty_exprs_max ~public env venv loc [e]
  | Papp2(o, e1, e2) ->
    let public = not (CT.is_ct_op2 o) in
    ty_exprs_max ~public env venv loc [e1; e2]
  | PappN(o, es)     ->
    let public = not (CT.is_ct_opN o) in
    ty_exprs_max ~public env venv loc es

  | Pif(_, e1, e2, e3) ->
      let ty1 = ty_expr env venv loc e1 in
      let ty2 = ty_expr env venv loc e2 in
      let ty3 = ty_expr env venv loc e3 in
      match ty1 with
      | Indirect _ -> assert false
      | Direct l1 ->
        let do_indirect lp2 le2 lp3 le3 =
          let lp = Env.fresh2 env in
          let le = Env.fresh2 env in
          (* The condition expression is also added to the constraints because it can be deduced from the result value*)
          VlPairs.add_le l1 lp; VlPairs.add_le lp2 lp; VlPairs.add_le lp3 lp;
          VlPairs.add_le l1 le; VlPairs.add_le le2 le; VlPairs.add_le le3 le;
          Indirect(lp, le) in
        match ty2, ty3 with
        | Direct l2, Direct l3 ->
          let le = Env.fresh2 env in
          VlPairs.add_le l1 le; VlPairs.add_le l2 le; VlPairs.add_le l3 le;
          Direct le
        | Indirect(lp2, le2), Indirect(lp3, le3) ->
          do_indirect lp2 le2 lp3 le3
        | Indirect(lp2, le2), Direct le3 ->
          do_indirect lp2 le2 (Env.public2 env) le3
        | Direct le2, Indirect (lp3, le3) ->
          do_indirect (Env.public2 env) le2 lp3 le3

and ensure_smaller env venv loc e l =
  let ety = ty_expr env venv loc e in
  match ety with
  | Direct le | Indirect (le, _) -> ensure_add2 loc e ety (Direct l) le l 

and ensure_public env venv loc e = ensure_smaller env venv loc e (Env.public2 env)

and ensure_public_address env venv loc x =
  let ety = Env.get_i venv x in
  match ety with
  | Direct _ -> () (* stack or reg arrays have public addresses by definition *)
  | Indirect (le, _) ->
    let (n1, s1), (n2, s2) = le, (Env.public2 env) in
    (try Lvl.add_le n1 n2 with Lvl.Unsat unsat -> error_unsat loc.L.base_loc unsat pp_var_i x ety (Direct (Env.public2 env)));
    try Lvl.add_le s1 s2 with Lvl.Unsat unsat -> raise (Insert_dfence_ptr (loc, x))

and ty_exprs_max ~(public:bool) env venv loc es : vty =
  let l = if public then Env.public2 env else Env.fresh2 env in
  List.iter (fun e -> ensure_smaller env venv loc e l) es;
  Direct l

(* --------------------------------------------------------- *)
(* Type checking of lvalue                                   *)

let ty_lval loc env ((msf, venv) as msf_e : msf_e) x ety : msf_e =
  (* First path the type ety to make it consistant with the variable info *)
  match x with
  | Lnone _ -> msf_e
  | Lvar x ->
      (* TODO assumption: p = e when p is a pointer and e a direct value means p
         points to a new position, where the expression is *)
      (* as opposed to assigning the pointer directly to the given value *)
      (* likewise, assuming x = p means storing the value pointed by p in x *)
      (* what with p = [ x ]? I believe it does not compile *)
      let lp, le =
        match ety with
        | Direct le -> Env.public2 env, le
        | Indirect(lp, le) -> lp, le in
      let xty = if is_ptr (kind_i x)
          then Indirect(lp, le)
          else Direct le in
      let msf = MSF.update msf (L.unloc x) in 
      let venv = Env.set_ty env venv x xty in
      msf,
      begin match (L.unloc x).v_kind with
      | Stack (Direct)    -> Env.corruption_speculative env venv le
      | Stack (Pointer _) -> Env.corruption_speculative env venv lp
      | _ -> venv
      end

  | Lmem(_, _, x, i) ->
      ensure_public env venv loc (Pvar (gkvar x));
      ensure_public env venv loc i;
        (* programmes are assumed to be safe, thus corruption from memory store
           with [x + i] is speculative only *)
      msf, Env.corruption_speculative env venv (content_ty ety)

  | Laset(_, aa, ws, x, i) ->
      ensure_public_address env venv loc x;
      ensure_public env venv loc i;
      let le = content_ty ety in
      let venv =
        let l = Env.fresh2 env in
        let xty =
          match Env.get_i venv x with
          | Direct lx -> VlPairs.add_le lx l; VlPairs.add_le le l; Direct l
          | Indirect (lp, lx) -> VlPairs.add_le lx l; VlPairs.add_le le l;
              Indirect (lp, l)
        in
        Env.set_ty env venv x xty in
      let venv =
        match (L.unloc x).v_kind with
        | Reg (_, Direct) -> venv
        | _ -> Env.corruption_speculative env venv le
      in
      msf, venv

  | Lasub(_, _, _, x, i) ->
      (* ensure_public_address env venv (L.loc x) x; *)
      (* ensure_public env venv (L.loc x) i; *)
      let le = content_ty ety in
      let l = Env.fresh2 env in
      let xty =
        match Env.get_i venv x with
        | Direct lx -> VlPairs.add_le lx l; VlPairs.add_le le l; Direct l
        | Indirect (lp, lx) -> VlPairs.add_le lx l; VlPairs.add_le le l;
            Indirect (lp, l)
      in
      msf, Env.set_ty env venv x xty

let ty_lvals1 loc env (msf_e : msf_e) xs ety : msf_e =
  List.fold_left (fun msf_e x -> ty_lval loc env msf_e x ety) msf_e xs

let ty_lvals loc env (msf_e : msf_e) xs tys : msf_e =
  List.fold_left2 (ty_lval loc env) msf_e xs tys

(* -------------------------------------------------------------- *)
(* declassify                                                     *)
(* TODO ensure declassify cannot occur on potentially corrupted   *)
(* stack values                                                   *)

(* right now only used by syscall, which only consists of randombytes
   it is thus tailored for this specific function. *)
let ensure_public_address_expr env venv loc e =
  ensure_public env venv loc e 

(* --------------------------------------------------------------- *)
(* [ty_instr env msf i] return msf' such that env, msf |- i : msf' *)

let rec ty_instr is_ct_asm fenv env ((msf,venv) as msf_e :msf_e) i =
  let loc = i.i_loc in
  match i.i_desc with
  | Csyscall (xs, o, es) ->
    (* TODO: generalize to other syscalls *)
    assert (match o with Syscall_t.RandomBytes _ -> true);
    List.iter (ensure_public_address_expr env venv loc) es;
    (* We don't known what happen to MSF after external function call *)
    ty_lvals1 loc env (MSF.toinit, venv) xs (Env.dsecret env)

  | Cassgn(mso, _, _, (Pvar x as msi)) when MSF.is_msf msf x.gv ->
    move_msf ~loc:loc.L.base_loc env msf_e mso msi

  | Cassgn(x, _, _, e) ->
    let ety = ty_expr env venv loc e in
    ty_lval loc env msf_e x (declassify_ty env i.i_annot ety)

  | Copn(xs, _, o, es) ->
    begin match is_special o, xs, es with
    | Init_msf, [ms], _ ->
      let ms = reg_lval_opt ~direct:true loc.L.base_loc ms in
      let venv = Env.set_init_msf env venv ms in
      let ms = Option.map_default MSF.exact1 MSF.toinit ms in
      ms, venv

    | Fence, _, _ -> msf, Env.set_fence env venv 

    | Init_msf, _, _ -> assert false

    | Update_msf, [mso], [b; msi] ->
      let mso = reg_lval ~direct:true loc.L.base_loc mso and msi = reg_expr ~direct:true loc.L.base_loc msi in
      (* do not check b, if check_msf_trans succeed then b is public *)
      MSF.check_msf_trans msf msi b;
      let _, venv = ty_lvals1 loc env (msf, venv) xs (Env.dpublic env) in
      MSF.exact1 mso, venv

    | Update_msf, _, _ -> assert false

    | Mov_msf, [mso], [msi] ->
      move_msf ~loc:loc.L.base_loc env msf_e mso msi

    | Mov_msf, _, _ -> assert false

    | Protect, [x], [e; ms] ->
      let _ = reg_lval ~direct:false loc.L.base_loc x and _ = reg_expr ~direct:false loc.L.base_loc e and
          ms = reg_expr ~direct:true loc.L.base_loc ms in
      MSF.check_msf_exact msf ms;
      let xty =
        match ty_expr env venv loc e with
        | Direct (n, _) -> Direct (n, n)
        | Indirect ((n, _), le) -> Indirect ((n, n), le) in

      ty_lval loc env msf_e x xty

    | Protect, _, _ -> assert false

    | Dfence, [x], [e] ->
      let _ = reg_lval ~direct:false loc.L.base_loc x and _ = reg_expr ~direct:false loc.L.base_loc e in
      let xty =
        match ty_expr env venv loc e with
        | Direct (n, _) -> Direct (n, n)
        | Indirect ((n, _), le) -> Indirect ((n, n), le) in

      ty_lval loc env msf_e x xty
 
    | Dfence, _, _ -> assert false      

    | Spill o, _, es ->
        let xs = List.map (reg_expr ~direct:false loc.L.base_loc) es in
        if o = Pseudo_operator.Spill then msf, Env.set_spill env venv xs
        else msf, Env.set_unspill env venv xs

    | Other, _, _  ->
      let public = not (CT.is_ct_sopn is_ct_asm o) in
      let ety = ty_exprs_max ~public env venv loc es in
      ty_lvals1 loc env msf_e xs (declassify_ty env i.i_annot ety)
    end

  | Cif(e, c1, c2) ->
    if is_inline i then
      let msf1, venv1 = ty_cmd is_ct_asm fenv env (msf, venv) c1 in
      let msf2, venv2 = ty_cmd is_ct_asm fenv env (msf, venv) c2 in
      MSF.max msf1 msf2, Env.max env venv1 venv2
    else begin
      ensure_public env venv loc e;
      let msf1, venv1 = ty_cmd is_ct_asm fenv env (MSF.enter_if msf e, venv) c1 in
      let msf2, venv2 = ty_cmd is_ct_asm fenv env (MSF.enter_if msf (Papp1(Onot, e)), venv) c2 in
      MSF.max msf1 msf2, Env.max env venv1 venv2
    end

  | Cfor(x, (_, e1, e2), c) ->
      ensure_public env venv loc e1;
      ensure_public env venv loc e2;

      let msf = MSF.loop env i.i_loc msf in
      (* let w, _ = written_vars [i] in *)
      let venv1 = Env.freshen env venv in (* venv <= venv1 *)
      let msf_e = ty_lval loc env (msf, venv1) (Lvar x) (Env.dpublic env) in
      let (msf', venv') = ty_cmd is_ct_asm fenv env msf_e c in
      let msf' = MSF.end_loop loc.L.base_loc msf msf' in
      Env.ensure_le loc.L.base_loc venv' venv1; (* venv' <= venv1 *)
      msf', venv1

  | Cwhile(_, c1, e, _, c2) ->
    (* c1; while e do (c2; c1) *)
    (* env, msf <= env1, msf1
       env1, msf1 |- c1 : msf2, env2   env2 |- e : public
       env2, enter_if e msf2 |- c2 : env1, msf1
       --------------------------------------------------------------------------------
       env, msf |- while c1 e c2 : enter_if e msf1
     *)
    let msf1 = MSF.loop env i.i_loc msf in
    (* let w, _ = written_vars [i] in *)
    (* NOTE cannot restrict refreshed variables to local modified vars
       because of memory corruption: if loop body corrupts some stack variable
       constrained to public, the test fails, while marking all stack variables
       as secret is sufficient *)

    let venv1 = Env.freshen env venv in (* venv <= venv1 *)
    let (msf2, venv2) = ty_cmd is_ct_asm fenv env (msf1, venv1) c1 in
    ensure_public env venv2 loc e;
    let (msf', venv') = ty_cmd is_ct_asm fenv env (MSF.enter_if msf2 e, venv2) c2 in
    let _ = MSF.end_loop loc.L.base_loc msf1 msf' in
    Env.ensure_le loc.L.base_loc venv' venv1; (* venv' <= venv1 *)
    MSF.enter_if msf2 (Papp1(Onot, e)), venv2

  | Ccall (xs, f, es) ->
    let fty = FEnv.get_fty fenv f in
    let modmsf = fty.modmsf in
    let tyout, tyin, resulting_corruption = Env.clone_for_call env fty in

    let input_ty e vfty =
      match vfty with
      | IsMsf ->
        (* we don't check that e is public, it is ensured by being msf *)
        let ms = reg_expr ~direct:true loc.L.base_loc e in
        MSF.check_msf_exact msf ms
      | IsNormal ety' ->
        let ety = ty_expr env venv loc e in
        match ety, ety' with
        | Direct le, Direct le' -> ensure_add2 loc e ety ety' le le'
        | Direct le, Indirect (_, le') -> ensure_add2 loc e ety ety' le le'
        | Indirect(lp, le), Direct le' -> 
          ensure_add2 loc e ety ety' lp (Env.public2 env); 
          ensure_add2 loc e ety ety' le le'
        | Indirect(lp, le), Indirect(lp', le') -> 
          ensure_add2 loc e ety ety' lp lp'; 
          ensure_add2 loc e ety ety' le le'
        in
    List.iter2 input_ty es tyin;

    (* callee function has its own effect on this function corruption *)
    let venv = Env.corruption env venv resulting_corruption in

    (* compute the resulting venv *)
    let output_ty msf_e x vfty =
      let ty =
        match vfty with
        | IsMsf -> Env.dpublic env
        | IsNormal ty -> declassify_ty env i.i_annot ty in
      let (msf, venv) = ty_lval loc env msf_e x ty in
      let msf = if vfty = IsMsf then MSF.add (reg_lval ~direct:true loc.L.base_loc x) msf else msf in
      (msf, venv) in
    let msf = if is_Modified modmsf then MSF.toinit else msf in
    List.fold_left2 output_ty (msf, venv) xs tyout

and ty_cmd is_ct_asm fenv env msf_e c =
  List.fold_left (ty_instr is_ct_asm fenv env) msf_e c


(* ------------------------------------------------------------------- *)
(* Do the inference + type checking of function                        *)
(*
#nomodmsf #constraints = "l1 <= transient, l2 <= l1"
   fn f (#public #secret reg u64[1] x, #poly = l1 stack u8 c) ->
        #poly=l1 #poly=l2 u64[1]
*)

let init_constraint fenv f = init_constraint fenv.fenv f

let rec patch_c loc patch c = 
  match c with
  | [] -> raise Not_found 
  | i :: c -> 
    if i.i_loc.L.uid_loc = loc.L.uid_loc then
      match i.i_desc with
      | Cwhile (a, c1, e, ii, c2) ->
          let i = {i with i_desc = Cwhile(a, c1 @ patch, e, ii, c2) } in
          i :: c
      | _ -> patch @ i :: c
    else  
      try patch_i loc patch i :: c 
      with Not_found -> i :: patch_c loc patch c
  
and patch_i loc patch i = 
  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ | Ccall _ -> raise Not_found
  | Cif(e, c1, c2) -> 
    (try {i with i_desc = Cif(e, patch_c loc patch c1, c2) }
     with Not_found -> {i with i_desc = Cif(e, c1, patch_c loc patch c2) })
  | Cfor (x,r,c) -> {i with i_desc = Cfor(x,r, patch_c loc patch c) }
  | Cwhile(a, c1, e, ii, c2) ->
    (try {i with i_desc = Cwhile(a, patch_c loc patch c1, e, ii, c2) }
     with Not_found -> {i with i_desc = Cwhile(a, c1, e, ii, patch_c loc patch c2) })

  
  

  


let rec ty_fun is_ct_asm fenv fn =
  try Hf.find fenv.fenv.env_ty fn
  with Not_found ->
    let (fd, fty) = ty_fun_infer is_ct_asm fenv fn in
    Hf.add fenv.fenv.env_ty fn fty;
    Hf.add fenv.patchs fn fd;
    fty

and ty_fun_infer is_ct_asm fenv fn =
  let f = FEnv.get_fun_def fenv fn in
  (* First compute all function call by f and recurse *)
  let _, called = written_vars_fc f in
  Mf.iter (fun fn _ -> ignore (ty_fun is_ct_asm fenv fn)) called;
  
  let rec aux body = 
    try 
      let env, venv, tyin, tyout, modmsf = init_constraint fenv f in
      (* init msf status *)
      let msf =
        List.fold_left2 (fun msf x ty ->
            if ty = IsMsf then MSF.add (L.mk_loc x.v_dloc x) msf else msf)
          MSF.toinit f.f_args tyin in
      (* start type checking of the body *)
      let msf, venv = ty_cmd is_ct_asm fenv env (msf, venv) body in
      (* build the resulting type *)
      let doout x (omsf, ty) =
        let le_ty ty1 ty2 =
          try
            match ty1, ty2 with
            | Direct le1, Direct le2 -> VlPairs.add_le le1 le2
            | Indirect(lp1, le1), Indirect(lp2, le2) ->
              VlPairs.add_le lp1 lp2; VlPairs.add_le le1 le2
            | _, _ -> assert false
          with Lvl.Unsat _unsat ->
            error ~loc:(L.loc x)
              "return type for %a is %a it should be less than %a"
                 pp_var_i x pp_vty ty1 pp_vty ty2 in
        match omsf with
        | Some true  -> MSF.check_msf_exact msf x; IsMsf
        | Some false ->
          if MSF.is_msf_exact msf x then
            error ~loc:(L.loc x)
              "return annotation for %a should be %s" pp_var_i x smsf;
          le_ty (Env.get_i venv x) ty;
          IsNormal ty
        | None ->
          if MSF.is_msf_exact msf x then IsMsf
          else (le_ty (Env.get_i venv x) ty; IsNormal ty) in
      
      let tyout = List.map2 doout f.f_ret tyout in
      let resulting_corruption = Env.get_resulting_corruption venv in
      let (n1, s1) = resulting_corruption in
      
      let constraints = Env.constraints env in
      let add ls vty =
        match vty with
        | IsMsf -> ls
        | IsNormal (Direct (n, s)) -> n :: s :: ls
        | IsNormal (Indirect ((np, sp), (ne, se))) -> np :: sp :: ne :: se :: ls in
      let to_keep = List.fold_left add (List.fold_left add [n1; s1] tyin) tyout in
      
      C.prune constraints to_keep;
      let fty = { modmsf; tyin; tyout; constraints; resulting_corruption; } in
      if !Glob_options.debug then
        Format.eprintf
          "Before optimization:@.%a@."
          pp_funty
          (f.f_name.fn_name, fty);
      let tomax = List.fold_left add [] tyin in
      let tomin = List.fold_left add [n1; s1] tyout in
      C.optimize constraints ~tomin ~tomax;
      body, fty
    with 
    | Insert_dfence (loc, e) -> 
      let xs = Sv.elements (vars_e e) in
      let xs = List.map (L.mk_loc loc.L.base_loc) xs in
      aux_patch loc xs body
    | Insert_dfence_ptr(loc, x) -> aux_patch loc [x] body
        

    and aux_patch loc xs body = 
      let doit x = 
        let op = 
          match (L.unloc x).v_ty with
          | Bty (U ws) -> Slh_ops.SLHdfence ws
          | Arr(ws, len) ->  SLHdfence_ptr (Conv.pos_of_int (arr_size ws len))
          | t -> 
              error ~loc:loc.L.base_loc 
                "%a need to be protected, don't know how to protect a variable of this type" 
                pp_var (L.unloc x)
        in
        { i_desc = Copn([Lvar x], E.AT_keep, Oslh op, [Pvar (gkvar x)])
        ; i_loc = L.refresh_i_loc loc
        ; i_info = ()
        ; i_annot = [] } in 
      let patch = List.map doit xs in
      aux (patch_c loc patch body) in
    let f_body, fty = aux f.f_body in
    { f with f_body}, fty
      

let patch_prog is_ct_asm ((glob, prog):(unit, 'asm) prog) fl =
  let fenv = { fenv = { env_ty = Hf.create 101; env_def = prog }; patchs = Hf.create 101 } in
  let fl =
    if fl = [] then
      List.rev_map (fun f -> f.f_name) prog
    else
      let get fn =
        try (List.find (fun f -> f.f_name.fn_name = fn) prog).f_name
        with Not_found ->
          hierror ~loc:Lnone ~kind:"speculative constant type checker" "unknown function %s" fn in
      List.map get fl in
  let sigs = List.map (fun fn -> fn.fn_name, ty_fun is_ct_asm fenv fn) fl in
  let funcs = List.map (fun fd -> FEnv.get_patch fenv fd.f_name) prog in
  (glob, funcs), sigs

