From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import
  compiler_util
  expr
  fexpr
  sopn
  utils.
Require Export
  arch_decl
  arch_extra
  riscv_params_core.
Require Import
  riscv_decl
  riscv_instr_decl
  riscv.

Local Notation E n := (sopn.ADExplicit n None).


Variant riscv_extra_op : Type :=  
  | SWAP of wsize
  | Oriscv_SLHinit
  | Oriscv_SLHmove
  | Oriscv_SLHupdate
  | Oriscv_SLHprotect  of wsize
  | Oriscv_add_large_imm.

Scheme Equality for riscv_extra_op.

Lemma riscv_extra_op_eq_axiom : Equality.axiom riscv_extra_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_riscv_extra_op_dec_bl
       internal_riscv_extra_op_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build riscv_extra_op riscv_extra_op_eq_axiom.

#[ export ]
Instance eqTC_riscv_extra_op : eqTypeC riscv_extra_op :=
  { ceqP := riscv_extra_op_eq_axiom }.

Definition Oriscv_SLHinit_str := append "Oriscv_" SLHinit_str.
Definition Oriscv_SLHinit_instr :=
  mk_instr_desc_safe (pp_s Oriscv_SLHinit_str)
      [::]
      [::]
      [:: ty_msf ]
      [:: E 0 ]
      se_init_sem
      true.


Definition riscv_se_update_sem (b:bool) (w: wmsf) : wmsf * wmsf :=
  let aux :=  wrepr Uptr (0) in
  let w := if ~~b then aux else w in
  (aux, w).

Definition Oriscv_SLHupdate_str := append "Oriscv_" SLHupdate_str.
Definition Oriscv_SLHupdate_instr :=
  mk_instr_desc_safe (pp_s Oriscv_SLHupdate_str)
                [:: sbool; ty_msf]
                [:: E 0; E 1]
                [:: ty_msf; ty_msf]
                [:: E 2; E 1]
                riscv_se_update_sem
                true.

Definition Oriscv_SLHmove_str := append "Oriscv_" SLHmove_str.
Definition Oriscv_SLHmove_instr :=
  mk_instr_desc_safe (pp_s Oriscv_SLHmove_str)
      [:: ty_msf ]
      [:: E 1 ]
      [:: ty_msf ]
      [:: E 0 ]
      se_move_sem
      true.

Definition Oriscv_SLHprotect_str := append "Ox86_" SLHprotect_str.
Definition Oriscv_SLHprotect_instr  :=
  let ty := sword riscv_reg_size in
  let tin := [:: ty; ty] in
  let semi := fun (x y : word riscv_reg_size) => (wand x  y) in
  fun (ws:wsize) =>
    (* if (ws <= Uptr)%CMP then *)
      mk_instr_desc_safe (pp_sz SLHprotect_str ws)
        tin
        [:: E 1; E 2]
        [::ty]
        [:: E 0]
        (semi)
        true.

(* [conflicts] ensures that the returned register is distinct from the first
   argument. *)
Definition Oriscv_add_large_imm_instr : instruction_desc :=
  let ty := sword riscv_reg_size in
  let tin := [:: ty; ty] in
  let semi := fun (x y : word riscv_reg_size) => (x + y)%R in
  {| str    := (fun _ => "add_large_imm"%string)
   ; tin    := tin
   ; i_in   := [:: E 1; E 2]
   ; tout   := [:: ty]
   ; i_out  := [:: E 0]
   ; conflicts := [:: (APout 0, APin 0)]
   ; semi   := sem_prod_ok tin semi
   ; semu   := @values.vuincl_app_sopn_v [:: ty; ty] [:: ty] (sem_prod_ok tin semi) refl_equal
   ; i_safe := [::]
   ; i_valid := true
   ; i_safe_wf := refl_equal
   ; i_semi_errty :=  fun _ => sem_prod_ok_error (tin:=tin) semi _
   ; i_semi_safe := fun _ => values.sem_prod_ok_safe (tin:=tin) semi
 |}.


Definition get_instr_desc (o: riscv_extra_op) : instruction_desc :=
  match o with
  | SWAP ws => Oswap_instr (sword ws)
  | Oriscv_SLHinit => Oriscv_SLHinit_instr
  | Oriscv_SLHmove => Oriscv_SLHmove_instr
  | Oriscv_SLHupdate => Oriscv_SLHupdate_instr
  | Oriscv_SLHprotect ws => Oriscv_SLHprotect_instr ws
  | Oriscv_add_large_imm => Oriscv_add_large_imm_instr
   end.
  
(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[ export ]
Instance riscv_extra_op_decl : asmOp riscv_extra_op | 1 :=
  {
    asm_op_instr := get_instr_desc;
    prim_string := [::];
  }.

Module E.

Definition pass_name := "asmgen"%string.

Definition internal_error (ii : instr_info) (msg : string) :=
  {|
    pel_msg := compiler_util.pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := true;
  |}.

Definition error (ii : instr_info) (msg : string) :=
  {|
    pel_msg := compiler_util.pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := false;
  |}.

End E.

Definition asm_args_of_opn_args
  : seq RISCVFopn_core.opn_args -> seq (asm_op_msb_t * lexprs * rexprs) :=
  map (fun '(les, aop, res) => ((None, aop), les, res)).


  
(* Definition assemble_slh_update *)
(*   (ii : instr_info) *)
(*   (les : seq lexpr) *)
(*   (res : seq rexpr) : *)
(*   cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) := *)
(*   if (les, res) is ([:: LLvar aux; ms0 ], [:: Rexpr b; msf ]) *)
(*   then *)
(*     Let _ := assert (~~(Sv.mem aux (free_vars b) || Sv.mem aux (free_vars_r msf)) && *)
(*                      (vtype aux == sword U64)) *)
(*                     (E.se_update_arguments ii) in *)
(*     let res' := [:: Rexpr (Fapp1 Onot b); Rexpr (Fvar aux); msf ] in *)
(*     ok *)
(*       [:: *)
(*          [:: LLvar aux ] ::= (MOV U64) [:: re_i U64 (-1) ]; *)
(*                [:: ms0 ] ::= (CMOVcc U64) res' *)
(*       ] *)
(*   else *)
(*     Error (E.se_update_arguments ii). *)

Record SLH_condt := {
  SLH_cond_kind : condition_kind;
  SLH_cond_fst : option fexpr;
  SLH_cond_snd : option fexpr;
}.


Definition SLH_condt_not (c : SLH_condt) : SLH_condt :=
  let ck :=
    match c.(SLH_cond_kind) with
    | EQ => NE
    | NE => EQ
    | GE sg => LT sg
    | LT sg => GE sg
    end
  in
  {|
    SLH_cond_kind:= ck;
    SLH_cond_fst:= c.(SLH_cond_fst);
    SLH_cond_snd:= c.(SLH_cond_snd);
  |}
.

Definition SLH_assemble_cond_arg ii e : cexec (option fexpr) :=
  match e with
  | Fvar x => ok (Some e)
  | Fapp1 (Oword_of_int U32) (Fconst 0) => ok None
  | _ => Error (E.error ii "Can't assemble condition.")
  end.

(* Returns a condition_kind + a boolean describing if the arguments must be
   swapped. *)

Definition SLH_assemble_cond_app2 (o : sop2) :=
  match o with
  | Oeq (Op_w U32) => Some (EQ, false)
  | Oneq (Op_w U32) => Some (NE, false)
  | Olt (Cmp_w sg U32) => Some (LT sg, false)
  | Oge (Cmp_w sg U32) => Some (GE sg, false)
  | Ogt (Cmp_w sg U32) => Some (LT sg, true)
  | Ole (Cmp_w sg U32) => Some (GE sg, true)
  | _ => None
  end.

Fixpoint SLH_assemble_cond ii (e : fexpr) : cexec SLH_condt :=
  match e with
  | Fapp1 Onot e =>
    Let c := SLH_assemble_cond ii e in ok (SLH_condt_not c)
  | Fapp2 o e0 e1 =>
    Let: (o, swap) :=
      o2r (E.error ii "Could not match condition.") (SLH_assemble_cond_app2 o)
    in
    Let arg0 := SLH_assemble_cond_arg ii e0 in
    Let arg1 := SLH_assemble_cond_arg ii e1 in
    let: (arg0, arg1) := if swap then (arg1, arg0) else (arg0, arg1) in
    ok {|
      SLH_cond_kind := o;
      SLH_cond_fst := arg0;
      SLH_cond_snd := arg1;
    |}
  | _ =>
      Error (E.error ii "Can't assemble condition.")
  end.

Definition frconst i := fconst riscv_reg_size i.  

Definition SLH_instr_combine (a: cexec  (seq (asm_op_msb_t * lexprs * rexprs))) (b: cexec  (seq (asm_op_msb_t * lexprs * rexprs))) :=
  match a, b with
  | (ok _  s), (ok _  t) => ok (cat s t)
  | Error a, _ 
  | _, Error a => Error a
  end.

Definition SLH_instr_not (out: var_i) : cexec (seq (asm_op_msb_t * lexprs * rexprs))  := (ok [:: ((None, SLTIU), [:: LLvar out], [:: Rexpr (Fvar out); Rexpr (frconst 1)])]).


Definition SLH_eq_to_instr  (arg1: option fexpr) (arg2: option fexpr) out ii : cexec  (seq (asm_op_msb_t * lexprs * rexprs)):= 
  match arg1 , arg2 with
  | Some (Fvar x), Some (Fvar y) => ok [::
                                          ((None, XOR), [:: LLvar out], [:: Rexpr (Fvar x); Rexpr (Fvar y)]);
                                        ((None, SLTIU), [:: LLvar out], [:: Rexpr (Fvar out); Rexpr (frconst 1)])]
  | None, Some (Fvar x)
  | Some (Fvar x), None => ok [::((None, SLTIU), [:: LLvar out], [:: Rexpr (Fvar x); Rexpr (frconst 1)])]
  | None, None => ok [::((None, LI), [:: LLvar out], [:: Rexpr (frconst 1)])]
  | _ , _=>
      Error (E.error ii "Can't assemble condition.")
  end.

(* Definition SLH_lt_to_instr (sg: signedness) (arg1: option fexpr) (arg2: option fexpr) out ii : cexec  (seq (asm_op_msb_t * lexprs * rexprs)):= *)
(*   let op := match sg with | Signed => SLT | Unsigned => SLTU end in *)
(*   let opi := match sg with | Signed => SLT | Unsigned => SLTIU end in *)
(*   match arg1 , arg2 with   *)
(*   | Some (Fvar x), Some (Fvar y) => ok [::((None, op), [:: LLvar out], [:: Rexpr (Fvar x); Rexpr (Fvar y)])] *)
(*   | None, Some (Fvar x) => ok [:: *)
(*                                  ((None, LI), [:: LLvar out], [:: Rexpr (frconst 0)]); *)
(*                                  ((None, opi), [:: LLvar out], [:: Rexpr (Fvar out); Rexpr (Fvar x)])] *)
(*   | Some (Fvar x), None => ok [:: *)
(*                                  ((None, LI), [:: LLvar out], [:: Rexpr (frconst 0)]); *)
(*                                  ((None, opi), [:: LLvar out], [:: Rexpr (Fvar x); Rexpr (Fvar out)])] *)
(*   | None, None => ok [:: *)
(*                         ((None, LI), [:: LLvar out], [:: Rexpr (frconst (0))]) *)
(*                     ] *)
(*   | _ , _=> *)
(*       Error (E.error ii "Can't assemble condition.") *)
(*   end. *)

Definition SLH_lt_to_instr (sg: signedness) (arg1: option fexpr) (arg2: option fexpr) out ii : cexec  (seq (asm_op_msb_t * lexprs * rexprs)):=
  let op := match sg with | Signed => SLT | Unsigned => SLTU end in
  let opi := match sg with | Signed => SLTI | Unsigned => SLTIU end in
  match arg1 , arg2 with  
  | Some (Fvar x), Some (Fvar y) => ok [::((None, op), [:: LLvar out], [:: Rexpr (Fvar x); Rexpr (Fvar y)])]
  | None, Some (Fvar x) =>  (*0<x*)
      match sg with
      | Signed => ok [:: ((None, NEG), [:: LLvar out], [:: Rexpr (Fvar x)]);
                      ((None, SRLI), [:: LLvar out], [:: Rexpr (Fvar out); Rexpr (frconst 31)])]
      | Unsigned => (SLH_instr_combine (SLH_eq_to_instr None (Some (Fvar x)) out ii) (SLH_instr_not out))
      end
  | Some (Fvar x), None => ok [:: ((None, opi), [:: LLvar out], [:: Rexpr (Fvar x);  Rexpr (frconst (0)) ])]
  | None, None => ok [::
                        ((None, LI), [:: LLvar out], [:: Rexpr (frconst (0))])
                    ]
  |  _, _ =>
      Error (E.error ii "Can't assemble condition.")
  end.
    

Definition condt_to_instr (c: SLH_condt) out ii : cexec (seq (asm_op_msb_t * lexprs * rexprs)) := 
  match c with
  | {| SLH_cond_kind:= ck; SLH_cond_fst:= arg1; SLH_cond_snd:= arg2; |} =>
      match ck with
      | EQ => SLH_eq_to_instr arg1 arg2 out ii
      | NE => SLH_instr_combine (SLH_eq_to_instr arg1 arg2 out ii) (SLH_instr_not out)
      | LT sg => SLH_lt_to_instr sg arg1 arg2 out ii
      | GE sg => SLH_instr_combine (SLH_lt_to_instr sg arg1 arg2 out ii) (SLH_instr_not out)
      end
end.
 

Definition assemble_extra
           (ii: instr_info)
           (o: riscv_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with
  | SWAP sz =>  
    if (sz == U32)%CMP then
      match outx, inx with
      | [:: LLvar x; LLvar y], [:: Rexpr (Fvar z); Rexpr (Fvar w)] =>
        (* x, y = swap(z, w) *)
        Let _ := assert (v_var x != v_var w)
          (E.internal_error ii "bad risc-v swap : x = w") in
        Let _ := assert (v_var y != v_var x)
          (E.internal_error ii "bad risc-v swap : y = x") in
        Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y; z; w])
          (E.error ii "risc-v swap only valid for register of type u32") in
              
        ok [:: ((None, XOR), [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fvar w)]);
               (* x = z ^ w *)
               ((None, XOR), [:: LLvar y], [:: Rexpr (Fvar x); Rexpr (Fvar w)]);
               (* y = x ^ w = z ^ w ^ w = z *)
               ((None, XOR), [:: LLvar x], [:: Rexpr (Fvar x); Rexpr (Fvar y)])
           ]   (* x = x ^ y = z ^ w ^ z = w *)
      | _, _ => Error (E.error ii "only register is accepted on source and destination of the swap instruction on risc-v")
      end
    else
      Error (E.error ii "risc-v swap only valid for register of type u32")
            
  | Oriscv_add_large_imm =>
    match outx, inx with
    | [:: LLvar x], [:: Rexpr (Fvar y); Rexpr (Fapp1 (Oword_of_int ws) (Fconst imm))] =>
      Let _ := assert (v_var x != v_var y)
         (E.internal_error ii "bad riscv_add_large_imm: invalid register") in
      Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y])
          (E.error ii "riscv_add_large_imm only valid for register of type u32") in
      ok (asm_args_of_opn_args (RISCVFopn_core.smart_addi x y imm))
    | _, _ =>
      Error (E.internal_error ii "bad riscv_add_large_imm: invalid args or dests")
    end

  | Oriscv_SLHinit =>
      match outx, inx with
      (* alias for subi x  x0 1*)
      (* wiz an alias for addi x  x0 -1*)
      | [:: LLvar x], [::] =>
          ok [:: ((None, FENCE), [::], [::]);
              
              ((None, LI), [:: LLvar x], [:: Rexpr (frconst (-1))])
            ]
      | _, _ => Error (E.error ii "Wrong parameters for msf_init in risc-v")
      end

  | Oriscv_SLHmove =>
      match outx, inx with
      | [:: LLvar x], [::Rexpr (Fvar y)] =>
          ok[::
              ((None, MV), [:: LLvar x], [:: Rexpr (Fvar y)])
            ]
      | _, _ => Error (E.error ii "Wrong parameters for mov_msf in risc-v")
      end
        
  | Oriscv_SLHprotect ws =>
      match outx, inx with
      | [:: LLvar x], [:: Rexpr (Fvar y); Rexpr (Fvar z)] =>
          ok[::
               ((None, AND), [:: LLvar x], [:: Rexpr (Fvar y);  Rexpr (Fvar z)])
            ]
      | _, _ => Error (E.error ii "Wrong parameters for protect in risc-v")
      end

  | Oriscv_SLHupdate =>
      match outx, inx with
      | [:: LLvar aux; LLvar x], [:: Rexpr b; Rexpr (Fvar msf)] =>
          Let _ := assert (~~(Sv.mem aux (free_vars_r (Rexpr (Fvar msf)))) &&
                               (vtype aux == sword U32)) 
                      (E.error ii "Could not assign variable in #update_msf" ) in 
          (* test  \in {0f, 1t} *)
          (* test  = - test     test \in {0f, -1t} *)
          (* msf = msf and  test     msf \in {0f, msft} *)
          match (SLH_assemble_cond ii b) with
          | ok _ c =>  match condt_to_instr c aux ii with
                       | (ok _  s) => ok (cat s [::((None, NEG), [:: LLvar aux], [:: Rexpr (Fvar aux)]);
                                                   ((None, AND), [:: LLvar x], [:: Rexpr (Fvar aux); Rexpr (Fvar msf)])])
                       | Error e => Error e
                       end
          | Error e => Error e
          end
            
      | _, _ => Error (E.error ii "Wrong parameters for #update_msf in risc-v")
      end

  end.

#[ export ]
Instance riscv_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt riscv_op riscv_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition riscv_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ riscv_extra.

Definition Oriscv {atoI : arch_toIdent} o : @sopn riscv_extended_op _ := Oasm (BaseOp (None, o)).
