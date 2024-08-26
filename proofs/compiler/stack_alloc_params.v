From mathcomp Require Import ssreflect.
Require Import expr.

Record concrete_slice := {
  cs_ofs : Z;
  cs_len : Z;
}.

(* [ptr_kind] is [ptr_kind_init] with one more piece of information,
   the offset of the region (in cases [Pdirect] and [Pstkptr]). *)
Variant ptr_kind :=
| Pdirect of var & Z & wsize & concrete_slice & v_scope
| Pregptr of var
| Pstkptr of var & Z & wsize & concrete_slice & var.

(* TODO: move close to ptr_kind? *)
Variant vptr_kind :=
  | VKglob of Z * wsize
  | VKptr  of ptr_kind.

(* TODO: remove? *)
Definition var_kind := option vptr_kind.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
.

Record stack_alloc_params :=
  {
    (* Return an instruction that computes an address from an base address and
     an offset. *)
    sap_mov_ofs :
      lval            (* The variable to save the address to. *)
      -> assgn_tag    (* The tag present in the source. *)
      -> vptr_kind    (* The kind of address to compute. *)
      -> pexpr        (* Variable with base address. *)
      -> pexpr        (* Offset. *)
      -> option instr_r;
    (* Build an instruction that assigns an immediate value *)
    sap_immediate : var_i -> Z -> instr_r;
    (* Build an instruction that swap two registers *)
    (* [sap_swap t d1 d2 s1 s2] is equivalent to d1,d2 = s2, s1 *)
    sap_swap : assgn_tag -> var_i -> var_i -> var_i -> var_i -> instr_r;

  }.

End WITH_PARAMS.

Variant mov_kind :=
  | MK_LEA
  | MK_MOV.

Definition mk_mov vpk :=
  match vpk with
  | VKglob _ | VKptr (Pdirect _ _ _ _ Sglob) => MK_LEA
  | _ => MK_MOV
  end.

Definition add {pd:PointerData} := Papp2 (Oadd (Op_w Uptr)).
