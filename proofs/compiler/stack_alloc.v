(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import strings word utils type var expr.
Require Import compiler_util byteset.
Require slh_lowering.
Require Import ZArith.
Require Import stack_alloc_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "stack allocation".

  Definition stk_error_gen (internal:bool) (x:var_i) msg := {|
    pel_msg := msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := Some x.(v_info);
    pel_pass := Some pass;
    pel_internal := internal
  |}.

  Definition stk_error  := stk_error_gen false.
  Definition stk_ierror := stk_error_gen true.

  Definition stk_ierror_basic x msg :=
    stk_ierror x (pp_box [:: pp_s msg; pp_nobox [:: pp_s "("; pp_var x; pp_s ")"]]).

  Definition stk_error_no_var_gen (internal:bool) msg := {|
    pel_msg := msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := internal
  |}.

  Definition stk_error_no_var s := stk_error_no_var_gen false (pp_s s).
  Definition stk_ierror_no_var s := stk_error_no_var_gen true (pp_s s).

End E.

(* TODO: could [wsize_size] return a [positive] rather than a [Z]?
   If so, [size_of] could return a positive too.
*)
Definition size_of (t:stype) :=
  match t with
  | sword sz => wsize_size sz
  | sarr n   => Zpos n
  | sbool | sint => 1%Z
  end.

Definition slot := var.

Notation size_slot s := (size_of s.(vtype)).

Record region :=
  { r_slot : slot;        (* the name of the region        *)
      (* the size of the region is encoded in the type of [r_slot] *)
    r_align : wsize;      (* the alignment of the region   *)
    r_writable : bool;    (* the region is writable or not *)
  }.

Definition region_beq (r1 r2:region) :=
  [&& r1.(r_slot)     == r2.(r_slot),
      r1.(r_align)    == r2.(r_align) &
      r1.(r_writable) == r2.(r_writable)].

Definition region_same (r1 r2:region) :=
  (r1.(r_slot) == r2.(r_slot)).

Lemma region_axiom : Equality.axiom region_beq.
Proof.
  rewrite /region_beq => -[xs1 xa1 xw1] [xs2 xa2 xw2].
  by apply:(iffP and3P) => /= [[/eqP -> /eqP -> /eqP ->] | [-> -> ->]].
Qed.

HB.instance Definition _ := hasDecEq.Build region region_axiom.

Module CmpR.

  Definition t : eqType := region.

  Definition cmp (r1 r2: t) :=
    Lex (bool_cmp r1.(r_writable) r2.(r_writable))
     (Lex (wsize_cmp r1.(r_align) r2.(r_align))
          (var_cmp r1.(r_slot) r2.(r_slot))).

#[global]
  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [???] [???]]; rewrite /cmp !Lex_lex.
    + by repeat (apply lex_sym; first by apply cmp_sym); apply cmp_sym.
    + by repeat (apply lex_trans=> /=; first by apply cmp_ctrans); apply cmp_ctrans.
    move=> /lex_eq [] /= h1 /lex_eq [] /= h2 h3.
    by rewrite (cmp_eq h1) (cmp_eq h2) (cmp_eq h3).
  Qed.

End CmpR.

Module Mr := Mmake CmpR.

(* ------------------------------------------------------------------ *)

(* A slice represents a contiguous portion of memory.
  We have them in two flavors:
  - [concrete_slice] where the components are integers; concrete slices are used
    to describe the shape of the stack, since we know everything statically.
  - [symbolic_slice] where the components are symbolic expressions; symbolic
    slices are used in the analysis, since there we do not necessarily know the
    offsets statically.
*)

(* We reuse [pexpr], but only the arithmetic part is of interest here. *)
Record symbolic_slice := {
  ss_ofs : pexpr;
  ss_len : pexpr;
}.

Definition symbolic_slice_beq s1 s2 :=
  eq_expr s1.(ss_ofs) s2.(ss_ofs) && eq_expr s1.(ss_len) s2.(ss_len).

(* A symbolic zone is a memory portion written as a list of symbolic slices,
   each slice being included in the previous one.
   For instance, [i, j][k, l], is the [k, l]-slice of the [i, j]-slice. It could
   also be described as the slice [i+k, l]. We store it as [i, j][k, l]
   to remember some structure.
*)
Definition symbolic_zone := seq symbolic_slice.

(* TODO: pick this definition in a library instead *)
Fixpoint list_beq {A} (eqb : A -> A -> bool) (l1 l2 : list A) :=
  match l1, l2 with
  | [::], [::] => true
  | a1 :: l1, a2 :: l2 => eqb a1 a2 && list_beq eqb l1 l2
  | _, _ => false
  end.

Definition symbolic_zone_beq :=
  list_beq symbolic_slice_beq.

(* ------------------------------------------------------------------ *)
(* A zone inside a region. *)
Record sub_region := {
    sr_region : region;
    sr_zone  : symbolic_zone;
  }.

Definition sub_region_beq sr1 sr2 :=
  (sr1.(sr_region) == sr2.(sr_region)) && (symbolic_zone_beq sr1.(sr_zone) sr2.(sr_zone)).

(* ------------------------------------------------------------------ *)

(* TODO: we can certainly do better for globals (even if just for consistency).
   3 distinct directions:
   - PIdirect with sc = Sglob could be just PIglob g, with g the global
   - the globals (the real ones) could be described using PIdirect with sc = Sglob
   - every Pdirect could never be added to rmap since we enforce that
     sr = sub_region_direct s ws sc z (cf. the proof)
*)

(* Stack variables are classified into three categories:
   - PIdirect x cs sc:
       a stack slot (if sc = Slocal) or a global slot (if sc = Sglob);
       [x] is the name of the region, [cs] is the slice of the region where
       the slot is.
   - PIregptr p:
       a reg ptr, [p] is the name of the pointer to use in the target program.
   - PIstkptr x cs xp:
       a stack ptr,
       [x] is the name of the region where the pointer lies, [cs] is the slice
       of the region where the pointer is, [xp] is a pseudo-variable allowing
       to track that the pointer was not overwritten.

   More information:
   - global slot: direct slots with sc = Sglob are local stack variables
       assigned to globals (this can be useful, for instance, if you want
       to pass a global array to an inline function expecting a stack array
       as argument); this must not be confused with the globals themselves
       that do not appear in this classification.
   - stack ptrs have two associated sub-regions:
     - the one stored in [rmap] which is the region corresponding to the pointed
       zone of memory,
     - the zone of the pointer itself described by PIstkptr.
*)
Variant ptr_kind_init :=
| PIdirect of var & concrete_slice & v_scope
| PIregptr of var
| PIstkptr of var & concrete_slice & var.

(* An instance of this record is attached to each [reg ptr] argument of every
   function. *)
Record param_info := {
  pp_ptr      : var; (* the name of the pointer to use in the target *)
  pp_writable : bool; (* whether the pointer is writable *)
  pp_align    : wsize; (* the minimal alignment of the pointed memory zone *)
}.

Record pos_map := {
  vrip    : var; (* the variable containing rip (used for globals) *)
  vrsp    : var; (* the variable containing SP (the stack pointer) *)
  vxlen   : var; (* a variable used to compile syscalls *)
  globals : Mvar.t (Z * wsize);
    (* a map associating an offset and an alignment to each global *)
  locals  : Mvar.t ptr_kind;
    (* a map associating a ptr_kind to each stack variable *)
  vnew    : Sv.t;
    (* the set of fresh variables (we check that they do not appear in the
       source program) *)
}.

(* TODO: Z.land or is_align ?
   Could be just is_align (sub_region_addr sr) ws ? *)
Definition check_align al x (sr:sub_region) ws :=
  Let _ := assert ((al == Unaligned) || (ws <= sr.(sr_region).(r_align))%CMP) (* TODO: is this check needed? *)
                  (stk_ierror_basic x "unaligned offset") in
  (* FIXME SYMBOLIC: how to check the alignment ? *)
  (* idea: use align/misaligned instructions, only use aligned ones when we are statically sure that it's ok *)
(*   assert ((al == Unaligned) || (Z.land sr.(sr_zone).(z_ofs) (wsize_size ws - 1) == 0)%Z)
         (stk_ierror_basic x "unaligned sub offset"). *)
  ok tt.

Definition writable (x:var_i) (r:region) :=
  assert r.(r_writable)
    (stk_error x (pp_box [:: pp_s "cannot write to the constant pointer"; pp_var x; pp_s "targetting"; pp_var r.(r_slot) ])).

Module Region.

Inductive symbolic_forest :=
| Nodes : seq (symbolic_slice * symbolic_forest) -> symbolic_forest.

(* empty forest *)
Notation emptyf := (Nodes [::]).

(* TODO: it seems everything could be Borrowed
   Valid == Borrowed [::]
   Unknown == Borrowed [::full_zone]
   Do we really need the 3 cases? maybe for clarity
*)

(* A status synthetizes what we know about a sub-region. *)
Variant status :=
| Valid
  (* The sub-region is fully valid, we can read everywhere. *)
| Unknown
  (* We don't know anything about the sub-region, we cannot read anywhere. *)
| Borrowed of symbolic_forest.
  (* Some parts of the sub-region are "borrowed" by other variables, we cannot
     read in them. We remember a forest of disjoint symbolic zones
     that are borrowed. *)

Definition status_map := Mvar.t status.

Record region_map := {
  var_region : Mvar.t sub_region; (* the region associated to the source variable     *)
  region_var :> Mr.t status_map;  (* the status associated to variables in the region *)
    (* region -> var -> status *)
}.

Definition empty_status_map := Mvar.empty status.

Definition empty := {|
  var_region := Mvar.empty _;
  region_var := Mr.empty status_map;
|}.

Definition get_sub_region (rmap:region_map) (x:var_i) :=
  match Mvar.get rmap.(var_region) x with
  | Some sr => ok sr
  | None => Error (stk_error x (pp_box [:: pp_s "no region associated to variable"; pp_var x]))
  end.

Definition get_status_map rv (r:region) : status_map :=
  odflt empty_status_map (Mr.get rv r).

Definition get_status (sm:status_map) x :=
  odflt Unknown (Mvar.get sm x).

Definition get_var_status rv r x :=
  let sm := get_status_map rv r in
  get_status sm x.

Fixpoint split z :=
  match z with
  | [::] => ([::], {| ss_ofs := Pconst 0; ss_len := Pconst 0 |}) (* impossible *)
  | [::s] => ([::], s)
  | s :: z =>
    let: (z, last) := split z in
    (s :: z, last)
  end.

(* Returns the sub-zone of [z] starting at offset [ofs] and of length [len].
   There is a special case if we access the full sub-region. In that case, [z]
   is returned.
*)
Definition sub_zone_at_ofs (z:symbolic_zone) ofs len :=
  (* TODO: z is never nil, but check this *)
  let: (z', s) := split z in
  if eq_expr ofs (Pconst 0) && eq_expr len s.(ss_len) then z
  else
    match is_const s.(ss_ofs), is_const s.(ss_len), is_const ofs, is_const len with
    | Some sofs, Some slen, Some ofs, Some len => z' ++ [:: {| ss_ofs := Pconst (sofs + ofs); ss_len := len |}]
    | _, _, _, _ =>
      z ++ [:: {| ss_ofs := ofs; ss_len := len |}]
    end.

Definition sub_region_at_ofs sr ofs len :=
  {| sr_region := sr.(sr_region);
     sr_zone   := sub_zone_at_ofs sr.(sr_zone) ofs len
  |}.
(*
Fixpoint filter_tree (z : symbolic_zone) (tree : symbolic_tree) : option symbolic_tree :=
  match z with
  | [::] => Some tree
  | s :: z =>
    match tree with
    | Node s' l =>
      if symbolic_slice_beq s s' then
        let l' := pmap (filter_tree z) l in
        Some (Node s' l')
      else None
    end
  end.
*)
Definition symbolic_slice_ble (s1 s2 : symbolic_slice) :=
  let%opt ofs1 := is_const s1.(ss_ofs) in
  let%opt len1 := is_const s1.(ss_len) in
  let%opt ofs2 := is_const s2.(ss_ofs) in
  Some (ofs1 + len1 <=? ofs2)%Z.

Definition get_sub_forest s (f : symbolic_forest) : option symbolic_forest :=
  let: Nodes l := f in
  if l is [::] then Some f
  else
    let fix aux l :=
      match l with
      | [::] => None
      | (s', f') :: l =>
        if symbolic_slice_beq s s' then Some f'
        else if symbolic_slice_ble s s' then None
        else if symbolic_slice_ble s' s then aux l
        else
          Some emptyf
      end
    in
    aux l.

Definition sub_status_at_ofs (status:status) ofs len :=
  match status with
  | Valid => Valid
  | Unknown => Unknown
  | Borrowed l =>
    match get_sub_forest {| ss_ofs := ofs; ss_len := len |} l with
    | None => Valid
    | Some emptyf => Unknown
    | Some l => Borrowed l
    end
  end.

(*
(* TODO: If sub_region_at_ofs return sr, we don't want to filter. Should we deal
   with the special case ofs = 0 /\ len = size_of x here,
   instead of inside sub_region_at_ofs ? *)
Definition get_sub_region_bytes (rmap:region_map) (x:var_i) ofs len :=
  (* we get the bytes associated to variable [x] *)
  Let sr := get_sub_region rmap x in
  Let status := get_var_status rmap sr.(sr_region) x in
  let sr' := sub_region_at_ofs sr ofs len in
  ok (sr', filter_status sr'.(sr_zone) status).
*)
Definition is_valid status :=
  if status is Valid then true else false.

Definition check_valid x status :=
  assert (is_valid status)
         (stk_error x (pp_box [:: pp_s
           "the region associated to variable"; pp_var x; pp_s "is partial"])).
(*
(* could also be insert_zone z [::] -> means Valid = [::] may work *)
Fixpoint tree_of_zone z :=
  match z with
  | [::] => [::]
  | s :: z => [:: Node s (tree_of_zone z)]
  end.
*)

Fixpoint init_forest (z : symbolic_zone) (f : symbolic_forest) :=
  match z with
  | [::] => f
  | s :: z => Nodes [:: (s, init_forest z f)]
  end.

Fixpoint insert_sub_forest (f : symbolic_forest) z (subf : option symbolic_forest) : option symbolic_forest :=
  match z with
  | [::] => subf
  | s :: z =>
    let: Nodes l := f in
    if l is [::] then Some f
    else
      let fix aux (l:seq (symbolic_slice * symbolic_forest)) :=
        match l with
        | [::] =>
          match subf with
          | None => Some [::]
          | Some subf => Some [:: (s, init_forest z subf)]
          end
        | ((s', f') as tree) :: l' =>
          if symbolic_slice_beq s s' then
            match insert_sub_forest f' z subf with
            | None => Some l'
            | Some f => Some ((s, f) :: l')
            end
          else if odflt false (symbolic_slice_ble s s') then
            match subf with
            | None => Some l
            | Some subf => Some ((s, init_forest z subf) :: l)
            end
          else if odflt false (symbolic_slice_ble s' s) then
            let%opt l' := aux l' in
            Some (tree :: l')
          else (* not disjoint (or at least it was not proved) *)
            match is_const s.(ss_ofs), is_const s.(ss_len), is_const s'.(ss_ofs), is_const s'.(ss_len) with
            | Some ofs, Some len, Some ofs', Some len' =>
              (* special case: everything is constant, and [subf] is None (meaning Valid)
                 -> we check inclusion of s' in s and if ok, we remove [s']
                 Otherwise, we return None (meaning Unknown) *)
              if ((ofs <=? ofs') && (ofs' + len' <=? ofs + len))%Z then
                match subf with
                | None =>
                  let%opt l' := aux l' in
                  Some l'
                | Some _ => None
                end
              else None
            | _, _, _, _ =>
              None
            end
        end
      in
      match aux l with
      | None => Some emptyf
      | Some [::] => None
      | Some l => Some (Nodes l)
      end
  end.
(* pour la récursion interne:
    si la liste est vide : elle reste vide
    si la liste contient des choses disjointes : on ajoute
    - si on est None : on retire et on renvoie None
    si la liste contient s : on remplace et on appelle récursivement
    - si on est None : on retire et on renvoie None
    sinon, on est potentiellement non disjoint : on passe à liste vide
*)

Definition insert_sub_oforest (f : option symbolic_forest) z (subf : option symbolic_forest) : option symbolic_forest :=
  match f with
  | None => omap (init_forest z) subf
  | Some f => insert_sub_forest f z subf
  end.

(*
Definition z : symbolic_zone :=
  [:: {| ss_ofs := Pconst 0; ss_len := Pconst 10 |};
      {| ss_ofs := Pconst 1; ss_len := Pconst 1 |};
      {| ss_ofs := Pconst 0; ss_len := Pconst 1 |}].
Definition f : symbolic_forest :=
  Nodes [:: ({| ss_ofs := Pconst 0; ss_len := Pconst 10 |},
    Nodes [:: ({| ss_ofs := Pconst 1; ss_len := Pconst 1 |}, Nodes [::({| ss_ofs := Pconst 0; ss_len := Pconst 1 |}, emptyf)]);
              ({| ss_ofs := Pconst 8; ss_len := Pconst 1 |}, emptyf) ])].
Eval compute in insert_sub_forest3 (Some emptyf) [::] (Some emptyf).
Eval compute in insert_sub_forest2 f z None.
(* Eval compute in filter_status z (Borrowed [::tree]). *)
*)

(* None => non-disjoint zones, error
   Some None => disjoint zones
   Some z => suffix *)
Fixpoint get_suffix (z1 z2 : symbolic_zone) : option (option symbolic_zone) :=
  match z1 with
  | [::] => Some (Some z2)
  | s1 :: z1 =>
    match z2 with
    | [::] => None
    | s2 :: z2 =>
      if symbolic_slice_beq s1 s2 then get_suffix z1 z2
      else if odflt false (symbolic_slice_ble s1 s2) then Some None
      else if odflt false (symbolic_slice_ble s2 s1) then Some None
      else
        match is_const s1.(ss_ofs), is_const s1.(ss_len), is_const s2.(ss_ofs), is_const s2.(ss_len) with
        | Some ofs1, Some len1, Some ofs2, Some len2 =>
          let ofs := Z.max ofs1 ofs2 in
          let len := (Z.min (ofs1 + len1) (ofs2 + len2) - ofs)%Z in
          (* TODO: if this is the full zone, we could return None *)
          Some (Some [:: {| ss_ofs := ofs; ss_len := len |}])
        | _, _, _, _ => None
        end
    end
  end.

Definition insert_status rmap z x status subf :=
  let%opt z :=
    let%opt sr := Mvar.get rmap.(var_region) x in
    get_suffix sr.(sr_zone) z
  in
  match z with
  | None => Some status
  | Some z =>
    let f :=
      match status with
      | Valid => None
      | Unknown => Some emptyf
      | Borrowed f => Some f
      end
    in
    let f := insert_sub_oforest f z subf in
    match f with
    | None => Some Valid
    | Some emptyf => None (* Unknown *)
    | Some f => Some (Borrowed f)
    end
  end.

(* Clearing is equivalent to inserting empty. *)
Definition clear_status rmap z x status := insert_status rmap z x status (Some emptyf).

Definition clear_status_map rmap z (sm:status_map) :=
  Mvar.filter_map (clear_status rmap z) sm.

(* The name is chosen to be similar to [set_pure_bytes] and [set_move_bytes],
   but there are probably better ideas.
   TODO: factorize [set_clear_bytes] and [set_pure_bytes] ?
*)
Definition set_clear_status (rmap:region_map) sr :=
  let sm := get_status_map rmap sr.(sr_region) in
  let sm := clear_status_map rmap sr.(sr_zone) sm in
  Mr.set rmap sr.(sr_region) sm.

Definition set_clear_pure rmap sr :=
  {| var_region := rmap.(var_region);
     region_var := set_clear_status rmap sr |}.

Definition set_clear rmap x sr :=
  Let _ := writable x sr.(sr_region) in
  ok (set_clear_pure rmap sr).

(* We don't put Unknown in the map, we just remove it from the map. *)
Definition set_status sm x status :=
  match status with
  | Unknown => Mvar.remove sm x
  | _ => Mvar.set sm x status
  end.

(* word : clear + move *)
Definition set_word_status (rmap:region_map) sr x status :=
  let sm := get_status_map rmap sr.(sr_region) in
  let sm := clear_status_map rmap sr.(sr_zone) sm in
  let sm := set_status sm x status in
  Mr.set rmap sr.(sr_region) sm.

(*
(* TODO: take [bytes] as an argument ? *)
Definition set_pure_bytes rv (x:var) sr ofs len :=
  let z     := sr.(sr_zone) in
  let z1    := sub_zone_at_ofs z ofs len in
  let i     := interval_of_zone z1 in
  let bm    := get_bytes_map sr.(sr_region) rv in
  let bytes := if ofs is Some _ then ByteSet.add i (get_bytes x bm)
               else get_bytes x bm
  in
  (* clear all bytes corresponding to z1 *)
  let bm := clear_bytes_map i bm in
  (* set the bytes *)
  let bm := Mvar.set bm x bytes in
  Mr.set rv sr.(sr_region) bm.

Definition set_bytes rv (x:var_i) sr (ofs : option Z) (len : Z) :=
  Let _     := writable x sr.(sr_region) in
  ok (set_pure_bytes rv x sr ofs len).

(* TODO: as many functions are similar, maybe we could have one big function
   taking flags as arguments that tell whether we have to check align/check valid... *)
Definition set_sub_region rmap (x:var_i) sr (ofs : option Z) (len : Z) :=
  Let rv := set_bytes rmap x sr ofs len in
  ok {| var_region := Mvar.set rmap.(var_region) x sr;
        region_var := rv |}.
*)
Definition zone_of_cs cs : symbolic_zone :=
  [:: {| ss_ofs := Pconst cs.(cs_ofs); ss_len := Pconst cs.(cs_len) |}].

Definition sub_region_stkptr s ws cs :=
  let r := {| r_slot := s; r_align := ws; r_writable := true |} in
  let z := zone_of_cs cs in
  {| sr_region := r; sr_zone := z |}.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

Definition set_move_status rv x sr status :=
  let sm := get_status_map rv sr.(sr_region) in
  let sm := Mvar.set sm x status in
  Mr.set rv sr.(sr_region) sm.

Definition set_move (rmap:region_map) x sr status :=
  let rv := set_move_status rmap x sr status in
  {| var_region := Mvar.set rmap.(var_region) x sr;
     region_var := rv |}.

Definition set_move_sub_status rmap sr x status substatus :=
  let f :=
    match substatus with
    | Valid => None
    | Unknown => Some emptyf
    | Borrowed l => Some l
    end
  in
  let status := odflt Unknown (insert_status rmap sr.(sr_zone) x status f) in
  let sm := get_status_map rmap sr.(sr_region) in
  let sm := Mvar.set sm x status in
  Mr.set rmap sr.(sr_region) sm.

Definition set_move_sub (rmap:region_map) sr x status substatus :=
  let rv := set_move_sub_status rmap sr x status substatus in
  {| var_region := rmap.(var_region);
     region_var := rv |}.

Definition set_stack_ptr (rmap:region_map) s ws cs (x':var) :=
  let sr := sub_region_stkptr s ws cs in
  let rv := set_move_status rmap x' sr Valid in
  {| var_region := rmap.(var_region);
     region_var := rv |}.

Definition check_stack_ptr rmap s ws cs x' :=
  let sr := sub_region_stkptr s ws cs in
  let status := get_var_status rmap sr.(sr_region) x' in
  is_valid status.

End WITH_POINTER_DATA.

(*
(* Precondition size_of x = ws && length sr.sr_zone = wsize_size ws *)
Definition set_word rmap (x:var_i) sr ws :=
  Let _ := check_align Aligned x sr ws in
  set_sub_region rmap x sr (Some 0)%Z (size_slot x).

(* If we write to array [x] at offset [ofs], we invalidate the corresponding
   memory zone for the other variables, and mark it as valid for [x].
   The offset [ofs] can be None, meaning its exact value is not known. In this
   case, the full zone [z] associated to array [x] is invalidated for the
   other variables, and remains the zone associated to [x]. It is a safe
   approximation.
*)
(* [set_word], [set_stack_ptr] and [set_arr_word] could be factorized? -> think more about it *)
Definition set_arr_word (rmap:region_map) al (x:var_i) ofs ws :=
  Let sr := get_sub_region rmap x in
  Let _ := check_align al x sr ws in
  set_sub_region rmap x sr ofs (wsize_size ws).

Definition set_arr_call rmap x sr := set_sub_region rmap x sr (Some 0)%Z (size_slot x).

Definition set_move_bytes rv x sr bytesy :=
  let bm := get_bytes_map sr.(sr_region) rv in
  let bytes := get_bytes x bm in
  let bytes := ByteSet.remove bytes (interval_of_zone sr.(sr_zone)) in
  let bytes := ByteSet.union bytes bytesy in
  let bm := Mvar.set bm x bytes in
  Mr.set rv sr.(sr_region) bm.

Definition set_move_sub (rmap:region_map) x sr bytes :=
  let rv := set_move_bytes rmap x sr bytes in
  {| var_region := rmap.(var_region);
     region_var := rv |}.

Definition set_arr_sub (rmap:region_map) (x:var_i) ofs len sr_from bytesy :=
  Let sr := get_sub_region rmap x in
  let sr' := sub_region_at_ofs sr (Some ofs) len in
  Let _ := assert (sr' == sr_from)
                  (stk_ierror x
                    (pp_box [::
                      pp_s "the assignment to sub-array"; pp_var x;
                      pp_s "cannot be turned into a nop: source and destination regions are not equal"]))
  in
  ok (set_move_sub rmap x sr' bytesy).

(* identical to [set_sub_region], except clearing
   TODO: fusion with set_arr_sub ? not sure its worth
*)
Definition set_move (rmap:region_map) (x:var) sr bytesy :=
  let rv := set_move_bytes rmap x sr bytesy in
  {| var_region := Mvar.set rmap.(var_region) x sr;
     region_var := rv |}.

Definition set_arr_init rmap x sr := set_move rmap x sr.
*)
End Region.

Import Region.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {pd : PointerData}
  {msfsz : MSFsize}
  {asmop : asmOp asm_op}
.

Context (string_of_sr : sub_region -> string).

Definition mul := Papp2 (Omul (Op_w Uptr)).
Definition add := Papp2 (Oadd (Op_w Uptr)).

(* TODO: do we need to do the check here? I think we can always return the
   "else" version, and in a later pass, it will be recognized as a constant? *)
(* It seems indeed that it is an optim, mk_lea recognize that it is a constant. *)
Definition mk_ofs aa ws e1 :=
  let sz := mk_scale aa ws in
  if is_const e1 is Some i then
    cast_const (i * sz)%Z
  else
    mul (cast_const sz) (cast_ptr e1).

Definition mk_ofs_int aa ws e1 :=
  let sz := mk_scale aa ws in
  if is_const e1 is Some i then Pconst (i * sz)%Z else (Papp2 (Omul Op_int) (Pconst sz) e1).

(* Do we want the optim for constants? *)
Definition add_ofs ofs1 ofs2 :=
  (* or is_wconst_of_size ?? *)
  match is_wconst Uptr ofs1 with
  | Some w1 => cast_const (wunsigned w1 + ofs2)
  | None => add ofs1 (cast_const ofs2)
  end.
(*
Definition mk_ofsi aa ws e1 :=
  if is_const e1 is Some i then Some (i * (mk_scale aa ws))%Z
  else None.
*)
Section CHECK.

Context (print_rmap : instr_info -> region_map -> region_map).

(* The code in this file is called twice.
   - First, it is called from the stack alloc OCaml oracle. Indeed, the oracle
     returns initial results, and performs stack and reg allocation using
     these results. Based on the program that it obtains,
     it fixes some of the results and returns them.
   - Second, it is called as a normal compilation pass on the results returned
     by the oracle.

   When the code is called from the OCaml oracle, all the checks
   that are performed so that the pass can be proved correct are actually not
   needed. We introduce this boolean [check] to deactivate some of the tests
   when the code is called from the oracle.

   TODO: deactivate more tests (or even do not use rmap) when [check] is [false]
*)
Variable (check : bool).

Definition assert_check E b (e:E) :=
  if check then assert b e
  else ok tt.

Context
  (shparams : slh_lowering.sh_params)
  (saparams : stack_alloc_params).

Section Section.

Variables (pmap:pos_map).

Section ALLOC_E.

Variables (rmap: region_map).

Definition get_global (x:var_i) :=
  match Mvar.get pmap.(globals) x with
  | None => Error (stk_ierror_basic x "unallocated global variable")
  | Some z => ok z
  end.

Definition get_local (x:var) := Mvar.get pmap.(locals) x.

Definition check_diff (x:var_i) :=
  if Sv.mem x pmap.(vnew) then
    Error (stk_ierror_basic x "the code writes to one of the new variables")
  else ok tt.

Definition check_var (x:var_i) :=
  match get_local x with
  | None => ok tt
  | Some _ =>
    Error (stk_error x (pp_box [::
      pp_var x; pp_s "is a stack variable, but a reg variable is expected"]))
  end.

Definition with_var xi x :=
  {| v_var := x; v_info := xi.(v_info) |}.

Definition base_ptr sc :=
  match sc with
  | Slocal => pmap.(vrsp)
  | Sglob => pmap.(vrip)
  end.

Definition addr_from_pk (x:var_i) (pk:ptr_kind) :=
  match pk with
  | Pdirect _ ofs _ cs sc => ok (with_var x (base_ptr sc), ofs + cs.(cs_ofs))
  | Pregptr p             => ok (with_var x p,             0)
  | Pstkptr _ _ _ _ _     =>
    Error (stk_error x (pp_box [::
      pp_var x; pp_s "is a stack pointer, it should not appear in an expression"]))
  end%Z.

Definition addr_from_vpk x (vpk:vptr_kind) :=
  match vpk with
  | VKglob zws => ok (with_var x pmap.(vrip), zws.1)
  | VKptr pk => addr_from_pk x pk
  end.
(*
Definition mk_addr_ptr x aa ws (pk:ptr_kind) (e1:pexpr) :=
  Let xofs := addr_from_pk x pk in
  ok (xofs.1, mk_ofs aa ws e1 xofs.2).

Definition mk_addr x aa ws (vpk:vptr_kind) (e1:pexpr) :=
  Let xofs := addr_from_vpk x vpk in
  ok (xofs.1, mk_ofs aa ws e1 xofs.2).
*)
Definition get_var_kind x :=
  let xv := x.(gv) in
  if is_glob x then
    Let z := get_global xv in
    ok (Some (VKglob z))
  else
    ok (omap VKptr (get_local xv)).

Definition sub_region_full x r :=
  let z := [:: {| ss_ofs := Pconst 0; ss_len := Pconst (size_slot x) |}] in
  {| sr_region := r; sr_zone := z |}.

Definition sub_region_glob x ws :=
  let r := {| r_slot := x; r_align := ws; r_writable := false |} in
  sub_region_full x r.

Definition get_sub_region_status (rmap:region_map) (x:var_i) :=
  Let sr := get_sub_region rmap x in
  let status := get_var_status rmap sr.(sr_region) x in
  ok (sr, status).

(* TODO: better name *)
(* We need the vpk only to get the alignment in case VKglob *)
Definition gget_sub_region_status rmap (x:var_i) vpk :=
  match vpk with
  | VKglob (_, ws) =>
    let sr := sub_region_glob x ws in
    ok (sr, Valid)
  | VKptr _pk =>
    get_sub_region_status rmap x
  end.
(*
Definition check_vpk rmap (x:var_i) vpk :=
  match vpk with
  | VKglob (_, ws) =>
    let sr := sub_region_glob x ws in
    ok (sr, Valid)
  | VKptr _pk =>
    get_sub_region_bytes rmap x
  end.

Definition check_vpk_word rmap al x vpk ofs ws :=
  Let: (sr, sr', bytes) := check_vpk rmap x vpk ofs (wsize_size ws) in
  Let _ := check_valid x sr' bytes in
  check_align al x sr ws.
*)
Definition bad_arg_number := stk_ierror_no_var "invalid number of args".

Fixpoint alloc_e (e:pexpr) ty :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e
  | Pvar   x =>
    let xv := x.(gv) in
    Let vk := get_var_kind x in
    match vk with
    | None => Let _ := check_diff xv in ok e
    | Some vpk =>
      if is_word_type ty is Some ws then
        if subtype (sword ws) (vtype xv) then
          Let: (_, status) := gget_sub_region_status rmap xv vpk in
          Let _ := check_valid xv status in
(*           Let _ := check_vpk_word rmap Aligned xv vpk (Some 0%Z) ws in *)
(*           Let pofs := mk_addr xv AAdirect ws vpk (Pconst 0) in *)
          Let: (p, ofs) := addr_from_vpk xv vpk in
          ok (Pload Aligned ws p (cast_const ofs))
        else Error (stk_ierror_basic xv "invalid type for expression")
      else Error (stk_ierror_basic xv "not a word variable in expression")
    end

  | Pget al aa ws x e1 =>
    let xv := x.(gv) in
    Let e1 := alloc_e e1 sint in
    Let vk := get_var_kind x in
    match vk with
    | None => Let _ := check_diff xv in ok (Pget al aa ws x e1)
    | Some vpk =>
      Let: (_, status) := gget_sub_region_status rmap xv vpk in
      Let _ := check_valid xv status in
      Let: (p, ofs) := addr_from_vpk xv vpk in
      let ofs := add_ofs (mk_ofs aa ws e1) ofs in
(*       Let pofs := mk_addr xv aa ws vpk e1 in *)
      ok (Pload al ws p ofs)
    end

  | Psub aa ws len x e1 =>
    Error (stk_ierror_basic x.(gv) "Psub")

  | Pload al ws x e1 =>
    Let _ := check_var x in
    Let _ := check_diff x in
    Let e1 := alloc_e e1 (sword Uptr) in
    ok (Pload al ws x e1)

  | Papp1 o e1 =>
    Let e1 := alloc_e e1 (type_of_op1 o).1 in
    ok (Papp1 o e1)

  | Papp2 o e1 e2 =>
    let tys := type_of_op2 o in
    Let e1 := alloc_e e1 tys.1.1 in
    Let e2 := alloc_e e2 tys.1.2 in
    ok (Papp2 o e1 e2)

  | PappN o es =>
    Let es := mapM2 bad_arg_number alloc_e es (type_of_opN o).1 in
    ok (PappN o es)

  | Pif t e e1 e2 =>
    Let e := alloc_e e sbool in
    Let e1 := alloc_e e1 ty in
    Let e2 := alloc_e e2 ty in
    ok (Pif ty e e1 e2)
  end.

  Definition alloc_es es ty := mapM2 bad_arg_number alloc_e es ty.

End ALLOC_E.

Definition sub_region_direct x align cs sc :=
  let r := {| r_slot := x; r_align := align; r_writable := sc != Sglob |} in
  let z := zone_of_cs cs in
  {| sr_region := r; sr_zone := z |}.

Definition sub_region_stack x align cs :=
  sub_region_direct x align cs Slocal.

Definition sub_region_pk x pk :=
  match pk with
  | Pdirect x ofs align sub Slocal => ok (sub_region_stack x align sub)
  | _ => Error (stk_ierror x (pp_box [:: pp_var x; pp_s "is not in the stack"]))
  end.

(* We write in variable [x]. We clear the zone corresponding to [x] for all
   variables of the same region, and set [status] as the new status of [x]. *)
Definition set_word rmap sr (x:var_i) status ws :=
  Let _ := writable x sr.(sr_region) in
  Let _ := check_align Aligned x sr ws in
  ok
    {| var_region := rmap.(var_region);
       region_var := set_word_status rmap sr x status |}.

Definition alloc_lval (rmap: region_map) (r:lval) (ty:stype) :=
  match r with
  | Lnone _ _ => ok (rmap, r)

  | Lvar x =>
    match get_local x with
    | None => Let _ := check_diff x in ok (rmap, r)
    | Some pk =>
      if is_word_type (vtype x) is Some ws then
        if subtype (sword ws) ty then
          Let sr   := sub_region_pk x pk in
          Let rmap := set_word rmap sr x Valid ws in
(*           Let pofs := mk_addr_ptr x AAdirect ws pk (Pconst 0) in *)
          Let: (p, ofs) := addr_from_pk x pk in
          let r := Lmem Aligned ws p (cast_const ofs) in
          ok (rmap, r)
        else Error (stk_ierror_basic x "invalid type for assignment")
      else Error (stk_ierror_basic x "not a word variable in assignment")
    end

  | Laset al aa ws x e1 =>
    Let e1 := alloc_e rmap e1 sint in
    match get_local x with
    | None => Let _ := check_diff x in ok (rmap, Laset al aa ws x e1)
    | Some pk =>
      Let: (sr, status) := get_sub_region_status rmap x in
      Let rmap := set_word rmap sr x status ws in
(*       Let pofs := mk_addr_ptr x aa ws pk e1 in *)
      Let: (p, ofs) := addr_from_pk x pk in
      let ofs := add_ofs (mk_ofs aa ws e1) ofs in
      let r := Lmem al ws p ofs in
      ok (rmap, r)
    end

  | Lasub aa ws len x e1 =>
    Error (stk_ierror_basic x "Lasub")

  | Lmem al ws x e1 =>
    Let _ := check_var x in
    Let _ := check_diff x in
    Let e1 := alloc_e rmap e1 (sword Uptr) in
    ok (rmap, Lmem al ws x e1)
  end.

Definition nop := Copn [::] AT_none sopn_nop [::].

(* If a stack pointer already contains the right pointer, there is no need to
   assign it again, and a nop is issued. *)
Definition is_nop rmap x (sry:sub_region) s ws cs f : bool :=
  if Mvar.get rmap.(var_region) x is Some srx then
    (sub_region_beq srx sry) && check_stack_ptr rmap s ws cs f
  else false.

Definition get_addr (x:var_i) dx tag vpk y ofs :=
  let oir := sap_mov_ofs saparams dx tag vpk y ofs in
  match oir with
  | None =>
    let err_pp := pp_box [:: pp_s "cannot compute address"; pp_var x] in
    Error (stk_error x err_pp)
  | Some ir =>
    ok ir
  end.

(*
(* TODO: better error message *)
Definition get_addr is_spilling rmap x dx tag sry bytesy vpk y ofs :=
  let ir := if is_nop is_spilling rmap x sry
            then Some nop
            else sap_mov_ofs saparams dx tag vpk y ofs in
  let rmap := Region.set_move rmap x sry bytesy in
  (rmap, ir).

Definition get_ofs_sub aa ws x e1 :=
  match mk_ofsi aa ws e1 with
  | None     => Error (stk_ierror_basic x "cannot take/set a subarray on a unknown starting position")
  | Some ofs => ok ofs
  end.

Definition get_Lvar_sub lv :=
  match lv with
  | Lvar x => ok (x, None)
  | Lasub aa ws len x e1 =>
    Let ofs := get_ofs_sub aa ws x e1 in
    ok (x, Some (ofs, arr_size ws len))
  | _      => Error (stk_ierror_no_var "get_Lvar_sub: variable/subarray expected")
  end.

Definition get_Pvar_sub e :=
  match e with
  | Pvar x => ok (x, None)
  | Psub aa ws len x e1 =>
    Let ofs := get_ofs_sub aa ws x.(gv) e1 in
    ok (x, Some (ofs, arr_size ws len))
  | _      => Error (stk_ierror_no_var "get_Pvar_sub: variable/subarray expected")
  end.
*)
Definition is_stack_ptr vpk :=
  match vpk with
  | VKptr (Pstkptr s ofs ws z f) => Some (s, ofs, ws, z, f)
  | _ => None
  end.

(* Not so elegant: function [addr_from_vpk] can fail, but it
   actually fails only on the [Pstkptr] case, that is treated apart.
   Thus function [mk_addr_pexpr] never fails, but this is not checked statically.
*)
Definition mk_addr_pexpr rmap x vpk :=
  if is_stack_ptr vpk is Some (s, ofs, ws, cs, f) then
    Let _ :=
      assert
        (check_stack_ptr rmap s ws cs f)
        (stk_error x (pp_box [::
          pp_s "the stack pointer"; pp_var x; pp_s "is no longer valid"]))
    in
    ok (Pload Aligned Uptr (with_var x pmap.(vrsp)) (cast_const (ofs + cs.(cs_ofs))), 0%Z)
  else
    Let xofs := addr_from_vpk x vpk in
    ok (Plvar xofs.1, xofs.2).

(* TODO: the check [is_lvar] was removed, was it really on purpose? *)
(* TODO : currently, we check that the source array is valid and set the target
   array as valid too. We could, instead, give the same validity to the target
   array as the source one.
   [check_vpk] should be replaced with some function returning the valid bytes
   of y...
*)
(* Precondition is_sarr ty *)
Definition alloc_array_move rmap r tag e :=
  Let: (sry, statusy, vpk, ey, ofs) :=
    match e with
    | Pvar y =>
      let yv := y.(gv) in
      Let vk := get_var_kind y in
      match vk with
      | None => Error (stk_ierror_basic yv "register array remains")
      | Some vpk =>
        Let: (sr, status) := gget_sub_region_status rmap yv vpk in
        Let eofs := mk_addr_pexpr rmap yv vpk in
        ok (sr, status, vpk, eofs.1, cast_const eofs.2)
      end
    | Psub aa ws len y e1 =>
      let yv := y.(gv) in
      Let vk := get_var_kind y in
      match vk with
      | None => Error (stk_ierror_basic yv "register array remains")
      | Some vpk =>
        Let: (sr, status) := gget_sub_region_status rmap yv vpk in
        let ofs := mk_ofs aa ws e1 in
        let sr := sub_region_at_ofs sr (mk_ofs_int aa ws e1) (Pconst (arr_size ws len)) in
        let status := sub_status_at_ofs status (mk_ofs_int aa ws e1) (Pconst (arr_size ws len)) in
        Let eofs := mk_addr_pexpr rmap yv vpk in
        ok (sr, status, vpk, eofs.1, add_ofs ofs eofs.2)
      end
    | _ => Error (stk_ierror_no_var "alloc_array_move: variable/subarray expected (y)")
    end
  in

  match r with
  | Lvar x => 
    match get_local x with
    | None => Error (stk_ierror_basic x "register array remains")
    | Some pk =>
      match pk with
      | Pdirect s _ ws cs sc =>
        let sr := sub_region_direct s ws cs sc in
        Let _  :=
          assert (sub_region_beq sr sry)
                 (stk_ierror x
                    (pp_box [::
                      pp_s "the assignment to array"; pp_var x;
                      pp_s "cannot be turned into a nop: source (";
                      pp_s (string_of_sr sry);
                      pp_s ") and destination (";
                      pp_s (string_of_sr sr);
                      pp_s ") regions are not equal"]))
        in
        let rmap := set_move rmap x sry statusy in (* TODO: we always do set_move -> factorize *)
        ok (rmap, nop)
      | Pregptr p =>
        let rmap := set_move rmap x sry statusy in (* TODO: we always do set_move -> factorize *)
        Let ir := get_addr x (Lvar (with_var x p)) tag vpk ey ofs in
        ok (rmap, ir)
      | Pstkptr slot ofsx ws cs x' =>
        if is_nop rmap x sry slot ws cs x' then
          let rmap := set_move rmap x sry statusy in (* TODO: we always do set_move -> factorize *)
          ok (rmap, nop)
        else
          let rmap := set_move rmap x sry statusy in (* TODO: we always do set_move -> factorize *)
          let rmap := set_stack_ptr rmap slot ws cs x' in
          let dx_ofs := cast_const (ofsx + cs.(cs_ofs)) in
          let dx := Lmem Aligned Uptr (with_var x pmap.(vrsp)) dx_ofs in
          Let ir := get_addr x dx tag vpk ey ofs in
          ok (rmap, ir)
      end
    end
  | Lasub aa ws len x e =>
    match get_local (v_var x) with
    | None   => Error (stk_ierror_basic x "register array remains")
    | Some _ =>
      Let: (sr, status) := get_sub_region_status rmap x in
      let ofs := mk_ofs_int aa ws e in
      let sr' := sub_region_at_ofs sr ofs (Pconst (arr_size ws len)) in
      Let _ :=
        assert (sub_region_beq sr' sry)
               (stk_ierror x
                 (pp_box [::
                   pp_s "the assignment to sub-array"; pp_var x;
                   pp_s "cannot be turned into a nop: source (";
                   pp_vbox [::
                   pp_s (string_of_sr sry);
                   pp_s ") and destination (";
                   pp_s (string_of_sr sr')
                   ];
                   pp_s ") regions are not equal"]))
      in
      let rmap := set_move_sub rmap sr' x status statusy in
      ok (rmap, nop)
    end

  | _ => Error (stk_ierror_no_var "alloc_array_move: variable/subarray expected (x)")
  end.

Definition is_protect_ptr_fail (rs:lvals) (o:sopn) (es:pexprs) :=
  match o, rs, es with
  | Oslh (SLHprotect_ptr_fail _), [::r], [:: e; msf] => Some (r, e, msf)
  | _, _, _ => None
  end.

Definition lower_protect_ptr_fail ii lvs t es :=
  slh_lowering.lower_slho shparams ii lvs t (SLHprotect Uptr) es.

(* This seems to be a duplication of alloc_array_move, but we are able to share
   the corresponding proofs *)
Definition alloc_protect_ptr rmap ii r t e msf :=
  Let: (sry, statusy, vpk, ey) :=
    match e with
    | Pvar y =>
      let yv := y.(gv) in
      Let vk := get_var_kind y in
      match vk with
      | None => Error (stk_ierror_basic yv "register array remains")
      | Some vpk =>
        Let _ := assert (if vpk is VKptr (Pregptr _) then true else false)
                        (stk_error_no_var "argument of protect_ptr should be a reg ptr") in
        Let _ := assert (if r is Lvar _ then true else false)
                        (stk_error_no_var "destination of protect_ptr should be a reg ptr") in
        Let: (sr, status) := gget_sub_region_status rmap yv vpk in
        Let: (e, _ofs) := mk_addr_pexpr rmap yv vpk in (* ofs is ensured to be 0 *)
        ok (sr, status, vpk, e)
      end
    | Psub _ _ _ _ _ =>
      Error (stk_error_no_var "argument of protect_ptr cannot be a sub array")
    | _ => Error (stk_ierror_no_var "alloc_protect_ptr: variable/subarray expected (y)")
    end
  in

  match r with
  | Lvar x => 
    match get_local x with
    | None => Error (stk_ierror_basic x "register array remains")
    | Some pk =>
      match pk with
      | Pregptr p =>
        let rmap := set_move rmap x sry statusy in
        let dx := Lvar (with_var x p) in
        Let msf := add_iinfo ii (alloc_e rmap msf (sword msf_size)) in
        Let ir := lower_protect_ptr_fail ii [::dx] t [:: ey; msf] in
        ok (rmap, ir)
      | _ => Error (stk_error_no_var "only reg ptr can receive the result of protect_ptr")
      end
    end
  | Lasub _ _ _ _ _ =>
    Error (stk_error_no_var "cannot assign protect_ptr in a sub array")

  | _ => Error (stk_ierror_no_var "alloc_array_move: variable/subarray expected (x)")
  end.

(* We do not update the [var_region] part *)
(* there seems to be an invariant: all Pdirect are in the rmap *)
(* long-term TODO: we can avoid putting PDirect in the rmap (look in pmap instead) *)
Definition alloc_array_move_init rmap r tag e :=
  if is_array_init e then
    match r with
    | Lvar x =>
      Let sr :=
        match get_local x with
        | None    => Error (stk_ierror_basic x "register array remains")
        | Some pk =>
          match pk with
          | Pdirect x' _ ws cs sc =>
            if sc is Slocal then
              ok (sub_region_stack x' ws cs)
            else
              Error (stk_error x (pp_box [:: pp_s "cannot initialize glob array"; pp_var x]))
          | _ =>
            get_sub_region rmap x
          end
        end
      in
      let rmap := set_move rmap x sr Valid in
      ok (rmap, nop)
    | _ => Error (stk_ierror_no_var "arrayinit of non-variable")
    end
  else alloc_array_move rmap r tag e.

Definition bad_lval_number := stk_ierror_no_var "invalid number of lval".

Definition alloc_lvals rmap rs tys :=
  fmapM2 bad_lval_number alloc_lval rmap rs tys.

Section LOOP.
(*
Definition incl_status status1 status2 :=
  match status1, status2 with
  | Unknown, _ => true
  | _, Valid => true
  | Borrowed zs1, Borrowed zs2 => all (fun z => has (incl_zones z) zs1) zs2
  | _, _ => false
  end.

Definition incl_bytes_map (_r: region) (bm1 bm2: bytes_map) :=
  Mvar.incl (fun x => ByteSet.subset) bm1 bm2.

Definition incl (rmap1 rmap2:region_map) :=
  Mvar.incl (fun x r1 r2 => r1 == r2) rmap1.(var_region) rmap2.(var_region) &&
  Mr.incl incl_bytes_map rmap1.(region_var) rmap2.(region_var).
*)

Definition merge_forest (f1 f2 : symbolic_forest) :=
  let: Nodes l1 := f1 in
  foldl (fun acc '(s, f) =>
    let%opt acc := acc in
    insert_sub_forest acc [:: s] (Some f)) (Some f2) l1.

Definition merge_status (_x:var) (status1 status2: option status) :=
  let%opt status1 := status1 in
  let%opt status2 := status2 in
  match status1, status2 with
  | Unknown, _ | _, Unknown => None
  | Valid, s | s, Valid => Some s
  | Borrowed f1, Borrowed f2 =>
    let%opt f := merge_forest f1 f2 in
    Some (Borrowed f)
  end.

Definition merge_status_map (_r:region) (bm1 bm2: option status_map) :=
  match bm1, bm2 with
  | Some bm1, Some bm2 =>
    let bm := Mvar.map2 merge_status bm1 bm2 in
    if Mvar.is_empty bm then None
    else Some bm
  | _, _ => None
  end.

Definition merge (rmap1 rmap2:region_map) :=
  {| var_region :=
       Mvar.map2 (fun _ osr1 osr2 =>
        match osr1, osr2 with
        | Some sr1, Some sr2 => if sub_region_beq sr1 sr2 then osr1 else None
        | _, _ => None
        end) rmap1.(var_region) rmap2.(var_region);
     region_var := Mr.map2 merge_status_map rmap1.(region_var) rmap2.(region_var) |}.
(*
 Variable ii:instr_info.

 Variable check_c2 : region_map -> cexec ((region_map * region_map) * (pexpr * (seq cmd * seq cmd)) ).

 Fixpoint loop2 (n:nat) (m:region_map) :=
    match n with
    | O => Error (pp_at_ii ii (stk_ierror_no_var "loop2"))
    | S n =>
      Let m' := check_c2 m in
      if incl m m'.1.2 then ok (m'.1.1, m'.2)
      else loop2 n (merge m m'.1.2)
    end.
*)
End LOOP.

Record stk_alloc_oracle_t :=
  { sao_align : wsize
  ; sao_size: Z
  ; sao_ioff: Z
  ; sao_extra_size: Z
  ; sao_max_size : Z
  ; sao_max_call_depth : Z
  ; sao_params : seq (option param_info)  (* Allocation of pointer params *)
  ; sao_return : seq (option nat)         (* Where to find the param input region *)
  ; sao_slots : seq (var * wsize * Z)
  ; sao_alloc: seq (var * ptr_kind_init)   (* Allocation of local variables without params, and stk ptr *)
  ; sao_to_save: seq (var * Z)
  ; sao_rsp: saved_stack
  ; sao_return_address: return_address_location
  }.

Definition sao_frame_size sao :=
  if is_RAnone sao.(sao_return_address) then
    (sao.(sao_size) + sao.(sao_extra_size))%Z
  else
    (round_ws sao.(sao_align) (sao.(sao_size) + sao.(sao_extra_size)))%Z.

Section PROG.

Context (local_alloc: funname -> stk_alloc_oracle_t).

Definition get_Pvar e :=
  match e with
  | Pvar x => ok x
  | _      => Error (stk_ierror_no_var "get_Pvar: variable expected")
  end.

(* We clear the arguments. This is not necessary in the classic case, because
   we also clear them when assigning the results in alloc_call_res
   (this works if each writable reg ptr is returned (which is currently
   checked by the pretyper) and if each result variable has the same size
   as the corresponding input variable).
   But this complexifies the proof and needs a few more
   checks in stack_alloc to be valid. Thus, for the sake of simplicity, it was
   decided to make the clearing of the arguments twice : here and in
   alloc_call_res.

   We use two rmaps:
   - the initial rmap [rmap0] is used to check the validity of the sub-regions;
   - the current rmap [rmap] is [rmap0] with all the previous writable sub-regions cleared.
   Actually, we could use [rmap] to check the validity, and that would partially
   enforce that the arguments correspond to disjoint regions (in particular,
   writable sub-regions are pairwise disjoint), so with this version we could
   simplify check_all_disj. If we first check the validity and clear the writable regions,
   and then check the validity of the non-writable ones, we can even remove [check_all_disj].
   But the error message (disjoint regions) is much clearer when we have [check_all_disj],
   so I leave it as it is now.
*)
Definition alloc_call_arg_aux rmap0 rmap (sao_param: option param_info) (e:pexpr) :=
  Let x := get_Pvar e in
  Let _ := assert (~~is_glob x)
                  (stk_ierror_basic x.(gv) "global variable in argument of a call") in
  let xv := gv x in
  match sao_param, get_local xv with
  | None, None =>
    Let _ := check_diff xv in
    ok (rmap, (None, Pvar x))
  | None, Some _ => Error (stk_ierror_basic xv "argument not a reg")
  | Some pi, Some (Pregptr p) =>
    Let: (sr, status) := get_sub_region_status rmap0 xv in
    Let _ := check_valid xv status in
    Let _  := check_align Aligned xv sr pi.(pp_align) in
    Let rmap :=
      if pi.(pp_writable) then
        set_clear rmap xv sr
      else ok rmap
    in
    ok (rmap, (Some (pi.(pp_writable),sr), Pvar (mk_lvar (with_var xv p))))
  | Some _, _ => Error (stk_ierror_basic xv "the argument should be a reg ptr")
  end.

Definition alloc_call_args_aux rmap sao_params es :=
  fmapM2 (stk_ierror_no_var "bad params info") (alloc_call_arg_aux rmap) rmap sao_params es.

Fixpoint disjoint_zones z1 z2 : bool :=
  match z1, z2 with
  | [::], _ | _, [::] => false
  | s1 :: z1, s2 :: z2 =>
    if symbolic_slice_beq s1 s2 then disjoint_zones z1 z2
    else if odflt false (symbolic_slice_ble s1 s2) then true
    else if odflt false (symbolic_slice_ble s2 s1) then true
    else (* not disjoint (or at least it was not proved) *)
      false
  end.

Definition disj_sub_regions sr1 sr2 :=
  ~~(region_same sr1.(sr_region) sr2.(sr_region)) ||
  disjoint_zones sr1.(sr_zone) sr2.(sr_zone).

Fixpoint check_all_disj (notwritables writables:seq sub_region) (srs:seq (option (bool * sub_region) * pexpr)) :=
  match srs with
  | [::] => true
  | (None, _) :: srs => check_all_disj notwritables writables srs
  | (Some (writable, sr), _) :: srs =>
    if all (disj_sub_regions sr) writables then
      if writable then
        if all (disj_sub_regions sr) notwritables then
          check_all_disj notwritables (sr::writables) srs
        else false
      else check_all_disj (sr::notwritables) writables srs
    else false
  end.

Definition alloc_call_args rmap (sao_params: seq (option param_info)) (es:seq pexpr) :=
  Let es := alloc_call_args_aux rmap sao_params es in
  Let _  := assert (check_all_disj [::] [::] es.2)
                   (stk_error_no_var "some writable reg ptr are not disjoints") in
  ok es.

Definition check_lval_reg_call (r:lval) :=
  match r with
  | Lnone _ _ => ok tt
  | Lvar x =>
    match get_local x with
    | None   => Let _ := check_diff x in ok tt
    | Some _ => Error (stk_ierror_basic x "call result should be stored in reg")
    end
  | Laset _ aa ws x e1 => Error (stk_ierror_basic x "array assignement in lval of a call")
  | Lasub aa ws len x e1 => Error (stk_ierror_basic x "sub-array assignement in lval of a call")
  | Lmem al ws x e1  => Error (stk_ierror_basic x "call result should be stored in reg")
  end.

Definition get_regptr (x:var_i) :=
  match get_local x with
  | Some (Pregptr p) => ok (with_var x p)
  | _ => Error (stk_ierror x (pp_box [:: pp_s "variable"; pp_var x; pp_s "should be a reg ptr"]))
  end.

Definition alloc_lval_call (srs:seq (option (bool * sub_region) * pexpr)) rmap (r: lval) (i:option nat) :=
  match i with
  | None =>
    Let _ := check_lval_reg_call r in
    ok (rmap, r)
  | Some i =>
    match nth (None, Pconst 0) srs i with
    | (Some (_,sr), _) =>
      match r with
      | Lnone i _ => ok (rmap, Lnone i (sword Uptr))
      | Lvar x =>
        Let p := get_regptr x in
        let rmap := set_move rmap x sr Valid in (* FIXME: no align check *)
        (* TODO: Lvar p or Lvar (with_var x p) like in alloc_call_arg? *)
        ok (rmap, Lvar p)
      | Laset _ aa ws x e1 => Error (stk_ierror_basic x "array assignement in lval of a call")
      | Lasub aa ws len x e1 => Error (stk_ierror_basic x "sub-array assignement in lval of a call")
      | Lmem al ws x e1  => Error (stk_ierror_basic x "call result should be stored in reg ptr")
      end
    | (None, _) => Error (stk_ierror_no_var "alloc_lval_call")
    end
  end.

Definition alloc_call_res rmap srs ret_pos rs :=
  fmapM2 bad_lval_number (alloc_lval_call srs) rmap rs ret_pos.

Definition alloc_call (sao_caller:stk_alloc_oracle_t) rmap rs fn es :=
  let sao_callee := local_alloc fn in
  Let es  := alloc_call_args rmap sao_callee.(sao_params) es in
  let '(rmap, es) := es in
  Let rs  := alloc_call_res rmap es sao_callee.(sao_return) rs in
  Let _   := assert_check (~~ is_RAnone sao_callee.(sao_return_address))
               (stk_ierror_no_var "cannot call export function")
  in
  Let _   :=
    let local_size := sao_frame_size sao_caller in
    assert_check (local_size + sao_callee.(sao_max_size) <=? sao_caller.(sao_max_size))%Z
                 (stk_ierror_no_var "error in max size computation")
  in
  Let _   := assert_check (sao_callee.(sao_align) <= sao_caller.(sao_align))%CMP
                          (stk_ierror_no_var "non aligned function call")
  in
  let es  := map snd es in
  ok (rs.1, Ccall rs.2 fn es).

(* Before stack_alloc :
     Csyscall [::x] (getrandom len) [::t]
     t : arr n & len <= n.
     return arr len.
   After:
     xlen: Uptr
     xlen := len;
     Csyscall [::xp] (getrandom len) [::p, xlen]
*)
Definition alloc_syscall ii rmap rs o es :=
  add_iinfo ii
  match o with
  | RandomBytes len =>
    (* per the semantics, we have [len <= wbase Uptr], but we need [<] *)
    Let _ := assert (len <? wbase Uptr)%Z
                    (stk_error_no_var "randombytes: the requested size is too large")
    in
    match rs, es with
    | [::Lvar x], [::Pvar xe] =>
      let xe := xe.(gv) in
      let xlen := with_var xe (vxlen pmap) in
      Let p  := get_regptr xe in
      Let xp := get_regptr x in
      Let sr := get_sub_region rmap xe in
      let rmap := set_move rmap x sr Valid in (* FIXME *)
      ok (rmap,
          [:: MkI ii (sap_immediate saparams xlen (Zpos len));
              MkI ii (Csyscall [::Lvar xp] o [:: Plvar p; Plvar xlen])])
    | _, _ =>
      Error (stk_ierror_no_var "randombytes: invalid args or result")
    end
  end.

Definition is_swap_array o :=
  match o with
  | Opseudo_op (pseudo_operator.Oswap ty) => is_sarr ty
  | _ => false
  end.

Definition alloc_array_swap rmap rs t es :=
  match rs, es with
  | [:: Lvar x; Lvar y], [::Pvar z'; Pvar w'] =>
    let z := z'.(gv) in
    Let pz  := get_regptr z in
    Let: (srz, statusz) := get_sub_region_status rmap z in
    let w := w'.(gv) in
    Let pw := get_regptr w in
    Let: (srw, statusw) := get_sub_region_status rmap w in
    let rmap := set_move rmap x srw statusw in
    let rmap := set_move rmap y srz statusz in
    Let px := get_regptr x in
    Let py := get_regptr y in
    Let _ := assert ((is_lvar z') && (is_lvar w'))
              (stk_ierror_no_var "global reg ptr ...") in
    ok (rmap, saparams.(sap_swap) t px py pz pw)
  | _, _ =>
    Error (stk_error_no_var "swap: invalid args or result, only reg ptr are accepted")
  end.

Fixpoint alloc_i sao (rmap:region_map) (i: instr) : cexec (region_map * cmd) :=
  let (ii, ir) := i in
  Let: (rmap, c) :=
    match ir with
    | Cassgn r t ty e =>
      if is_sarr ty then
        Let ri := add_iinfo ii (alloc_array_move_init rmap r t e) in
        ok (ri.1, [:: MkI ii ri.2])
      else
        Let e := add_iinfo ii (alloc_e rmap e ty) in
        Let r := add_iinfo ii (alloc_lval rmap r ty) in
        ok (r.1, [:: MkI ii (Cassgn r.2 t ty e)])

    | Copn rs t o e =>
      if is_protect_ptr_fail rs o e is Some (r, e, msf) then
         Let rs := alloc_protect_ptr rmap ii r t e msf in
         ok (rs.1, [:: MkI ii rs.2])
      else
      if is_swap_array o then
        Let rs := add_iinfo ii (alloc_array_swap rmap rs t e) in
        ok (rs.1, [:: MkI ii rs.2])
      else
      Let e  := add_iinfo ii (alloc_es rmap e (sopn_tin o)) in
      Let rs := add_iinfo ii (alloc_lvals rmap rs (sopn_tout o)) in
      ok (rs.1, [:: MkI ii (Copn rs.2 t o e)])

    | Csyscall rs o es =>
      alloc_syscall ii rmap rs o es

    | Cif e c1 c2 =>
      Let e := add_iinfo ii (alloc_e rmap e sbool) in
      Let c1 := fmapM (alloc_i sao) rmap c1 in
      Let c2 := fmapM (alloc_i sao) rmap c2 in
      let rmap:= merge c1.1 c2.1 in
      ok (rmap, [:: MkI ii (Cif e (flatten c1.2) (flatten c2.2))])

    | Cwhile a c1 e c2 =>
      Let c1' := fmapM (alloc_i sao) rmap c1 in
      let rmap1 := c1'.1 in
      Let e := add_iinfo ii (alloc_e rmap1 e sbool) in
      Let c2' := fmapM (alloc_i sao) rmap1 c2 in
      let rmap2 := c2'.1 in
      Let c3' := fmapM (alloc_i sao) rmap2 c1 in
      let rmap3 := c3'.1 in
      let rmap := merge rmap1 rmap3 in
      ok (rmap, [:: MkI ii (Cwhile a (flatten c1'.2) e (flatten c2'.2))])

    | Ccall rs fn es =>
      Let ri := add_iinfo ii (alloc_call sao rmap rs fn es) in
      ok (ri.1, [::MkI ii ri.2])

    | Cfor _ _ _  => Error (pp_at_ii ii (stk_ierror_no_var "don't deal with for loop"))

    end
    in
    ok (print_rmap ii rmap, c).

End PROG.

End Section.

Definition init_stack_layout (mglob : Mvar.t (Z * wsize)) sao :=
  let add (xsr: var * wsize * Z)
          (slp:  Mvar.t (Z * wsize) * Z) :=
    let '(stack, p) := slp in
    let '(x,ws,ofs) := xsr in
    if Mvar.get stack x is Some _ then Error (stk_ierror_no_var "duplicate stack region")
    else if Mvar.get mglob x is Some _ then Error (stk_ierror_no_var "a region is both glob and stack")
    else
      if (p <= ofs)%CMP then
        let len := size_slot x in
        if (ws <= sao.(sao_align))%CMP then
          if (Z.land ofs (wsize_size ws - 1) == 0)%Z then
            let stack := Mvar.set stack x (ofs, ws) in
            ok (stack, (ofs + len)%Z)
          else Error (stk_ierror_no_var "bad stack region alignment")
        else Error (stk_ierror_no_var "bad stack alignment")
      else Error (stk_ierror_no_var "stack region overlap") in
  Let _ := assert (0 <=? sao.(sao_ioff))%Z (stk_ierror_no_var "negative initial stack offset") in
  Let sp := foldM add (Mvar.empty _, sao.(sao_ioff)) sao.(sao_slots) in
  let '(stack, size) := sp in
  if (size <= sao.(sao_size))%CMP then ok stack
  else Error (stk_ierror_no_var "stack size").

Definition add_alloc globals stack (xpk:var * ptr_kind_init) (lrx: Mvar.t ptr_kind * region_map * Sv.t) :=
  let '(locals, rmap, sv) := lrx in
  let '(x, pk) := xpk in
  if Sv.mem x sv then Error (stk_ierror_no_var "invalid reg pointer")
  else if Mvar.get locals x is Some _ then
    Error (stk_ierror_no_var "the oracle returned two results for the same var")
  else
    Let svrmap :=
      match pk with
      | PIdirect x' cs sc =>
        let vars := if sc is Slocal then stack else globals in
        match Mvar.get vars x' with
        | None => Error (stk_ierror_no_var "unknown region")
        | Some (ofs', ws') =>
          if [&& (size_slot x <= cs.(cs_len))%CMP, (0%Z <= cs.(cs_ofs))%CMP &
                 ((cs.(cs_ofs) + cs.(cs_len))%Z <= size_slot x')%CMP] then
            let rmap :=
              if sc is Slocal then
                let sr := sub_region_stack x' ws' cs in
                set_move rmap x sr Valid
              else
                rmap
            in
            ok (sv, Pdirect x' ofs' ws' cs sc, rmap)
          else Error (stk_ierror_no_var "invalid slot")
        end
      | PIstkptr x' cs xp =>
        if ~~ is_sarr x.(vtype) then
          Error (stk_ierror_no_var "a stk ptr variable must be an array")
        else
        match Mvar.get stack x' with
        | None => Error (stk_ierror_no_var "unknown stack region")
        | Some (ofs', ws') =>
          if Sv.mem xp sv then Error (stk_ierror_no_var "invalid stk ptr (not unique)")
          else if xp == x then Error (stk_ierror_no_var "a pseudo-var is equal to a program var")
          else if Mvar.get locals xp is Some _ then Error (stk_ierror_no_var "a pseudo-var is equal to a program var")
          else
            if [&& (Uptr <= ws')%CMP,
                (0%Z <= cs.(cs_ofs))%CMP,
                (Z.land cs.(cs_ofs) (wsize_size Uptr - 1) == 0)%Z,
                (wsize_size Uptr <= cs.(cs_len))%CMP &
                ((cs.(cs_ofs) + cs.(cs_len))%Z <= size_slot x')%CMP] then
              ok (Sv.add xp sv, Pstkptr x' ofs' ws' cs xp, rmap)
          else Error (stk_ierror_no_var "invalid ptr kind")
        end
      | PIregptr p =>
        if ~~ is_sarr x.(vtype) then
          Error (stk_ierror_no_var "a reg ptr variable must be an array")
        else
        if Sv.mem p sv then Error (stk_ierror_no_var "invalid reg pointer already exists")
        else if Mvar.get locals p is Some _ then Error (stk_ierror_no_var "a pointer is equal to a program var")
        else if vtype p != sword Uptr then Error (stk_ierror_no_var "invalid pointer type")
        else ok (Sv.add p sv, Pregptr p, rmap)
      end in
    let '(sv,pk, rmap) := svrmap in
    let locals := Mvar.set locals x pk in
    ok (locals, rmap, sv).

Definition init_local_map vrip vrsp vxlen globals stack sao :=
  Let _ := assert (vxlen != vrip) (stk_ierror_no_var "two fresh variables are equal") in
  Let _ := assert (vxlen != vrsp) (stk_ierror_no_var "two fresh variables are equal") in
  let sv := Sv.add vxlen (Sv.add vrip (Sv.add vrsp Sv.empty)) in
  Let aux := foldM (add_alloc globals stack) (Mvar.empty _, empty, sv) sao.(sao_alloc) in
  let '(locals, rmap, sv) := aux in
  ok (locals, rmap, sv).

(** For each function, the oracle returns:
  - the size of the stack block;
  - an allocation for local variables;
  - an allocation for the variables to save;
  - where to save the stack pointer (of the caller); (* TODO: merge with above? *)
  - how to pass the return address (non-export functions only)

  It can call back the partial stack-alloc transformation that given an oracle (size of the stack block and allocation of stack variables)
  will transform the body of the current function.

  The oracle is implemented as follows:
   1/ stack allocation
   2/ Reg allocation
   3/ if we have remaining register to save the stack pointer we use on those register
      else
        4/ we restart stack allocation and we keep one position in the stack to save the stack pointer
        5/ Reg allocation
*)

Definition check_result pmap rmap paramsi params oi (x:var_i) :=
  match oi with
  | Some i =>
    match nth None paramsi i with
    | Some sr_param =>
      Let _ := assert (x.(vtype) == (nth x params i).(vtype))
                      (stk_ierror_no_var "reg ptr in result not corresponding to a parameter") in
      Let: (sr, status) := get_sub_region_status rmap x in
      Let _ := check_valid x status in
      Let _  := assert (sub_region_beq sr_param sr) (stk_ierror_no_var "invalid reg ptr in result") in
      Let p  := get_regptr pmap x in
      ok p
    | None => Error (stk_ierror_no_var "invalid function info")
    end
  | None =>
    Let _ := check_var pmap x in
    Let _ := check_diff pmap x in
    ok x
  end.

(* TODO: clean the 3 [all2] functions *)
Definition check_all_writable_regions_returned paramsi (ret_pos:seq (option nat)) :=
  all2 (fun i osr =>
    match osr with
    | Some sr => if sr.(sr_region).(r_writable) then Some i \in ret_pos else true
    | None => true
    end) (iota 0 (size paramsi)) paramsi.

Definition check_results pmap rmap paramsi params ret_pos res :=
  Let _ := assert (check_all_writable_regions_returned paramsi ret_pos)
                  (stk_ierror_no_var "a writable region is not returned")
  in
  mapM2 (stk_ierror_no_var "invalid function info")
        (check_result pmap rmap paramsi params) ret_pos res.

(* TODO: is duplicate region the best error msg ? *)
Definition init_param (mglob stack : Mvar.t (Z * wsize)) accu pi (x:var_i) :=
  let: (disj, lmap, rmap) := accu in
  Let _ := assert (~~ Sv.mem x disj) (stk_ierror_no_var "a parameter already exists") in
  if Mvar.get lmap x is Some _ then Error (stk_ierror_no_var "a stack variable also occurs as a parameter")
  else
  match pi with
  | None => ok (accu, (None, x))
  | Some pi =>
    Let _ := assert (vtype pi.(pp_ptr) == sword Uptr) (stk_ierror_no_var "bad ptr type") in
    Let _ := assert (~~Sv.mem pi.(pp_ptr) disj) (stk_ierror_no_var "duplicate region") in
    Let _ := assert (is_sarr x.(vtype)) (stk_ierror_no_var "bad reg ptr type") in
    if Mvar.get lmap pi.(pp_ptr) is Some _ then Error (stk_ierror_no_var "a pointer is equal to a local var")
    else if Mvar.get mglob x is Some _ then Error (stk_ierror_no_var "a region is both glob and param")
    else if Mvar.get stack x is Some _ then Error (stk_ierror_no_var "a region is both stack and param")
    else
    let r :=
      {| r_slot := x;
         r_align := pi.(pp_align); r_writable := pi.(pp_writable) |} in
    let sr := sub_region_full x r in
    ok (Sv.add pi.(pp_ptr) disj,
        Mvar.set lmap x (Pregptr pi.(pp_ptr)),
        set_move rmap x sr Valid,
        (Some sr, with_var x pi.(pp_ptr)))
  end.

Definition init_params mglob stack disj lmap rmap sao_params params :=
  fmapM2 (stk_ierror_no_var "invalid function info")
    (init_param mglob stack) (disj, lmap, rmap) sao_params params.

Definition alloc_fd_aux p_extra mglob (fresh_reg : string -> stype -> Ident.ident) (local_alloc: funname -> stk_alloc_oracle_t) sao fd : cexec _ufundef :=
  let vrip := {| vtype := sword Uptr; vname := p_extra.(sp_rip) |} in
  let vrsp := {| vtype := sword Uptr; vname := p_extra.(sp_rsp) |} in
  let vxlen := {| vtype := sword Uptr; vname := fresh_reg "__len__"%string (sword Uptr) |} in
  let ra := sao.(sao_return_address) in
  Let stack := init_stack_layout mglob sao in
  Let mstk := init_local_map vrip vrsp vxlen mglob stack sao in
  let '(locals, rmap, disj) := mstk in
  (* adding params to the map *)
  Let rparams :=
    init_params mglob stack disj locals rmap sao.(sao_params) fd.(f_params) in
  let: (sv, lmap, rmap, alloc_params) := rparams in
  let paramsi := map fst alloc_params in
  let params : seq var_i := map snd alloc_params in
  let pmap := {|
        vrip    := vrip;
        vrsp    := vrsp;
        vxlen   := vxlen;
        globals := mglob;
        locals  := lmap;
        vnew    := sv;
      |} in
  Let _ := assert (0 <=? sao.(sao_extra_size))%Z
                  (stk_ierror_no_var "negative extra size")
  in
  Let _ :=
    let local_size := sao_frame_size sao in
    assert_check (local_size <=? sao.(sao_max_size))%Z
                 (stk_ierror_no_var "sao_max_size too small")
  in
  Let rbody := fmapM (alloc_i pmap local_alloc sao) rmap fd.(f_body) in
  let: (rmap, body) := rbody in
  Let res :=
      check_results pmap rmap paramsi fd.(f_params) sao.(sao_return) fd.(f_res) in
  ok {|
    f_info := f_info fd;
    f_tyin := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_params) fd.(f_tyin);
    f_params := params;
    f_body := flatten body;
    f_tyout := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_return) fd.(f_tyout);
    f_res := res;
    f_extra := f_extra fd |}.

Definition alloc_fd p_extra mglob (fresh_reg : string -> stype -> Ident.ident) (local_alloc: funname -> stk_alloc_oracle_t) fn fd :=
  let: sao := local_alloc fn in
  Let fd := alloc_fd_aux p_extra mglob fresh_reg local_alloc sao fd in
  let f_extra := {|
        sf_align  := sao.(sao_align);
        sf_stk_sz := sao.(sao_size);
        sf_stk_ioff := sao.(sao_ioff);
        sf_stk_extra_sz := sao.(sao_extra_size);
        sf_stk_max := sao.(sao_max_size);
        sf_max_call_depth := sao.(sao_max_call_depth);
        sf_to_save := sao.(sao_to_save);
        sf_save_stack := sao.(sao_rsp);
        sf_return_address := sao.(sao_return_address);
        sf_align_args := map (oapp pp_align U8) sao.(sao_params)
      |} in
  ok (swith_extra fd f_extra).

Fixpoint ptake (A:Type) p (r l:list A) :=
  match p, l with
  | xH, x :: l => Some (x::r, l)
  | xI p, x :: l =>
    match ptake p (x::r) l with
    | None => None
    | Some (r, l) => ptake p r l
    end
  | xO p, l =>
    match ptake p r l with
    | None => None
    | Some (r, l) => ptake p r l
    end
  | _, [::] => None
  end.

Definition ztake (A:Type) z (l:list A) :=
  match z with
  | Zpos p =>
    match ptake p [::] l with
    | None => None
    | Some (r, l) => Some (rev r, l)
    end
  | Z0     => Some([::], l)
  | _      => None
  end.

Definition check_glob data gv :=
  match gv with
  | @Gword ws w => assert (LE.decode ws data == w) (stk_ierror_no_var "bad decode")
  | @Garr p t =>
    Let _ := foldM (fun wd i =>
             match read t Aligned i U8 with
             | Ok w =>
               if wd == w then ok (i+1)%Z
               else Error (stk_ierror_no_var "bad decode array eq")
             | _ => Error (stk_ierror_no_var "bad decode array len")
             end) 0%Z data in
    ok tt
  end.

Definition size_glob gv :=
  match gv with
  | @Gword ws _ => wsize_size ws
  | @Garr p _ => Zpos p
  end.

Definition init_map (l:list (var * wsize * Z)) data (gd:glob_decls) : cexec (Mvar.t (Z*wsize)) :=
  let add (vp:var * wsize * Z) (globals: Mvar.t (Z*wsize) * Z * seq u8) :=
    let '(v, ws, p) := vp in
    let '(mvar, pos, data) := globals in
    if (pos <=? p)%Z then
      if Z.land p (wsize_size ws - 1) == 0%Z then
        let s := size_slot v in
        match ztake (p - pos) data with
        | None => Error (stk_ierror_no_var "bad data 1")
        | Some (_, data) =>
        match ztake s data with
        | None =>  Error (stk_ierror_no_var "bad data 2")
        | Some (vdata, data) =>
          match assoc gd v with
          | None => Error (stk_ierror_no_var "unknown var")
          | Some gv =>
            Let _ := assert (s == size_glob gv) (stk_ierror_no_var "bad size") in
            Let _ := check_glob vdata gv in
            ok (Mvar.set mvar v (p,ws), p + s, data)%Z
          end
        end end
      else Error (stk_ierror_no_var "bad global alignment")
    else Error (stk_ierror_no_var "global overlap") in
  Let globals := foldM add (Mvar.empty (Z*wsize), 0%Z, data) l in
  let '(mvar, _, _) := globals in
  Let _ := assert (Sv.subset (sv_of_list fst gd) (sv_of_list (fun x => x.1.1) l))
                  (stk_ierror_no_var "missing globals") in
  ok mvar.

Definition alloc_prog (fresh_reg : string -> stype -> Ident.ident)
    rip rsp global_data global_alloc local_alloc (P:_uprog) : cexec _sprog :=
  Let mglob := init_map  global_alloc global_data P.(p_globs) in
  let p_extra :=  {|
    sp_rip   := rip;
    sp_rsp   := rsp;
    sp_globs := global_data;
    sp_glob_names := global_alloc;
  |} in
  Let _ := assert (rip != rsp) (stk_ierror_no_var "rip and rsp clash") in
  Let p_funs := map_cfprog_name (alloc_fd  p_extra mglob fresh_reg local_alloc) P.(p_funcs) in
  ok  {| p_funcs  := p_funs;
         p_globs := [::];
         p_extra := p_extra;
      |}.

End CHECK.

End WITH_PARAMS.
