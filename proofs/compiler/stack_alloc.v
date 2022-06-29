(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import strings word utils type var expr.
Require Import compiler_util byteset.
Require slh_lowering.
Require Import ZArith.

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
    pel_msg := pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := internal
  |}.

  Definition stk_error_no_var  := stk_error_no_var_gen false.
  Definition stk_ierror_no_var := stk_error_no_var_gen true.

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

Definition region_eqMixin := Equality.Mixin region_axiom.
Canonical  region_eqType  := Eval hnf in EqType region region_eqMixin.

Module CmpR.

  Definition t := [eqType of region].

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
(* Symbolic expressions *)

(* We introduce a type of symbolic expressions, which allows to keep track
   symbolically of the values hold by the variables of the program. Two
   variables mapped to the same symbolic expression hold the same value
   in every execution of the program.
   This type is based on [pexpr] and close to it. The main difference is the
   absence of constructors corresponding to [Parr_init] and [Pload], which are
   abstracted away.
*)
Inductive spexpr : Set :=
| SPconst : Z -> spexpr
| SPbool : bool -> spexpr
| SPvar : positive -> spexpr
| SPget : arr_access -> wsize -> spexpr -> spexpr -> spexpr
| SPsub : arr_access -> wsize -> positive -> spexpr -> spexpr -> spexpr
| SPapp1 : sop1 -> spexpr -> spexpr
| SPapp2 : sop2 -> spexpr -> spexpr -> spexpr
| SPappN : opN -> seq spexpr -> spexpr
| SPif : stype -> spexpr -> spexpr -> spexpr -> spexpr.

Fixpoint spexpr_beq (e1 e2 : spexpr) : bool :=
  match e1, e2 with
  | SPconst n1   , SPconst n2    => n1 == n2
  | SPbool  b1   , SPbool  b2    => b1 == b2
  | SPvar   x1   , SPvar   x2    => (x1 == x2)
  | SPget aa1 sz1 x1 e1, SPget aa2 sz2 x2 e2 =>
    (aa1 == aa2) && (sz1 == sz2) && (spexpr_beq x1 x2) && spexpr_beq e1 e2
  | SPsub aa1 sz1 len1 x1 e1, SPsub aa2 sz2 len2 x2 e2 =>
    (aa1 == aa2) && (sz1 == sz2) && (len1 == len2) && (spexpr_beq x1 x2) && spexpr_beq e1 e2
  | SPapp1 o1 e1 , SPapp1  o2 e2 => (o1 == o2) && spexpr_beq e1 e2
  | SPapp2 o1 e11 e12, SPapp2 o2 e21 e22  =>
    (o1 == o2) && spexpr_beq e11 e21 && spexpr_beq e12 e22
  | SPappN o1 es1, SPappN o2 es2 =>
    (o1 == o2) && all2 spexpr_beq es1 es2
  | SPif t1 b1 e11 e12, SPif t2 b2 e21 e22  =>
    (t1 == t2) && spexpr_beq b1 b2 && spexpr_beq e11 e21 && spexpr_beq e12 e22
  | _, _ => false
  end.

Lemma spexpr_eq_axiom : Equality.axiom spexpr_beq.
Proof.
  rewrite /Equality.axiom.
  fix Hrec 1; move =>
    [n1|b1|x1|aa1 w1 x1 e1|aa1 w1 x1 e1 len1|o1 e1|o1 e11 e12|o1 es1|st1 t1 e11 e12]
    [n2|b2|x2|aa2 w2 x2 e2|aa2 w2 x2 e2 len2|o2 e2|o2 e21 e22|o2 es2|st2 t2 e21 e22] /=;
  try by constructor.
  + by apply (iffP idP) => [|[]] /eqP ->.
  + by apply (iffP idP) => [|[]] /eqP ->.
  + by apply (iffP idP) => [|[]] /eqP ->.
  + by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /Hrec -> /Hrec ->.
  + by apply (iffP idP) => [/andP[]/andP[]/andP[]/andP[] | []] /eqP -> /eqP -> /eqP -> /Hrec -> /Hrec ->.
  + by apply (iffP idP) => [/andP[] | []] /eqP -> /Hrec ->.
  + by apply (iffP idP) => [/andP[]/andP[] | []] /eqP -> /Hrec -> /Hrec ->.
  + by apply (iffP idP) => [/andP[] | []] /eqP -> /(reflect_all2_eqb Hrec) ->.
  by apply (iffP idP) => [/andP[]/andP[]/andP[] | []] /eqP -> /Hrec -> /Hrec -> /Hrec ->.
Qed.

Definition spexpr_eqMixin := Equality.Mixin spexpr_eq_axiom.
Canonical  spexpr_eqType  := Eval hnf in EqType spexpr spexpr_eqMixin.

(* ------------------------------------------------------------------ *)

(* A slice represents a contiguous portion of memory.
  We have them in two flavors:
  - [concrete_slice] where the components are integers; concrete slices are used
    to describe the shape of the stack, since we know everything statically.
  - [symbolic_slice] where the components are symbolic expressions; symbolic
    slices are used in the analysis, since there we do not necessarily know the
    offsets statically. In some places, we treat the case of [SPconst]
    particularly to recover some precision in the case everything is constant.
*)
Record concrete_slice := {
  cs_ofs : Z;
  cs_len : Z;
}.

Record symbolic_slice := {
  ss_ofs : spexpr;
  ss_len : spexpr;
}.

Definition symbolic_slice_beq s1 s2 :=
  (s1.(ss_ofs) == s2.(ss_ofs)) && (s1.(ss_len) == s2.(ss_len)).

Lemma symbolic_slice_eq_axiom : Equality.axiom symbolic_slice_beq.
Proof.
  rewrite /Equality.axiom.
  move=> [ofs1 len1] [ofs2 len2].
  by apply:(iffP andP) => /= [[/eqP -> /eqP ->] | [-> ->]].
Qed.

Definition symbolic_slice_eqMixin := Equality.Mixin symbolic_slice_eq_axiom.
Canonical  symbolic_slice_eqType  := EqType symbolic_slice symbolic_slice_eqMixin.

(* A symbolic zone is a memory portion written as a list of symbolic slices,
   each slice being included in the previous one.
   For instance, [i, j][k, l], is the [k, l]-slice of the [i, j]-slice. It could
   also be described as the slice [i+k, l]. We store it as [i, j][k, l]
   because it helps to remember some structure.
*)
Definition symbolic_zone := seq symbolic_slice.

(* ------------------------------------------------------------------ *)
(* A zone inside a region. *)
Record sub_region := {
    sr_region : region;
    sr_zone  : symbolic_zone;
  }.

Definition sub_region_beq sr1 sr2 := 
  (sr1.(sr_region) == sr2.(sr_region)) && (sr1.(sr_zone) == sr2.(sr_zone)).

Lemma sub_region_eq_axiom : Equality.axiom sub_region_beq.
Proof.
  rewrite /sub_region_beq => -[mp1 sub1] [mp2 sub2].
  by apply:(iffP andP) => /= [[/eqP -> /eqP ->] | [-> ->]].
Qed.

Definition sub_region_eqMixin := Equality.Mixin sub_region_eq_axiom.
Canonical sub_region_eqType := EqType sub_region sub_region_eqMixin.

(* ------------------------------------------------------------------ *)
(* idea: could we use a gvar instead of var & v_scope? *)
Variant ptr_kind_init :=
| PIdirect of var & concrete_slice & v_scope
| PIregptr of var
| PIstkptr of var & concrete_slice & var.

Variant ptr_kind :=
| Pdirect of var & Z & wsize & concrete_slice & v_scope
| Pregptr of var
| Pstkptr of var & Z & wsize & concrete_slice & var.

Record param_info := { 
  pp_ptr      : var;
  pp_writable : bool;
  pp_align    : wsize;
}.

Record pos_map := {
  vrip    : var;
  vrsp    : var;
  vxlen   : var;
  globals : Mvar.t (Z * wsize);
  locals  : Mvar.t ptr_kind;
  vnew    : Sv.t;
}.

(* TODO: Z.land or is_align ?
   Could be just is_align (sub_region_addr sr) ws ? *)
Definition check_align x (sr:sub_region) ws :=
  Let _ := assert (ws <= sr.(sr_region).(r_align))%CMP
                  (stk_ierror_basic x "unaligned offset") in
  (* FIXME SYMBOLIC: how to check the alignment ? *)
(*  assert (Z.land sr.(sr_zone).(z_ofs) (wsize_size ws - 1) == 0)%Z
         (stk_ierror_basic x "unaligned sub offset"). *)
  ok tt.

Definition writable (x:var_i) (r:region) :=
  assert r.(r_writable)
    (stk_error x (pp_box [:: pp_s "cannot write to the constant pointer"; pp_var x; pp_s "targetting"; pp_var r.(r_slot) ])).

Module Region.

(* A status synthetizes what we know about a sub-region. *)
Variant status :=
| Valid (* The sub-region is fully valid, we can read everywhere. *)
| Unknown (* We don't know anything about the sub-region. *)
| Borrowed of seq symbolic_zone.
  (* Some parts of the sub-region are "borrowed" by other variables, we cannot
     read in them. We remember a list of non-necessarily disjoint symbolic zones
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

Definition get_status_map (r:region) rv : status_map :=
  odflt empty_status_map (Mr.get rv r).

Definition get_status (x:var) (status_map:status_map) :=
  odflt Unknown (Mvar.get status_map x).

(* FIXME SYMBOLIC: do we really want to have a default value or should we throw
   an error if not in the table? *)
Definition get_var_status rv r x :=
  let bm := get_status_map r rv in
  let bytes := get_status x bm in
  bytes.

Definition is_spexpr_const sp :=
  match sp with
  | SPconst n => Some n
  | _ => None
  end.

Fixpoint split_last A (s : seq A) :=
  match s with
  | [::] => None
  | a :: l =>
    match split_last l with
    | None => Some ([::], a)
    | Some (l, b) => Some (a::l, b)
    end
  end.

(* Returns the sub-zone of [z] starting at offset [ofs] and of length [len].
   If [ofs] and [len] are constants, we look at the last slice [i, j] of the
   zone. If i and j are constants too, we merge the two slices, giving
   [i+ofs, len]. Otherwise, we just add the slice at the end of the zone.

   TODO: Oapp2 Add ofs1 ofs2 -> is_const ?
   obtenir des zones en "forme normale"
*)
Definition sub_zone_at_ofs z ofs len :=
  match split_last z with
  | None => [:: {| ss_ofs := ofs; ss_len := len |}]
  | Some (z', s) =>
    match is_spexpr_const s.(ss_len), is_spexpr_const ofs, is_spexpr_const len with
    | Some len1, Some ofs2, Some len2 => (* if (ofs2 == 0) && (len1 == len2) then z else *)
    match is_spexpr_const s.(ss_ofs) with
    | Some ofs1 => z' ++ [:: {| ss_ofs := SPconst (ofs1 + ofs2); ss_len := SPconst len2 |}]
    | _ => z ++ [:: {| ss_ofs := ofs; ss_len := len |}]
    end
    | _, _, _ => z ++ [:: {| ss_ofs := ofs; ss_len := len |}]
    end
  end.

Definition sub_region_at_ofs sr ofs len :=
  {| sr_region := sr.(sr_region);
     sr_zone   := sub_zone_at_ofs sr.(sr_zone) ofs len
  |}.

(* Returns whether two zones are disjoint. Since we manipulate symbolic
   expressions, most of the time we cannot answer positively. In presence of
   constants, we have a precise check.
*)
Fixpoint disjoint_zones (z1 z2 : symbolic_zone) :=
  match z1, z2 with
  | [::], _ | _, [::] => false
  | s1 :: z1, s2 :: z2 =>
    if s1 == s2 then disjoint_zones z1 z2 else
    match is_spexpr_const s1.(ss_ofs), is_spexpr_const s1.(ss_len), is_spexpr_const s2.(ss_ofs), is_spexpr_const s2.(ss_len) with
    | Some ofs1, Some len1, Some ofs2, Some len2 => (ofs2 + len2 <=? ofs1)%Z || (ofs1 + len1 <=? ofs2)%Z
    | _, _, _, _ => false
    end
  end.
Section test.
Context (string_of_sr : sub_region -> string) (string_of_borrowed : seq symbolic_zone -> string). (* maybe this could be written in Coq *)

(* FIXME SYMBOLIC: do we really need to return two sub-regions? *)
Definition check_valid (rmap:region_map) (x:var_i) ofs len :=
  (* we get the status associated to variable [x] *)
  Let sr := get_sub_region rmap x in
  let status := get_var_status rmap sr.(sr_region) x in
  let sr' := sub_region_at_ofs sr ofs len in
  let valid :=
    match status with
    | Valid => true
    | Unknown => false
    | Borrowed z => all (disjoint_zones sr'.(sr_zone)) z
    end
  in
  Let _ :=
    assert valid
      (stk_error x (pp_box [:: pp_s "the region ";
                               pp_s (string_of_sr sr');
                               pp_s " associated to variable"; pp_var x; pp_s "is partial.";
                               pp_s "It is in conflict with zone ";
                               pp_s
                               (match status with
                               | Borrowed z => string_of_borrowed z
                               | _ => ""
                               end)]))
  in
  ok (sr, sr').

(* We don't try to be clever here (e.g. no special case when everything is
   constant). This is not needed, since we check systematically inclusion in
   other places. We can thus afford to potentially introduce a bit of redundant
   information here.

   We could also define this function as:
   if incl z1 z2 then Some z2 else if incl z2 z1 then Some z1 else None
*)
Fixpoint merge_zones (z1 z2 : symbolic_zone) :=
  match z1, z2 with
  | [::], _ | _, [::] => Some [::]
  | s1 :: z1, s2 :: z2 =>
    if s1 == s2 then
      match merge_zones z1 z2 with
      | Some z => Some (s1 :: z)
      | None => None
      end
    else
      match z1, z2 with
      | [::], [::] =>
        if negb (is_spexpr_const s1.(ss_ofs) && is_spexpr_const s1.(ss_len) && is_spexpr_const s2.(ss_ofs) && is_spexpr_const s2.(ss_len))
        then Some [::] else None
      | _, _ => None
      end
  end.

(* If we can merge [z] with one of the zones in [zs], we do it. Otherwise,
   we add [z] at the end.
*)
Fixpoint insert_zone (z : symbolic_zone) (zs : seq symbolic_zone) :=
  match zs with
  | [::] => [:: z]
  | z1 :: zs =>
    match merge_zones z z1 with
    | Some z => z :: zs
    | None => z1 :: insert_zone z zs
    end
  end.

Definition clear_status z status :=
  match status with
  | Valid => Borrowed [:: z]
  | Unknown => Unknown
  | Borrowed z2 => Borrowed (insert_zone z z2)
  end.

Definition clear_status_map z (sm:status_map) :=
  Mvar.map (clear_status z) sm.

Fixpoint incl_zones (z1 z2 : symbolic_zone) :=
  match z1, z2 with
  | _, [::] => true
  | [::], _ => false
  | s1 :: z1, [:: s2] =>
    (s1 == s2) ||
    match is_spexpr_const s1.(ss_ofs), is_spexpr_const s1.(ss_len), is_spexpr_const s2.(ss_ofs), is_spexpr_const s2.(ss_len) with
    | Some ofs1, Some len1, Some ofs2, Some len2 => (ofs2 <=? ofs1)%Z && (ofs1 + len1 <=? ofs2 + len2)%Z
    | _, _, _, _ => false
    end
  | s1 :: z1, s2 :: z2 =>
    (s1 == s2) && incl_zones z1 z2
  end.

Definition set_pure_status rv x sr :=
  let sm := get_status_map sr.(sr_region) rv in
  let sm := clear_status_map sr.(sr_zone) sm in
  let sm := Mvar.set sm x Valid in
  Mr.set rv sr.(sr_region) sm.

(* We don't take ofs and len as args any more.
   [sr] should be [sub_region_at_ofs sr ofs len].
*)
Definition set_pure_status_sub rv x sr :=
  let sm     := get_status_map sr.(sr_region) rv in
  let status := get_status x sm in
  let status :=
    match status with
    | Valid => Valid
    | Unknown => Unknown
    | Borrowed zs =>
      match filter (fun z => negb (incl_zones z sr.(sr_zone))) zs with
      | [::] => Valid (* actually, Valid could be defined as Borrowed [::] <- really think about it *)
      | zs => Borrowed zs
      end
    end
  in
  (* clear status corresponding to z1 *)
  let sm := clear_status_map sr.(sr_zone) sm in
  (* set the new status *)
  let sm := Mvar.set sm x status in
  Mr.set rv sr.(sr_region) sm.

Definition set_status rv (x:var_i) sr :=
  Let _     := writable x sr.(sr_region) in
  ok (set_pure_status rv x sr).

Definition set_status_sub rv (x:var_i) sr :=
  Let _     := writable x sr.(sr_region) in
  ok (set_pure_status_sub rv x sr).

(* TODO: as many functions are similar, maybe we could have one big function
   taking flags as arguments that tell whether we have to check align/check valid... *)
Definition set_sub_region rmap (x:var_i) sr :=
  Let rv := set_status rmap x sr in
  ok {| var_region := Mvar.set rmap.(var_region) x sr;
        region_var := rv |}.

Definition set_sub_region_sub rmap (x:var_i) sr :=
  Let rv := set_status_sub rmap x sr in
  ok {| var_region := rmap.(var_region);
        region_var := rv |}.

Definition sub_region_stkptr s ws cs :=
  let r := {| r_slot := s; r_align := ws; r_writable := true |} in
  let z := [:: {| ss_ofs := SPconst cs.(cs_ofs); ss_len := SPconst cs.(cs_len) |}] in
  {| sr_region := r; sr_zone := z |}.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

Definition set_stack_ptr (rmap:region_map) s ws cs (x':var) :=
  let sr := sub_region_stkptr s ws cs in
  let sr := sub_region_at_ofs sr (SPconst 0) (SPconst (wsize_size Uptr)) in
  let rv := set_pure_status rmap x' sr in
  {| var_region := rmap.(var_region);
     region_var := rv |}.

(* TODO: fusion with check_valid ? *)
(* FIXME SYMBOLIC: the comment of "let z :=" seems strange *)
Definition check_stack_ptr rmap s ws z x' :=
  let sr := sub_region_stkptr s ws z in
  let status := get_var_status rmap sr.(sr_region) x' in
  let sr' := sub_region_at_ofs sr (SPconst 0) (SPconst (wsize_size Uptr)) in
  let valid :=
    match status with
    | Valid => true
    | Unknown => false
    | Borrowed z => all (disjoint_zones sr'.(sr_zone)) z
    end
  in
  valid.

End WITH_POINTER_DATA.

(* Precondition size_of x = ws && length sr.sr_zone = wsize_size ws *)
Definition set_word rmap (x:var_i) sr ws :=
  Let _ := check_align x sr ws in
  let sr := sub_region_at_ofs sr (SPconst 0) (SPconst (size_slot x)) in
  set_sub_region rmap x sr.

(* If we write to array [x] at offset [ofs], we invalidate the corresponding
   memory zone for the other variables, and mark it as valid for [x].
   The offset [ofs] can be None, meaning its exact value is not known. In this
   case, the full zone [z] associated to array [x] is invalidated for the
   other variables, and remains the zone associated to [x]. It is a safe
   approximation.
*)
(* [set_word], [set_stack_ptr] and [set_arr_word] could be factorized? -> think more about it *)
Definition set_arr_word (rmap:region_map) (x:var_i) ofs ws :=
  Let sr := get_sub_region rmap x in
  Let _ := check_align x sr ws in
  let sr := sub_region_at_ofs sr ofs (SPconst (wsize_size ws)) in
  set_sub_region_sub rmap x sr.

Definition set_arr_call rmap (x:var_i) sr :=
  let sr := sub_region_at_ofs sr (SPconst O) (SPconst (size_slot x)) in
  set_sub_region rmap x sr.

(* We make the variable point to a new sub_region: we mark it as valid. *)
Definition set_move_status rv x sr :=
  let sm := get_status_map sr.(sr_region) rv in
  let sm := Mvar.set sm x Valid in
  Mr.set rv sr.(sr_region) sm.

Definition set_move_sub (rmap:region_map) x sr :=
  let rv := set_move_status rmap x sr in
  {| var_region := rmap.(var_region);
     region_var := rv |}.

Definition set_arr_sub (rmap:region_map) (x:var_i) ofs len sr_from :=
  Let sr := get_sub_region rmap x in
  let sr' := sub_region_at_ofs sr ofs len in
  Let _ := assert (sr' == sr_from)
                  (stk_ierror x
                    (pp_box [::
                      pp_s "the assignment to sub-array"; pp_var x;
                      pp_s "cannot be turned into a nop: source (";
                      pp_vbox [::
                      pp_s (string_of_sr sr_from);
                      pp_s ") and destination (";
                      pp_s (string_of_sr sr')
                      ];
                      pp_s ") regions are not equal"]))
  in
  ok (set_move_sub rmap x sr').

(* identical to [set_sub_region], except clearing
   TODO: fusion with set_arr_sub ? not sure its worth
*)
Definition set_move (rmap:region_map) (x:var) sr :=
  let rv := set_move_status rmap x sr in
  {| var_region := Mvar.set rmap.(var_region) x sr;
     region_var := rv |}.

Definition set_arr_init (rmap:region_map) x sr := set_move rmap x sr.

Definition incl_status status1 status2 :=
  match status1, status2 with
  | Unknown, _ => true
  | _, Valid => true
  | Borrowed zs1, Borrowed zs2 => all (fun z => has (incl_zones z) zs1) zs2
  | _, _ => false
  end.

Definition incl_status_map (_r: region) (sm1 sm2: status_map) := 
  Mvar.incl (fun _ => incl_status) sm1 sm2.

Definition incl (rmap1 rmap2:region_map) :=
  Mvar.incl (fun x r1 r2 => r1 == r2) rmap1.(var_region) rmap2.(var_region) &&
  Mr.incl incl_status_map rmap1.(region_var) rmap2.(region_var).

(* FIXME SYMBOLIC: looks a lot like clean_status, can we merge implementations? *)
Definition merge_status (x:var) (status1 status2: option status) :=
  match status1, status2 with
  | Some status1, Some status2 =>
    match status1, status2 with
    | Valid, _ => Some status2
    | _, Valid => Some status1
    | Unknown, _ | _, Unknown => None
    | Borrowed zs1, Borrowed zs2 =>
      Some (Borrowed (foldl (fun zs1 z2 => insert_zone z2 zs1) zs1 zs2))
    end
  | _, _ => None
  end.

Definition merge_status_map (_r:region) (sm1 sm2: option status_map) :=
  match sm1, sm2 with
  | Some sm1, Some sm2 => 
    let sm := Mvar.map2 merge_status sm1 sm2 in
    if Mvar.is_empty sm then None
    else Some sm
  | _, _ => None
  end.

Definition merge (rmap1 rmap2:region_map) := 
  {| var_region := 
       Mvar.map2 (fun _ osr1 osr2 =>
        match osr1, osr2 with
        | Some sr1, Some sr2 => if sr1 == sr2 then osr1 else None
        | _, _ => None
        end) rmap1.(var_region) rmap2.(var_region);
     region_var := Mr.map2 merge_status_map rmap1.(region_var) rmap2.(region_var) |}.
End test.
End Region.

Import Region.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {pd : PointerData}
  {msfsz : MSFsize}
  {asmop : asmOp asm_op}
.

Context (string_of_sr : sub_region -> string)
        (string_of_borrowed : seq symbolic_zone -> string).

Definition mul := Papp2 (Omul (Op_w Uptr)).
Definition add := Papp2 (Oadd (Op_w Uptr)).

Definition mk_ofs aa ws e1 ofs := 
  let sz := mk_scale aa ws in
  if is_const e1 is Some i then 
    cast_const (i * sz + ofs)%Z
  else 
    add (mul (cast_const sz) (cast_ptr e1)) (cast_const ofs).

Definition mk_ofs_sp aa ws e1 :=
  let sz := mk_scale aa ws in
  if is_spexpr_const e1 is Some i then SPconst (i * sz)
  else SPapp2 (Oadd Op_int) (SPconst sz) e1.

Section CHECK.

(* The code in this file is called twice.
   - First, it is called from the stack alloc OCaml oracle. Indeed, the oracle
     returns initial results, and performs stack and reg allocation using
     these results. Based on the program that it obtains,
     it fixes some of the results and returns them.
   - Second, it is called as a normal compilation pass on the results returned
     by the oracle.

   When the code is called from the OCaml oracle, all the checks
   that are performed so that the pass can be proved correct are actually not
   needed. We introduce this boolen [check] to deactivate some of the tests
   when the code is called from the oracle.

   TODO: deactivate more tests (or even do not use rmap) when [check] is [false]
*)
Variable (check : bool).

Definition assert_check E b (e:E) :=
  if check then assert b e
  else ok tt.

Variant vptr_kind :=
  | VKglob of Z * wsize
  | VKptr  of ptr_kind.

Definition var_kind := option vptr_kind.

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
  }.

Variant mov_kind :=
  | MK_LEA
  | MK_MOV.

Definition mk_mov vpk :=
  match vpk with
  | VKglob _ | VKptr (Pdirect _ _ _ _ Sglob) => MK_LEA
  | _ => MK_MOV
  end.

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
  | Sglobal => pmap.(vrip)
  end.

Definition addr_from_pk (x:var_i) (pk:ptr_kind) :=
  match pk with
  | Pdirect _ ofs _ cs sc => ok (with_var x (base_ptr sc), ofs + cs.(cs_ofs))
  | Pregptr p            => ok (with_var x p,             0)
  | Pstkptr _ _ _ _ _    =>
    Error (stk_error x (pp_box [::
      pp_var x; pp_s "is a stack pointer, it should not appear in an expression"]))
  end%Z.

Definition addr_from_vpk x (vpk:vptr_kind) :=
  match vpk with
  | VKglob zws => ok (with_var x pmap.(vrip), zws.1)
  | VKptr pk => addr_from_pk x pk
  end.

Definition mk_addr_ptr x aa ws (pk:ptr_kind) (e1:pexpr) :=
  Let xofs := addr_from_pk x pk in
  ok (xofs.1, mk_ofs aa ws e1 xofs.2).

Definition mk_addr x aa ws (vpk:vptr_kind) (e1:pexpr) :=
  Let xofs := addr_from_vpk x vpk in
  ok (xofs.1, mk_ofs aa ws e1 xofs.2).

Definition get_var_kind x :=
  let xv := x.(gv) in
  if is_glob x then
    Let z := get_global xv in
    ok (Some (VKglob z))
  else 
    ok (omap VKptr (get_local xv)).

Definition sub_region_full x r :=
  let z := [:: {| ss_ofs := SPconst 0; ss_len := SPconst (size_slot x) |}] in
  {| sr_region := r; sr_zone := z |}.

Definition sub_region_glob x ws :=
  let r := {| r_slot := x; r_align := ws; r_writable := false |} in
  sub_region_full x r.

Definition check_vpk rmap (x:var_i) vpk ofs len :=
  match vpk with
  | VKglob (_, ws) =>
    let sr := sub_region_glob x ws in
    ok (sr, sub_region_at_ofs sr ofs len)
  | VKptr _pk => 
    check_valid string_of_sr string_of_borrowed rmap x ofs len
  end.

(* We could write [check_vpk] as follows.
  Definition check_vpk' rmap (x : gvar) ofs len :=
    let (sr, bytes) := check_gvalid rmap x in
    let sr' := sub_region_at_ofs sr.(sr_zone) ofs len in
    let isub_ofs := interval_of_zone sr'.(sr_zone) in
    (* we check if [isub_ofs] is a subset of one of the intervals of [bytes] *)
    (* useless test when [x] is glob, but factorizes call to [sub_region_at_ofs] *)
    Let _   := assert (ByteSet.mem bytes isub_ofs)
                      (Cerr_stk_alloc "check_valid: the region is partial") in
    ok sr'.
*)

Definition check_vpk_word rmap x vpk ofs ws :=
  Let srs := check_vpk rmap x vpk ofs (SPconst (wsize_size ws)) in
  check_align x srs.1 ws.

Record table := {
  bindings : Mvar.t spexpr;
  counter : positive;
}.

Definition table_fresh t :=
  let e := SPvar t.(counter) in
  let t :=
    {| bindings := t.(bindings);
       counter  := Pos.succ t.(counter)
    |}
  in
  (t, e).

Definition table_fresh_var t x :=
  let e := SPvar t.(counter) in
  let t :=
    {| bindings := Mvar.set t.(bindings) x e;
       counter  := Pos.succ t.(counter)
    |}
  in
  (t, e).

Definition binding_var t (x:var_i) :=
  match Mvar.get t.(bindings) x with
  | Some sp => (t, sp)
  | None => table_fresh_var t x
  end.

Definition clear_table t c :=
  let sv := write_c c in
  {| bindings := Sv.fold (fun x acc => Mvar.remove acc x) sv t.(bindings);
     counter := t.(counter);
  |}.

Definition merge_table (t1 t2 : table) :=
  let b :=
    Mvar.map2 (fun _ osp1 osp2 =>
      match osp1, osp2 with
      | Some sp1, Some sp2 => if sp1 == sp2 then osp1 else None
      | _, _ => None
      end) t1.(bindings) t2.(bindings)
  in
  let p := Pos.max t1.(counter) t2.(counter) in
  {| bindings := b; counter := p |}.

(* TODO: clean & move *)
Definition fmap :=
fun (aT bT cT : Type) (f : aT -> bT -> aT * cT) =>
fix mapM (a : aT) (xs : seq bT) {struct xs} : aT * seq cT :=
  match xs with
  | [::] => (a, [::])
  | x :: xs0 => let y := f a x in (let ys := mapM y.1 xs0 in (ys.1, y.2 :: ys.2))
  end.

(* FIXME: not sure we need to be as precise since lowering is before stack_alloc,
   a lot of pexpr have already been turned into asm_op *)
Fixpoint spexpr_of_pexpr t p : table * spexpr :=
  match p with
  | Pconst z => (t, SPconst z)
  | Pbool b => (t, SPbool b)
  | Pvar x => binding_var t x.(gv)
  | Pget aa ws x p =>
    let (t, sp) := spexpr_of_pexpr t p in
    let (t, x') := binding_var t x.(gv) in
    (t, SPget aa ws x' sp)
  | Psub aa ws len x e =>
    let (t, sp) := spexpr_of_pexpr t e in
    let (t, x') := binding_var t x.(gv) in
    (t, SPsub aa ws len x' sp)
  | Parr_init _ | Pload _ _ _ => table_fresh t
  | Papp1 op e =>
    let (t, sp) := spexpr_of_pexpr t e in
    (t, SPapp1 op sp)
  | Papp2 op e1 e2 =>
    let (t, sp1) := spexpr_of_pexpr t e1 in
    let (t, sp2) := spexpr_of_pexpr t e2 in
    (t, SPapp2 op sp1 sp2)
  | PappN op es =>
    let (t, sps) := fmap spexpr_of_pexpr t es in
    (t, SPappN op sps)
  | Pif ty b e1 e2 =>
    let (t, sp) := spexpr_of_pexpr t b in
    let (t, sp1) := spexpr_of_pexpr t e1 in
    let (t, sp2) := spexpr_of_pexpr t e2 in
    (t, SPif ty sp sp1 sp2)
  end.

(* TODO SYMBOLIC: try not to update t, or only locally; in one word, do not return t,
  this should also work
*)
Fixpoint alloc_e t (e:pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok (t, e)
  | Pvar   x =>
    let xv := x.(gv) in
    Let vk := get_var_kind x in
    match vk with
    | None => Let _ := check_diff xv in ok (t, e)
    | Some vpk => 
      if is_word_type (vtype xv) is Some ws then
        Let _ := check_vpk_word rmap xv vpk (SPconst 0) ws in
        (* FIXME SYMBOLIC: ws or U8 is the same, ws is really needed? *)
        Let pofs := mk_addr xv AAdirect ws vpk (Pconst 0) in
        ok (t, Pload ws pofs.1 pofs.2)
      else Error (stk_ierror_basic xv "not a word variable in expression")
    end

  | Pget aa ws x e1 =>
    let xv := x.(gv) in
    Let: (t, e1) := alloc_e t e1 in
    Let vk := get_var_kind x in
    match vk with
    | None => Let _ := check_diff xv in ok (t, Pget aa ws x e1)
    | Some vpk =>
      let (t, e1') := spexpr_of_pexpr t e1 in
      let ofs := (mk_ofs_sp aa ws e1') in
      Let _ := check_vpk_word rmap xv vpk ofs ws in
      Let pofs := mk_addr xv aa ws vpk e1 in
      ok (t, Pload ws pofs.1 pofs.2)
    end

  | Psub aa ws len x e1 =>
    Error (stk_ierror_basic x.(gv) "Psub")

  | Pload ws x e1 =>
    Let _ := check_var x in
    Let _ := check_diff x in
    Let: (t, e1) := alloc_e t e1 in
    ok (t, Pload ws x e1)

  | Papp1 o e1 =>
    Let: (t, e1) := alloc_e t e1 in
    ok (t, Papp1 o e1)

  | Papp2 o e1 e2 =>
    Let: (t, e1) := alloc_e t e1 in
    Let: (t, e2) := alloc_e t e2 in
    ok (t, Papp2 o e1 e2)

  | PappN o es => 
    Let: (t, es) := fmapM alloc_e t es in
    ok (t, PappN o es)

  | Pif ty e e1 e2 =>
    Let: (t, e) := alloc_e t e in
    Let: (t, e1) := alloc_e t e1 in
    Let: (t, e2) := alloc_e t e2 in
    ok (t, Pif ty e e1 e2)
  end.

  Definition alloc_es := fmapM alloc_e.

End ALLOC_E.

Definition sub_region_direct x align sc cs :=
  let r := {| r_slot := x; r_align := align; r_writable := sc != Sglob |} in
  let z := [:: {| ss_ofs := SPconst cs.(cs_ofs); ss_len := SPconst cs.(cs_len) |}] in
  {| sr_region := r; sr_zone := z |}.

Definition sub_region_stack x align z :=
  sub_region_direct x align Slocal z.

Definition sub_region_pk x pk :=
  match pk with
  | Pdirect x ofs align sub Slocal => ok (sub_region_stack x align sub)
  | _ => Error (stk_ierror x (pp_box [:: pp_var x; pp_s "is not in the stack"]))
  end.

Definition alloc_lval (trmap: table * region_map) (r:lval) (ty:stype) :=
  let (t, rmap) := trmap in
  match r return cexec (table * region_map * _) with
  | Lnone _ _ => ok (t, rmap, r)

  | Lvar x =>
    (* TODO: could we remove this [check_diff] and use an invariant in the proof instead? *)
    match get_local x with
    | None => Let _ := check_diff x in ok (t, rmap, r)
    | Some pk => 
      if is_word_type (vtype x) is Some ws then 
        if subtype (sword ws) ty then
          Let pofs := mk_addr_ptr x AAdirect ws pk (Pconst 0) in
          Let sr   := sub_region_pk x pk in
          let r := Lmem ws pofs.1 pofs.2 in
          Let rmap := Region.set_word rmap x sr ws in
          ok (t, rmap, r)
        else Error (stk_ierror_basic x "invalid type for assignment")
      else Error (stk_ierror_basic x "not a word variable in assignment")
    end

  | Laset aa ws x e1 =>
    (* TODO: could we remove this [check_diff] and use an invariant in the proof instead? *)
    Let: (t, e1) := alloc_e rmap t e1 in
    match get_local x with
    | None => Let _ := check_diff x in ok (t, rmap, Laset aa ws x e1)
    | Some pk => 
      let (t, e1') := spexpr_of_pexpr t e1 in
      let ofs := (mk_ofs_sp aa ws e1') in
      Let rmap := set_arr_word rmap x ofs ws in
      Let pofs := mk_addr_ptr x aa ws pk e1 in
      let r := Lmem ws pofs.1 pofs.2 in
      ok (t, rmap, r)
    end

  | Lasub aa ws len x e1 =>
    Error (stk_ierror_basic x "Lasub")

  | Lmem ws x e1 =>
    Let _ := check_var x in
    Let _ := check_diff x in
    Let: (t, e1) := alloc_e rmap t e1 in
    ok (t, rmap, Lmem ws x e1)
  end.

Definition nop := Copn [::] AT_none sopn_nop [::].

(* [is_spilling] is used for stack pointers. *)
Definition is_nop is_spilling rmap (x:var) (sry:sub_region) : bool :=
  if is_spilling is Some (s, ws, z, f) then
    if Mvar.get rmap.(var_region) x is Some srx then
      (srx == sry) && check_stack_ptr rmap s ws z f
    else false
  else false.

(* TODO: better error message *)
Definition get_addr is_spilling rmap x dx tag sry vpk y ofs :=
  let ir := if is_nop is_spilling rmap x sry
            then Some nop
            else sap_mov_ofs saparams dx tag vpk y ofs in
  let rmap := Region.set_move rmap x sry in
  (rmap, ir).

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
    Let _   := assert (check_stack_ptr rmap s ws cs f)
                      (stk_error x (pp_box [:: pp_s "the stack pointer"; pp_var x; pp_s "is no longer valid"])) in
    ok (Pload Uptr (with_var x pmap.(vrsp)) (cast_const (ofs + cs.(cs_ofs))), 0%Z)
  else
    Let xofs := addr_from_vpk x vpk in
    ok (Plvar xofs.1, xofs.2).

Definition mk_addr_pexpr' rmap x aa ws vpk e1 :=
  Let xofs := mk_addr_pexpr rmap x vpk in
  ok (xofs.1, mk_ofs aa ws e1 xofs.2).

(* TODO: the check [is_lvar] was removed, was it really on purpose? *)
(* TODO : currently, we check that the source array is valid and set the target
   array as valid too. We could, instead, give the same validity to the target
   array as the source one.
   [check_vpk] should be replaced with some function returning the valid bytes
   of y...
*)
(* Precondition is_sarr ty *)
Definition alloc_array_move t rmap r tag e :=

  Let sryl :=
    match e with
    | Pvar y =>
      let yv := y.(gv) in
      Let vk := get_var_kind y in
      match vk with
      | None => Error (stk_ierror_basic yv "register array remains")
      | Some vpk =>
        Let srs := check_vpk rmap yv vpk (SPconst 0) (SPconst (size_slot yv)) in
        let sry := srs.1 in
        Let: (e1, e2) := mk_addr_pexpr' rmap yv AAdirect U8 vpk (Pconst 0) in
        ok (t, sry, vpk, e1, e2)
      end
    | Psub aa ws len y e1 =>
      let yv := y.(gv) in
      Let vk := get_var_kind y in
      match vk with
      | None => Error (stk_ierror_basic yv "register array remains")
      | Some vpk =>
        let (t, e) := spexpr_of_pexpr t e1 in
        let ofs := (mk_ofs_sp aa ws e) in
        Let srs := check_vpk rmap yv vpk ofs (SPconst (arr_size ws len)) in
        let sry := srs.2 in
        Let: (e1, e2) := mk_addr_pexpr' rmap yv aa ws vpk e1 in
        ok (t, sry, vpk, e1, e2)
      end

    | _      => Error (stk_ierror_no_var "get_Pvar_sub: variable/subarray expected")
    end
  in
  let '(t, sry, vpk, ey, ofs) := sryl in

  match r with
  | Lvar x =>
    match get_local (v_var x) with
    | None    => Error (stk_ierror_basic x "register array remains")
    | Some pk =>
      match pk with
      | Pdirect s _ ws zx sc =>
        let sr := sub_region_direct s ws sc zx in
        Let _  :=
          assert (sr == sry)
                 (stk_ierror x
                    (pp_box [::
                      pp_s "the assignment to array"; pp_var x;
                      pp_s "cannot be turned into a nop: source (";
                      pp_s (string_of_sr sry);
                      pp_s ") and destination (";
                      pp_s (string_of_sr sr);
                      pp_s ") regions are not equal"]))
        in
        let rmap := Region.set_move rmap x sry in
        ok (t, rmap, nop)
      | Pregptr p =>
        let (rmap, oir) :=
            get_addr None rmap x (Lvar (with_var x p)) tag sry vpk ey ofs in
        match oir with
        | None =>
          let err_pp := pp_box [:: pp_s "cannot compute address"; pp_var x] in
          Error (stk_error x err_pp)
        | Some ir =>
          ok (t, rmap, ir)
        end
      | Pstkptr slot ofsx ws cs x' =>
        let is_spilling := Some (slot, ws, cs, x') in
        let dx_ofs := cast_const (ofsx + cs.(cs_ofs)) in
        let dx := Lmem Uptr (with_var x pmap.(vrsp)) dx_ofs in
        let (rmap, oir) := get_addr is_spilling rmap x dx tag sry vpk ey ofs in
        match oir with
        | None =>
          let err_pp := pp_box [:: pp_s "cannot compute address"; pp_var x] in
          Error (stk_error x err_pp)
        | Some ir =>
          ok (t, Region.set_stack_ptr rmap slot ws cs x', ir)
        end
      end
    end

  | Lasub aa ws len x e =>
    match get_local (v_var x) with
    | None   => Error (stk_ierror_basic x "register array remains")
    | Some _ =>
      let (t, e') := spexpr_of_pexpr t e in
      let ofs := (mk_ofs_sp aa ws e') in
      Let rmap := Region.set_arr_sub string_of_sr rmap x ofs (SPconst (arr_size ws len)) sry in
      ok (t, rmap, nop)
    end

  | _ => Error (stk_ierror_no_var "get_Lvar_sub: variable/subarray expected")

  end.

Definition is_protect_ptr_fail (rs:lvals) (o:sopn) (es:pexprs) :=
  match o, rs, es with
  | Oslh (SLHprotect_ptr_fail _), [::r], [:: e; msf] => Some (r, e, msf)
  | _, _, _ => None
  end.

Definition lower_protect_ptr_fail ii lvs t es :=
  slh_lowering.lower_slho shparams ii lvs t (SLHprotect Uptr) es. 

(* This seems to be a duplication of alloc_array_move, but we are able to share the corresponding proofs *)
Definition alloc_protect_ptr (t:table) rmap ii r (tag:assgn_tag) e msf :=
  Let sryl :=
    match e with
    | Pvar y =>
      let vy := y.(gv) in
      Let vk := get_var_kind y in
      match vk with
      | None => Error (stk_error_no_var "argument of protect_ptr should be a reg ptr")
      | Some vpk =>
        Let _ := assert (if vpk is VKptr (Pregptr _) then true else false)
                        (stk_error_no_var "argument of protect_ptr should be a reg ptr") in
        Let srs := check_vpk rmap vy vpk (SPconst 0) (SPconst (size_slot vy)) in
        let sry := srs.2 in
        Let: (e, _ofs) := mk_addr_pexpr rmap vy vpk in (* ofs is ensured to be 0 *)
        ok (sry, vpk, e)
      end
    | _ => Error (stk_error_no_var "argument of protect_ptr cannot be a sub array" )
    end
  in
  let '(sry, vpk, ey) := sryl in
  match r with
  | Lvar x =>
    match get_local (v_var x) with
    | None    => Error (stk_error_no_var "only reg ptr can receive the result of protect_ptr")
    | Some pk =>
      match pk with
      | Pregptr px =>
        let dx := Lvar (with_var x px) in
        Let: (t, msf) := add_iinfo ii (alloc_e rmap t msf) in
        Let ir := lower_protect_ptr_fail ii [::dx] tag [:: ey; msf] in
        let rmap := Region.set_move rmap x sry in
        ok (t, rmap, ir)
      | _ => Error (stk_error_no_var "only reg ptr can receive the result of protect_ptr")
      end
    end
  | _ => Error (stk_error_no_var "cannot assign protect_ptr in a sub array" )
  end.

(* This function is also defined in array_init.v *)
(* TODO: clean *)
Definition is_array_init e := 
  match e with
  | Parr_init _ => true
  | _ => false
  end.

(* We do not update the [var_region] part *)
(* there seems to be an invariant: all Pdirect are in the rmap *)
(* long-term TODO: we can avoid putting PDirect in the rmap (look in pmap instead) *)
Definition alloc_array_move_init t rmap r tag e :=
  if is_array_init e then
    match r with
    | Lvar x =>
      Let sr := 
        match get_local x with
        | None    => Error (stk_ierror_basic x "register array remains")
        | Some pk =>
          match pk with
          | Pdirect x' _ ws z sc =>
            if sc is Slocal then
              ok (sub_region_stack x' ws z)
            else
              Error (stk_error x (pp_box [:: pp_s "cannot initialize glob array"; pp_var x]))
          | _ => 
            get_sub_region rmap x
          end
        end
      in
      let rmap := Region.set_move_sub rmap x sr in
      ok (t, rmap, nop)
    | _ => Error (stk_ierror_no_var "arrayinit of non-variable")
    end
  else alloc_array_move t rmap r tag e.

Definition bad_lval_number := stk_ierror_no_var "invalid number of lval".

Definition alloc_lvals rmap rs tys := 
  fmapM2 bad_lval_number alloc_lval rmap rs tys.

Section LOOP.

 Variable ii:instr_info.

 (* the positive makes sure we generate fresh variable names *)
 Variable check_c2 : positive * region_map -> cexec (((positive * region_map) * (positive * region_map)) * (pexpr * (seq cmd * seq cmd)) ).

 Fixpoint loop2 (n:nat) (m:positive * region_map) := 
    match n with
    | O => Error (pp_at_ii ii (stk_ierror_no_var "loop2"))
    | S n =>
      Let: (prmap1, prmap2, c) := check_c2 m in
      if incl m.2 prmap2.2 then ok (prmap1, c)
      else loop2 n (prmap2.1, merge m.2 prmap2.2)
    end.

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

Section PROG.

Context (local_alloc: funname -> stk_alloc_oracle_t).

Definition get_Pvar e := 
  match e with
  | Pvar x => ok x
  | _      => Error (stk_ierror_no_var "get_Pvar: variable expected")
  end.

(* The name is chosen to be similar to [set_pure_bytes] and [set_move_bytes],
   but there are probably better ideas.
   TODO: factorize [set_clear_bytes] and [set_pure_bytes] ?
*)
Definition set_clear_status rv sr ofs len :=
  let z     := sr.(sr_zone) in
  let z1    := sub_zone_at_ofs z ofs len in
  let sm    := get_status_map sr.(sr_region) rv in
  (* clear all bytes corresponding to z1 *)
  let sm := clear_status_map z1 sm in
  Mr.set rv sr.(sr_region) sm.

Definition set_clear_pure rmap sr ofs len :=
  {| var_region := rmap.(var_region);
     region_var := set_clear_status rmap sr ofs len |}.

Definition set_clear rmap x sr ofs len :=
  Let _ := writable x sr.(sr_region) in
  ok (set_clear_pure rmap sr ofs len).

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
    Let srs := Region.check_valid string_of_sr string_of_borrowed rmap0 xv (SPconst 0) (SPconst (size_slot xv)) in
    let sr := srs.1 in
    Let rmap := if pi.(pp_writable) then set_clear rmap xv sr (SPconst 0) (SPconst (size_slot xv)) else ok rmap in
    Let _  := check_align xv sr pi.(pp_align) in
    ok (rmap, (Some (pi.(pp_writable),sr), Pvar (mk_lvar (with_var xv p))))
  | Some _, _ => Error (stk_ierror_basic xv "the argument should be a reg ptr")
  end.

Definition alloc_call_args_aux rmap sao_params es :=
  fmapM2 (stk_ierror_no_var "bad params info") (alloc_call_arg_aux rmap) rmap sao_params es.

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
  | Laset aa ws x e1 => Error (stk_ierror_basic x "array assignement in lval of a call")
  | Lasub aa ws len x e1 => Error (stk_ierror_basic x "sub-array assignement in lval of a call")
  | Lmem ws x e1     => Error (stk_ierror_basic x "call result should be stored in reg")
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
        Let rmap := Region.set_arr_call rmap x sr in
        (* TODO: Lvar p or Lvar (with_var x p) like in alloc_call_arg? *)
        ok (rmap, Lvar p)
      | Laset aa ws x e1 => Error (stk_ierror_basic x "array assignement in lval of a call")
      | Lasub aa ws len x e1 => Error (stk_ierror_basic x "sub-array assignement in lval of a call")
      | Lmem ws x e1     => Error (stk_ierror_basic x "call result should be stored in reg ptr")
      end
    | (None, _) => Error (stk_ierror_no_var "alloc_lval_call")
    end
  end.

Definition alloc_call_res rmap srs ret_pos rs := 
  fmapM2 bad_lval_number (alloc_lval_call srs) rmap rs ret_pos.

Definition is_RAnone ral :=
  if ral is RAnone then true else false.

Definition alloc_call (sao_caller:stk_alloc_oracle_t) rmap ini rs fn es := 
  let sao_callee := local_alloc fn in
  Let es  := alloc_call_args rmap sao_callee.(sao_params) es in
  let '(rmap, es) := es in
  Let rs  := alloc_call_res rmap es sao_callee.(sao_return) rs in (*
  Let _   := assert_check (~~ is_RAnone sao_callee.(sao_return_address))
               (Cerr_stk_alloc "cannot call export function")
  in *)
  Let _   :=
    let local_size :=
      if is_RAnone sao_caller.(sao_return_address) then
        (sao_caller.(sao_size) + sao_caller.(sao_extra_size) + wsize_size sao_caller.(sao_align) - 1)%Z
      else
        (round_ws sao_caller.(sao_align) (sao_caller.(sao_size) + sao_caller.(sao_extra_size)))%Z
    in
    assert_check (local_size + sao_callee.(sao_max_size) <=? sao_caller.(sao_max_size))%Z
                 (stk_ierror_no_var "error in max size computation")
  in
  Let _   := assert_check (sao_callee.(sao_align) <= sao_caller.(sao_align))%CMP
                          (stk_ierror_no_var "non aligned function call")
  in
  let es  := map snd es in
  ok (rs.1, Ccall ini rs.2 fn es).

Definition lval_table t r e :=
  match r with
  | Lvar x =>
    let (t, ap) := spexpr_of_pexpr t e in
    {|
      bindings := Mvar.set t.(bindings) x ap;
      counter := t.(counter)
    |}
  | Laset _ _ x _ | Lasub _ _ _ x _ => let (t, _) := table_fresh_var t x in t
  | _ => t
  end.

Definition lval_table_fresh tab r :=
  match r with
  | Lvar x | Laset _ _ x _ => {|
      bindings := Mvar.set tab.(bindings) x (SPvar tab.(counter));
      counter := Pos.succ tab.(counter)
    |}
  | _ => tab
  end.

(* Before stack_alloc :
     Csyscall [::x] (getrandom len) [::t] 
     t : arr n & len <= n.
     return arr len.
   After: 
     xlen: Uptr 
     xlen := len;
     Csyscall [::xp] (getrandom len) [::p, xlen] 
*)
Definition alloc_syscall ii t rmap rs o es := 
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
      let sr := sub_region_at_ofs sr (SPconst 0) (SPconst (Zpos len)) in
      Let rmap := set_sub_region rmap x sr in
      let t := lval_table_fresh t x in
      ok (t, rmap,
          [:: MkI ii (sap_immediate saparams xlen (Zpos len));
              MkI ii (Csyscall [::Lvar xp] o [:: Plvar p; Plvar xlen])])
    | _, _ =>
      Error (stk_ierror_no_var "randombytes: invalid args or result")
    end
  end.

(* To gain precision, we have a special case when an assembly instruction is just
   a move. *)
Context (is_move_op : asm_op_t -> bool).

Fixpoint alloc_i sao print_trmap (trmap:table * region_map) (i: instr) : cexec (table * region_map * cmd) :=
  let (t, rmap) := trmap in
  let (ii, ir) := i in
  Let c :=
    match ir with
    | Cassgn r tag ty e => 
      if is_sarr ty then
        Let: (t, rmap, i) := add_iinfo ii (alloc_array_move_init t rmap r tag e) in
        let t := lval_table t r e in
        ok (t, rmap, [:: MkI ii i])
      else
        Let: (t, e') := add_iinfo ii (alloc_e rmap t e) in
        Let: (t, rmap, r') := add_iinfo ii (alloc_lval (t, rmap) r ty) in
        let t := lval_table t r e in
        ok (t, rmap, [:: MkI ii (Cassgn r' tag ty e')])

    | Copn rs tag o e => 
      if is_protect_ptr_fail rs o e is Some (r, e, msf) then
         Let: (t, rs1, rs2) := alloc_protect_ptr t rmap ii r tag e msf in
         ok (t, rs1, [:: MkI ii rs2])
      else
      Let: (t, e')  := add_iinfo ii (alloc_es rmap t e) in
      Let: (t, rmap, rs') := add_iinfo ii (alloc_lvals (t, rmap) rs (sopn_tout o)) in
      let t :=
        match rs, o, e with
        | [:: x], Oasm op, [:: e] =>
          if is_move_op op then
            lval_table t x e
          else
            foldl lval_table_fresh t rs
        | _, _, _ =>
          foldl lval_table_fresh t rs
        end
      in
      ok (t, rmap, [:: MkI ii (Copn rs' tag o e')])

    | Csyscall rs o es =>
      alloc_syscall ii t rmap rs o es

    | Cif e c1 c2 => 
      Let: (t,  e) := add_iinfo ii (alloc_e rmap t e) in
      Let: (t1, rmap1, c1) := fmapM (alloc_i sao print_trmap) (t, rmap) c1 in
      Let: (t2, rmap2, c2) := fmapM (alloc_i sao print_trmap) (t, rmap) c2 in
      let t := merge_table t1 t2 in
      let rmap := merge rmap1 rmap2 in
      ok (t, rmap, [:: MkI ii (Cif e (flatten c1) (flatten c2))])

(* FIXME SYMBOLIC : clear t when entering the loop, not just after *)
(* compute the set of assigned variables in the body *)
    | Cwhile a c1 e c2 => 
      let t := clear_table t (c1 ++ c2) in
      let check_c (prmap : positive * region_map) :=
        let t := {| bindings := t.(bindings); counter := prmap.1 |} in
        Let: (t1, rmap1, c1) := fmapM (alloc_i sao print_trmap) (t, prmap.2) c1 in
        Let: (t', e) := add_iinfo ii (alloc_e rmap1 t1 e) in
        Let: (t2, rmap2, c2) := fmapM (alloc_i sao print_trmap) (t', rmap1) c2 in
        ok ((t1.(counter), rmap1), (t2.(counter), rmap2), (e, (c1, c2))) in
      Let: (p, rmap, c) := loop2 ii check_c Loop.nb (t.(counter), rmap) in
      ok (t, rmap, [:: MkI ii (Cwhile a (flatten c.2.1) c.1 (flatten c.2.2))])

    | Ccall ini rs fn es =>
      Let: (rmap, i) := add_iinfo ii (alloc_call sao rmap ini rs fn es) in
      let t := foldl lval_table_fresh t rs in
      ok (t, rmap, [::MkI ii i])

    | Cfor _ _ _  => Error (pp_at_ii ii (stk_ierror_no_var "don't deal with for loop"))

    end in
  ok (print_trmap ii c.1, c.2).

End PROG.

End Section.

Context (is_move_op : asm_op_t -> bool).

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
                Region.set_arr_init rmap x sr
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
  Let aux := foldM (add_alloc globals stack) (Mvar.empty _, Region.empty, sv) sao.(sao_alloc) in
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
    | Some sr =>
      Let _ := assert (x.(vtype) == (nth x params i).(vtype))
                      (stk_ierror_no_var "reg ptr in result not corresponding to a parameter") in
      Let srs := check_valid string_of_sr string_of_borrowed rmap x (SPconst 0) (SPconst (size_slot x)) in
      let sr' := srs.1 in
      Let _  := assert (sr == sr') (stk_ierror_no_var "invalid reg ptr in result") in
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
  let: (disj, lmap, t, rmap) := accu in
  Let _ := assert (~~ Sv.mem x disj) (stk_ierror_no_var "a parameter already exists") in
  if Mvar.get lmap x is Some _ then Error (stk_ierror_no_var "a stack variable also occurs as a parameter")
  else
    let t := {|
      bindings := Mvar.set t.(bindings) x (SPvar t.(counter));
      counter := Pos.succ t.(counter)
    |} in
    match pi with
    | None => ok (disj, lmap, t, rmap, (None, x))
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
          t,
          set_move rmap x sr,
          (Some sr, with_var x pi.(pp_ptr)))
    end.

Definition init_params mglob stack disj lmap t rmap sao_params params :=
  fmapM2 (stk_ierror_no_var "invalid function info")
    (init_param mglob stack) (disj, lmap, t, rmap) sao_params params.

Definition table_global t (mglob:Mvar.t (Z*wsize)) :=
  Mvar.fold (fun x _ t =>
    {| bindings := Mvar.set t.(bindings) x (SPvar t.(counter));
       counter := Pos.succ t.(counter) |}) mglob t.

Definition alloc_fd_aux print_trmap p_extra mglob (fresh_reg : Ident.name -> stype -> Ident.ident) (local_alloc: funname -> stk_alloc_oracle_t) sao fd : cexec _ufundef :=
  let vrip := {| vtype := sword Uptr; vname := p_extra.(sp_rip) |} in
  let vrsp := {| vtype := sword Uptr; vname := p_extra.(sp_rsp) |} in
  let vxlen := {| vtype := sword Uptr; vname := fresh_reg (Ident.name_of_string "__len__") (sword Uptr) |} in
  let ra := sao.(sao_return_address) in
  Let stack := init_stack_layout mglob sao in
  Let mstk := init_local_map vrip vrsp vxlen mglob stack sao in
  let '(locals, rmap, disj) := mstk in
  (* hacky : we do it for each function... we could do it once and pass it around *)
  let t := table_global {| bindings := Mvar.empty _; counter := 1 |} mglob in
  (* adding params to the map *)
  Let rparams :=
    init_params mglob stack disj locals t rmap sao.(sao_params) fd.(f_params) in
  let: (sv, lmap, t, rmap, alloc_params) := rparams in
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
    let local_size :=
      if is_RAnone sao.(sao_return_address) then
        (sao.(sao_size) + sao.(sao_extra_size) + wsize_size sao.(sao_align) - 1)%Z
      else
        (round_ws sao.(sao_align) (sao.(sao_size) + sao.(sao_extra_size)))%Z
    in
    assert_check (local_size <=? sao.(sao_max_size))%Z
                 (stk_ierror_no_var "sao_max_size too small")
  in
  Let rbody := fmapM (alloc_i pmap local_alloc is_move_op sao print_trmap) (t, rmap) fd.(f_body) in
  let: (t, rmap, body) := rbody in
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

Definition alloc_fd print_trmap p_extra mglob (fresh_reg : Ident.name -> stype -> Ident.ident) (local_alloc: funname -> stk_alloc_oracle_t) fn fd :=
  let: sao := local_alloc fn in
  Let fd := alloc_fd_aux print_trmap p_extra mglob fresh_reg local_alloc sao fd in
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
             match read t i U8 with
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

Definition alloc_prog print_trmap (fresh_reg : Ident.name -> stype -> Ident.ident)
    rip rsp global_data global_alloc local_alloc (P:_uprog) : cexec _sprog :=
  Let mglob := init_map global_alloc global_data P.(p_globs) in
  let p_extra :=  {|
    sp_rip   := rip;
    sp_rsp   := rsp;
    sp_globs := global_data;
  |} in
  Let _ := assert (rip != rsp) (stk_ierror_no_var "rip and rsp clash") in
  Let p_funs := map_cfprog_name (alloc_fd print_trmap p_extra mglob fresh_reg local_alloc) P.(p_funcs) in
  ok  {| p_funcs  := p_funs;
         p_globs := [::];
         p_extra := p_extra;
        |}.

End CHECK.

End WITH_PARAMS.
