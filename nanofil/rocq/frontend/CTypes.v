(** Semantic type resolution, struct and union layout, constant expression
    evaluation, expression elaboration, and diagnostic reporting for C.

    This module ports the recursive semantic engine of nanofil/src/c_types.pl
    on top of CTypeAst.v, CTypeTables.v, and CIeee.v. Every function is pure,
    zero-axiom, and fuel-bounded so both OCaml extraction and CertiRocq λANF
    lower it directly without host floating-point operations or environment
    mutations. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp CTypeAst CTypeTables.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Error formatting and type printing

    Semantic diagnostics format types the same way SWI-Prolog prints `~w`
    over c_types terms, keeping error messages aligned with reject tests. *)

Definition c_binop_name (op : c_binop) : string :=
  match op with
  | BLor => "lor" | BLand => "land" | BOr => "or" | BXor => "xor" | BAnd => "and"
  | BEq => "eq" | BNe => "ne" | BLt => "lt" | BGt => "gt" | BLe => "le" | BGe => "ge"
  | BShl => "shl" | BShr => "shr" | BAdd => "add" | BSub => "sub"
  | BMul => "mul" | BDiv => "div" | BMod => "mod"
  end.

Definition c_unop_name (op : c_unop) : string :=
  match op with
  | UNeg => "neg" | UPlus => "plus" | UBnot => "bnot" | UNot => "not"
  | UDeref => "deref" | UAddr => "addr"
  | UPreInc => "preinc" | UPreDec => "predec"
  | UPostInc => "postinc" | UPostDec => "postdec"
  end.

Definition c_int_kind_name (k : c_int_kind) : string :=
  match k with
  | IBool => "bool" | IChar => "char" | ISChar => "schar" | IUChar => "uchar"
  | IShort => "short" | IUShort => "ushort" | IInt => "int" | IUInt => "uint"
  | ILong => "long" | IULong => "ulong" | ILLong => "llong" | IULLong => "ullong"
  end.

Definition c_float_kind_name (k : c_float_kind) : string :=
  match k with FFloat => "float" | FDouble => "double" | FLDouble => "ldouble" end.

Definition su_id_str (id : su_id) : string :=
  match id with
  | SUInt n => z_to_string n
  | SUBuiltin s => s
  end.

Fixpoint c_type_diag_str (t : c_type) : string :=
  let fix list_strs (xs : list c_type) : list string :=
    match xs with
    | [] => []
    | x :: rest => c_type_diag_str x :: list_strs rest
    end in
  match t with
  | TVoid => "void"
  | TIntK k => c_int_kind_name k
  | TFloatK k => c_float_kind_name k
  | TPtr inner => "ptr(" ++ c_type_diag_str inner ++ ")"
  | TArray elem len =>
      let ls := match len with
                | ALNone => "none"
                | ALConst n => z_to_string n
                | ALVlaStar => "vla(star)"
                | ALVlaExpr _ => "vla(_)"
                | ALDyn v => "dyn(tmp(" ++ v ++ "))"
                end in
      "array(" ++ c_type_diag_str elem ++ "," ++ ls ++ ")"
  | TFunc ret ps v =>
      let pstr := match ps with
                  | None => "unspecified"
                  | Some xs => "[" ++ String.concat "," (list_strs xs) ++ "]"
                  end in
      let vstr := if v then "variadic" else "fixed" in
      "func(" ++ c_type_diag_str ret ++ "," ++ pstr ++ "," ++ vstr ++ ")"
  | TStruct id => "struct(" ++ su_id_str id ++ ")"
  | TUnion id => "union(" ++ su_id_str id ++ ")"
  | TAtomic s p => "atomic(" ++ c_type_diag_str s ++ "," ++ z_to_string p ++ ")"
  | TVec e n a =>
      "vec(" ++ c_type_diag_str e ++ "," ++ z_to_string n ++ "," ++ z_to_string a ++ ")"
  | TQual _ inner => c_type_diag_str inner
  | TBad why => "bad(" ++ why ++ ")"
  end.

Definition sema_err {A : Type} (loc : c_loc) (msg : string) : c_tr A :=
  let prefix :=
    match loc with
    | Loc f 0 => if String.eqb f "constant" then "constant" else loc_to_string loc
    | _ => loc_to_string loc
    end in
  TErr (TESema (prefix ++ ": " ++ msg)).

(** ## Struct and union layout engine

    Lays out natural, packed, and `#pragma pack(N)` structs and unions
    following System V x86-64 ABI bit-field and alignment rules. *)

Inductive su_packing : Type :=
| PackNatural
| PackPacked
| PackCap (n : Z).

Inductive member_align_req : Type :=
| MANone
| MAReq (base : option Z) (explicit : Z)
| MABad (why : string).

Inductive su_field : Type :=
| SFField (name : option string) (ty : c_type) (align : member_align_req)
| SFBits (name : option string) (ty : c_type) (width : Z)
| SFBad (why : string).

Inductive placed_member : Type :=
| PMNormal (m : c_member_layout)
| PMPackedBits (name : option string) (ty : c_type) (start width : Z).

Definition member_offset_end (kind : su_kind) (end0 sz al : Z) : Z * Z :=
  match kind with
  | KStruct =>
      let off := Z.div (Z.div (end0 + 7) 8 + al - 1) al * al in
      (off, 8 * (off + sz))
  | KUnion => (0, Z.max end0 (8 * sz))
  end.

Definition bitfield_start_end (kind : su_kind) (end0 w unit_bits : Z) : Z * Z :=
  match kind with
  | KUnion => (0, Z.max end0 w)
  | KStruct =>
      let start :=
        if (0 <? w) && Z.eqb (Z.div end0 unit_bits) (Z.div (end0 + w - 1) unit_bits) then end0
        else Z.div (end0 + unit_bits - 1) unit_bits * unit_bits in
      (start, start + w)
  end.

Definition field_size_natural_align (ty : c_type) (env : c_type_env)
  : c_tr (Z * Z) :=
  match ty with
  | TArray elem ALNone =>
      match type_size_align elem env with
      | TOk (_, al) => TOk (0, al)
      | TErr e => TErr e
      end
  | _ => type_size_align ty env
  end.

Definition packed_window (end_b start w sz : Z) : option (Z * Z) :=
  let off := Z.min (Z.div start 8) (end_b - sz) in
  let pos := start - 8 * off in
  if (0 <=? off) && (pos + w <=? 8 * sz) then Some (off, pos) else None.

Definition place_packed_unit (end_b : Z) (env : c_type_env) (pm : placed_member)
  : c_tr c_member_layout :=
  match pm with
  | PMNormal m => TOk m
  | PMPackedBits name ty start w =>
      match type_size_align ty env with
      | TErr e => TErr e
      | TOk (sz, _) =>
          match packed_window end_b start w sz with
          | Some (off0, pos0) => TOk (mkMemLayout name ty off0 (MBBits pos0 w))
          | None =>
              if sz <=? 4 then
                match int_info ty with
                | Some (_, sg) =>
                    let cands :=
                      match sg with
                      | CUnsigned => [(1, TUChar); (2, TUShort)]
                      | CSigned => [(1, TSChar); (2, TShort)]
                      end in
                    let fix pick (cs : list (Z * c_type)) :=
                      match cs with
                      | [] => TErr (TEBad "a packed bit-field that no access of its type covers")
                      | (n, narrow) :: rest =>
                          if n <? sz then
                            match packed_window end_b start w n with
                            | Some (off1, pos1) => TOk (mkMemLayout name narrow off1 (MBBits pos1 w))
                            | None => pick rest
                            end
                          else pick rest
                      end in
                    pick cands
                | None => TErr (TEBad "a packed bit-field that no access of its type covers")
                end
              else TErr (TEBad "a packed bit-field that no access of its type covers")
          end
      end
  end.

Definition place_natural_bitfield (kind : su_kind) (name : option string)
  (ty : c_type) (w : Z) (env : c_type_env) (end0 al0 : Z)
  : c_tr (list placed_member * Z * Z) :=
  match type_size_align ty env with
  | TErr e => TErr e
  | TOk (sz, fal) =>
      let unit_bits := 8 * sz in
      let '(start, end1) := bitfield_start_end kind end0 w unit_bits in
      match name with
      | None => TOk ([], end1, al0)
      | Some _ =>
          let unit_off := Z.div start unit_bits * sz in
          let pos := Z.modulo start unit_bits in
          TOk ([PMNormal (mkMemLayout name ty unit_off (MBBits pos w))],
               end1, Z.max al0 fal)
      end
  end.

Definition place_field_member (kind : su_kind) (packing : su_packing)
  (env : c_type_env) (fld : su_field) (end0 al0 : Z)
  : c_tr (list placed_member * Z * Z) :=
  match fld with
  | SFBad why => TErr (TEBad why)
  | SFField name ty MANone =>
      match field_size_natural_align ty env with
      | TErr e => TErr e
      | TOk (fsz, nat_al) =>
          let fal :=
            match packing with
            | PackPacked => 1
            | PackCap n => if n <? nat_al then n else nat_al
            | PackNatural => nat_al
            end in
          let '(off, end1) := member_offset_end kind end0 fsz fal in
          TOk ([PMNormal (mkMemLayout name ty off MBNone)], end1, Z.max al0 fal)
      end
  | SFField name ty (MAReq obase explicit) =>
      match field_size_natural_align ty env with
      | TErr e => TErr e
      | TOk (fsz, nat_al) =>
          let base_al := match obase with None => nat_al | Some b => b end in
          match packing with
          | PackCap n =>
              if n <? Z.max base_al explicit then
                TErr (TEBad "#pragma pack of an explicitly aligned member")
              else
                let fal := Z.max base_al explicit in
                let '(off, end1) := member_offset_end kind end0 fsz fal in
                TOk ([PMNormal (mkMemLayout name ty off MBNone)], end1, Z.max al0 fal)
          | PackPacked =>
              let '(off, end1) := member_offset_end kind end0 fsz explicit in
              TOk ([PMNormal (mkMemLayout name ty off MBNone)], end1, Z.max al0 explicit)
          | PackNatural =>
              let fal := Z.max base_al explicit in
              let '(off, end1) := member_offset_end kind end0 fsz fal in
              TOk ([PMNormal (mkMemLayout name ty off MBNone)], end1, Z.max al0 fal)
          end
      end
  | SFField _ _ (MABad why) => TErr (TEBad why)
  | SFBits name ty w =>
      match packing with
      | PackNatural => place_natural_bitfield kind name ty w env end0 al0
      | PackCap n =>
          match type_size_align ty env with
          | TErr e => TErr e
          | TOk (_, fal) =>
              if fal <=? n then place_natural_bitfield kind name ty w env end0 al0
              else TErr (TEBad "#pragma pack of a bit-field")
          end
      | PackPacked =>
          match type_size_align ty env with
          | TErr e => TErr e
          | TOk (sz, _) =>
              let unit_bits := 8 * sz in
              let '(start, end1) :=
                if Z.eqb w 0 then bitfield_start_end kind end0 0 unit_bits
                else match kind with
                | KUnion => (0, Z.max end0 w)
                | KStruct => (end0, end0 + w)
                end in
              match name with
              | None => TOk ([], end1, al0)
              | Some _ => TOk ([PMPackedBits name ty start w], end1, al0)
              end
          end
      end
  end.

Definition aligned_su_def (d : su_def) (req : Z) : su_def :=
  match d with
  | SUDef kind ms sz0 al0 =>
      let al := Z.max al0 req in
      let sz := Z.div (sz0 + al - 1) al * al in
      SUDef kind ms sz al
  | _ => d
  end.

Definition su_layout (kind : su_kind) (packing : su_packing)
  (fields : list su_field) (req : Z) (env : c_type_env) : su_def :=
  let fix go (fs : list su_field) (end0 al0 : Z) (acc : list placed_member)
    : c_tr (list placed_member * Z * Z) :=
    match fs with
    | [] => TOk (rev_append acc [], end0, al0)
    | fld :: rest =>
        match place_field_member kind packing env fld end0 al0 with
        | TErr e => TErr e
        | TOk (pms, end1, al1) => go rest end1 al1 (rev_append pms acc)
        end
    end in
  let def0 :=
    match go fields 0 1 [] with
    | TErr (TEBad why) =>
        if String.eqb why "incomplete" then SUBad "incomplete member"
        else SUBad why
    | TErr _ => SUBad "incomplete member"
    | TOk (pms, end_bits, al) =>
        let end_b := Z.div (end_bits + 7) 8 in
        let fix finalize (xs : list placed_member) (acc : list c_member_layout)
          : c_tr (list c_member_layout) :=
          match xs with
          | [] => TOk (rev_append acc [])
          | pm :: rest =>
              match place_packed_unit end_b env pm with
              | TErr e => TErr e
              | TOk m => finalize rest (m :: acc)
              end
          end in
        match finalize pms [] with
        | TErr (TEBad why) => SUBad why
        | TErr _ => SUBad "incomplete member"
        | TOk ms =>
            let sz := Z.div (end_b + al - 1) al * al in
            SUDef kind ms sz al
        end
    end in
  aligned_su_def def0 req.

Fixpoint known_field_prefix (fs : list su_field) : list su_field :=
  match fs with
  | [] => []
  | SFBad _ :: _ => []
  | f :: rest => f :: known_field_prefix rest
  end.

Definition first_bad_field (fs : list su_field) : option string :=
  let fix go (xs : list su_field) :=
    match xs with
    | [] => None
    | SFBad why :: _ => Some why
    | _ :: rest => go rest
    end in
  go fs.

(** ## Constant arithmetic, bit counting, and operator folding *)

Fixpoint popcount_loop (fuel : nat) (x acc : Z) : Z :=
  match fuel with
  | O => acc
  | S f =>
      if x <=? 0 then acc
      else popcount_loop f (Z.land x (x - 1)) (acc + 1)
  end.

Fixpoint lsb_loop (fuel : nat) (x acc : Z) : Z :=
  match fuel with
  | O => acc
  | S f =>
      if Z.odd x then acc
      else lsb_loop f (Z.shiftr x 1) (acc + 1)
  end.

Definition bit_count_value (op : string) (bits x : Z) : option Z :=
  if String.eqb op "popcount" then Some (popcount_loop (Z.to_nat 128) x 0)
  else if String.eqb op "ffs" then
    Some (if Z.eqb x 0 then 0 else lsb_loop (Z.to_nat 128) x 0 + 1)
  else if String.eqb op "ctz" then
    if 0 <? x then Some (lsb_loop (Z.to_nat 128) x 0) else None
  else if String.eqb op "clz" then
    if 0 <? x then Some (bits - 1 - ilog x) else None
  else None.

Definition quotient_overflows (op : c_binop) (a b : Z) (t : c_type) : bool :=
  match op with
  | BDiv | BMod =>
      if Z.eqb b (-1) then
        match int_info t with
        | Some (sz, CSigned) => Z.eqb a (-(Z.shiftl 1 (8 * sz - 1)))
        | _ => false
        end
      else false
  | _ => false
  end.

Definition const_arith_op (op : c_binop) (a b : Z) : option c_const_val :=
  match op with
  | BAdd => Some (CVInt (a + b))
  | BSub => Some (CVInt (a - b))
  | BMul => Some (CVInt (a * b))
  | BDiv => Some (if Z.eqb b 0 then CVUb else CVInt (Z.quot a b))
  | BMod => Some (if Z.eqb b 0 then CVUb else CVInt (Z.rem a b))
  | BAnd => Some (CVInt (Z.land a b))
  | BOr => Some (CVInt (Z.lor a b))
  | BXor => Some (CVInt (Z.lxor a b))
  | _ => None
  end.

Definition const_compare_Z (op : c_binop) (a b : Z) : option bool :=
  match op with
  | BEq => Some (Z.eqb a b)
  | BNe => Some (negb (Z.eqb a b))
  | BLt => Some (a <? b)
  | BGt => Some (b <? a)
  | BLe => Some (a <=? b)
  | BGe => Some (b <=? a)
  | _ => None
  end.

Definition ieee_binop_of (op : c_binop) : option ieee_binop :=
  match op with
  | BAdd => Some IeeeAdd | BSub => Some IeeeSub
  | BMul => Some IeeeMul | BDiv => Some IeeeDiv
  | _ => None
  end.

Definition ieee_cond_of (op : c_binop) : option ieee_cond :=
  match op with
  | BEq => Some ICEq | BNe => Some ICNe
  | BLt => Some ICLt | BLe => Some ICLe
  | BGt => Some ICGt | BGe => Some ICGe
  | _ => None
  end.

Definition kind_binary_const (op : c_binop) (va : c_const_val) (ta : c_type)
  (vb : c_const_val) (tb : c_type) (res_t : c_type) : option c_const_val :=
  match op with
  | BLand =>
      match const_truth va ta, const_truth vb tb with
      | CVUb, _ => Some CVUb
      | CVInt a, bv =>
          if Z.eqb a 0 then Some (CVInt 0)
          else match bv with
          | CVUb => Some CVUb
          | CVInt b => Some (CVInt (if Z.eqb b 0 then 0 else 1))
          end
      end
  | BLor =>
      match const_truth va ta, const_truth vb tb with
      | CVUb, _ => Some CVUb
      | CVInt a, bv =>
          if negb (Z.eqb a 0) then Some (CVInt 1)
          else match bv with
          | CVUb => Some CVUb
          | CVInt b => Some (CVInt (if Z.eqb b 0 then 0 else 1))
          end
      end
  | BShl | BShr =>
      match va, vb with
      | CVUb, _ | _, CVUb => Some CVUb
      | CVInt a0, CVInt b =>
          match int_info res_t with
          | Some (sz, _) =>
              if (0 <=? b) && (b <? 8 * sz) then
                match convert_int a0 res_t with
                | Some a =>
                    let r := match op with BShl => Z.shiftl a b | _ => Z.shiftr a b end in
                    match convert_int r res_t with Some w => Some (CVInt w) | None => None end
                | None => None
                end
              else Some CVUb
          | None => None
          end
      end
  | BEq | BNe | BLt | BGt | BLe | BGe =>
      match binary_operands op ta tb with
      | Some (ct, _, _) =>
          match va, vb with
          | CVUb, _ | _, CVUb => Some CVUb
          | _, _ =>
              match const_convert va ta ct, const_convert vb tb ct with
              | Some (CVInt a), Some (CVInt b) =>
                  match float_fmt_of ct, ieee_cond_of op with
                  | Some k, Some cond => Some (CVInt (ieee_compare k cond a b))
                  | _, _ =>
                      match const_compare_Z op a b with
                      | Some ok => Some (CVInt (if ok then 1 else 0))
                      | None => None
                      end
                  end
              | Some CVUb, _ | _, Some CVUb => Some CVUb
              | _, _ => None
              end
          end
      | None => None
      end
  | _ =>
      match va, vb with
      | CVUb, _ | _, CVUb => Some CVUb
      | _, _ =>
          match const_convert va ta res_t, const_convert vb tb res_t with
          | Some (CVInt a), Some (CVInt b) =>
              match float_fmt_of res_t with
              | Some k =>
                  match ieee_binop_of op with
                  | Some iop => Some (CVInt (ieee_binary k iop a b))
                  | None => None
                  end
              | None =>
                  if quotient_overflows op a b res_t then Some CVUb
                  else
                    match const_arith_op op a b with
                    | Some CVUb => Some CVUb
                    | Some (CVInt r) =>
                        match convert_int r res_t with Some w => Some (CVInt w) | None => None end
                    | None => None
                    end
              end
          | Some CVUb, _ | _, Some CVUb => Some CVUb
          | _, _ => None
          end
      end
  end.

Definition constant_unary_op (t : c_type) (op : c_unop) (a : Z) : option c_const_val :=
  match float_fmt_of t with
  | Some k =>
      match op with
      | UPlus => Some (CVInt a)
      | UNeg => Some (CVInt (ieee_neg k a))
      | _ => None
      end
  | None =>
      let or0 :=
        match op with
        | UNeg => Some (-a)
        | UPlus => Some a
        | UBnot => Some (Z.lnot a)
        | _ => None
        end in
      match or0 with
      | Some r => match convert_int r t with Some w => Some (CVInt w) | None => None end
      | None => None
      end
  end.

(** ## Small declaration, atomic, and expression-tag helpers *)

Fixpoint object_declarator (d : c_dcl_type) : bool :=
  match d with
  | DTBase => true
  | DTArray inner _ => object_declarator inner
  | _ => false
  end.

Definition inherited_alignment (specs : list c_spec) (syn : c_dcl_type)
  (env : c_type_env) : option Z :=
  if negb (object_declarator syn) then None
  else
    let fix find_tname (ss : list c_spec) :=
      match ss with
      | [] => None
      | SpTname nm :: rest =>
          match lookup_talign env nm with
          | Some (Some a) => Some a
          | _ => find_tname rest
          end
      | _ :: rest => find_tname rest
      end in
    find_tname specs.

Definition enum_key_of (tag : option string) (es : c_enumerators)
  : option enum_key_t :=
  match tag with
  | Some nm => Some (EKTag nm)
  | None =>
      match es with
      | EnumList (Enumerator first _ :: _) | EnumPacked (Enumerator first _ :: _) =>
          Some (EKAnon first)
      | _ => None
      end
  end.

Definition atomic_su_base (ty base0 : c_type) : c_type :=
  match ty with
  | TAtomic _ p =>
      let '(qs, b) :=
        match base0 with TQual qs1 b1 => (qs1, b1) | _ => ([], base0) end in
      match b with
      | TAtomic _ _ => base0
      | _ =>
          match qs with
          | [] => TAtomic b p
          | _ => TQual qs (TAtomic b p)
          end
      end
  | _ => base0
  end.

Definition parameter_syntax (syn : c_dcl_type) : c_dcl_type :=
  match syn with
  | DTArray s _ => DTPtr s []
  | DTFunc s p => DTPtr (DTFunc s p) []
  | _ => syn
  end.

Definition expr_tag_key (kind : su_kind) (tag : option string)
  (ms : list c_member) (attrs : list (list attr_tok)) : string :=
  String.concat "" (rev_append (emit_spec (SpSu kind tag (Some ms) attrs) []) []).

Definition has_defining_su (specs : list c_spec) : bool :=
  existsb (fun sp =>
    match sp with SpSu _ _ (Some _) _ => true | _ => false end) specs.

(** Collect type names inside an expression whose specifiers define a struct
    or union, skipping statement expressions (which declare in their own
    blocks). *)
Fixpoint defining_type_names_expr (fuel : nat) (e : c_expr) (acc : list c_type_name)
  : list c_type_name :=
  match fuel with
  | O => acc
  | S f =>
      let go_tn (tn : c_type_name) (a : list c_type_name) :=
        match tn with
        | TypeName specs _ => if has_defining_su specs then tn :: a else a
        end in
      let fix go_list (es : list c_expr) (a : list c_type_name) :=
        match es with
        | [] => a
        | x :: rest => go_list rest (defining_type_names_expr f x a)
        end in
      let fix go_init (ini : c_init) (a : list c_type_name) :=
        match ini with
        | InitExpr x => defining_type_names_expr f x a
        | InitList entries =>
            let fix go_es (zs : list c_init_entry) (a0 : list c_type_name) :=
              match zs with
              | [] => a0
              | InitEntry _ i1 :: rest => go_es rest (go_init i1 a0)
              end in
            go_es entries a
        end in
      match e with
      | EBin _ a b | EAssign _ a b | EComma a b | EIndex a b | EGCond a b =>
          defining_type_names_expr f b (defining_type_names_expr f a acc)
      | EUn _ a | EMember a _ | EArrow a _ | ESizeofExpr a | EAlignofExpr a
      | ERealPart a | EImagPart a =>
          defining_type_names_expr f a acc
      | ECond c a b =>
          defining_type_names_expr f b
            (defining_type_names_expr f a (defining_type_names_expr f c acc))
      | ECall fn args =>
          go_list args (defining_type_names_expr f fn acc)
      | ECast tn a | EBitCast tn a | EVaArg a tn | EConvertVector a tn =>
          defining_type_names_expr f a (go_tn tn acc)
      | ESizeofType tn | EAlignofType tn | EOffsetof tn _ => go_tn tn acc
      | ETypesCompatible ta tb => go_tn tb (go_tn ta acc)
      | EComplit tn entries =>
          let a1 := go_tn tn acc in
          go_init (InitList entries) a1
      | EGeneric ctrl assocs =>
          let a1 := defining_type_names_expr f ctrl acc in
          let fix go_as (xs : list c_generic_assoc) (a0 : list c_type_name) :=
            match xs with
            | [] => a0
            | GAssocType tn x :: rest =>
                go_as rest (defining_type_names_expr f x (go_tn tn a0))
            | GAssocDefault x :: rest =>
                go_as rest (defining_type_names_expr f x a0)
            end in
          go_as assocs a1
      | EStmtExpr _ | EId _ | ENum _ _ _ | EChr _ | EFloat _ | EImag _
      | EStr _ | EWStr _ _ | ELabelAddr _ => acc
      end
  end.

Definition defining_type_names (e : c_expr) : list c_type_name :=
  rev_append (defining_type_names_expr (Z.to_nat 1024) e []) [].

Definition generic_atomic (name : string) (args : list c_expr) : option c_expr :=
  let void_tn := TypeName [SpTspec "void"] DTBase in
  if String.eqb name "__atomic_load" then
    match args with
    | [p; r; o] =>
        Some (ECast void_tn (EAssign "=" (EUn UDeref r)
                (ECall (EId "__atomic_load_n") [p; o])))
    | _ => None
    end
  else if String.eqb name "__atomic_store" then
    match args with
    | [p; v; o] =>
        Some (ECall (EId "__atomic_store_n") [p; EUn UDeref v; o])
    | _ => None
    end
  else if String.eqb name "__atomic_exchange" then
    match args with
    | [p; v; r; o] =>
        Some (ECast void_tn (EAssign "=" (EUn UDeref r)
                (ECall (EId "__atomic_exchange_n") [p; EUn UDeref v; o])))
    | _ => None
    end
  else if String.eqb name "__atomic_compare_exchange" then
    match args with
    | [p; e; d; w; s; f] =>
        Some (ECall (EId "__atomic_compare_exchange_n") [p; e; EUn UDeref d; w; s; f])
    | _ => None
    end
  else None.

Definition rmw_operand (op : string) (t : c_type) : bool :=
  if int_type t then true
  else match t with
  | TPtr _ => str_in op ["xchg"; "add"; "sub"]
  | TFloatK FFloat | TFloatK FDouble => String.eqb op "xchg"
  | _ => false
  end.

Definition gnu_operand (op : string) (t : c_type) : bool :=
  if int_type t then true
  else match t with TPtr _ => String.eqb op "xchg" | _ => false end.

Definition contains_substr (needle hay : string) : bool :=
  let nl := String.length needle in
  let hl := String.length hay in
  if (hl <? nl)%nat then false
  else
    let fix scan (fuel i : nat) : bool :=
      match fuel with
      | O => false
      | S f =>
          if String.eqb (String.substring i nl hay) needle then true
          else scan f (S i)
      end in
    scan (S (hl - nl)) 0%nat.

Definition order_positions (name : string) (nargs : nat) : option (list nat) :=
  if (starts_with "__atomic_" name || starts_with "__c11_atomic_" name) &&
     negb (str_in name ["__c11_atomic_init"; "__atomic_always_lock_free";
                        "__atomic_is_lock_free"; "__c11_atomic_is_lock_free"]) then
    match nargs with
    | O => None
    | S last =>
        if contains_substr "compare_exchange" name then
          match last with
          | O => None
          | S prev => Some [prev; last]
          end
        else Some [last]
    end
  else None.

Fixpoint literal_length (e : c_expr) : option Z :=
  match e with
  | ECast _ inner => literal_length inner
  | EStr bs => Some (Z.of_nat (List.length bs))
  | EWStr _ cs => Some (Z.of_nat (List.length cs))
  | _ => None
  end.

Definition binding_type_of (b : ord_binding) : c_type :=
  match b with
  | BTypedef t => t
  | BEnumConst _ t => t
  | BVar _ t => t
  | BGVar t _ _ _ => t
  | BFn t _ _ => t
  end.

Definition identifier_type (b : ord_binding) (name : string) (env : c_type_env) : c_type :=
  match b with
  | BEnumConst _ t => t
  | _ =>
      let t0 := binding_type_of b in
      match lookup_qtype env name with
      | Some rt => reflected_shape rt t0
      | None => t0
      end
  end.

Definition binding_node (b : ord_binding) (t : c_type) (name : string) : option c_typed_node :=
  match b with
  | BVar _ _ | BGVar _ _ _ _ => Some (TNode CatObj t (TFId name))
  | BFn _ _ _ => Some (TNode CatFun t (TFId name))
  | BEnumConst v _ => Some (TNode CatVal t (TFInt v))
  | BTypedef _ => None
  end.

Definition designator_node (t : c_type) (form : c_typed_form) : c_typed_node :=
  match t with
  | TFunc _ _ _ => TNode CatFun t form
  | _ => TNode CatObj t form
  end.

Definition member_node (xs : c_typed_node) (field : string) (t : c_type)
  : option c_typed_node :=
  match tree_cat xs with
  | CatObj => Some (TNode CatObj t (TFMember xs field))
  | CatVal => Some (TNode CatVal t (TFMember xs field))
  | CatFun => None
  end.

Definition assignment_type (x : c_typed_node) : c_type :=
  match x with
  | TNode CatObj t0 (TFBitfield _ _ w) => bitfield_promotion (value_type t0) w
  | _ =>
      let t0 := tree_type x in
      match unqualified t0 with
      | TAtomic s _ => s
      | _ => t0
      end
  end.

Definition arity_fits (ps : option (list c_type)) (variadic : bool) (nargs : nat) : bool :=
  match ps with
  | None => true
  | Some xs =>
      let np := List.length xs in
      if variadic then (np <=? nargs)%nat else Nat.eqb nargs np
  end.

Definition is_other_type_spec (sp : c_spec) : bool :=
  match sp with
  | SpTname _ | SpSu _ _ _ _ | SpEnum _ _
  | SpTypeofType _ | SpTypeofExpr _ | SpAtomic _ | SpAutoType => true
  | _ => false
  end.

Definition extract_su_packing (attrs : list (list attr_tok)) : su_packing :=
  if existsb packed_attr attrs then PackPacked
  else
    let fix find_pack (xs : list (list attr_tok)) :=
      match xs with
      | [] => PackNatural
      | a :: rest =>
          let fix find_entry (es : list (string * list attr_tok)) :=
            match es with
            | [] => find_pack rest
            | (w, AGroup [ATok (CAst.TInt n _ _)] :: _) :: more =>
                if String.eqb w "__nanofil_pack__" then PackCap n
                else find_entry more
            | _ :: more => find_entry more
            end in
          find_entry (attr_entries a)
      end in
    find_pack attrs.

Definition collect_aligned_entries (attrs : list (list attr_tok))
  : list (option (list attr_tok)) :=
  let fix go_attr (a : list attr_tok) (acc : list (option (list attr_tok))) :=
    let fix go_es (es : list (string * list attr_tok)) (a0 : list (option (list attr_tok))) :=
      match es with
      | [] => a0
      | (w, rest) :: more =>
          if String.eqb w "aligned" || String.eqb w "__aligned__" then
            let req := match rest with AGroup ts :: _ => Some ts | _ => None end in
            go_es more (req :: a0)
          else go_es more a0
      end in
    go_es (attr_entries a) acc in
  rev_append (fold_left (fun acc a => go_attr a acc) attrs []) [].

Definition typedefs_in_tokens (ts : list token) (env : c_type_env) : list string :=
  let fix go (xs : list token) (acc : list string) :=
    match xs with
    | [] => acc
    | mkTok (TId nm) _ :: rest =>
        match lookup_ordinary env nm with
        | Some (BTypedef _) =>
            if str_in nm acc then go rest acc else go rest (nm :: acc)
        | _ => go rest acc
        end
    | _ :: rest => go rest acc
    end in
  go ts [].

Definition attribute_expression (ts : list attr_tok) (env : c_type_env)
  : option c_expr :=
  let flat := flat_tokens ts in
  let tns := typedefs_in_tokens flat env in
  match c_constant_expression flat tns with
  | COk e => Some e
  | CErr _ => None
  end.

Definition z_in_list (z : Z) (xs : list Z) : bool :=
  existsb (Z.eqb z) xs.

(** ## Mutually recursive semantic core

    Declarations, specifiers, declarators, type reflection, expression
    elaboration, constant evaluation, and `_Generic` selection recurse into
    each other through `typeof`, array sizes, enum values, `sizeof`, and
    alignment requests. A single fuel parameter keeps the whole recursion
    structurally terminating for Rocq, OCaml extraction, and λANF. *)

Fixpoint decl_types_f (fuel : nat) (specs0 : list c_spec) (inits : list c_init_decl)
  (env0 : c_type_env) {struct fuel} : c_tr (list c_decl * c_type_env) :=
  match fuel with
  | O => TErr (TESema "type checker fuel exhausted")
  | S f =>
      let stg := decl_storage specs0 in
      let '(reqs0, specs) := alignment_requests specs0 in
      match specs_type_f f specs env0 with
      | TErr e => TErr e
      | TOk (base, env1) =>
          let fix go_inits (xs : list c_init_decl) (e : c_type_env) (acc : list c_decl)
            : c_tr (list c_decl * c_type_env) :=
            match xs with
            | [] => TOk (rev_append acc [], e)
            | InitDecl (Dcl oname syn asm_sym) init :: rest =>
                match oname with
                | None => go_inits rest e acc
                | Some name =>
                    match apply_declarator_f f syn base e with
                    | TErr err => TErr err
                    | TOk (ty0, e1) =>
                        let refl := reflect_type_f f (TypeName specs syn) ty0 e1 in
                        let e2 := bind_qtype name refl e1 in
                        let inh := inherited_alignment specs syn e2 in
                        match stg with
                        | StTypedef =>
                            let ota :=
                              match reqs0 with
                              | [] => TOk inh
                              | _ =>
                                  let has_alignas :=
                                    existsb (fun r =>
                                      match r with ARType _ | ARExpr _ => true | _ => false end) reqs0 in
                                  if has_alignas then TErr (TEBad "_Alignas on a typedef")
                                  else
                                    let fix eval_reqs (rs : list align_req) (mx : Z) : c_tr Z :=
                                      match rs with
                                      | [] => TOk mx
                                      | r :: rm =>
                                          match request_alignment_f f r e2 with
                                          | Some a => eval_reqs rm (Z.max mx a)
                                          | None => TErr (TEBad "alignment attributes")
                                          end
                                      end in
                                    match eval_reqs reqs0 0 with
                                    | TErr err => TErr err
                                    | TOk a0 =>
                                        if max_alignment <? a0 then
                                          TErr (TEBad "an alignment above 4096")
                                        else TOk (Some a0)
                                    end
                              end in
                            let '(ty1, ta1) :=
                              match ota with
                              | TErr (TEBad why) => (TBad why, None)
                              | TErr _ => (TBad "alignment attributes", None)
                              | TOk (Some a) =>
                                  match ty0 with
                                  | TVec el n _ => (TVec el n a, Some a)
                                  | _ => (ty0, Some a)
                                  end
                              | TOk None => (ty0, None)
                              end in
                            let e2a :=
                              match ty1 with
                              | TVec _ _ _ =>
                                  if negb (c_type_eqb ty1 ty0) then
                                    let r1 := match refl with TQual qs _ => qualify qs ty1 | _ => ty1 end in
                                    bind_qtype name r1 e2
                                  else e2
                              | _ => e2
                              end in
                            let e3 := bind_ordinary name (BTypedef ty1) e2a in
                            let e4 :=
                              match ta1 with
                              | None =>
                                  match lookup_talign e3 name with
                                  | Some _ => bind_talign name None e3
                                  | None => e3
                                  end
                              | Some a =>
                                  let e3a := bind_talign name (Some a) e3 in
                                  add_aligned_typedef ty1 e3a
                              end in
                            let e5 :=
                              match ty1 with
                              | TUnion uid =>
                                  if existsb (fun sp => match sp with SpAttr ts => transparent_attr ts | _ => false end) specs then
                                    mark_transparent_su uid e4
                                  else e4
                              | _ => e4
                              end in
                            go_inits rest e5 acc
                        | _ =>
                            let reqs :=
                              match inh with
                              | Some ia => ARValue ia :: reqs0
                              | None => reqs0
                              end in
                            let '(ty, oal) :=
                              match reqs with
                              | [] => (ty0, None)
                              | _ =>
                                  match ty0 with
                                  | TBad _ => (ty0, None)
                                  | TFunc _ _ _ => (TBad "alignment attributes", None)
                                  | _ =>
                                      match type_size_align (innermost_element ty0) e2 with
                                      | TErr _ => (TBad "alignment attributes", None)
                                      | TOk (_, nat_al) =>
                                          let fix eval_rs (rs : list align_req) (mx : Z) : option Z :=
                                            match rs with
                                            | [] => Some mx
                                            | r :: rm =>
                                                match request_alignment_f f r e2 with
                                                | Some a => eval_rs rm (Z.max mx a)
                                                | None => None
                                                end
                                            end in
                                          match eval_rs reqs nat_al with
                                          | None => (TBad "alignment attributes", None)
                                          | Some mx =>
                                              if Z.eqb mx nat_al then (ty0, None)
                                              else if mx <=? max_alignment then (ty0, Some mx)
                                              else (TBad "an alignment above 4096", None)
                                          end
                                      end
                                  end
                              end in
                            let e3 :=
                              match oal with
                              | Some a => bind_qalign name (Some a) e2
                              | None =>
                                  match lookup_qalign e2 name with
                                  | Some _ => bind_qalign name None e2
                                  | None => e2
                                  end
                              end in
                            let e4 :=
                              let oc :=
                                match refl with
                                | TQual qs _ =>
                                    if has_qual QConst qs && negb (has_qual QVolatile qs) &&
                                       arithmetic_type ty0 then
                                      match init with
                                      | Some (InitExpr ie) =>
                                          match const_eval_f f ie e3 with
                                          | Some (CVInt v0, from_t) =>
                                              match const_convert (CVInt v0) from_t ty0 with
                                              | Some (CVInt v) => Some v
                                              | _ => None
                                              end
                                          | _ => None
                                          end
                                      | _ => None
                                      end
                                    else None
                                | _ => None
                                end in
                              match oc with
                              | Some v => bind_cval name (Some v) e3
                              | None =>
                                  match stg, init with
                                  | StExtern, None => e3
                                  | _, _ =>
                                      match lookup_cval e3 name with
                                      | Some _ => bind_cval name None e3
                                      | None => e3
                                      end
                                  end
                              end in
                            go_inits rest e4 (mkCDecl name ty stg asm_sym init :: acc)
                        end
                    end
                end
            end in
          go_inits inits env1 []
      end
  end

with specs_type_f (fuel : nat) (specs : list c_spec) (env0 : c_type_env) {struct fuel}
  : c_tr (c_type * c_type_env) :=
  match fuel with
  | O => TErr (TESema "type checker fuel exhausted")
  | S f =>
      let kws := fold_right (fun sp acc => match sp with SpTspec k => k :: acc | _ => acc end) [] specs in
      let others := filter is_other_type_spec specs in
      let base_res : c_tr (c_type * c_type_env) :=
        match others, kws with
        | [other], [] =>
            match other with
            | SpTname nm =>
                if String.eqb nm "__builtin_va_list" then
                  TOk (TArray (TStruct va_list_id) (ALConst 1), env0)
                else if String.eqb nm "__int128_t" || String.eqb nm "__uint128_t" then
                  TOk (TBad "__int128", env0)
                else
                  match lookup_ordinary env0 nm with
                  | Some (BTypedef t0) => TOk (t0, env0)
                  | _ => TOk (TBad "unknown typedef", env0)
                  end
            | SpAutoType => TOk (TBad "__auto_type without an initializer", env0)
            | SpTypeofExpr e =>
                match elaborate_f f e env0 with
                | TOk (Some x) =>
                    let t0 := tree_type x in
                    if vm_type t0 then TOk (TBad "typeof a variably modified type", env0)
                    else TOk (unqualified t0, env0)
                | TOk None => TOk (TBad "typeof an expression that cannot be typed", env0)
                | TErr err => TErr err
                end
            | SpTypeofType tn =>
                match type_name_type_f f tn env0 with
                | TErr err => TErr err
                | TOk (t0, env1) =>
                    if vm_type t0 then TOk (TBad "typeof a variably modified type", env1)
                    else TOk (t0, env1)
                end
            | SpAtomic tn =>
                match type_name_type_f f tn env0 with
                | TErr err => TErr err
                | TOk (t0, env1) =>
                    let refl := reflect_type_f f tn t0 env1 in
                    match t0 with
                    | TBad _ => TOk (t0, env1)
                    | _ =>
                        let has_non_enum_q :=
                          match refl with
                          | TQual qs _ =>
                              existsb (fun q => match q with QEnum _ => false | _ => true end) qs
                          | _ => false
                          end in
                        if has_non_enum_q then TOk (TBad "_Atomic of a qualified type", env1)
                        else if atomic_object_type t0 then TOk (t0, env1)
                        else
                          match atomic_su_type t0 env1 with
                          | Some ta => TOk (ta, env1)
                          | None =>
                              TOk (TBad "_Atomic of a type other than an integer, pointer, float or double", env1)
                          end
                    end
                end
            | SpSu kind tag omems attrs =>
                match omems with
                | None =>
                    match tag with
                    | Some nm =>
                        match lookup_tag env0 nm with
                        | Some (TagSU k2 id) =>
                            if su_kind_eqb kind k2 then
                              TOk (match kind with KStruct => TStruct id | KUnion => TUnion id end, env0)
                            else
                              let '(id2, env1) := alloc_su_tag kind (Some nm) env0 in
                              TOk (match kind with KStruct => TStruct id2 | KUnion => TUnion id2 end, env1)
                        | _ =>
                            let '(id2, env1) := alloc_su_tag kind (Some nm) env0 in
                            TOk (match kind with KStruct => TStruct id2 | KUnion => TUnion id2 end, env1)
                        end
                    | None =>
                        let '(id2, env1) := alloc_su_tag kind None env0 in
                        TOk (match kind with KStruct => TStruct id2 | KUnion => TUnion id2 end, env1)
                    end
                | Some mems =>
                    let ekey := expr_tag_key kind tag mems attrs in
                    match lookup_expr_tag ekey env0 with
                    | Some id =>
                        TOk (match kind with KStruct => TStruct id | KUnion => TUnion id end, env0)
                    | None =>
                        let '(id, env1) :=
                          match tag with
                          | Some nm =>
                              match lookup_tag env0 nm with
                              | Some (TagSU k2 id0) =>
                                  if su_kind_eqb kind k2 then
                                    match lookup_su_def env0 id0 with
                                    | Some (SUIncomplete _) => (id0, env0)
                                    | _ => alloc_su_tag kind tag env0
                                    end
                                  else alloc_su_tag kind tag env0
                              | _ => alloc_su_tag kind tag env0
                              end
                          | None => alloc_su_tag kind None env0
                          end in
                        let su_ty := match kind with KStruct => TStruct id | KUnion => TUnion id end in
                        let fix go_mems (ms : list c_member) (e : c_type_env)
                          (facc : list su_field) (racc : list (option string * c_type))
                          : c_tr (list su_field * list (option string * c_type) * c_type_env) :=
                          match ms with
                          | [] => TOk (rev_append facc [], rev_append racc [], e)
                          | MStaticAssert loc expr _ :: rest =>
                              match const_eval_f f expr e with
                              | Some (CVInt v, t) =>
                                  if int_type t then
                                    if negb (Z.eqb v 0) then go_mems rest e facc racc
                                    else sema_err loc "static assertion failed"
                                  else sema_err loc "static assertion is not a constant"
                              | _ => sema_err loc "static assertion is not a constant"
                              end
                          | MField fspecs00 (Dcl fname fsyn _) owidth :: rest =>
                              let has_shared :=
                                existsb (fun sp => match sp with SpSharedBase => true | _ => false end) fspecs00 in
                              let fspecs0 :=
                                filter (fun sp => match sp with SpSharedBase => false | _ => true end) fspecs00 in
                              let '(freqs, fspecs1) := alignment_requests fspecs0 in
                              let '(fspecs, fpacked) := member_packing fspecs1 in
                              let base_and_env : c_tr (c_type * c_type_env) :=
                                if has_shared then
                                  match sc_member_base (te_scope e) with
                                  | Some b => TOk (b, e)
                                  | None => specs_type_f f fspecs e
                                  end
                                else
                                  match specs_type_f f fspecs e with
                                  | TErr err => TErr err
                                  | TOk (b, e1a) => TOk (b, set_member_base b e1a)
                                  end in
                              match base_and_env with
                              | TErr err => TErr err
                              | TOk (fbase, e1) =>
                                  match apply_declarator_f f fsyn fbase e1 with
                                  | TErr err => TErr err
                                  | TOk (fty, e2) =>
                                      let finh :=
                                        if fpacked then Some 1
                                        else inherited_alignment fspecs fsyn e2 in
                                      let ma : member_align_req :=
                                        match freqs, finh with
                                        | [], None => MANone
                                        | _, _ =>
                                            let fix eval_rs (rs : list align_req) (mx : Z) : option Z :=
                                              match rs with
                                              | [] => Some mx
                                              | r :: rm =>
                                                  match request_alignment_f f r e2 with
                                                  | Some a => eval_rs rm (Z.max mx a)
                                                  | None => None
                                                  end
                                              end in
                                            match eval_rs freqs 1 with
                                            | None => MABad "alignment attributes"
                                            | Some expl =>
                                                if max_alignment <? expl then
                                                  MABad "an alignment above 4096"
                                                else MAReq finh expl
                                            end
                                        end in
                                      match bad_type fty with
                                      | Some why => go_mems rest e2 (SFBad why :: facc) racc
                                      | None =>
                                          match ma with
                                          | MABad why => go_mems rest e2 (SFBad why :: facc) racc
                                          | _ =>
                                              let has_ma := match ma with MANone => false | _ => true end in
                                              match owidth with
                                              | Some wexpr =>
                                                  if has_ma then
                                                    go_mems rest e2 (SFBad "alignment attributes" :: facc) racc
                                                  else if vm_type fty then
                                                    go_mems rest e2 (SFBad "variably modified member" :: facc) racc
                                                  else
                                                    let ow :=
                                                      match int_info fty with
                                                      | None => None
                                                      | Some (sz, _) =>
                                                          match const_eval_f f wexpr e2 with
                                                          | Some (CVInt w, wt) =>
                                                              if int_type wt then
                                                                let mx := match fty with TIntK IBool => 1 | _ => 8 * sz end in
                                                                if (0 <=? w) && (w <=? mx) &&
                                                                   (negb (Z.eqb w 0) || match fname with None => true | Some _ => false end) then
                                                                  Some w
                                                                else None
                                                              else None
                                                          | _ => None
                                                          end
                                                      end in
                                                    match ow with
                                                    | None => go_mems rest e2 (SFBad "invalid bit-field" :: facc) racc
                                                    | Some w =>
                                                        let qt := reflect_type_f f (TypeName fspecs fsyn) fty e2 in
                                                        if atomic_qualified qt then
                                                          go_mems rest e2 (SFBad "_Atomic bit-field" :: facc) racc
                                                        else
                                                          let racc1 :=
                                                            match fname with
                                                            | None => racc
                                                            | Some _ => (fname, qt) :: racc
                                                            end in
                                                          go_mems rest e2 (SFBits fname fty w :: facc) racc1
                                                    end
                                              | None =>
                                                  if vm_type fty then
                                                    go_mems rest e2 (SFBad "variably modified member" :: facc) racc
                                                  else
                                                    let qt := reflect_type_f f (TypeName fspecs fsyn) fty e2 in
                                                    go_mems rest e2 (SFField fname fty ma :: facc) ((fname, qt) :: racc)
                                              end
                                          end
                                      end
                                  end
                              end
                          end in
                        match go_mems mems env1 [] [] with
                        | TErr err => TErr err
                        | TOk (flds, refls, env2) =>
                            let packing := extract_su_packing attrs in
                            let def_align_reqs := collect_aligned_entries attrs in
                            let fix eval_def_al (rs : list (option (list attr_tok))) (a0 : Z) : option Z :=
                              match rs with
                              | [] => Some a0
                              | None :: rm => eval_def_al rm (Z.max a0 16)
                              | Some ts :: rm =>
                                  match attribute_expression ts env2 with
                                  | None => None
                                  | Some ae =>
                                      match const_eval_f f ae env2 with
                                      | Some (CVInt n, nt) =>
                                          if int_type nt && is_pow2 n && (n <=? max_alignment) then
                                            eval_def_al rm (Z.max a0 n)
                                          else None
                                      | _ => None
                                      end
                                  end
                              end in
                            let def :=
                              match eval_def_al def_align_reqs 1 with
                              | None => SUBad "alignment attributes"
                              | Some req_al =>
                                  match first_bad_field flds with
                                  | Some why =>
                                      let pref := known_field_prefix flds in
                                      match su_layout kind packing pref 1 env2 with
                                      | SUDef _ known _ _ => SUPartial why known
                                      | _ => SUBad why
                                      end
                                  | None => su_layout kind packing flds req_al env2
                                  end
                              end in
                            let env3 := put_su_def id def env2 in
                            let env4 := put_qmembers id refls env3 in
                            let env5 :=
                              match kind with
                              | KUnion =>
                                  if existsb transparent_attr attrs then mark_transparent_su id env4
                                  else env4
                              | KStruct => env4
                              end in
                            let env6 :=
                              if te_expr_tags_mode env5 then put_expr_tag ekey id env5
                              else env5 in
                            TOk (su_ty, env6)
                        end
                    end
                end
            | SpEnum tag es =>
                match es with
                | EnumNone =>
                    match tag with
                    | Some nm =>
                        match lookup_tag env0 nm with
                        | Some (TagEnum t0) => TOk (t0, env0)
                        | _ => TOk (TUInt, env0)
                        end
                    | None => TOk (TUInt, env0)
                    end
                | EnumList items | EnumPacked items =>
                    let is_packed := match es with EnumPacked _ => true | _ => false end in
                    let fix go_enums (zs : list c_enumerator) (next_v : Z) (e : c_type_env) (vacc : list Z)
                      : c_tr (list Z * c_type_env) :=
                      match zs with
                      | [] => TOk (rev_append vacc [], e)
                      | Enumerator enm oexpr :: rest =>
                          let ov :=
                            match oexpr with
                            | None => TOk next_v
                            | Some expr =>
                                match const_eval_f f expr e with
                                | Some (CVInt v, vt) =>
                                    if int_type vt then TOk v else TErr TENotConstant
                                | _ => TErr TENotConstant
                                end
                            end in
                          match ov with
                          | TErr err => TErr err
                          | TOk v =>
                              let ct :=
                                if (-2147483648 <=? v) && (v <=? 2147483647) then TInt else TLong in
                              let e1 := bind_ordinary enm (BEnumConst v ct) e in
                              go_enums rest (v + 1) e1 (v :: vacc)
                          end
                      end in
                    match go_enums items 0 env0 [] with
                    | TErr err => TErr err
                    | TOk (vs, env1) =>
                        let under :=
                          if is_packed then packed_enum_underlying vs
                          else enum_underlying vs in
                        let env2 :=
                          match tag with
                          | Some nm => bind_tag nm (TagEnum under) env1
                          | None => env1
                          end in
                        TOk (under, env2)
                    end
                end
            | _ => TOk (TBad "conflicting type specifiers", env0)
            end
        | [], _ => TOk (keyword_type kws, env0)
        | _, _ => TOk (TBad "conflicting type specifiers", env0)
        end in
      match base_res with
      | TErr err => TErr err
      | TOk (ty0, env1) =>
          let has_addr_space :=
            existsb (fun sp => match sp with SpAttr ts => address_space_attr ts | _ => false end) specs in
          let has_vec :=
            existsb (fun sp => match sp with SpAttr ts => vector_attr ts | _ => false end) specs in
          let has_atomic_q :=
            existsb (fun sp => match sp with SpQual q => String.eqb q "atomic" | _ => false end) specs in
          let find_mode_spec :=
            let fix go (ss : list c_spec) :=
              match ss with
              | [] => None
              | SpAttr ts :: rest =>
                  match mode_attr ts with Some m => Some m | None => go rest end
              | _ :: rest => go rest
              end in
            go specs in
          if has_addr_space then TOk (TBad "address_space", env1)
          else if has_vec then
            let elem := unqualified ty0 in
            if negb (topt_vectors (te_opts env1)) then TOk (TBad "vector types", env1)
            else match elem with
            | TBad _ => TOk (elem, env1)
            | _ =>
                let find_vec_sz :=
                  let fix go (ss : list c_spec) :=
                    match ss with
                    | [] => None
                    | SpAttr ts :: rest =>
                        let fix go_es (es : list (string * list attr_tok)) :=
                          match es with
                          | [] => go rest
                          | (w, [AGroup arg_ts]) :: more =>
                              if String.eqb w "vector_size" || String.eqb w "__vector_size__" then
                                match attribute_expression arg_ts env1 with
                                | Some ae =>
                                    match const_eval_f f ae env1 with
                                    | Some (CVInt sz, st) => if int_type st then Some sz else go_es more
                                    | _ => go_es more
                                    end
                                | None => go_es more
                                end
                              else go_es more
                          | _ :: more => go_es more
                          end in
                        go_es (attr_entries ts)
                    | _ :: rest => go rest
                    end in
                  go specs in
                match find_vec_sz with
                | None => TOk (TBad "vector types", env1)
                | Some sz =>
                    let vec_elem_ok :=
                      match elem with
                      | TIntK IBool => false
                      | TIntK _ | TFloatK FFloat | TFloatK FDouble => true
                      | _ => false
                      end in
                    if negb vec_elem_ok then
                      TOk (TBad "a vector of a type other than an integer, float or double", env1)
                    else
                      match type_size_align elem env1 with
                      | TErr _ => TOk (TBad "vector types", env1)
                      | TOk (esz, _) =>
                          if negb (z_in_list sz [8; 16; 32]) then
                            TOk (TBad ("vector types of " ++ z_to_string sz ++ " bytes"), env1)
                          else
                            let n := Z.div sz esz in
                            let find_vec_al :=
                              let fix go (ss : list c_spec) :=
                                match ss with
                                | [] => None
                                | SpAttr ts :: rest =>
                                    let fix go_es (es : list (string * list attr_tok)) :=
                                      match es with
                                      | [] => go rest
                                      | (w, arg) :: more =>
                                          if String.eqb w "aligned" || String.eqb w "__aligned__" then
                                            match request_alignment_f f (ARAttr (ATok (TId "aligned") :: arg)) env1 with
                                            | Some a0 => Some a0
                                            | None => go_es more
                                            end
                                          else go_es more
                                      end in
                                    go_es (attr_entries ts)
                                | _ :: rest => go rest
                                end in
                              go specs in
                            let a := match find_vec_al with Some a0 => a0 | None => sz end in
                            TOk (TVec elem n a, env1)
                      end
                end
            end
          else if has_atomic_q then
            match atomic_su_type ty0 env1 with
            | Some ta => TOk (ta, env1)
            | None =>
                match ty0 with
                | TBad _ => TOk (ty0, env1)
                | _ =>
                    if atomic_object_type ty0 then
                      match find_mode_spec with
                      | Some m => TOk (mode_type ty0 m, env1)
                      | None =>
                          if existsb layout_attr_spec specs then TOk (TBad "alignment attributes", env1)
                          else TOk (ty0, env1)
                      end
                    else
                      TOk (TBad "_Atomic on a type other than an integer, pointer, float or double", env1)
                end
            end
          else
            match find_mode_spec with
            | Some m => TOk (mode_type ty0 m, env1)
            | None =>
                if existsb layout_attr_spec specs then TOk (TBad "alignment attributes", env1)
                else TOk (ty0, env1)
            end
      end
  end

with apply_declarator_f (fuel : nat) (syn : c_dcl_type) (base : c_type)
  (env0 : c_type_env) {struct fuel} : c_tr (c_type * c_type_env) :=
  match fuel with
  | O => TErr (TESema "type checker fuel exhausted")
  | S f =>
      match syn with
      | DTBase => TOk (base, env0)
      | DTPtr inner _ =>
          match apply_declarator_f f inner base env0 with
          | TErr e => TErr e
          | TOk (t, env1) => TOk (TPtr t, env1)
          end
      | DTArray inner sz_expr =>
          match apply_declarator_f f inner base env0 with
          | TErr e => TErr e
          | TOk (elem, env1) =>
              match sz_expr with
              | ASNone => TOk (TArray elem ALNone, env1)
              | ASStar => TOk (TArray elem ALVlaStar, env1)
              | ASExpr e =>
                  match const_eval_f f e env1 with
                  | Some (CVInt n, nt) =>
                      if int_type nt then
                        if 0 <=? n then TOk (TArray elem (ALConst n), env1)
                        else TOk (TBad "negative array size", env1)
                      else TOk (TArray elem (ALVlaExpr e), env1)
                  | _ => TOk (TArray elem (ALVlaExpr e), env1)
                  end
              end
          end
      | DTFunc inner params =>
          match apply_declarator_f f inner base env0 with
          | TErr e => TErr e
          | TOk (ret, env1) =>
              match params with
              | PUnspecified => TOk (TFunc ret None false, env1)
              | PKnr _ | PKnrDef _ _ =>
                  TErr (TESema "a parameter list without types is only allowed in a function definition")
              | PParams ps variadic =>
                  let saved := te_scope env1 in
                  let fix go_ps (xs : list c_param) (e : c_type_env) (acc : list c_type)
                    : c_tr (list c_type * c_type_env) :=
                    match xs with
                    | [] => TOk (rev_append acc [], e)
                    | Param pspecs (Dcl pname psyn _) :: rest =>
                        match specs_type_f f pspecs e with
                        | TErr err => TErr err
                        | TOk (pb, e1) =>
                            match apply_declarator_f f psyn pb e1 with
                            | TErr err => TErr err
                            | TOk (pt0, e2) =>
                                let pt1 := type_adjusted pt0 in
                                let e3 :=
                                  match pname with
                                  | Some nm => bind_ordinary nm (BVar VSNone pt1) e2
                                  | None => e2
                                  end in
                                go_ps rest e3 (pt1 :: acc)
                            end
                        end
                    end in
                  match go_ps ps env1 [] with
                  | TErr err => TErr err
                  | TOk (pts, env2) =>
                      TOk (TFunc ret (Some pts) variadic, with_scope env2 saved)
                  end
              end
          end
      end
  end

with type_name_type_f (fuel : nat) (tn : c_type_name) (env0 : c_type_env)
  {struct fuel} : c_tr (c_type * c_type_env) :=
  match fuel with
  | O => TErr (TESema "type checker fuel exhausted")
  | S f =>
      match tn with
      | TypeName specs syn =>
          match specs_type_f f specs env0 with
          | TErr e => TErr e
          | TOk (base, env1) => apply_declarator_f f syn base env1
          end
      end
  end

with reflect_type_f (fuel : nat) (tn : c_type_name) (ty : c_type)
  (env : c_type_env) {struct fuel} : c_type :=
  match fuel with
  | O => ty
  | S f =>
      match tn with
      | TypeName specs syn =>
          match syn with
              | DTBase =>
                  let find_base : c_type :=
                    let fix go (ss : list c_spec) :=
                      match ss with
                      | [] => ty
                      | SpTname nm :: rest =>
                          match lookup_qtype env nm with
                          | Some qt => qt
                          | None => go rest
                          end
                      | SpTypeofExpr e :: rest =>
                          match elaborate_f f e env with
                          | TOk (Some x) => tree_type x
                          | _ => go rest
                          end
                      | SpTypeofType tn1 :: rest =>
                          match type_name_type_f f tn1 env with
                          | TOk (t0, _) => reflect_type_f f tn1 t0 env
                          | _ => go rest
                          end
                      | SpAtomic tn1 :: rest =>
                          match type_name_type_f f tn1 env with
                          | TOk (t0, _) => qualify [QAtomic] (reflect_type_f f tn1 t0 env)
                          | _ => go rest
                          end
                      | SpEnum tag es :: rest =>
                          match enum_key_of tag es with
                          | Some k => TQual [QEnum k] ty
                          | None => go rest
                          end
                      | _ :: rest => go rest
                      end in
                    go specs in
                  let base := atomic_su_base ty find_base in
                  let qs :=
                    fold_right (fun sp acc =>
                      match sp with
                      | SpQual s => match qual_of_string s with Some q => q :: acc | None => acc end
                      | _ => acc
                      end) [] specs in
                  qualify qs base
              | DTPtr inner pqs =>
                  match ty with
                  | TPtr inner_ty =>
                      let rt := reflect_type_f f (TypeName specs inner) inner_ty env in
                      let qs :=
                        fold_right (fun s acc =>
                          match qual_of_string s with Some q => q :: acc | None => acc end) [] pqs in
                      qualify qs (TPtr rt)
                  | _ => ty
                  end
              | DTArray inner _ =>
                  match ty with
                  | TArray elem_ty len =>
                      TArray (reflect_type_f f (TypeName specs inner) elem_ty env) len
                  | _ => ty
                  end
              | DTFunc inner params =>
                  match ty with
                  | TFunc ret_ty ptypes variadic =>
                      let rret := reflect_type_f f (TypeName specs inner) ret_ty env in
                      let rps :=
                        match params, ptypes with
                        | PUnspecified, None => None
                        | PParams ps _, Some pts =>
                            let fix go_ps (a : list c_param) (b : list c_type) (acc : list c_type) :=
                              match a, b with
                              | Param psp (Dcl _ psyn _) :: ra, pt :: rb =>
                                  let r0 := reflect_type_f f (TypeName psp (parameter_syntax psyn)) pt env in
                                  go_ps ra rb (value_type r0 :: acc)
                              | _, _ => rev_append acc []
                              end in
                            Some (go_ps ps pts [])
                        | _, _ => ptypes
                        end in
                      TFunc rret rps variadic
                  | _ => ty
                  end
              end
      end
  end

with request_alignment_f (fuel : nat) (req : align_req) (env : c_type_env)
  {struct fuel} : option Z :=
  match fuel with
  | O => None
  | S f =>
      match req with
      | ARValue a => Some a
      | ARType (TypeName specs syn as tn) =>
          match inherited_alignment specs syn env with
          | Some ia => Some ia
          | None =>
              match type_name_type_f f tn env with
              | TOk (t, env1) =>
                  match type_size_align t env1 with TOk (_, a) => Some a | TErr _ => None end
              | TErr _ => None
              end
          end
      | ARExpr e =>
          match const_eval_f f e env with
          | Some (CVInt a, aty) =>
              if int_type aty && (Z.eqb a 0 || is_pow2 a) then Some a else None
          | _ => None
          end
      | ARAttr ts0 =>
          let ts := attr_unwrap ts0 in
          match ts with
          | [ATok (TId w)] =>
              if String.eqb w "aligned" || String.eqb w "__aligned__" then Some 16 else None
          | [ATok (TId w); AGroup arg_ts] =>
              if String.eqb w "aligned" || String.eqb w "__aligned__" then
                match attribute_expression arg_ts env with
                | None => None
                | Some ae =>
                    match const_eval_f f ae env with
                    | Some (CVInt a, aty) => if int_type aty && is_pow2 a then Some a else None
                    | _ => None
                    end
                end
              else None
          | _ => None
          end
      end
  end

with elaborate_f (fuel : nat) (e : c_expr) (env : c_type_env) {struct fuel}
  : c_tr (option c_typed_node) :=
  match fuel with
  | O => TOk None
  | S f =>
      let operand (e1 : c_expr) : c_tr (option (c_typed_node * c_type)) :=
        match elaborate_f f e1 env with
        | TErr err => TErr err
        | TOk None => TOk None
        | TOk (Some x) => let xv := value_node x in TOk (Some (xv, tree_type xv))
        end in
      let lowered_ty (e1 : c_expr) : c_tr (option c_type) :=
        match operand e1 with
        | TErr err => TErr err
        | TOk None => TOk None
        | TOk (Some (_, t0)) => TOk (Some (unqualified t0))
        end in
      let is_null_ptr (xv : c_typed_node) : bool :=
        let fix check_null (k : nat) (n : c_typed_node) : bool :=
          match k with
          | O => false
          | S k' =>
              let lt := lowered_node_type n in
              if int_type lt then
                match folded_f f n env with
                | TOk (Some (CVInt 0)) => true
                | _ => false
                end
              else
                match n with
                | TNode CatVal (TPtr TVoid) (TFCast _ inner) => check_null k' inner
                | _ => false
                end
          end in
        check_null (Z.to_nat 16) xv in
      let elab_arms (a b : c_expr) : c_tr (option (c_typed_node * c_typed_node * c_type)) :=
        match operand a with
        | TErr err => TErr err
        | TOk None => TOk None
        | TOk (Some (xa, ta)) =>
            match operand b with
            | TErr err => TErr err
            | TOk None => TOk None
            | TOk (Some (xb, tb)) =>
                let na := if is_ptr_type tb then is_null_ptr xa else false in
                let nb := if is_ptr_type ta then is_null_ptr xb else false in
                match arms_type ta na tb nb with
                | Some t => TOk (Some (xa, xb, t))
                | None => TOk None
                end
            end
        end in
      let const_int_of (e1 : c_expr) : option Z :=
        match const_eval_f f e1 env with
        | Some (CVInt v, vt) => if int_type vt then Some v else None
        | _ => None
        end in
      match e with
      | EId name =>
          match lookup_ordinary env name with
          | Some b =>
              let t := identifier_type b name env in
              TOk (binding_node b t name)
          | None =>
              if str_in name ["__func__"; "__FUNCTION__"; "__PRETTY_FUNCTION__"] then
                let len :=
                  if negb (String.eqb name "__PRETTY_FUNCTION__") then
                    match sc_enclosing_fn (te_scope env) with
                    | Some fn => ALConst (Z.of_nat (String.length fn) + 1)
                    | None => ALNone
                    end
                  else ALNone in
                TOk (Some (TNode CatObj (TArray TChar len) (TFPredefined name)))
              else TOk None
          end
      | ENum v0 suf rad =>
          let t0 := num_type v0 suf rad in
          match env_int_type env t0 with
          | Some t =>
              match convert_int v0 t with
              | Some v => TOk (Some (TNode CatVal t (TFInt v)))
              | None => TOk None
              end
          | None => TOk None
          end
      | EChr v =>
          match env_int_type env TInt with
          | Some t => TOk (Some (TNode CatVal t (TFInt v)))
          | None => TOk None
          end
      | EFloat s =>
          let '(t0, _) := float_literal_type_body s in
          match env_int_type env t0 with
          | Some t => TOk (Some (TNode CatVal t (TFFloat s)))
          | None => TOk None
          end
      | EImag s =>
          match elaborate_f f (EFloat s) env with
          | TErr err => TErr err
          | TOk (Some xf) =>
              match complex_of (tree_type xf) with
              | Some ct => TOk (Some (TNode CatVal ct (TFImag xf)))
              | None => TOk None
              end
          | TOk None => TOk None
          end
      | EStr bs =>
          TOk (Some (TNode CatObj (TArray TChar (ALConst (Z.of_nat (List.length bs) + 1))) (TFStr bs)))
      | EWStr wt cs =>
          let et := match wt with WInt => TInt | WUShort => TUShort | WUInt => TUInt end in
          TOk (Some (TNode CatObj (TArray et (ALConst (Z.of_nat (List.length cs) + 1))) (TFWStr wt cs)))
      | ECast tn inner =>
          match type_name_type_f f tn env with
          | TErr err => TErr err
          | TOk (t0, env1) =>
              match operand inner with
              | TErr err => TErr err
              | TOk None => TOk None
              | TOk (Some (xv, f0)) =>
                  let ft := unqualified f0 in
                  match unqualified t0 with
                  | TUnion uid as ut =>
                      if negb (c_type_eqb ft ut) then
                        match union_cast_member ut ft env1 with
                        | Some mname =>
                            elaborate_f f (EComplit tn [InitEntry [DField mname] (InitExpr inner)]) env
                        | None =>
                            if castable ft t0 then
                              TOk (Some (TNode CatVal (reflect_type_f f tn t0 env) (TFCast tn xv)))
                            else TOk None
                        end
                      else if castable ft t0 then
                        TOk (Some (TNode CatVal (reflect_type_f f tn t0 env) (TFCast tn xv)))
                      else TOk None
                  | _ =>
                      if castable ft t0 then
                        TOk (Some (TNode CatVal (reflect_type_f f tn t0 env) (TFCast tn xv)))
                      else TOk None
                  end
              end
          end
      | EComplit tn entries =>
          match type_name_type_f f tn env with
          | TErr err => TErr err
          | TOk (t0, _) =>
              TOk (Some (TNode CatObj (reflect_type_f f tn t0 env) (TFComplit tn entries)))
          end
      | EUn op inner =>
          match op with
          | UAddr =>
              match elaborate_f f inner env with
              | TErr err => TErr err
              | TOk (Some x) =>
                  match x with
                  | TNode CatVal _ _ | TNode CatObj _ (TFBitfield _ _ _) => TOk None
                  | _ => TOk (Some (TNode CatVal (TPtr (tree_type x)) (TFAddr x)))
                  end
              | TOk None => TOk None
              end
          | UDeref =>
              match operand inner with
              | TErr err => TErr err
              | TOk (Some (xv, TPtr t)) => TOk (Some (designator_node t (TFDeref xv)))
              | _ => TOk None
              end
          | UPreInc | UPreDec | UPostInc | UPostDec =>
              match elaborate_f f inner env with
              | TErr err => TErr err
              | TOk (Some x) =>
                  if modifiable x env then
                    let xv := value_node x in
                    let t := tree_type xv in
                    if scalar_type t then TOk (Some (TNode CatVal t (TFIncDec op x)))
                    else TOk None
                  else TOk None
              | TOk None => TOk None
              end
          | UPlus | UNeg | UBnot | UNot =>
              match operand inner with
              | TErr err => TErr err
              | TOk (Some (xv, t1)) =>
                  match unary_operand op t1 with
                  | Some t0 =>
                      match env_int_type env t0 with
                      | Some t => TOk (Some (TNode CatVal t (TFUn op xv)))
                      | None => TOk None
                      end
                  | None => TOk None
                  end
              | TOk None => TOk None
              end
          end
      | EIndex arr idx =>
          match elaborate_f f arr env with
          | TErr err => TErr err
          | TOk (Some xs) =>
              let t0 := tree_type xs in
              match unqualified t0 with
              | TVec el _ _ =>
                  match operand idx with
                  | TErr err => TErr err
                  | TOk (Some (xi, ti)) =>
                      if int_type ti then
                        match xs with
                        | TNode CatObj _ _ =>
                            let lt := match t0 with TQual qs _ => TQual qs el | _ => el end in
                            TOk (Some (TNode CatObj lt (TFVLane xs xi)))
                        | _ => TOk (Some (TNode CatVal el (TFVLane (value_node xs) xi)))
                        end
                      else TOk None
                  | TOk None => TOk None
                  end
              | _ => elaborate_f f (EUn UDeref (EBin BAdd arr idx)) env
              end
          | TOk None => elaborate_f f (EUn UDeref (EBin BAdd arr idx)) env
          end
      | EMember subj field =>
          match elaborate_f f subj env with
          | TErr err => TErr err
          | TOk (Some xs) =>
              let su := tree_type xs in
              match member_type su field env with
              | None => TOk None
              | Some t =>
                  let u := unqualified su in
                  match member_layout u field env with
                  | Some (_, _, MBBits _ w) =>
                      match xs with
                      | TNode CatObj _ _ => TOk (Some (TNode CatObj t (TFBitfield xs field w)))
                      | _ => TOk None
                      end
                  | _ => TOk (member_node xs field t)
                  end
              end
          | TOk None => TOk None
          end
      | EArrow subj field =>
          elaborate_f f (EMember (EUn UDeref subj) field) env
      | ERealPart inner =>
          match elaborate_f f inner env with
          | TErr err => TErr err
          | TOk (Some xs) =>
              let t0 := tree_type xs in
              match complex_type t0 with
              | Some _ =>
                  match member_type t0 "builtin.re" env with
                  | Some t => TOk (member_node xs "builtin.re" t)
                  | None => TOk None
                  end
              | None =>
                  if arithmetic_type (unqualified t0) then TOk (Some xs) else TOk None
              end
          | TOk None => TOk None
          end
      | EImagPart inner =>
          match elaborate_f f inner env with
          | TErr err => TErr err
          | TOk (Some xs) =>
              let t0 := tree_type xs in
              match complex_type t0 with
              | Some _ =>
                  match member_type t0 "builtin.im" env with
                  | Some t => TOk (member_node xs "builtin.im" t)
                  | None => TOk None
                  end
              | None => TOk None
              end
          | TOk None => TOk None
          end
      | EConvertVector a tn =>
          match operand a with
          | TErr err => TErr err
          | TOk (Some (_, TVec _ n _)) =>
              match type_name_type_f f tn env with
              | TErr err => TErr err
              | TOk (t0, _) =>
                  match unqualified t0 with
                  | TVec _ m _ as t =>
                      if Z.eqb n m then TOk (Some (TNode CatVal t (TFConvertVector a tn)))
                      else TOk None
                  | _ => TOk None
                  end
              end
          | _ => TOk None
          end
      | ECall fn args =>
          let regular_call (_ : unit) : c_tr (option c_typed_node) :=
            match operand fn with
            | TErr err => TErr err
            | TOk (Some (xv, TPtr (TFunc ret ps variadic))) =>
                let fix elab_args (xs : list c_expr) (acc : list c_typed_node)
                  : c_tr (option (list c_typed_node)) :=
                  match xs with
                  | [] => TOk (Some (rev_append acc []))
                  | a :: rest =>
                      match operand a with
                      | TErr err => TErr err
                      | TOk None => TOk None
                      | TOk (Some (xa, _)) => elab_args rest (xa :: acc)
                      end
                  end in
                match elab_args args [] with
                | TErr err => TErr err
                | TOk None => TOk None
                | TOk (Some xargs) =>
                    if negb (arity_fits ps variadic (List.length args)) then TOk None
                    else
                      let passes_ok :=
                        match ps with
                        | None => true
                        | Some ptypes =>
                            let fix go_p (a : list c_type) (b : list c_typed_node) : bool :=
                              match a, b with
                              | [], _ => true
                              | p :: rp, x :: rx =>
                                  let t := lowered_node_type x in
                                  let tp := unqualified p in
                                  parameter_accepts tp t (is_null_ptr x) env && go_p rp rx
                              | _, [] => false
                              end in
                            go_p ptypes xargs
                        end in
                      if passes_ok then TOk (Some (TNode CatVal ret (TFCall xv xargs)))
                      else TOk None
                end
            | _ => TOk None
            end in
          match fn with
          | EId name =>
              if String.eqb name "zhas_union" then
                match args with
                | [e1] => TOk (Some (TNode CatVal TVoid (TFBuiltin "zhas_union" [e1])))
                | _ => regular_call tt
                end
              else
                match lookup_ordinary env name with
                | Some _ => regular_call tt
                | None =>
                    if String.eqb name "__builtin_constant_p" then
                      match args with
                      | [e1] =>
                          let is_cp : bool :=
                            match const_eval_f f e1 env with
                            | Some (CVInt _, _) => true
                            | _ =>
                                let fix is_const_ptr (k : nat) (x : c_expr) : bool :=
                                  match k with
                                  | O => false
                                  | S k' =>
                                      match x with
                                      | ECast _ inner =>
                                          is_const_ptr k' inner ||
                                          match const_int_of inner with Some _ => true | None => false end
                                      | _ => match literal_length x with Some _ => true | None => false end
                                      end
                                  end in
                                if is_const_ptr (Z.to_nat 32) e1 then true
                                else
                                  let check_idx (s ix : c_expr) :=
                                    match literal_length s, const_int_of ix with
                                    | Some n, Some k => (0 <=? k) && (k <=? n)
                                    | _, _ => false
                                    end in
                                  match e1 with
                                  | EUn UDeref s => check_idx s (ENum 0 SufNone RadDec)
                                  | EIndex s ix => check_idx s ix
                                  | _ => false
                                  end
                            end in
                          elaborate_f f (ENum (if is_cp then 1 else 0) SufNone RadDec) env
                      | _ => regular_call tt
                      end
                    else
                      match checking_builtin name with
                      | Some (chk, plain) =>
                          match lookup_ordinary env chk with
                          | Some _ => elaborate_f f (ECall (EId chk) args) env
                          | None =>
                              let unchk_ok :=
                                str_in plain ["memcpy"; "memmove"; "mempcpy"; "memset"; "strcpy";
                                              "stpcpy"; "strncpy"; "stpncpy"; "strcat"; "strncat"] in
                              if unchk_ok then
                                let fix split_last_e (xs acc : list c_expr) :=
                                  match xs with
                                  | [] => None
                                  | [last] => Some (rev_append acc [], last)
                                  | x :: rest => split_last_e rest (x :: acc)
                                  end in
                                match split_last_e args [], lookup_ordinary env plain with
                                | Some (args0, sz_e), Some _ =>
                                    match const_int_of sz_e with
                                    | Some v =>
                                        if Z.eqb v 18446744073709551615 then
                                          elaborate_f f (ECall (EId plain) args0) env
                                        else TOk None
                                    | None => TOk None
                                    end
                                | _, _ => TOk None
                                end
                              else TOk None
                          end
                      | None =>
                          let try_var_orders : option c_expr :=
                            match order_positions name (List.length args) with
                            | None => None
                            | Some ps =>
                                let fix find_var (xs : list c_expr) (i : nat)
                                  (evals : list c_expr) (out : list c_expr) :=
                                  match xs with
                                  | [] => (rev_append evals [], rev_append out [])
                                  | a :: rest =>
                                      let in_ps := existsb (Nat.eqb i) ps in
                                      let is_var :=
                                        if in_ps then
                                          match const_int_of a with
                                          | Some _ => false
                                          | None =>
                                              match elaborate_f f a env with
                                              | TOk (Some ax) => int_type (unqualified (value_type (tree_type ax)))
                                              | _ => false
                                              end
                                          end
                                        else false in
                                      if is_var then
                                        find_var rest (S i) (a :: evals) (ENum 5 SufNone RadDec :: out)
                                      else
                                        find_var rest (S i) evals (a :: out)
                                  end in
                                let '(evals, args1) := find_var args 0%nat [] [] in
                                match evals with
                                | [] => None
                                | _ =>
                                    let void_tn := TypeName [SpTspec "void"] DTBase in
                                    Some (fold_left (fun acc o => EComma (ECast void_tn o) acc)
                                                    evals (ECall (EId name) args1))
                                end
                            end in
                          match try_var_orders with
                          | Some e_rew => elaborate_f f e_rew env
                          | None =>
                              let atomic_pointee (p : c_expr) : bool :=
                                match elaborate_f f p env with
                                | TOk (Some px) =>
                                    match value_type (tree_type px) with
                                    | TPtr t => atomic_qualified t
                                    | _ => false
                                    end
                                | _ => false
                                end in
                              let atomic_su_pointee (p : c_expr) : option (c_type * Z) :=
                                match lowered_ty p with
                                | TOk (Some (TPtr t0)) =>
                                    match unqualified t0 with
                                    | TAtomic s sz => Some (s, sz)
                                    | _ => None
                                    end
                                | _ => None
                                end in
                              let order_const (o : c_expr) : option Z :=
                                match const_int_of o with
                                | Some v => if (0 <=? v) && (v <=? 5) then Some v else None
                                | None => None
                                end in
                              let order_in (o : c_expr) (allowed : list Z) : option Z :=
                                match const_int_of o with
                                | Some v => if z_in_list v allowed then Some v else None
                                | None => None
                                end in
                              let cas_ok (p e_exp : c_expr) : bool :=
                                match lowered_ty p, lowered_ty e_exp with
                                | TOk (Some (TPtr t0)), TOk (Some (TPtr u0)) =>
                                    let t := unqualified t0 in
                                    let u := unqualified u0 in
                                    atomic_object_type t &&
                                    (c_type_eqb u t ||
                                     match u with TVoid => true | _ => is_ptr_type t && is_ptr_type u end)
                                | _, _ => false
                                end in
                              let void_tn := TypeName [SpTspec "void"] DTBase in
                              let try_atomic : option (c_tr (option c_typed_node)) :=
                                match generic_atomic name args with
                                | Some e_ga =>
                                    match args with
                                    | p :: _ =>
                                        match lowered_ty p with
                                        | TOk (Some (TPtr t0)) =>
                                            if gnu_operand "xchg" (unqualified t0) then Some (elaborate_f f e_ga env)
                                            else None
                                        | _ => None
                                        end
                                    | [] => None
                                    end
                                | None =>
                                    if String.eqb name "__c11_atomic_load" then
                                      match args with
                                      | [p; o] =>
                                          match atomic_su_pointee p, order_in o [0; 1; 2; 5] with
                                          | Some _, Some _ => Some (elaborate_f f (EComma o (EUn UDeref p)) env)
                                          | _, Some _ =>
                                              if atomic_pointee p then
                                                match lowered_ty p with
                                                | TOk (Some (TPtr t0)) =>
                                                    let t := unqualified t0 in
                                                    if atomic_object_type t then
                                                      if is_ptr_type t then Some (TOk (Some (TNode CatVal t (TFBuiltin name args))))
                                                      else Some (elaborate_f f (EComma o (EUn UDeref p)) env)
                                                    else None
                                                | _ => None
                                                end
                                              else None
                                          | _, None => None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__c11_atomic_store" then
                                      match args with
                                      | [p; v; o] =>
                                          match atomic_su_pointee p, order_in o [0; 3; 5] with
                                          | Some _, Some _ =>
                                              Some (elaborate_f f (ECast void_tn (EComma o (EAssign "=" (EUn UDeref p) v))) env)
                                          | _, Some _ =>
                                              if atomic_pointee p then
                                                match lowered_ty p with
                                                | TOk (Some (TPtr t0)) =>
                                                    if atomic_object_type (unqualified t0) then
                                                      Some (TOk (Some (TNode CatVal TVoid (TFBuiltin name args))))
                                                    else None
                                                | _ => None
                                                end
                                              else None
                                          | _, None => None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__c11_atomic_init" then
                                      match args with
                                      | [p; v] =>
                                          match atomic_su_pointee p with
                                          | Some _ =>
                                              Some (elaborate_f f (ECast void_tn (EAssign "=" (EUn UDeref p) v)) env)
                                          | None =>
                                              if atomic_pointee p then
                                                match lowered_ty p with
                                                | TOk (Some (TPtr t0)) =>
                                                    if atomic_object_type (unqualified t0) then
                                                      Some (TOk (Some (TNode CatVal TVoid (TFBuiltin name args))))
                                                    else None
                                                | _ => None
                                                end
                                              else None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__c11_atomic_exchange" then
                                      match args with
                                      | [p; _; o] =>
                                          match order_const o with
                                          | None => None
                                          | Some _ =>
                                              match atomic_su_pointee p with
                                              | Some (s, _) => Some (TOk (Some (TNode CatVal s (TFBuiltin name args))))
                                              | None =>
                                                  if atomic_pointee p then
                                                    match lowered_ty p with
                                                    | TOk (Some (TPtr t0)) =>
                                                        let t := unqualified t0 in
                                                        if rmw_operand "xchg" t then
                                                          Some (TOk (Some (TNode CatVal t (TFBuiltin name args))))
                                                        else None
                                                    | _ => None
                                                    end
                                                  else None
                                              end
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__c11_atomic_compare_exchange_strong" ||
                                            String.eqb name "__c11_atomic_compare_exchange_weak" then
                                      match args with
                                      | [p; ex; _; os; ofl] =>
                                          match order_const os, order_const ofl with
                                          | Some _, Some _ =>
                                              match atomic_su_pointee p with
                                              | Some (s, psize) =>
                                                  match type_size_align s env, lowered_ty ex with
                                                  | TOk (ssz, _), TOk (Some (TPtr u0)) =>
                                                      if Z.eqb ssz psize && c_type_eqb (unqualified u0) s then
                                                        Some (TOk (Some (TNode CatVal TBool (TFBuiltin name args))))
                                                      else None
                                                  | _, _ => None
                                                  end
                                              | None =>
                                                  if atomic_pointee p && cas_ok p ex then
                                                    Some (TOk (Some (TNode CatVal TBool (TFBuiltin name args))))
                                                  else None
                                              end
                                          | _, _ => None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__atomic_load_n" then
                                      match args with
                                      | [p; o] =>
                                          match order_in o [0; 1; 2; 5], lowered_ty p with
                                          | Some _, TOk (Some (TPtr t0)) =>
                                              let t := unqualified t0 in
                                              if int_type t || is_ptr_type t then
                                                if is_ptr_type t then Some (TOk (Some (TNode CatVal t (TFBuiltin name args))))
                                                else Some (elaborate_f f (EComma o (EUn UDeref p)) env)
                                              else None
                                          | _, _ => None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__atomic_store_n" then
                                      match args with
                                      | [p; v; o] =>
                                          match order_in o [0; 3; 5], lowered_ty p with
                                          | Some ov, TOk (Some (TPtr t0)) =>
                                              let t := unqualified t0 in
                                              if int_type t || is_ptr_type t then
                                                if is_ptr_type t || Z.eqb ov 5 || atomic_pointee p then
                                                  Some (TOk (Some (TNode CatVal TVoid (TFBuiltin name args))))
                                                else
                                                  Some (elaborate_f f (ECast void_tn (EComma o (EAssign "=" (EUn UDeref p) v))) env)
                                              else None
                                          | _, _ => None
                                          end
                                      | _ => None
                                      end
                                    else if fence_builtin name then
                                      match args with
                                      | [o] =>
                                          match order_const o with
                                          | Some _ => Some (TOk (Some (TNode CatVal TVoid (TFBuiltin name args))))
                                          | None => None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__atomic_compare_exchange_n" then
                                      match args with
                                      | [p; ex; _; w; os; ofl] =>
                                          match lowered_ty p, order_const os, order_const ofl, const_int_of w with
                                          | TOk (Some (TPtr t0)), Some _, Some _, Some _ =>
                                              if gnu_operand "xchg" (unqualified t0) && cas_ok p ex then
                                                Some (TOk (Some (TNode CatVal TBool (TFBuiltin name args))))
                                              else None
                                          | _, _, _, _ => None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__sync_val_compare_and_swap" ||
                                            String.eqb name "__sync_bool_compare_and_swap" then
                                      match args with
                                      | p :: _ :: _ :: _ =>
                                          match lowered_ty p with
                                          | TOk (Some (TPtr t0)) =>
                                              let t := unqualified t0 in
                                              if gnu_operand "xchg" t then
                                                let rt := if String.eqb name "__sync_val_compare_and_swap" then t else TBool in
                                                Some (TOk (Some (TNode CatVal rt (TFBuiltin name args))))
                                              else None
                                          | _ => None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__sync_lock_release" then
                                      match args with
                                      | p :: _ =>
                                          match lowered_ty p with
                                          | TOk (Some (TPtr t0)) =>
                                              if gnu_operand "xchg" (unqualified t0) then
                                                Some (TOk (Some (TNode CatVal TVoid (TFBuiltin name args))))
                                              else None
                                          | _ => None
                                          end
                                      | _ => None
                                      end
                                    else if String.eqb name "__sync_synchronize" then
                                      match args with
                                      | [] => Some (TOk (Some (TNode CatVal TVoid (TFBuiltin name args))))
                                      | _ => None
                                      end
                                    else if String.eqb name "__atomic_test_and_set" ||
                                            String.eqb name "__atomic_clear" then
                                      match args with
                                      | [p; o] =>
                                          match lowered_ty p, order_const o with
                                          | TOk (Some (TPtr t)), Some _ =>
                                              if negb (is_func_type t) then
                                                let rt := if String.eqb name "__atomic_test_and_set" then TBool else TVoid in
                                                Some (TOk (Some (TNode CatVal rt (TFBuiltin name args))))
                                              else None
                                          | _, _ => None
                                          end
                                      | _ => None
                                      end
                                    else
                                      match rmw_builtin name with
                                      | Some (fam, op, _) =>
                                          if String.eqb fam "c11" then
                                            match args with
                                            | [p; _; o] =>
                                                match order_const o, lowered_ty p with
                                                | Some _, TOk (Some (TPtr t0)) =>
                                                    let t := unqualified t0 in
                                                    if atomic_pointee p && rmw_operand op t then
                                                      Some (TOk (Some (TNode CatVal t (TFBuiltin name args))))
                                                    else None
                                                | _, _ => None
                                                end
                                            | _ => None
                                            end
                                          else if String.eqb fam "gnu" then
                                            match args with
                                            | [p; _; o] =>
                                                match order_const o, lowered_ty p with
                                                | Some _, TOk (Some (TPtr t0)) =>
                                                    let t := unqualified t0 in
                                                    if gnu_operand op t then
                                                      Some (TOk (Some (TNode CatVal t (TFBuiltin name args))))
                                                    else None
                                                | _, _ => None
                                                end
                                            | _ => None
                                            end
                                          else
                                            match args with
                                            | p :: _ :: _ =>
                                                match lowered_ty p with
                                                | TOk (Some (TPtr t0)) =>
                                                    let t := unqualified t0 in
                                                    if gnu_operand op t then
                                                      Some (TOk (Some (TNode CatVal t (TFBuiltin name args))))
                                                    else None
                                                | _ => None
                                                end
                                            | _ => None
                                            end
                                      | None => None
                                      end
                                end in
                              match try_atomic with
                              | Some res => res
                              | None =>
                                  let try_nan :=
                                    match args, nan_builtin name with
                                    | [EStr []], Some (t, _) => Some (TOk (Some (TNode CatVal t (TFBuiltin name []))))
                                    | _, _ => None
                                    end in
                                  match try_nan with
                                  | Some res => res
                                  | None =>
                                      if generic_vector_builtin name then
                                        if String.eqb name "__builtin_shufflevector" then
                                          match args with
                                          | a :: b :: is_args =>
                                              match operand a, operand b with
                                              | TOk (Some (_, TVec el1 n1 _)), TOk (Some (_, TVec el2 n2 _)) =>
                                                  if c_type_eqb el1 el2 && Z.eqb n1 n2 then
                                                    match type_size_align el1 env with
                                                    | TOk (esz, _) =>
                                                        let k := Z.of_nat (List.length is_args) in
                                                        TOk (Some (TNode CatVal (TVec el1 k (esz * k)) (TFBuiltin name args)))
                                                    | TErr _ => TOk None
                                                    end
                                                  else TOk None
                                              | _, _ => TOk None
                                              end
                                          | _ => TOk None
                                          end
                                        else
                                          match args with
                                          | a :: bs =>
                                              match operand a with
                                              | TOk (Some (_, TVec el n _ as vt)) =>
                                                  let fix all_match (xs : list c_expr) : bool :=
                                                    match xs with
                                                    | [] => true
                                                    | x :: rest =>
                                                        match operand x with
                                                        | TOk (Some (_, TVec e2 n2 _)) =>
                                                            c_type_eqb el e2 && Z.eqb n n2 && all_match rest
                                                        | _ => false
                                                        end
                                                    end in
                                                  if all_match bs then TOk (Some (TNode CatVal vt (TFBuiltin name args)))
                                                  else TOk None
                                              | _ => TOk None
                                              end
                                          | [] => TOk None
                                          end
                                      else
                                        let try_fb :=
                                          match args, float_builtin name, nan_builtin name with
                                          | [], Some (t, _), None => Some t
                                          | _, _, _ => builtin_type name
                                          end in
                                        match try_fb with
                                        | Some t => TOk (Some (TNode CatVal t (TFBuiltin name args)))
                                        | None =>
                                            if str_in name ["__atomic_always_lock_free";
                                                            "__c11_atomic_is_lock_free";
                                                            "__atomic_is_lock_free"] then
                                              match args with
                                              | [sz_e; p_e] =>
                                                  match const_int_of sz_e, operand p_e with
                                                  | Some sz, TOk (Some (xp, pt0)) =>
                                                      let pt := unqualified pt0 in
                                                      let lf_ok :=
                                                        is_pow2 sz && (sz <=? 16) &&
                                                        (Z.eqb sz 1 ||
                                                         String.eqb name "__c11_atomic_is_lock_free" ||
                                                         is_null_ptr xp ||
                                                         match pt with
                                                         | TPtr TVoid => false
                                                         | TPtr t =>
                                                             match type_size_align t env with
                                                             | TOk (_, a) => sz <=? a
                                                             | TErr _ => false
                                                             end
                                                         | _ => false
                                                         end) in
                                                      if lf_ok then elaborate_f f (ENum 1 SufNone RadDec) env
                                                      else if String.eqb name "__atomic_always_lock_free" then
                                                        elaborate_f f (ENum 0 SufNone RadDec) env
                                                      else TOk None
                                                  | _, _ => TOk None
                                                  end
                                              | _ => TOk None
                                              end
                                            else if String.eqb name "__builtin_classify_type" then
                                              match args with
                                              | [e1] =>
                                                  match elaborate_f f e1 env with
                                                  | TErr err => TErr err
                                                  | TOk (Some x) =>
                                                      match type_class_number (unqualified (tree_type x)) with
                                                      | Some v => elaborate_f f (ENum v SufNone RadDec) env
                                                      | None => TOk None
                                                      end
                                                  | TOk None => TOk None
                                                  end
                                              | _ => TOk None
                                              end
                                            else if String.eqb name "__builtin_choose_expr" then
                                              match args with
                                              | [c; a; b] =>
                                                  match const_int_of c with
                                                  | Some v =>
                                                      if negb (Z.eqb v 0) then elaborate_f f a env
                                                      else elaborate_f f b env
                                                  | None =>
                                                      TErr (TESema "__builtin_choose_expr needs a constant condition")
                                                  end
                                              | _ => TOk None
                                              end
                                            else
                                              match hint_builtin name args with
                                              | Some he =>
                                                  elaborate_f f (ECast (TypeName [SpTspec "void"] DTBase) he) env
                                              | None => regular_call tt
                                              end
                                        end
                                  end
                              end
                          end
                      end
                end
          | _ => regular_call tt
          end
      | EAssign op lhs rhs =>
          match elaborate_f f lhs env with
          | TErr err => TErr err
          | TOk None => TOk None
          | TOk (Some x) =>
              if negb (modifiable x env) then TOk None
              else
                let t := assignment_type x in
                match operand rhs with
                | TErr err => TErr err
                | TOk None => TOk None
                | TOk (Some (xb, _)) =>
                    let ta := unqualified t in
                    let tb := lowered_node_type xb in
                    let ok :=
                      if String.eqb op "=" then assignable tb (is_null_ptr xb) ta (Some env)
                      else
                        match compound_assign_binop op with
                        | Some bop =>
                            (scalar_type ta || is_vec_type ta ||
                             match complex_type ta with Some _ => true | None => false end) &&
                            match binary_operands bop ta tb with
                            | Some (_, _, tr) => assignable tr false ta None
                            | None => false
                            end
                        | None => false
                        end in
                    if ok then TOk (Some (TNode CatVal t (TFAssign op x xb)))
                    else TOk None
                end
          end
      | EComma a b =>
          match operand a with
          | TErr err => TErr err
          | TOk None => TOk None
          | TOk (Some (xa, _)) =>
              match operand b with
              | TErr err => TErr err
              | TOk None => TOk None
              | TOk (Some (xv, t)) => TOk (Some (TNode CatVal t (TFComma xa xv)))
              end
          end
      | ESizeofExpr inner =>
          match elaborate_f f inner env with
          | TErr err => TErr err
          | TOk (Some x) =>
              match x with
              | TNode CatObj _ (TFBitfield _ _ _) => TOk None
              | _ => TOk (Some (TNode CatVal TULong (TFSizeofExpr x)))
              end
          | TOk None => TOk None
          end
      | ESizeofType tn => TOk (Some (TNode CatVal TULong (TFSizeofType tn)))
      | EAlignofType tn => TOk (Some (TNode CatVal TULong (TFAlignofType tn)))
      | EAlignofExpr inner =>
          match elaborate_f f inner env with
          | TErr err => TErr err
          | TOk (Some x) => TOk (Some (TNode CatVal TULong (TFAlignofExpr x)))
          | TOk None => TOk None
          end
      | EOffsetof tn path => TOk (Some (TNode CatVal TULong (TFOffsetof tn path)))
      | ELabelAddr name =>
          match lookup_label_addr env name with
          | Some n =>
              elaborate_f f (ECast (TypeName [SpTspec "void"] (DTPtr DTBase [])) (ENum n SufNone RadDec)) env
          | None => TOk None
          end
      | EBin op a b =>
          match operand a with
          | TErr err => TErr err
          | TOk None => TOk None
          | TOk (Some (xa, ta)) =>
              match operand b with
              | TErr err => TErr err
              | TOk None => TOk None
              | TOk (Some (xb, tb)) =>
                  match expression_binary_type op ta tb with
                  | Some t0 =>
                      match env_int_type env t0 with
                      | Some t => TOk (Some (TNode CatVal t (TFBin op xa xb)))
                      | None => TOk None
                      end
                  | None => TOk None
                  end
              end
          end
      | ECond c a b =>
          match operand c with
          | TErr err => TErr err
          | TOk (Some (xc, tc)) =>
              if scalar_type tc then
                match elab_arms a b with
                | TErr err => TErr err
                | TOk (Some (xa, xb, t)) => TOk (Some (TNode CatVal t (TFCond xc xa xb)))
                | TOk None => TOk None
                end
              else TOk None
          | TOk None => TOk None
          end
      | EGCond c b =>
          match elab_arms c b with
          | TErr err => TErr err
          | TOk (Some (xc, xb, t)) =>
              if scalar_type (tree_type xc) then TOk (Some (TNode CatVal t (TFGCond xc xb)))
              else TOk None
          | TOk None => TOk None
          end
      | EVaArg a tn =>
          match operand a with
          | TErr err => TErr err
          | TOk (Some (xa, _)) =>
              match type_name_type_f f tn env with
              | TErr err => TErr err
              | TOk (t0, _) =>
                  TOk (Some (TNode CatVal (reflect_type_f f tn t0 env) (TFVaArg tn xa)))
              end
          | TOk None => TOk None
          end
      | EBitCast tn inner =>
          match operand inner with
          | TErr err => TErr err
          | TOk (Some (xa, ta)) =>
              match type_name_type_f f tn env with
              | TErr err => TErr err
              | TOk (t0, _) =>
                  let t := unqualified t0 in
                  if bit_castable ta t env then TOk (Some (TNode CatVal t (TFBitCast xa)))
                  else TOk None
              end
          | TOk None => TOk None
          end
      | EStmtExpr (Stmt _ (SBlock items) as body) =>
          let fix block_ty (xs : list c_block_item) (e : c_type_env) : c_tr (option c_type) :=
            match xs with
            | [] => TOk (Some TVoid)
            | [last] =>
                let fix last_stmt (s : c_stmt) : c_tr (option c_type) :=
                  match s with
                  | Stmt _ (SExpr expr) =>
                      match elaborate_f f expr e with
                      | TErr err => TErr err
                      | TOk (Some x) => TOk (Some (tree_type (value_node x)))
                      | TOk None => TOk None
                      end
                  | Stmt _ (SLabel _ b1) => last_stmt b1
                  | _ => TOk (Some TVoid)
                  end in
                match last with
                | BIStmt s => last_stmt s
                | BIDecl _ => TOk (Some TVoid)
                end
            | BIDecl (IDecl _ dsp dinits) :: rest =>
                match decl_types_f f dsp dinits e with
                | TErr err => TErr err
                | TOk (ds, e1) =>
                    let e2 := fold_left (fun acc d => bind_ordinary (cd_name d) (BVar VSNone (cd_type d)) acc) ds e1 in
                    block_ty rest e2
                end
            | _ :: rest => block_ty rest e
            end in
          match block_ty items env with
          | TErr err => TErr err
          | TOk (Some t) => TOk (Some (TNode CatVal t (TFStmtExpr body)))
          | TOk None => TOk None
          end
      | EStmtExpr _ => TOk None
      | ETypesCompatible ta tb =>
          let comp_tn (tn : c_type_name) : c_tr c_type :=
            match type_name_type_f f tn env with
            | TErr err => TErr err
            | TOk (t0, _) =>
                let r := reflect_type_f f tn t0 env in
                let t :=
                  match r with
                  | TQual qs r1 =>
                      let es := filter (fun q => match q with QEnum _ => true | _ => false end) qs in
                      qualify es r1
                  | _ => r
                  end in
                TOk t
            end in
          match comp_tn ta, comp_tn tb with
          | TOk a, TOk b =>
              elaborate_f f (ENum (if compatible_type a b None then 1 else 0) SufNone RadDec) env
          | TErr err, _ | _, TErr err => TErr err
          end
      | EGeneric ctrl assocs =>
          match operand ctrl with
          | TErr err => TErr err
          | TOk None => TOk None
          | TOk (Some (_, ct0)) =>
              let ct :=
                match elaborate_f f ctrl env with
                | TOk (Some cx) =>
                    match enum_marked (tree_type cx) with
                    | Some (k, _) => TQual [QEnum k] ct0
                    | None => ct0
                    end
                | _ => ct0
                end in
              match generic_selection_f f ct assocs env (Loc "constant" 0) with
              | TErr err => TErr err
              | TOk sel => elaborate_f f sel env
              end
          end
      end
  end

with folded_f (fuel : nat) (xv : c_typed_node) (env : c_type_env) {struct fuel}
  : c_tr (option c_const_val) :=
  match fuel with
  | O => TOk None
  | S f =>
      match xv with
      | TNode CatVal t0 form =>
          match form with
          | TFInt v => TOk (Some (CVInt v))
          | TFFloat s =>
              match float_literal s with
              | Some (v, ft) => if c_type_eqb ft t0 then TOk (Some (CVInt v)) else TOk None
              | None => TOk None
              end
          | TFBuiltin name args =>
              match args with
              | [] =>
                  match float_builtin name with Some (_, v) => TOk (Some (CVInt v)) | None => TOk None end
              | [a] =>
                  match bit_builtin name with
                  | Some (op, bty) =>
                      match const_eval_f f a env with
                      | Some (CVInt v0, vt) =>
                          if int_type vt then
                            match int_info bty with
                            | Some (bytes, _) =>
                                let bits := 8 * bytes in
                                let x := Z.modulo v0 (Z.shiftl 1 bits) in
                                match bit_count_value op bits x with
                                | Some res => TOk (Some (CVInt res))
                                | None => TOk None
                                end
                            | None => TOk None
                            end
                          else TOk None
                      | _ => TOk None
                      end
                  | None => TOk None
                  end
              | [_; ty_e] =>
                  if String.eqb name "__builtin_object_size" ||
                     String.eqb name "__builtin_dynamic_object_size" then
                    match const_eval_f f ty_e env with
                    | Some (CVInt k, kt) =>
                        if int_type kt then
                          if Z.eqb k 0 || Z.eqb k 1 then TOk (Some (CVInt 18446744073709551615))
                          else if Z.eqb k 2 || Z.eqb k 3 then TOk (Some (CVInt 0))
                          else TOk None
                        else TOk None
                    | _ => TOk None
                    end
                  else TOk None
              | _ => TOk None
              end
          | TFUn UNot inner =>
              match folded_f f inner env with
              | TErr err => TErr err
              | TOk (Some v0) =>
                  match const_truth v0 (lowered_node_type inner) with
                  | CVUb => TOk (Some CVUb)
                  | CVInt b => TOk (Some (CVInt (if Z.eqb b 0 then 1 else 0)))
                  end
              | TOk None => TOk None
              end
          | TFUn op inner =>
              match folded_f f inner env with
              | TErr err => TErr err
              | TOk (Some CVUb) => TOk (Some CVUb)
              | TOk (Some (CVInt v0)) => TOk (constant_unary_op (unqualified t0) op v0)
              | TOk None => TOk None
              end
          | TFBin BSub xa xb =>
              let la := lowered_node_type xa in
              let lb := lowered_node_type xb in
              match la, lb with
              | TPtr e0, TPtr _ =>
                  match constant_address_f f xa env, constant_address_f f xb env with
                  | Some a, Some b =>
                      let e := unqualified e0 in
                      let osz :=
                        match e with
                        | TVoid => Some 1
                        | _ => match type_size_align e env with TOk (sz, _) => Some sz | TErr _ => None end
                        end in
                      match osz with
                      | Some sz =>
                          if 0 <? sz then
                            match convert_int (Z.quot (a - b) sz) (unqualified t0) with
                            | Some v => TOk (Some (CVInt v))
                            | None => TOk None
                            end
                          else TOk None
                      | None => TOk None
                      end
                  | _, _ => TOk None
                  end
              | _, _ =>
                  match folded_f f xa env with
                  | TErr err => TErr err
                  | TOk None => TOk None
                  | TOk (Some va) =>
                      match folded_f f xb env with
                      | TErr err => TErr err
                      | TOk None => TOk None
                      | TOk (Some vb) =>
                          TOk (kind_binary_const BSub va la vb lb (unqualified t0))
                      end
                  end
              end
          | TFBin op xa xb =>
              match folded_f f xa env with
              | TErr err => TErr err
              | TOk None => TOk None
              | TOk (Some va) =>
                  match folded_f f xb env with
                  | TErr err => TErr err
                  | TOk None => TOk None
                  | TOk (Some vb) =>
                      TOk (kind_binary_const op va (lowered_node_type xa) vb (lowered_node_type xb) (unqualified t0))
                  end
              end
          | TFCond xc xa xb =>
              match folded_f f xc env with
              | TErr err => TErr err
              | TOk None => TOk None
              | TOk (Some vc) =>
                  match folded_f f xa env with
                  | TErr err => TErr err
                  | TOk None => TOk None
                  | TOk (Some va) =>
                      match folded_f f xb env with
                      | TErr err => TErr err
                      | TOk None => TOk None
                      | TOk (Some vb) =>
                          match const_truth vc (lowered_node_type xc) with
                          | CVUb => TOk (Some CVUb)
                          | CVInt test =>
                              let t := unqualified t0 in
                              if negb (Z.eqb test 0) then TOk (const_convert va (lowered_node_type xa) t)
                              else TOk (const_convert vb (lowered_node_type xb) t)
                          end
                      end
                  end
              end
          | TFCast _ inner =>
              let t := unqualified t0 in
              let try_arith : c_tr (option c_const_val) :=
                if arithmetic_type t then
                  match folded_f f inner env with
                  | TErr err => TErr err
                  | TOk (Some v0) => TOk (const_convert v0 (lowered_node_type inner) t)
                  | TOk None => TOk None
                  end
                else TOk None in
              match try_arith with
              | TErr err => TErr err
              | TOk (Some v) => TOk (Some v)
              | TOk None =>
                  if int_type t then
                    match constant_address_f f inner env with
                    | Some a => TOk (const_convert (CVInt a) TULong t)
                    | None => TOk None
                    end
                  else TOk None
              end
          | TFSizeofType tn =>
              match type_name_type_f f tn env with
              | TErr (TESema msg) => TErr (TESema msg)
              | TErr _ => TOk None
              | TOk (t, env1) =>
                  match sizeof_size t env1 with TOk v => TOk (Some (CVInt v)) | TErr _ => TOk None end
              end
          | TFSizeofExpr x =>
              match sizeof_size (tree_type x) env with TOk v => TOk (Some (CVInt v)) | TErr _ => TOk None end
          | TFAlignofType (TypeName specs syn as tn) =>
              match type_name_type_f f tn env with
              | TErr (TESema msg) => TErr (TESema msg)
              | TErr _ => TOk None
              | TOk (t, env1) =>
                  match type_size_align t env1 with
                  | TOk (_, v0) =>
                      match inherited_alignment specs syn env with
                      | Some a => TOk (Some (CVInt a))
                      | None => TOk (Some (CVInt v0))
                      end
                  | TErr _ => TOk None
                  end
              end
          | TFAlignofExpr x =>
              match expr_alignment x env with TOk v => TOk (Some (CVInt v)) | TErr _ => TOk None end
          | TFOffsetof tn path =>
              match type_name_type_f f tn env with
              | TErr (TESema msg) => TErr (TESema msg)
              | TErr _ => TOk None
              | TOk (t, env1) =>
                  let fix walk (ds : list c_designator) (cur_t : c_type) (off : Z) : option Z :=
                    match ds with
                    | [] => Some off
                    | DField fld :: rest =>
                        match member_type_offset cur_t fld env1 with
                        | Some (ft, foff) => walk rest ft (off + foff)
                        | None => None
                        end
                    | DIndex ix :: rest =>
                        match cur_t with
                        | TArray elem _ =>
                            match const_eval_f f ix env1 with
                            | Some (CVInt i, _) =>
                                match type_size_align elem env1 with
                                | TOk (esz, _) => walk rest elem (off + i * esz)
                                | TErr _ => None
                                end
                            | _ => None
                            end
                        | _ => None
                        end
                    | DRange _ _ :: _ => None
                    end in
                  match walk path t 0 with Some v => TOk (Some (CVInt v)) | None => TOk None end
              end
          | TFComma xa xv1 =>
              match folded_f f xa env with
              | TErr err => TErr err
              | TOk (Some _) => folded_f f xv1 env
              | TOk None => TOk None
              end
          | TFLoad (TNode CatObj (TQual qs _) (TFId nm)) =>
              if has_qual QConst qs then
                match lookup_cval env nm with
                | Some (Some v) => TOk (Some (CVInt v))
                | _ => TOk None
                end
              else TOk None
          | _ => TOk None
          end
      | _ => TOk None
      end
  end

with const_eval_f (fuel : nat) (e : c_expr) (env : c_type_env) {struct fuel}
  : option (c_const_val * c_type) :=
  match fuel with
  | O => None
  | S f =>
      match elaborate_f f e env with
      | TOk (Some x) =>
          let xv := value_node x in
          match folded_f f xv env with
          | TOk (Some v) => Some (v, lowered_node_type xv)
          | _ => None
          end
      | _ => None
      end
  end

with constant_address_f (fuel : nat) (xp : c_typed_node) (env : c_type_env)
  {struct fuel} : option Z :=
  match fuel with
  | O => None
  | S f =>
      match xp with
      | TNode CatVal (TPtr pt) form =>
          match form with
          | TFCast _ inner =>
              match inner with
              | TNode CatVal (TPtr _) _ => constant_address_f f inner env
              | _ =>
                  let lt := lowered_node_type inner in
                  if int_type lt then
                    match folded_f f inner env with
                    | TOk (Some (CVInt a)) => Some a
                    | _ => None
                    end
                  else None
              end
          | TFBin op xa xb =>
              let sgn := match op with BAdd => Some 1 | BSub => Some (-1) | _ => None end in
              match sgn with
              | None => None
              | Some s =>
                  let pair :=
                    match constant_address_f f xa env with
                    | Some a0 => Some (a0, xb)
                    | None =>
                        match op with
                        | BAdd =>
                            match constant_address_f f xb env with
                            | Some a0 => Some (a0, xa)
                            | None => None
                            end
                        | _ => None
                        end
                    end in
                  match pair with
                  | Some (a0, xi) =>
                      if int_type (lowered_node_type xi) then
                        match folded_f f xi env with
                        | TOk (Some (CVInt i)) =>
                            let t1 := unqualified pt in
                            let osz :=
                              match t1 with
                              | TVoid => Some 1
                              | _ => match type_size_align t1 env with TOk (sz, _) => Some sz | TErr _ => None end
                              end in
                            match osz with
                            | Some sz => Some (a0 + s * i * sz)
                            | None => None
                            end
                        | _ => None
                        end
                      else None
                  | None => None
                  end
              end
          | TFAddr l | TFDecay l => lvalue_address_f f l env
          | _ => None
          end
      | _ => None
      end
  end

with lvalue_address_f (fuel : nat) (l : c_typed_node) (env : c_type_env)
  {struct fuel} : option Z :=
  match fuel with
  | O => None
  | S f =>
      match l with
      | TNode CatObj _ (TFDeref xp) => constant_address_f f xp env
      | TNode CatObj _ (TFMember (TNode CatObj su0 _ as base) fld) =>
          match lvalue_address_f f base env with
          | Some a0 =>
              match member_type_offset (unqualified su0) fld env with
              | Some (_, off) => Some (a0 + off)
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  end

with generic_selection_f (fuel : nat) (ctrl_ty : c_type)
  (assocs : list c_generic_assoc) (env : c_type_env) (loc : c_loc)
  {struct fuel} : c_tr c_expr :=
  match fuel with
  | O => sema_err loc "_Generic fuel exhausted"
  | S f =>
      let fix type_assocs (xs : list c_generic_assoc)
        (acc : list (option c_type * c_expr)) : c_tr (list (option c_type * c_expr)) :=
        match xs with
        | [] => TOk (rev_append acc [])
        | GAssocDefault e :: rest => type_assocs rest ((None, e) :: acc)
        | GAssocType tn e :: rest =>
            match type_name_type_f f tn env with
            | TErr err => TErr err
            | TOk (t0, _) =>
                if complete_type t0 env && negb (is_func_type t0) then
                  let rt := reflect_type_f f tn t0 env in
                  type_assocs rest ((Some rt, e) :: acc)
                else
                  sema_err loc "_Generic association requires a complete object type"
            end
        end in
      match type_assocs assocs [] with
      | TErr err => TErr err
      | TOk typed =>
          let fix check_unique (xs : list (option c_type * c_expr)) : c_tr unit :=
            match xs with
            | [] => TOk tt
            | (ot, _) :: rest =>
                let dup :=
                  existsb (fun '(ou, _) =>
                    match ot, ou with
                    | None, None => true
                    | Some t, Some u => compatible_type t u None
                    | _, _ => false
                    end) rest in
                if dup then sema_err loc "_Generic has duplicate compatible associations"
                else check_unique rest
            end in
          match check_unique typed with
          | TErr err => TErr err
          | TOk _ =>
              let fix find_match (xs : list (option c_type * c_expr)) : option c_expr :=
                match xs with
                | [] => None
                | (Some t, e) :: rest =>
                    if compatible_type ctrl_ty t None then Some e else find_match rest
                | (None, _) :: rest => find_match rest
                end in
              match find_match typed with
              | Some e => TOk e
              | None =>
                  let fix find_def (xs : list (option c_type * c_expr)) : option c_expr :=
                    match xs with
                    | [] => None
                    | (None, e) :: _ => Some e
                    | (Some _, _) :: rest => find_def rest
                    end in
                  match find_def typed with
                  | Some e => TOk e
                  | None => sema_err loc "_Generic has no matching association"
                  end
              end
          end
      end
  end.

(** ## Public entry points and K&R / reflection wrappers *)

Definition type_fuel : nat := Z.to_nat 10000.

Definition decl_types (specs : list c_spec) (inits : list c_init_decl)
  (env : c_type_env) : c_tr (list c_decl * c_type_env) :=
  decl_types_f type_fuel specs inits env.

Definition specs_type (specs : list c_spec) (env : c_type_env)
  : c_tr (c_type * c_type_env) :=
  specs_type_f type_fuel specs env.

Definition apply_declarator (syn : c_dcl_type) (base : c_type)
  (env : c_type_env) : c_tr (c_type * c_type_env) :=
  apply_declarator_f type_fuel syn base env.

Definition type_name_type (tn : c_type_name) (env : c_type_env)
  : c_tr (c_type * c_type_env) :=
  type_name_type_f type_fuel tn env.

Definition reflect_type (tn : c_type_name) (ty : c_type)
  (env : c_type_env) : c_type :=
  reflect_type_f type_fuel tn ty env.

Definition elaborate (e : c_expr) (env : c_type_env)
  : c_tr (option c_typed_node) :=
  elaborate_f type_fuel e env.

Definition folded (xv : c_typed_node) (env : c_type_env) : c_tr (option c_const_val) :=
  folded_f type_fuel xv env.

Definition const_eval (e : c_expr) (env : c_type_env)
  : option (c_const_val * c_type) :=
  const_eval_f type_fuel e env.

Definition constant_value (e : c_expr) (env : c_type_env) : c_tr (Z * c_type) :=
  match const_eval e env with
  | Some (CVInt v, t) => TOk (v, t)
  | _ => TErr TENotConstant
  end.

Definition const_value (e : c_expr) (env : c_type_env) : c_tr (Z * c_type) :=
  match constant_value e env with
  | TOk (v, t) => if int_type t then TOk (v, t) else TErr TENotConstant
  | TErr err => TErr err
  end.

Definition constant_address (xp : c_typed_node) (env : c_type_env) : option Z :=
  constant_address_f type_fuel xp env.

Definition generic_selection (ctrl : c_type) (assocs : list c_generic_assoc)
  (env : c_type_env) (loc : c_loc) : c_tr c_expr :=
  generic_selection_f type_fuel ctrl assocs env loc.

Definition null_pointer_constant (xv : c_typed_node) (env : c_type_env) : bool :=
  let fix go (k : nat) (n : c_typed_node) : bool :=
    match k with
    | O => false
    | S k' =>
        if int_type (lowered_node_type n) then
          match folded n env with TOk (Some (CVInt 0)) => true | _ => false end
        else
          match n with
          | TNode CatVal (TPtr TVoid) (TFCast _ inner) => go k' inner
          | _ => false
          end
    end in
  go (Z.to_nat 16) xv.

Definition transparent_argument (param0 : c_type) (xv : c_typed_node)
  (env : c_type_env) : option c_type :=
  let param := unqualified param0 in
  let t := lowered_node_type xv in
  if c_type_eqb t param then None
  else transparent_member param t (null_pointer_constant xv env) env.

Definition assigned (e : c_expr) (env : c_type_env) (to_t : c_type) (loc : c_loc)
  : c_tr unit :=
  match elaborate e env with
  | TErr err => TErr err
  | TOk None => TErr (TESema (loc_to_string loc ++ ": expression cannot be typed"))
  | TOk (Some x) =>
      let xv := value_node x in
      let t := lowered_node_type xv in
      let n := null_pointer_constant xv env in
      if assignable t n to_t (Some env) then TOk tt
      else sema_err loc ("cannot assign " ++ c_type_diag_str t ++ " to " ++ c_type_diag_str to_t)
  end.

Definition expression_tags (e : c_expr) (env0 : c_type_env) : c_type_env :=
  match defining_type_names e with
  | [] => env0
  | tns =>
      let env1 := with_expr_tags_mode env0 true in
      let env2 :=
        fold_left (fun acc tn =>
          match type_name_type tn acc with TOk (_, e1) => e1 | TErr _ => acc end)
          tns env1 in
      with_expr_tags_mode env2 false
  end.

Definition reflect_params (dcl : c_dcl_type) (ts : list c_type)
  (env0 : c_type_env) : c_type_env :=
  match dcl with
  | DTFunc _ (PParams ps _) =>
      let fix go (a : list c_param) (b : list c_type) (e : c_type_env) :=
        match a, b with
        | Param psp (Dcl (Some nm) psyn _) :: ra, pt :: rb =>
            let r0 := reflect_type (TypeName psp (parameter_syntax psyn)) pt e in
            go ra rb (bind_qtype nm (value_type r0) e)
        | _ :: ra, _ :: rb => go ra rb e
        | _, _ => e
        end in
      go ps ts env0
  | _ => env0
  end.

Definition knr_definition (loc : c_loc) (names : list string)
  (decls : list c_item) (prototyped : bool) (env : c_type_env)
  : c_tr (c_params * list c_item) :=
  let declared :=
    fold_right (fun item acc =>
      match item with
      | IDecl dloc dsp inits =>
          fold_right (fun ini a0 =>
            match ini with
            | InitDecl (Dcl (Some nm) syn _) oinit => (nm, (dloc, dsp, syn, oinit)) :: a0
            | _ => a0
            end) acc inits
      | _ => acc
      end) [] decls in
  let fix check_decls (xs : list (string * (c_loc * list c_spec * c_dcl_type * option c_init)))
    : c_tr unit :=
    match xs with
    | [] => TOk tt
    | (nm, (_, _, _, oinit)) :: rest =>
        if negb (str_in nm names) then
          sema_err loc ("parameter named '" ++ nm ++ "' is missing")
        else match oinit with
        | Some _ => sema_err loc "C does not support default arguments"
        | None => check_decls rest
        end
    end in
  match check_decls declared with
  | TErr err => TErr err
  | TOk _ =>
      let fix build_ps (ns : list string) (pacc : list c_param) (lacc : list c_item)
        : c_tr (list c_param * list c_item) :=
        match ns with
        | [] => TOk (rev_append pacc [], rev_append lacc [])
        | nm :: rest =>
            let info :=
              match assoc_str nm declared with
              | Some (dloc, dsp, syn, _) => TOk (dloc, dsp, syn)
              | None =>
                  if topt_gnu89 (te_opts env) then TOk (loc, [SpTspec "int"], DTBase)
                  else
                    sema_err loc
                      ("parameter '" ++ nm ++ "' was not declared, defaults to 'int'; ISO C99 and later do not support implicit int")
              end in
            match info with
            | TErr err => TErr err
            | TOk (dloc, dsp, syn) =>
                let oprom : option (list c_spec) :=
                  if prototyped then None
                  else
                    match specs_type dsp env with
                    | TOk (pb, env1) =>
                        match apply_declarator syn pb env1 with
                        | TOk (pt0, _) =>
                            let t := unqualified (type_adjusted pt0) in
                            let p := default_promotion t in
                            if negb (c_type_eqb p t) then
                              match p with
                              | TIntK IInt => Some [SpTspec "int"]
                              | TFloatK FDouble => Some [SpTspec "double"]
                              | _ => None
                              end
                            else None
                        | TErr _ => None
                        end
                    | TErr _ => None
                    end in
                match oprom with
                | Some pspecs =>
                    let fresh := "%knr_" ++ nm in
                    let p := Param pspecs (Dcl (Some fresh) DTBase None) in
                    let l := IDecl dloc dsp [InitDecl (Dcl (Some nm) syn None) (Some (InitExpr (EId fresh)))] in
                    build_ps rest (p :: pacc) (l :: lacc)
                | None =>
                    let p := Param dsp (Dcl (Some nm) syn None) in
                    build_ps rest (p :: pacc) lacc
                end
            end
        end in
      match build_ps names [] [] with
      | TErr err => TErr err
      | TOk (ps, ls) => TOk (PParams ps false, ls)
      end
  end.

(** ## Semantic diagnostics

    Locates the first operand in evaluation order that fails elaboration and
    produces the exact diagnostic message expected by nanofil's reject tests. *)

Fixpoint first_unsupported_expr (fuel : nat) (e : c_expr) (env : c_type_env)
  : option string :=
  match fuel with
  | O => None
  | S f =>
      let check_tn (tn : c_type_name) : option string :=
        match type_name_type tn env with
        | TOk (t, _) =>
            match unsupported_value_type t with
            | Some why => Some (why ++ " is not supported")
            | None => None
            end
        | TErr _ => None
        end in
      let or_else (a : option string) (b : unit -> option string) :=
        match a with Some _ => a | None => b tt end in
      let fix check_list (es : list c_expr) : option string :=
        match es with
        | [] => None
        | x :: rest => or_else (first_unsupported_expr f x env) (fun _ => check_list rest)
        end in
      match e with
      | ECast tn a | EBitCast tn a | EVaArg a tn | EConvertVector a tn =>
          or_else (check_tn tn) (fun _ => first_unsupported_expr f a env)
      | ESizeofType tn | EAlignofType tn | EOffsetof tn _ | EComplit tn _ => check_tn tn
      | ETypesCompatible ta tb => or_else (check_tn ta) (fun _ => check_tn tb)
      | EBin _ a b | EAssign _ a b | EComma a b | EIndex a b | EGCond a b =>
          or_else (first_unsupported_expr f a env) (fun _ => first_unsupported_expr f b env)
      | EUn _ a | EMember a _ | EArrow a _ | ESizeofExpr a | EAlignofExpr a
      | ERealPart a | EImagPart a => first_unsupported_expr f a env
      | ECond c a b =>
          or_else (first_unsupported_expr f c env) (fun _ =>
          or_else (first_unsupported_expr f a env) (fun _ => first_unsupported_expr f b env))
      | ECall fn args =>
          or_else (first_unsupported_expr f fn env) (fun _ => check_list args)
      | EGeneric c _ => first_unsupported_expr f c env
      | _ => None
      end
  end.

Definition missing_member_msg (t : c_type) (fld : string) (env : c_type_env) : string :=
  match unqualified t with
  | TStruct id | TUnion id =>
      match lookup_su_def env id with
      | Some (SUBad why) | Some (SUPartial why _) =>
          why ++ " is not supported (member " ++ fld ++ ")"
      | _ => "no member named " ++ fld
      end
  | _ => "no member named " ++ fld
  end.

Definition modifiable_fault_msg (x : c_typed_node) (what : string) : string :=
  match x with
  | TNode CatObj _ _ => what ++ " a read-only lvalue"
  | _ => what ++ " a non-lvalue"
  end.

Fixpoint fault_inner (fuel : nat) (e : c_expr) (env : c_type_env) : option string :=
  match fuel with
  | O => None
  | S f =>
      let is_untyped (e1 : c_expr) : bool :=
        match elaborate e1 env with TOk (Some _) => false | _ => true end in
      let low_ty (e1 : c_expr) : option c_type :=
        match elaborate e1 env with
        | TOk (Some x) => Some (lowered_node_type (value_node x))
        | _ => None
        end in
      let scalar_flt (e1 : c_expr) : option string :=
        if is_untyped e1 then fault_inner f e1 env
        else match low_ty e1 with
        | Some t => if scalar_type t then None else Some ("a " ++ c_type_diag_str t ++ " value is not a scalar")
        | None => None
        end in
      let operands_flt (es : list c_expr) : option string :=
        let fix go (xs : list c_expr) :=
          match xs with
          | [] => None
          | x :: rest => if is_untyped x then fault_inner f x env else go rest
          end in
        go es in
      let arms_flt (a b : c_expr) : option string :=
        match operands_flt [a; b] with
        | Some m => Some m
        | None =>
            match elaborate a env, elaborate b env with
            | TOk (Some xa0), TOk (Some xb0) =>
                let xa := value_node xa0 in
                let xb := value_node xb0 in
                let ta := tree_type xa in
                let tb := tree_type xb in
                let na := if is_ptr_type tb then null_pointer_constant xa env else false in
                let nb := if is_ptr_type ta then null_pointer_constant xb env else false in
                match arms_type ta na tb nb with
                | Some _ => None
                | None =>
                    Some ("incompatible ?: operands " ++ c_type_diag_str (unqualified ta) ++
                          " and " ++ c_type_diag_str (unqualified tb))
                end
            | _, _ => None
            end
        end in
      match e with
      | EId nm => Some ("undeclared identifier " ++ nm)
      | ELabelAddr nm => Some ("the address of label " ++ nm ++ " outside its function")
      | EIndex a i => fault_inner f (EUn UDeref (EBin BAdd a i)) env
      | EUn op inner =>
          if is_untyped inner then fault_inner f inner env
          else match op with
          | UDeref => Some "dereferencing a non-pointer"
          | UAddr =>
              match elaborate inner env with
              | TOk (Some (TNode CatObj _ (TFBitfield _ _ _))) =>
                  Some "cannot take the address of a bit-field"
              | _ => Some "& of a non-lvalue"
              end
          | UPlus | UNeg | UBnot | UNot =>
              match low_ty inner with
              | Some t => Some ("invalid operand to " ++ c_unop_name op ++ ": " ++ c_type_diag_str t)
              | None => None
              end
          | UPreInc | UPreDec | UPostInc | UPostDec =>
              match elaborate inner env with
              | TOk (Some x) =>
                  if negb (modifiable x env) then
                    Some (modifiable_fault_msg x (c_unop_name op ++ " of"))
                  else Some (c_unop_name op ++ " of a non-scalar lvalue")
              | _ => None
              end
          end
      | EMember subj fld =>
          if is_untyped subj then fault_inner f subj env
          else match elaborate subj env with
          | TOk (Some xs) =>
              let is_subj :=
                match xs with
                | TNode CatObj _ _ => true
                | TNode CatVal t _ => is_su_type (unqualified t)
                | _ => false
                end in
              if is_subj then Some (missing_member_msg (tree_type xs) fld env)
              else Some "member access on a non-lvalue"
          | _ => None
          end
      | ERealPart inner =>
          if is_untyped inner then fault_inner f inner env
          else Some "__real__ of a value that is not complex"
      | EImagPart inner =>
          if is_untyped inner then fault_inner f inner env
          else Some "__imag__ of a value that is not complex"
      | EArrow subj fld =>
          if is_untyped subj then fault_inner f subj env
          else match low_ty subj with
          | Some (TPtr t) => Some (missing_member_msg t fld env)
          | _ => Some "-> on a non-pointer"
          end
      | ECast tn inner =>
          match type_name_type tn env with
          | TOk (to_t, _) =>
              if is_untyped inner then fault_inner f inner env
              else match low_ty inner with
              | Some from_t => Some ("cannot convert " ++ c_type_diag_str from_t ++ " to " ++ c_type_diag_str to_t)
              | None => None
              end
          | TErr _ => None
          end
      | EBitCast tn inner =>
          match type_name_type tn env with
          | TOk (to_t, _) =>
              if is_untyped inner then fault_inner f inner env
              else match low_ty inner with
              | Some from_t =>
                  Some ("__builtin_bit_cast from " ++ c_type_diag_str from_t ++ " to " ++
                        c_type_diag_str to_t ++ ", which is not an object of the same size that is not an array")
              | None => None
              end
          | TErr _ => None
          end
      | ECall fn args =>
          let regular_call_flt (_ : unit) :=
            if is_untyped fn then fault_inner f fn env
            else match low_ty fn with
            | Some (TPtr (TFunc _ ps variadic)) =>
                let sym :=
                  match fn with
                  | EId nm =>
                      match lookup_ordinary env nm with
                      | Some (BFn _ s _) => s
                      | _ => "function pointer"
                      end
                  | _ => "function pointer"
                  end in
                let na := List.length args in
                let arity_msg :=
                  match ps with
                  | None => None
                  | Some pts =>
                      let np := List.length pts in
                      if (na <? np)%nat then Some ("too few arguments to " ++ sym)
                      else if negb variadic && (np <? na)%nat then Some ("too many arguments to " ++ sym)
                      else None
                  end in
                match arity_msg with
                | Some m => Some m
                | None =>
                    let fix args_flt (ops : option (list c_type)) (xs : list c_expr) : option string :=
                      match xs with
                      | [] => None
                      | a :: rest =>
                          let '(op, ops1) :=
                            match ops with
                            | None => (None, None)
                            | Some [] => (None, Some [])
                            | Some (p :: rp) => (Some p, Some rp)
                            end in
                          if is_untyped a then fault_inner f a env
                          else match elaborate a env with
                          | TOk (Some xa0) =>
                              let xa := value_node xa0 in
                              let t := lowered_node_type xa in
                              match op with
                              | None =>
                                  if arithmetic_type t || is_ptr_type t then args_flt ops1 rest
                                  else None
                              | Some p =>
                                  let tp := unqualified p in
                                  if negb (parameter_accepts tp t (null_pointer_constant xa env) env) then
                                    Some ("cannot assign " ++ c_type_diag_str t ++ " to " ++ c_type_diag_str tp)
                                  else if negb (is_su_type tp) then args_flt ops1 rest
                                  else None
                              end
                          | _ => None
                          end
                      end in
                    args_flt ps args
                end
            | _ => Some "called object is not a function"
            end in
          match fn with
          | EId nm =>
              match lookup_ordinary env nm with
              | Some _ => regular_call_flt tt
              | None =>
                  if atomic_name nm then
                    if rmw_atomic nm then
                      Some (nm ++ " needs a pointer to an integer (an _Atomic one for __c11 builtins), or to a pointer to exchange, compare it or (__c11) add to it, and constant memory orders")
                    else if fence_builtin nm then
                      Some (nm ++ " needs a constant memory order")
                    else if starts_with "__c11" nm then
                      Some (nm ++ " needs a pointer to an _Atomic integer, pointer, float or double and a constant memory order it supports (relaxed, consume, acquire or seq_cst for a load; relaxed, release or seq_cst for a store)")
                    else
                      Some (nm ++ " needs a pointer to an integer or pointer and a constant memory order it supports (relaxed, consume, acquire or seq_cst for a load; relaxed, release or seq_cst for a store)")
                  else match checking_builtin nm with
                  | Some (chk, plain) =>
                      Some (nm ++ " needs " ++ chk ++ " declared, or " ++ plain ++ " declared and an object size of (size_t)-1")
                  | None =>
                      match builtin_type nm, float_builtin nm with
                      | Some _, _ | _, Some _ => None
                      | None, None => regular_call_flt tt
                      end
                  end
              end
          | _ => regular_call_flt tt
          end
      | EAssign op a b =>
          if is_untyped a then fault_inner f a env
          else match elaborate a env with
          | TOk (Some x) =>
              if negb (modifiable x env) then Some (modifiable_fault_msg x "assignment to")
              else
                let ta := unqualified (tree_type x) in
                if String.eqb op "=" || scalar_type ta then
                  if is_untyped b then fault_inner f b env
                  else match low_ty b with
                  | Some tb =>
                      if String.eqb op "=" then
                        Some ("cannot assign " ++ c_type_diag_str tb ++ " to " ++ c_type_diag_str ta)
                      else match compound_assign_binop op with
                      | Some bop =>
                          match binary_operands bop ta tb with
                          | Some (_, _, tr) =>
                              Some ("cannot assign " ++ c_type_diag_str tr ++ " to " ++ c_type_diag_str ta)
                          | None =>
                              Some ("invalid operands to " ++ c_binop_name bop ++ ": " ++
                                    c_type_diag_str ta ++ " and " ++ c_type_diag_str tb)
                          end
                      | None => None
                      end
                  | None => None
                  end
                else None
          | _ => None
          end
      | EComma a b => operands_flt [a; b]
      | EAlignofExpr inner => fault_inner f inner env
      | ESizeofExpr inner =>
          if is_untyped inner then fault_inner f inner env
          else Some "sizeof of a bit-field"
      | EBin BLand a b | EBin BLor a b =>
          match scalar_flt a with Some m => Some m | None => scalar_flt b end
      | EBin op a b =>
          match operands_flt [a; b] with
          | Some m => Some m
          | None =>
              match low_ty a, low_ty b with
              | Some ta, Some tb =>
                  Some ("invalid operands to " ++ c_binop_name op ++ ": " ++
                        c_type_diag_str ta ++ " and " ++ c_type_diag_str tb)
              | _, _ => None
              end
          end
      | ECond c a b =>
          match arms_flt a b with Some m => Some m | None => scalar_flt c end
      | EGCond c b =>
          match arms_flt c b with Some m => Some m | None => scalar_flt c end
      | EGeneric c assocs =>
          if is_untyped c then fault_inner f c env
          else match elaborate c env with
          | TOk (Some cx) =>
              match generic_selection (tree_type (value_node cx)) assocs env (Loc "constant" 0) with
              | TOk sel => fault_inner f sel env
              | TErr _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

Definition fault (e : c_expr) (env : c_type_env) : option string :=
  match first_unsupported_expr (Z.to_nat 256) e env with
  | Some m => Some m
  | None => fault_inner (Z.to_nat 256) e env
  end.

Definition elaborate_loc (e : c_expr) (env : c_type_env) (loc : c_loc)
  : c_tr (option c_typed_node) :=
  match elaborate e env with
  | TErr err => TErr err
  | TOk (Some x) => TOk (Some x)
  | TOk None =>
      match fault e env with
      | Some msg => sema_err loc msg
      | None => TOk None
      end
  end.
