(** Core semantic types, symbol environments, layout helpers, and conversion
    rules for the Gallina C type checker.

    This module ports the non-recursive data model of nanofil/src/c_types.pl:
    C types, reflected qualifiers, struct and union layouts, integer
    promotions, usual arithmetic conversions, type compatibility, and operator
    typing rules. All definitions are pure and zero-axiom so both OCaml
    extraction and CertiRocq λANF compile them directly. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Semantic types and typed expression trees

    Code generation operates on unqualified types, while type checking keeps
    qualifiers and enum identities via [TQual] so constness, volatility,
    atomicity, and enum compatibility checks agree with C11. Grouping integer
    and floating primitives under [TIntK] and [TFloatK] keeps [c_type] compact
    (12 constructors) for fast pattern compilation in Rocq and λANF. *)

Inductive su_id : Type :=
| SUInt (n : Z)
| SUBuiltin (name : string).

Definition su_id_eqb (a b : su_id) : bool :=
  match a with
  | SUInt x => match b with SUInt y => Z.eqb x y | _ => false end
  | SUBuiltin x => match b with SUBuiltin y => String.eqb x y | _ => false end
  end.

Definition su_id_key (id : su_id) : string :=
  match id with
  | SUInt n => ("#" ++ z_to_string n)%string
  | SUBuiltin s => ("@" ++ s)%string
  end.

Inductive enum_key_t : Type :=
| EKTag (name : string)
| EKAnon (first : string).

Definition enum_key_eqb (a b : enum_key_t) : bool :=
  match a with
  | EKTag x => match b with EKTag y => String.eqb x y | _ => false end
  | EKAnon x => match b with EKAnon y => String.eqb x y | _ => false end
  end.

(** Reflected qualifiers ordered to match Prolog's standard term order
    (`atomic`, `const`, `restrict`, `volatile`, then `enum(...)`). *)
Inductive c_qual : Type :=
| QAtomic
| QConst
| QRestrict
| QVolatile
| QEnum (k : enum_key_t).

Definition c_qual_rank (q : c_qual) : Z :=
  match q with
  | QAtomic => 0
  | QConst => 1
  | QRestrict => 2
  | QVolatile => 3
  | QEnum (EKTag _) => 4
  | QEnum (EKAnon _) => 5
  end.

Definition c_qual_eqb (a b : c_qual) : bool :=
  let ra := c_qual_rank a in
  let rb := c_qual_rank b in
  if negb (Z.eqb ra rb) then false
  else
    match a with
    | QEnum k1 => match b with QEnum k2 => enum_key_eqb k1 k2 | _ => false end
    | _ => true
    end.

Definition string_ltb (a b : string) : bool :=
  let la := String.length a in
  let lb := String.length b in
  let lim := Nat.min la lb in
  let fix go (fuel i : nat) : bool :=
    match fuel with
    | O => (la <? lb)%nat
    | S f =>
        match String.get i a, String.get i b with
        | Some ca, Some cb =>
            let ka := code ca in
            let kb := code cb in
            if Nat.eqb ka kb then go f (S i) else (ka <? kb)%nat
        | _, _ => (la <? lb)%nat
        end
    end in
  go lim 0%nat.

Definition c_qual_ltb (a b : c_qual) : bool :=
  let ra := c_qual_rank a in
  let rb := c_qual_rank b in
  if Z.eqb ra rb then
    match a with
    | QEnum (EKTag x) => match b with QEnum (EKTag y) => string_ltb x y | _ => false end
    | QEnum (EKAnon x) => match b with QEnum (EKAnon y) => string_ltb x y | _ => false end
    | _ => false
    end
  else ra <? rb.

Inductive c_arr_len : Type :=
| ALNone
| ALConst (n : Z)
| ALVlaStar
| ALVlaExpr (e : c_expr)
| ALDyn (tmp : string).

Definition su_kind_eqb (a b : su_kind) : bool :=
  match a with
  | KStruct => match b with KStruct => true | KUnion => false end
  | KUnion => match b with KUnion => true | KStruct => false end
  end.

Definition c_arr_len_eqb (a b : c_arr_len) : bool :=
  match a with
  | ALNone => match b with ALNone => true | _ => false end
  | ALVlaStar => match b with ALVlaStar => true | _ => false end
  | ALConst x => match b with ALConst y => Z.eqb x y | _ => false end
  | ALDyn x => match b with ALDyn y => String.eqb x y | _ => false end
  | ALVlaExpr e1 =>
      match b with
      | ALVlaExpr e2 =>
          String.eqb (String.concat "" (rev_append (emit_expr e1 []) []))
                     (String.concat "" (rev_append (emit_expr e2 []) []))
      | _ => false
      end
  end.

Inductive c_int_kind : Type :=
| IBool | IChar | ISChar | IUChar | IShort | IUShort
| IInt | IUInt | ILong | IULong | ILLong | IULLong.

Definition c_int_kind_tag (k : c_int_kind) : Z :=
  match k with
  | IBool => 0 | IChar => 1 | ISChar => 2 | IUChar => 3
  | IShort => 4 | IUShort => 5 | IInt => 6 | IUInt => 7
  | ILong => 8 | IULong => 9 | ILLong => 10 | IULLong => 11
  end.

Definition c_int_kind_eqb (a b : c_int_kind) : bool :=
  Z.eqb (c_int_kind_tag a) (c_int_kind_tag b).

Inductive c_float_kind : Type :=
| FFloat | FDouble | FLDouble.

Definition c_float_kind_tag (k : c_float_kind) : Z :=
  match k with FFloat => 0 | FDouble => 1 | FLDouble => 2 end.

Definition c_float_kind_eqb (a b : c_float_kind) : bool :=
  Z.eqb (c_float_kind_tag a) (c_float_kind_tag b).

(** Semantic C types matching `c_types.pl`. *)
Inductive c_type : Type :=
| TVoid
| TIntK (k : c_int_kind)
| TFloatK (k : c_float_kind)
| TPtr (inner : c_type)
| TArray (elem : c_type) (len : c_arr_len)
| TFunc (ret : c_type) (params : option (list c_type)) (variadic : bool)
| TStruct (id : su_id)
| TUnion (id : su_id)
| TAtomic (su : c_type) (padded : Z)
| TVec (elem : c_type) (count : Z) (align : Z)
| TQual (qs : list c_qual) (inner : c_type)
| TBad (why : string).

Definition TBool : c_type := TIntK IBool.
Definition TChar : c_type := TIntK IChar.
Definition TSChar : c_type := TIntK ISChar.
Definition TUChar : c_type := TIntK IUChar.
Definition TShort : c_type := TIntK IShort.
Definition TUShort : c_type := TIntK IUShort.
Definition TInt : c_type := TIntK IInt.
Definition TUInt : c_type := TIntK IUInt.
Definition TLong : c_type := TIntK ILong.
Definition TULong : c_type := TIntK IULong.
Definition TLLong : c_type := TIntK ILLong.
Definition TULLong : c_type := TIntK IULLong.
Definition TFloat : c_type := TFloatK FFloat.
Definition TDouble : c_type := TFloatK FDouble.
Definition TLDouble : c_type := TFloatK FLDouble.

Fixpoint list_eqb {A : Type} (eq : A -> A -> bool) (xs ys : list A) : bool :=
  match xs with
  | [] => match ys with [] => true | _ => false end
  | x :: rx => match ys with y :: ry => eq x y && list_eqb eq rx ry | [] => false end
  end.

Fixpoint c_type_eqb (a b : c_type) : bool :=
  let fix list_ty_eqb (xs ys : list c_type) : bool :=
    match xs with
    | [] => match ys with [] => true | _ => false end
    | x :: rx => match ys with y :: ry => c_type_eqb x y && list_ty_eqb rx ry | [] => false end
    end in
  match a with
  | TVoid => match b with TVoid => true | _ => false end
  | TIntK k1 => match b with TIntK k2 => c_int_kind_eqb k1 k2 | _ => false end
  | TFloatK k1 => match b with TFloatK k2 => c_float_kind_eqb k1 k2 | _ => false end
  | TPtr x => match b with TPtr y => c_type_eqb x y | _ => false end
  | TArray x l1 => match b with TArray y l2 => c_arr_len_eqb l1 l2 && c_type_eqb x y | _ => false end
  | TFunc r1 p1 v1 =>
      match b with
      | TFunc r2 p2 v2 =>
          Bool.eqb v1 v2 && c_type_eqb r1 r2 &&
          match p1 with
          | None => match p2 with None => true | Some _ => false end
          | Some xs => match p2 with Some ys => list_ty_eqb xs ys | None => false end
          end
      | _ => false
      end
  | TStruct x => match b with TStruct y => su_id_eqb x y | _ => false end
  | TUnion x => match b with TUnion y => su_id_eqb x y | _ => false end
  | TAtomic s1 p1 => match b with TAtomic s2 p2 => Z.eqb p1 p2 && c_type_eqb s1 s2 | _ => false end
  | TVec e1 n1 a1 => match b with TVec e2 n2 a2 => Z.eqb n1 n2 && Z.eqb a1 a2 && c_type_eqb e1 e2 | _ => false end
  | TQual q1 x => match b with TQual q2 y => list_eqb c_qual_eqb q1 q2 && c_type_eqb x y | _ => false end
  | TBad w1 => match b with TBad w2 => String.eqb w1 w2 | _ => false end
  end.

Inductive c_storage : Type :=
| StNone
| StTypedef
| StStatic
| StExtern
| StAuto
| StRegister
| StThreadLocal (inner : c_storage).

Record c_decl : Type := mkCDecl {
  cd_name : string;
  cd_type : c_type;
  cd_storage : c_storage;
  cd_asm : option string;
  cd_init : option c_init;
}.

Inductive c_member_bits : Type :=
| MBNone
| MBBits (pos width : Z).

Record c_member_layout : Type := mkMemLayout {
  ml_name : option string;
  ml_type : c_type;
  ml_off : Z;
  ml_bits : c_member_bits;
}.

Inductive su_def : Type :=
| SUIncomplete (tag : option string)
| SUDef (kind : su_kind) (members : list c_member_layout) (size align : Z)
| SUPartial (why : string) (members : list c_member_layout)
| SUBad (why : string).

Inductive var_slot : Type :=
| VSNone
| VSLocal (id : Z)
| VSNamed (name : string).

Inductive ord_binding : Type :=
| BTypedef (ty : c_type)
| BEnumConst (val : Z) (ty : c_type)
| BVar (slot : var_slot) (ty : c_type)
| BGVar (ty : c_type) (sym : string) (link : string) (tls : bool)
| BFn (ty : c_type) (sym : string) (link : string).

Inductive tag_binding : Type :=
| TagSU (kind : su_kind) (id : su_id)
| TagEnum (underlying : c_type).

Inductive c_node_cat : Type :=
| CatObj
| CatFun
| CatVal.

Inductive c_typed_node : Type :=
| TNode (cat : c_node_cat) (ty : c_type) (form : c_typed_form)

with c_typed_form : Type :=
| TFId (name : string)
| TFPredefined (name : string)
| TFInt (v : Z)
| TFFloat (chars : string)
| TFImag (inner : c_typed_node)
| TFStr (bytes : list Z)
| TFWStr (wt : wide_type) (codes : list Z)
| TFLoad (inner : c_typed_node)
| TFDecay (inner : c_typed_node)
| TFAddr (inner : c_typed_node)
| TFDeref (inner : c_typed_node)
| TFCast (tn : c_type_name) (inner : c_typed_node)
| TFComplit (tn : c_type_name) (entries : list c_init_entry)
| TFIncDec (op : c_unop) (inner : c_typed_node)
| TFUn (op : c_unop) (inner : c_typed_node)
| TFBin (op : c_binop) (lhs rhs : c_typed_node)
| TFCond (c a b : c_typed_node)
| TFGCond (c b : c_typed_node)
| TFAssign (op : string) (lhs rhs : c_typed_node)
| TFComma (lhs rhs : c_typed_node)
| TFMember (subj : c_typed_node) (field : string)
| TFBitfield (subj : c_typed_node) (field : string) (width : Z)
| TFVLane (vec idx : c_typed_node)
| TFCall (fn : c_typed_node) (args : list c_typed_node)
| TFBuiltin (name : string) (args : list c_expr)
| TFConvertVector (arg : c_expr) (tn : c_type_name)
| TFSizeofExpr (inner : c_typed_node)
| TFSizeofType (tn : c_type_name)
| TFAlignofType (tn : c_type_name)
| TFAlignofExpr (inner : c_typed_node)
| TFOffsetof (tn : c_type_name) (path : list c_designator)
| TFVaArg (tn : c_type_name) (arg : c_typed_node)
| TFBitCast (inner : c_typed_node)
| TFStmtExpr (body : c_stmt).

Inductive c_const_val : Type :=
| CVInt (v : Z)
| CVUb.

Inductive c_type_err : Type :=
| TENotConstant
| TEBad (why : string)
| TESema (msg : string).

Inductive c_tr (A : Type) : Type :=
| TOk (v : A)
| TErr (e : c_type_err).

Arguments TOk {A} v.
Arguments TErr {A} e.

(** ## Scoped and unscoped semantic environment

    Block scopes save and restore [c_scope], while record definitions and
    sequential tag ids in [c_defs] grow monotonically across the unit. *)

Record c_scope : Type := mkCScope {
  sc_ords : smap ord_binding;
  sc_qtypes : smap c_type;
  sc_qalign : smap (option Z);
  sc_talign : smap (option Z);
  sc_cval : smap (option Z);
  sc_labels : smap Z;
  sc_tags : smap tag_binding;
  sc_member_base : option c_type;
  sc_enclosing_fn : option string;
}.

Record c_defs : Type := mkCDefs {
  df_su : smap su_def;
  df_qmembers : smap (list (option string * c_type));
  df_transparent : smap bool;
  df_aligned_typedefs : list c_type;
  df_expr_tags : smap su_id;
  df_next : Z;
}.

Record c_type_opts : Type := mkCTypeOpts {
  topt_vectors : bool;
  topt_gnu89 : bool;
}.

Definition default_type_opts : c_type_opts := mkCTypeOpts true false.

Record c_type_env : Type := mkCTypeEnv {
  te_scope : c_scope;
  te_defs : c_defs;
  te_opts : c_type_opts;
  te_pp_mode : bool;
  te_expr_tags_mode : bool;
}.

Definition empty_scope : c_scope :=
  mkCScope smap_empty smap_empty smap_empty smap_empty smap_empty
           smap_empty smap_empty None None.

Definition va_list_id : su_id := SUBuiltin "builtin.va_list".
Definition complex_float_id : su_id := SUBuiltin "builtin.complex.float".
Definition complex_double_id : su_id := SUBuiltin "builtin.complex.double".
Definition complex_ldouble_id : su_id := SUBuiltin "builtin.complex.ldouble".

Definition va_list_def : su_def :=
  SUDef KStruct
    [ mkMemLayout (Some "gp_offset") TUInt 0 MBNone;
      mkMemLayout (Some "fp_offset") TUInt 4 MBNone;
      mkMemLayout (Some "overflow_arg_area") (TPtr TVoid) 8 MBNone;
      mkMemLayout (Some "reg_save_area") (TPtr TVoid) 16 MBNone ]
    24 8.

Definition complex_def_of (f : c_type) (sz al : Z) : su_def :=
  SUDef KStruct
    [ mkMemLayout (Some "builtin.re") f 0 MBNone;
      mkMemLayout (Some "builtin.im") f sz MBNone ]
    (2 * sz) al.

Definition empty_defs : c_defs :=
  let m0 := smap_empty in
  let m1 := smap_add (su_id_key va_list_id) va_list_def m0 in
  let m2 := smap_add (su_id_key complex_float_id) (complex_def_of TFloat 4 4) m1 in
  let m3 := smap_add (su_id_key complex_double_id) (complex_def_of TDouble 8 8) m2 in
  let m4 := smap_add (su_id_key complex_ldouble_id) (complex_def_of TLDouble 16 16) m3 in
  mkCDefs m4 smap_empty smap_empty [] smap_empty 0.

Definition empty_type_env_opts (opts : c_type_opts) : c_type_env :=
  mkCTypeEnv empty_scope empty_defs opts false false.

Definition empty_type_env : c_type_env :=
  empty_type_env_opts default_type_opts.

Definition with_scope (env : c_type_env) (sc : c_scope) : c_type_env :=
  mkCTypeEnv sc (te_defs env) (te_opts env) (te_pp_mode env) (te_expr_tags_mode env).

Definition with_defs (env : c_type_env) (df : c_defs) : c_type_env :=
  mkCTypeEnv (te_scope env) df (te_opts env) (te_pp_mode env) (te_expr_tags_mode env).

Definition with_expr_tags_mode (env : c_type_env) (b : bool) : c_type_env :=
  mkCTypeEnv (te_scope env) (te_defs env) (te_opts env) (te_pp_mode env) b.

Definition lookup_ordinary (env : c_type_env) (name : string) : option ord_binding :=
  smap_find name (sc_ords (te_scope env)).

Definition bind_ordinary (name : string) (v : ord_binding) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (smap_add name v (sc_ords sc))
                           (sc_qtypes sc) (sc_qalign sc) (sc_talign sc)
                           (sc_cval sc) (sc_labels sc) (sc_tags sc)
                           (sc_member_base sc) (sc_enclosing_fn sc)).

Definition lookup_qtype (env : c_type_env) (name : string) : option c_type :=
  smap_find name (sc_qtypes (te_scope env)).

Definition bind_qtype (name : string) (t : c_type) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (sc_ords sc) (smap_add name t (sc_qtypes sc))
                           (sc_qalign sc) (sc_talign sc) (sc_cval sc)
                           (sc_labels sc) (sc_tags sc)
                           (sc_member_base sc) (sc_enclosing_fn sc)).

Definition lookup_qalign (env : c_type_env) (name : string) : option (option Z) :=
  smap_find name (sc_qalign (te_scope env)).

Definition bind_qalign (name : string) (a : option Z) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (sc_ords sc) (sc_qtypes sc)
                           (smap_add name a (sc_qalign sc)) (sc_talign sc)
                           (sc_cval sc) (sc_labels sc) (sc_tags sc)
                           (sc_member_base sc) (sc_enclosing_fn sc)).

Definition lookup_talign (env : c_type_env) (name : string) : option (option Z) :=
  smap_find name (sc_talign (te_scope env)).

Definition bind_talign (name : string) (a : option Z) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (sc_ords sc) (sc_qtypes sc) (sc_qalign sc)
                           (smap_add name a (sc_talign sc))
                           (sc_cval sc) (sc_labels sc) (sc_tags sc)
                           (sc_member_base sc) (sc_enclosing_fn sc)).

Definition lookup_cval (env : c_type_env) (name : string) : option (option Z) :=
  smap_find name (sc_cval (te_scope env)).

Definition bind_cval (name : string) (v : option Z) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (sc_ords sc) (sc_qtypes sc) (sc_qalign sc)
                           (sc_talign sc) (smap_add name v (sc_cval sc))
                           (sc_labels sc) (sc_tags sc)
                           (sc_member_base sc) (sc_enclosing_fn sc)).

Definition lookup_label_addr (env : c_type_env) (name : string) : option Z :=
  smap_find name (sc_labels (te_scope env)).

Definition bind_label_addr (name : string) (n : Z) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (sc_ords sc) (sc_qtypes sc) (sc_qalign sc)
                           (sc_talign sc) (sc_cval sc)
                           (smap_add name n (sc_labels sc)) (sc_tags sc)
                           (sc_member_base sc) (sc_enclosing_fn sc)).

Definition lookup_tag (env : c_type_env) (name : string) : option tag_binding :=
  smap_find name (sc_tags (te_scope env)).

Definition bind_tag (name : string) (tb : tag_binding) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (sc_ords sc) (sc_qtypes sc) (sc_qalign sc)
                           (sc_talign sc) (sc_cval sc) (sc_labels sc)
                           (smap_add name tb (sc_tags sc))
                           (sc_member_base sc) (sc_enclosing_fn sc)).

Definition set_member_base (t : c_type) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (sc_ords sc) (sc_qtypes sc) (sc_qalign sc)
                           (sc_talign sc) (sc_cval sc) (sc_labels sc)
                           (sc_tags sc) (Some t) (sc_enclosing_fn sc)).

Definition set_enclosing_fn (fn : option string) (env : c_type_env) : c_type_env :=
  let sc := te_scope env in
  with_scope env (mkCScope (sc_ords sc) (sc_qtypes sc) (sc_qalign sc)
                           (sc_talign sc) (sc_cval sc) (sc_labels sc)
                           (sc_tags sc) (sc_member_base sc) fn).

Definition lookup_su_def (env : c_type_env) (id : su_id) : option su_def :=
  smap_find (su_id_key id) (df_su (te_defs env)).

Definition put_su_def (id : su_id) (d : su_def) (env : c_type_env) : c_type_env :=
  let df := te_defs env in
  with_defs env (mkCDefs (smap_add (su_id_key id) d (df_su df))
                         (df_qmembers df) (df_transparent df)
                         (df_aligned_typedefs df) (df_expr_tags df) (df_next df)).

Definition lookup_qmembers (env : c_type_env) (id : su_id)
  : option (list (option string * c_type)) :=
  smap_find (su_id_key id) (df_qmembers (te_defs env)).

Definition put_qmembers (id : su_id) (ms : list (option string * c_type))
  (env : c_type_env) : c_type_env :=
  let df := te_defs env in
  with_defs env (mkCDefs (df_su df)
                         (smap_add (su_id_key id) ms (df_qmembers df))
                         (df_transparent df) (df_aligned_typedefs df)
                         (df_expr_tags df) (df_next df)).

Definition is_transparent_su (env : c_type_env) (id : su_id) : bool :=
  match smap_find (su_id_key id) (df_transparent (te_defs env)) with
  | Some true => true
  | _ => false
  end.

Definition mark_transparent_su (id : su_id) (env : c_type_env) : c_type_env :=
  let df := te_defs env in
  with_defs env (mkCDefs (df_su df) (df_qmembers df)
                         (smap_add (su_id_key id) true (df_transparent df))
                         (df_aligned_typedefs df) (df_expr_tags df) (df_next df)).

Definition add_aligned_typedef (t : c_type) (env : c_type_env) : c_type_env :=
  let df := te_defs env in
  with_defs env (mkCDefs (df_su df) (df_qmembers df) (df_transparent df)
                         (t :: df_aligned_typedefs df) (df_expr_tags df) (df_next df)).

Definition has_aligned_typedef (t : c_type) (env : c_type_env) : bool :=
  existsb (c_type_eqb t) (df_aligned_typedefs (te_defs env)).

Definition lookup_expr_tag (key : string) (env : c_type_env) : option su_id :=
  smap_find key (df_expr_tags (te_defs env)).

Definition put_expr_tag (key : string) (id : su_id) (env : c_type_env) : c_type_env :=
  let df := te_defs env in
  with_defs env (mkCDefs (df_su df) (df_qmembers df) (df_transparent df)
                         (df_aligned_typedefs df)
                         (smap_add key id (df_expr_tags df)) (df_next df)).

Definition alloc_su_tag (kind : su_kind) (tag : option string) (env : c_type_env)
  : su_id * c_type_env :=
  let df := te_defs env in
  let id := SUInt (df_next df) in
  let df1 := mkCDefs (smap_add (su_id_key id) (SUIncomplete tag) (df_su df))
                     (df_qmembers df) (df_transparent df)
                     (df_aligned_typedefs df) (df_expr_tags df)
                     (df_next df + 1) in
  let env1 := with_defs env df1 in
  let env2 := match tag with
              | Some nm => bind_tag nm (TagSU kind id) env1
              | None => env1
              end in
  (id, env2).

(** ## Qualifiers, complex types, and basic type predicates

    These helpers strip, merge, and classify types without invoking the
    expression elaborator. *)

Fixpoint insert_qual (q : c_qual) (qs : list c_qual) : list c_qual :=
  match qs with
  | [] => [q]
  | h :: rest =>
      if c_qual_eqb q h then qs
      else if c_qual_ltb q h then q :: qs
      else h :: insert_qual q rest
  end.

Definition sort_quals (qs : list c_qual) : list c_qual :=
  fold_left (fun acc q => insert_qual q acc) qs [].

Fixpoint qualify (qs : list c_qual) (t : c_type) : c_type :=
  match t with
  | TQual qs1 inner => qualify (app qs qs1) inner
  | TArray elem len =>
      match qs with
      | [] => t
      | _ => TArray (qualify qs elem) len
      end
  | _ =>
      match sort_quals qs with
      | [] => t
      | sorted => TQual sorted t
      end
  end.

Fixpoint unqualified (t : c_type) : c_type :=
  match t with
  | TQual _ inner => unqualified inner
  | TPtr inner => TPtr (unqualified inner)
  | TArray elem len => TArray (unqualified elem) len
  | TFunc ret params v =>
      TFunc (unqualified ret)
            (match params with None => None | Some ps => Some (map unqualified ps) end) v
  | _ => t
  end.

Definition complex_type (t0 : c_type) : option c_type :=
  match unqualified t0 with
  | TStruct (SUBuiltin k) =>
      if String.eqb k "builtin.complex.float" then Some TFloat
      else if String.eqb k "builtin.complex.double" then Some TDouble
      else if String.eqb k "builtin.complex.ldouble" then Some TLDouble
      else None
  | _ => None
  end.

Definition complex_of (f : c_type) : option c_type :=
  match f with
  | TFloatK FFloat => Some (TStruct complex_float_id)
  | TFloatK FDouble => Some (TStruct complex_double_id)
  | TFloatK FLDouble => Some (TStruct complex_ldouble_id)
  | _ => None
  end.

Definition qual_of_string (s : string) : option c_qual :=
  if String.eqb s "const" then Some QConst
  else if String.eqb s "volatile" then Some QVolatile
  else if String.eqb s "restrict" then Some QRestrict
  else if String.eqb s "atomic" then Some QAtomic
  else None.

Definition has_qual (q : c_qual) (qs : list c_qual) : bool :=
  existsb (c_qual_eqb q) qs.

Definition atomic_qualified (t : c_type) : bool :=
  match t with
  | TQual qs _ => has_qual QAtomic qs
  | _ => false
  end.

Fixpoint readonly_object_type (t : c_type) : bool :=
  match t with
  | TQual qs inner => has_qual QConst qs || readonly_object_type inner
  | TArray elem _ => readonly_object_type elem
  | _ => false
  end.

Definition variable_size (l : c_arr_len) : bool :=
  match l with ALVlaStar | ALVlaExpr _ | ALDyn _ => true | _ => false end.

Fixpoint vm_type (t : c_type) : bool :=
  match t with
  | TQual _ inner => vm_type inner
  | TPtr inner => vm_type inner
  | TArray elem len => variable_size len || vm_type elem
  | TFunc ret params _ =>
      vm_type ret ||
      match params with
      | None => false
      | Some ps => existsb vm_type ps
      end
  | _ => false
  end.

Fixpoint vla_type (t : c_type) : bool :=
  match t with
  | TQual _ inner => vla_type inner
  | TArray elem len => variable_size len || vla_type elem
  | _ => false
  end.

Fixpoint unsupported_value_type (t : c_type) : option string :=
  match t with
  | TBad why => Some why
  | TArray elem _ => unsupported_value_type elem
  | _ => None
  end.

Fixpoint bad_type (t : c_type) : option string :=
  let fix first_bad (ps : list c_type) : option string :=
    match ps with
    | [] => None
    | p :: rest =>
        match bad_type p with
        | Some w => Some w
        | None => first_bad rest
        end
    end in
  match t with
  | TBad why => Some why
  | TArray elem _ => bad_type elem
  | TFunc ret params _ =>
      match bad_type ret with
      | Some w => Some w
      | None => match params with None => None | Some ps => first_bad ps end
      end
  | _ => None
  end.

Definition type_adjusted (t : c_type) : c_type :=
  match t with
  | TArray elem _ => TPtr elem
  | TFunc r ps v => TPtr (TFunc r ps v)
  | _ => t
  end.

Fixpoint value_type (t : c_type) : c_type :=
  match t with
  | TQual _ inner => value_type inner
  | TAtomic s _ => s
  | TArray elem _ => TPtr elem
  | TFunc r ps v => TPtr (TFunc r ps v)
  | _ => t
  end.

Fixpoint array_type (t : c_type) : bool :=
  match t with
  | TQual _ inner => array_type inner
  | TArray _ _ => true
  | _ => false
  end.

Fixpoint innermost_element (t : c_type) : c_type :=
  match t with
  | TArray elem _ => innermost_element elem
  | _ => t
  end.

(** ## Integer types, floating types, promotions, and conversions

    These rules encode the x86-64 System V Linux integer widths, signedness,
    conversion ranks, and usual arithmetic conversions. *)

Inductive c_sign : Type := CSigned | CUnsigned.

Definition c_sign_eqb (a b : c_sign) : bool :=
  match a with
  | CSigned => match b with CSigned => true | CUnsigned => false end
  | CUnsigned => match b with CUnsigned => true | CSigned => false end
  end.

Definition int_kind_info (k : c_int_kind) : Z * c_sign * Z :=
  match k with
  | IBool => (1, CUnsigned, 0)
  | IChar => (1, CSigned, 1)
  | ISChar => (1, CSigned, 1)
  | IUChar => (1, CUnsigned, 1)
  | IShort => (2, CSigned, 2)
  | IUShort => (2, CUnsigned, 2)
  | IInt => (4, CSigned, 3)
  | IUInt => (4, CUnsigned, 3)
  | ILong => (8, CSigned, 4)
  | IULong => (8, CUnsigned, 4)
  | ILLong => (8, CSigned, 5)
  | IULLong => (8, CUnsigned, 5)
  end.

Definition integer_type_info (t : c_type) : option (Z * c_sign * Z) :=
  match t with TIntK k => Some (int_kind_info k) | _ => None end.

Definition int_type (t : c_type) : bool :=
  match t with TIntK _ => true | _ => false end.

Definition int_info (t : c_type) : option (Z * c_sign) :=
  match t with
  | TIntK k => let '(sz, sg, _) := int_kind_info k in Some (sz, sg)
  | _ => None
  end.

Definition float_type (t : c_type) : bool :=
  match t with TFloatK _ => true | _ => false end.

Definition arithmetic_type (t : c_type) : bool :=
  match t with TIntK _ | TFloatK _ => true | _ => false end.

Definition float_fmt_of (t : c_type) : option ieee_fmt :=
  match t with
  | TFloatK FFloat => Some FmtS
  | TFloatK FDouble => Some FmtD
  | TFloatK FLDouble => Some FmtX
  | _ => None
  end.

Definition atomic_object_type (t : c_type) : bool :=
  match t with
  | TIntK _ | TPtr _ | TFloatK FFloat | TFloatK FDouble => true
  | _ => false
  end.

Definition type_class (t : c_type) : option string :=
  match t with
  | TIntK k =>
      let '(sz, _, _) := int_kind_info k in
      Some (if Z.eqb sz 8 then "l" else "w")
  | TFloatK FFloat => Some "s"
  | TFloatK FDouble => Some "d"
  | TFloatK FLDouble => Some "x"
  | TPtr _ => Some "p"
  | _ => None
  end.

Definition scalar_type (t : c_type) : bool :=
  match t with TIntK _ | TFloatK _ | TPtr _ => true | _ => false end.

Definition unsigned_of (t : c_type) : option c_type :=
  match t with
  | TIntK IChar | TIntK ISChar => Some TUChar
  | TIntK IShort => Some TUShort
  | TIntK IInt => Some TUInt
  | TIntK ILong => Some TULong
  | TIntK ILLong => Some TULLong
  | _ => None
  end.

Definition integer_promotion (t : c_type) : c_type :=
  match t with
  | TIntK k => let '(_, _, r) := int_kind_info k in if r <? 3 then TInt else t
  | _ => t
  end.

Definition default_promotion (t : c_type) : c_type :=
  match t with
  | TFloatK FFloat => TDouble
  | _ => integer_promotion t
  end.

Definition float_kind_max (a b : c_float_kind) : c_float_kind :=
  match a with
  | FLDouble => FLDouble
  | FDouble => match b with FLDouble => FLDouble | _ => FDouble end
  | FFloat => b
  end.

Definition usual_arith_conversion (ta0 tb0 : c_type) : option c_type :=
  if negb (arithmetic_type ta0 && arithmetic_type tb0) then None
  else
    match ta0 with
    | TFloatK fa =>
        match tb0 with
        | TFloatK fb => Some (TFloatK (float_kind_max fa fb))
        | _ => Some ta0
        end
    | _ =>
        match tb0 with
        | TFloatK _ => Some tb0
        | _ =>
            let a := integer_promotion ta0 in
            let b := integer_promotion tb0 in
            match integer_type_info a, integer_type_info b with
            | Some (sza, sga, ra), Some (szb, sgb, rb) =>
                if c_type_eqb a b then Some a
                else if c_sign_eqb sga sgb then
                  Some (if rb <=? ra then a else b)
                else if c_sign_eqb sga CUnsigned && (rb <=? ra) then Some a
                else if c_sign_eqb sgb CUnsigned && (ra <=? rb) then Some b
                else if c_sign_eqb sga CSigned && (szb <? sza) then Some a
                else if c_sign_eqb sgb CSigned && (sza <? szb) then Some b
                else if c_sign_eqb sga CSigned then unsigned_of a
                else unsigned_of b
            | _, _ => None
            end
        end
    end.

Definition signed_word (sg : c_sign) (u m : Z) : Z :=
  match sg with
  | CSigned => if Z.shiftr m 1 <=? u then u - m else u
  | CUnsigned => u
  end.

Definition convert_int (v : Z) (t : c_type) : option Z :=
  match t with
  | TIntK IBool => Some (if Z.eqb v 0 then 0 else 1)
  | TIntK k =>
      let '(sz, sg, _) := int_kind_info k in
      let m := Z.shiftl 1 (8 * sz) in
      let u := Z.modulo v m in
      Some (signed_word sg u m)
  | _ => None
  end.

Definition integer_range (sg : c_sign) (bits : Z) : Z * Z :=
  match sg with
  | CSigned =>
      let lo := -(Z.shiftl 1 (bits - 1)) in
      (lo, -lo - 1)
  | CUnsigned => (0, Z.shiftl 1 bits - 1)
  end.

Definition const_truth (v : c_const_val) (t : c_type) : c_const_val :=
  match v with
  | CVUb => CVUb
  | CVInt n =>
      match float_fmt_of t with
      | Some k => CVInt (ieee_compare k ICNe n 0)
      | None => CVInt (if Z.eqb n 0 then 0 else 1)
      end
  end.

Definition const_convert (v0 : c_const_val) (from_t to_t : c_type)
  : option c_const_val :=
  match v0 with
  | CVUb => Some CVUb
  | CVInt v =>
      if c_type_eqb from_t to_t then Some (CVInt v)
      else match to_t with
      | TIntK IBool => Some (const_truth (CVInt v) from_t)
      | _ =>
          match from_t with
          | TIntK _ =>
              match to_t with
              | TIntK _ =>
                  match convert_int v to_t with Some w => Some (CVInt w) | None => None end
              | TFloatK _ =>
                  match float_fmt_of to_t with
                  | Some k => Some (CVInt (ieee_from_int k v))
                  | None => None
                  end
              | _ => None
              end
          | TFloatK _ =>
              match float_fmt_of from_t with
              | None => None
              | Some fk =>
                  match float_fmt_of to_t with
                  | Some tk => Some (CVInt (ieee_convert fk tk v))
                  | None =>
                      match int_info to_t with
                      | Some (sz, sg) =>
                          match ieee_to_int fk v with
                          | Some i =>
                              let '(lo, hi) := integer_range sg (8 * sz) in
                              if (lo <=? i) && (i <=? hi) then Some (CVInt i) else Some CVUb
                          | None => Some CVUb
                          end
                      | None => None
                      end
                  end
              end
          | _ => None
          end
      end
  end.

Definition fits_int_type (v : Z) (t : c_type) : bool :=
  match int_info t with
  | Some (sz, CSigned) => v <? Z.shiftl 1 (8 * sz - 1)
  | Some (sz, CUnsigned) => v <? Z.shiftl 1 (8 * sz)
  | None => false
  end.

Definition constant_types_for (rad : int_radix) (suf : int_suffix) : list c_type :=
  match rad with
  | RadDec =>
      match suf with
      | SufNone => [TInt; TLong; TLLong]
      | SufU => [TUInt; TULong; TULLong]
      | SufL => [TLong; TLLong]
      | SufUL => [TULong; TULLong]
      | SufLL => [TLLong]
      | SufULL => [TULLong]
      end
  | RadOther =>
      match suf with
      | SufNone => [TInt; TUInt; TLong; TULong; TLLong; TULLong]
      | SufU => [TUInt; TULong; TULLong]
      | SufL => [TLong; TULong; TLLong; TULLong]
      | SufUL => [TULong; TULLong]
      | SufLL => [TLLong; TULLong]
      | SufULL => [TULLong]
      end
  end.

Definition num_type (v : Z) (suf : int_suffix) (rad : int_radix) : c_type :=
  let fix pick (ts : list c_type) : c_type :=
    match ts with
    | [] => TULLong
    | t :: rest => if fits_int_type v t then t else pick rest
    end in
  pick (constant_types_for rad suf).

Definition env_int_type (env : c_type_env) (t0 : c_type) : option c_type :=
  if te_pp_mode env then
    match int_info t0 with
    | Some (_, CSigned) => Some TLong
    | Some (_, CUnsigned) => Some TULong
    | None => None
    end
  else Some t0.

Definition bitfield_promotion (t : c_type) (w : Z) : c_type :=
  match int_info t with
  | Some (_, CSigned) => if w <=? 32 then TInt else t
  | Some (_, CUnsigned) =>
      if w <? 32 then TInt
      else if w <=? 32 then TUInt
      else t
  | None => t
  end.

Definition float_literal_type_body (s : string) : c_type * list ascii :=
  let cs := list_ascii_of_string s in
  let fix split_last (xs acc : list ascii) : option (list ascii * ascii) :=
    match xs with
    | [] => None
    | [c] => Some (rev_append acc [], c)
    | c :: rest => split_last rest (c :: acc)
    end in
  match split_last cs [] with
  | Some (body, suf) =>
      if Ascii.eqb suf "f"%char || Ascii.eqb suf "F"%char then (TFloat, body)
      else if Ascii.eqb suf "l"%char || Ascii.eqb suf "L"%char then (TLDouble, body)
      else (TDouble, cs)
  | None => (TDouble, cs)
  end.

Definition float_literal (s : string) : option (Z * c_type) :=
  let '(t, digits) := float_literal_type_body s in
  match float_fmt_of t with
  | Some k =>
      match ieee_parse k digits with
      | Some bits => Some (bits, t)
      | None => None
      end
  | None => None
  end.

(** ## Keyword type combinations and enum underlying types *)

Fixpoint insert_str (s : string) (xs : list string) : list string :=
  match xs with
  | [] => [s]
  | h :: rest =>
      if string_ltb s h then s :: xs
      else h :: insert_str s rest
  end.

Definition sort_strs (xs : list string) : list string :=
  fold_left (fun acc s => insert_str s acc) xs [].

Definition str_list_eqb (xs ys : list string) : bool :=
  list_eqb String.eqb xs ys.

Definition keyword_combo (s : list string) : c_type :=
  if str_list_eqb s ["void"] then TVoid
  else if str_list_eqb s ["bool"] then TBool
  else if str_list_eqb s ["char"] then TChar
  else if str_list_eqb s ["char"; "signed"] then TSChar
  else if str_list_eqb s ["char"; "unsigned"] then TUChar
  else if str_list_eqb s ["short"] ||
          str_list_eqb s ["short"; "signed"] ||
          str_list_eqb s ["int"; "short"] ||
          str_list_eqb s ["int"; "short"; "signed"] then TShort
  else if str_list_eqb s ["short"; "unsigned"] ||
          str_list_eqb s ["int"; "short"; "unsigned"] then TUShort
  else if str_list_eqb s ["int"] ||
          str_list_eqb s ["signed"] ||
          str_list_eqb s ["int"; "signed"] then TInt
  else if str_list_eqb s ["unsigned"] ||
          str_list_eqb s ["int"; "unsigned"] then TUInt
  else if str_list_eqb s ["long"] ||
          str_list_eqb s ["long"; "signed"] ||
          str_list_eqb s ["int"; "long"] ||
          str_list_eqb s ["int"; "long"; "signed"] then TLong
  else if str_list_eqb s ["long"; "unsigned"] ||
          str_list_eqb s ["int"; "long"; "unsigned"] then TULong
  else if str_list_eqb s ["long"; "long"] ||
          str_list_eqb s ["long"; "long"; "signed"] ||
          str_list_eqb s ["int"; "long"; "long"] ||
          str_list_eqb s ["int"; "long"; "long"; "signed"] then TLLong
  else if str_list_eqb s ["long"; "long"; "unsigned"] ||
          str_list_eqb s ["int"; "long"; "long"; "unsigned"] then TULLong
  else if str_list_eqb s ["float"] then TFloat
  else if str_list_eqb s ["double"] then TDouble
  else if str_list_eqb s ["double"; "long"] then TLDouble
  else if str_list_eqb s ["complex"] ||
          str_list_eqb s ["complex"; "double"] then TStruct complex_double_id
  else if str_list_eqb s ["complex"; "float"] then TStruct complex_float_id
  else if str_list_eqb s ["complex"; "double"; "long"] then TStruct complex_ldouble_id
  else if str_in "complex" s then TBad "_Complex"
  else if str_in "int128" s then TBad "__int128"
  else if str_in "float16" s then TBad "_Float16"
  else if str_in "bf16" s then TBad "__bf16"
  else TBad "invalid type specifiers".

Definition keyword_type (kws : list string) : c_type :=
  match kws with
  | [] => TInt
  | _ => keyword_combo (sort_strs kws)
  end.

Definition min_max_Z (xs : list Z) : option (Z * Z) :=
  match xs with
  | [] => None
  | h :: rest =>
      Some (fold_left (fun '(lo, hi) x => (Z.min lo x, Z.max hi x)) rest (h, h))
  end.

Definition enum_underlying (vs : list Z) : c_type :=
  match min_max_Z vs with
  | None => TUInt
  | Some (lo, hi) =>
      if (0 <=? lo) && (hi <=? 4294967295) then TUInt
      else if (-2147483648 <=? lo) && (hi <=? 2147483647) then TInt
      else if 0 <=? lo then TULong
      else TLong
  end.

Definition packed_enum_underlying (vs : list Z) : c_type :=
  match min_max_Z vs with
  | None => TUChar
  | Some (lo, hi) =>
      if 0 <=? lo then
        if hi <=? 255 then TUChar
        else if hi <=? 65535 then TUShort
        else if hi <=? 4294967295 then TUInt
        else TULong
      else
        if (-128 <=? lo) && (hi <=? 127) then TSChar
        else if (-32768 <=? lo) && (hi <=? 32767) then TShort
        else if (-2147483648 <=? lo) && (hi <=? 2147483647) then TInt
        else TLong
  end.

(** ## Attribute token queries and machine modes *)

Definition attr_items (ts : list attr_tok) : list (list attr_tok) :=
  attribute_items ts.

Definition attr_unwrap (ts : list attr_tok) : list attr_tok :=
  match ts with
  | [AGroup inner] => inner
  | _ => ts
  end.

Definition attr_entries (ts : list attr_tok) : list (string * list attr_tok) :=
  let items := attr_items (attr_unwrap ts) in
  fold_right (fun item acc =>
    match item with
    | ATok (TId w) :: rest | ATok (TKw w) :: rest => (w, rest) :: acc
    | _ => acc
    end) [] items.

Definition has_attr_word (words : list string) (ts : list attr_tok) : bool :=
  existsb (fun '(w, _) => str_in w words) (attr_entries ts).

Definition packed_attr (ts : list attr_tok) : bool :=
  has_attr_word ["packed"; "__packed__"] ts.

Definition aligned_attr (ts : list attr_tok) : bool :=
  has_attr_word ["aligned"; "__aligned__"] ts.

Definition vector_attr (ts : list attr_tok) : bool :=
  has_attr_word ["vector_size"; "__vector_size__"; "ext_vector_type"] ts.

Definition transparent_attr (ts : list attr_tok) : bool :=
  has_attr_word ["transparent_union"; "__transparent_union__"] ts.

Definition address_space_attr (ts : list attr_tok) : bool :=
  has_attr_word ["address_space"; "__address_space__"] ts.

Definition layout_attr_spec (sp : c_spec) : bool :=
  match sp with
  | SpAlignasType _ | SpAlignasExpr _ => true
  | SpAttr ts =>
      has_attr_word ["aligned"; "__aligned__"; "packed"; "__packed__"] ts
  | _ => false
  end.

Definition mode_attr (ts : list attr_tok) : option string :=
  let fix find_mode (es : list (string * list attr_tok)) : option string :=
    match es with
    | [] => None
    | (w, rest) :: more =>
        if String.eqb w "mode" || String.eqb w "__mode__" then
          match rest with
          | AGroup [ATok (TId m0)] :: _ => Some (strip_dunders m0)
          | _ => find_mode more
          end
        else find_mode more
    end in
  find_mode (attr_entries ts).

Definition mode_bytes (m : string) : option Z :=
  if String.eqb m "QI" || String.eqb m "byte" then Some 1
  else if String.eqb m "HI" then Some 2
  else if String.eqb m "SI" then Some 4
  else if String.eqb m "DI" || String.eqb m "word" ||
          String.eqb m "unwind_word" || String.eqb m "pointer" then Some 8
  else if String.eqb m "TI" then Some 16
  else None.

Definition float_mode (m : string) : option c_type :=
  if String.eqb m "SF" then Some TFloat
  else if String.eqb m "DF" then Some TDouble
  else None.

Definition int_type_of_bytes_sign (bytes : Z) (sg : c_sign) : option c_type :=
  match sg with
  | CSigned =>
      if Z.eqb bytes 1 then Some TSChar
      else if Z.eqb bytes 2 then Some TShort
      else if Z.eqb bytes 4 then Some TInt
      else if Z.eqb bytes 8 then Some TLong
      else None
  | CUnsigned =>
      if Z.eqb bytes 1 then Some TUChar
      else if Z.eqb bytes 2 then Some TUShort
      else if Z.eqb bytes 4 then Some TUInt
      else if Z.eqb bytes 8 then Some TULong
      else None
  end.

Fixpoint mode_type (t0 : c_type) (m : string) : c_type :=
  match t0 with
  | TBad why => TBad why
  | TQual qs inner =>
      match mode_type inner m with
      | TBad w => TBad w
      | t1 => TQual qs t1
      end
  | TIntK IBool => TBad ("mode " ++ m ++ " on this type")
  | TIntK _ =>
      match int_info t0, mode_bytes m with
      | Some (_, sg), Some bytes =>
          match int_type_of_bytes_sign bytes sg with
          | Some t1 => t1
          | None => TBad "mode TI (__int128)"
          end
      | _, _ => TBad ("mode " ++ m ++ " on this type")
      end
  | TFloatK FFloat | TFloatK FDouble =>
      match float_mode m with
      | Some tf => tf
      | None => TBad ("mode " ++ m ++ " on this type")
      end
  | _ => TBad ("mode " ++ m ++ " on this type")
  end.

Fixpoint flat_tok_aux (t : attr_tok) (acc : list token) : list token :=
  let loc := Loc "attr" 0 in
  let fix go (xs : list attr_tok) (a : list token) : list token :=
    match xs with
    | [] => a
    | y :: rest => go rest (flat_tok_aux y a)
    end in
  match t with
  | AGroup inner =>
      mkTok (TPunct ")") loc :: go inner (mkTok (TPunct "(") loc :: acc)
  | ATok k => mkTok k loc :: acc
  end.

Definition flat_tokens (ts : list attr_tok) : list token :=
  rev_append (fold_left (fun acc t => flat_tok_aux t acc) ts []) [].

Inductive align_req : Type :=
| ARValue (a : Z)
| ARType (tn : c_type_name)
| ARExpr (e : c_expr)
| ARAttr (ts : list attr_tok).

Fixpoint alignment_requests_loop (specs : list c_spec)
  (reqs : list align_req) (kept : list c_spec) : list align_req * list c_spec :=
  match specs with
  | [] => (rev_append reqs [], rev_append kept [])
  | SpAlignasType tn :: rest =>
      alignment_requests_loop rest (ARType tn :: reqs) kept
  | SpAlignasExpr e :: rest =>
      alignment_requests_loop rest (ARExpr e :: reqs) kept
  | SpAttr [AGroup inner] :: rest =>
      if aligned_attr inner then
        let items := attr_items inner in
        let aligned_items := filter aligned_attr items in
        let other_items := filter (fun it => negb (aligned_attr it)) items in
        let reqs1 := fold_left (fun acc it => ARAttr [AGroup it] :: acc) aligned_items reqs in
        let kept1 :=
          match other_items with
          | [] => kept
          | _ => SpAttr [AGroup (join_attr_items other_items)] :: kept
          end in
        alignment_requests_loop rest reqs1 kept1
      else
        alignment_requests_loop rest reqs (SpAttr [AGroup inner] :: kept)
  | SpAttr ts :: rest =>
      if aligned_attr ts then
        alignment_requests_loop rest (ARAttr ts :: reqs) kept
      else
        alignment_requests_loop rest reqs (SpAttr ts :: kept)
  | sp :: rest =>
      alignment_requests_loop rest reqs (sp :: kept)
  end.

Definition alignment_requests (specs : list c_spec) : list align_req * list c_spec :=
  alignment_requests_loop specs [] [].

Definition is_bare_packed_item (item : list attr_tok) : bool :=
  match item with
  | [ATok (TId w)] | [ATok (TKw w)] =>
      String.eqb w "packed" || String.eqb w "__packed__"
  | _ => false
  end.

Fixpoint member_packing_loop (specs : list c_spec) (packed : bool) (kept : list c_spec)
  : list c_spec * bool :=
  match specs with
  | [] => (rev_append kept [], packed)
  | SpAttr [AGroup inner] :: rest =>
      let items := attr_items inner in
      if existsb is_bare_packed_item items then
        let others := filter (fun it => negb (is_bare_packed_item it)) items in
        let kept1 :=
          match others with
          | [] => kept
          | _ => SpAttr [AGroup (join_attr_items others)] :: kept
          end in
        member_packing_loop rest true kept1
      else
        member_packing_loop rest packed (SpAttr [AGroup inner] :: kept)
  | sp :: rest =>
      member_packing_loop rest packed (sp :: kept)
  end.

Definition member_packing (specs : list c_spec) : list c_spec * bool :=
  member_packing_loop specs false [].

Definition decl_storage (specs : list c_spec) : c_storage :=
  let fix find_non_tl (ss : list c_spec) : c_storage :=
    match ss with
    | [] => StNone
    | SpStorage s :: rest =>
        if String.eqb s "thread_local" then find_non_tl rest
        else if String.eqb s "typedef" then StTypedef
        else if String.eqb s "static" then StStatic
        else if String.eqb s "extern" then StExtern
        else if String.eqb s "auto" then StAuto
        else if String.eqb s "register" then StRegister
        else find_non_tl rest
    | _ :: rest => find_non_tl rest
    end in
  let has_tl :=
    existsb (fun sp =>
      match sp with SpStorage s => String.eqb s "thread_local" | _ => false end) specs in
  let base := find_non_tl specs in
  if has_tl then StThreadLocal base else base.

Definition is_pow2 (n : Z) : bool :=
  (0 <? n) && Z.eqb (Z.land n (n - 1)) 0.

Definition max_alignment : Z := 4096.

(** ## Sizes, alignments, member lookup, and compatibility

    These queries inspect an existing [c_type_env] without allocating new
    tags or modifying scopes. *)

Fixpoint type_size_align_aux (fuel : nat) (t : c_type) (env : c_type_env)
  : c_tr (Z * Z) :=
  match fuel with
  | O => TErr (TEBad "incomplete")
  | S f =>
      match t with
      | TQual _ inner => type_size_align_aux f inner env
      | TIntK k => let '(sz, _, _) := int_kind_info k in TOk (sz, sz)
      | TFloatK FFloat => TOk (4, 4)
      | TFloatK FDouble => TOk (8, 8)
      | TFloatK FLDouble => TOk (16, 16)
      | TPtr _ => TOk (8, 8)
      | TAtomic _ p => TOk (p, p)
      | TArray elem len =>
          match len with
          | ALConst n =>
              match type_size_align_aux f elem env with
              | TOk (esz, eal) => TOk (esz * n, eal)
              | TErr e => TErr e
              end
          | ALNone => TErr (TEBad "incomplete")
          | _ => TErr (TEBad "variable length array")
          end
      | TVec elem n a =>
          match type_size_align_aux f elem env with
          | TOk (esz, _) => TOk (esz * n, a)
          | TErr e => TErr e
          end
      | TStruct id | TUnion id =>
          match lookup_su_def env id with
          | Some (SUDef _ _ sz al) => TOk (sz, al)
          | Some (SUPartial why _) | Some (SUBad why) => TErr (TEBad why)
          | _ => TErr (TEBad "incomplete")
          end
      | TBad why => TErr (TEBad why)
      | TVoid | TFunc _ _ _ => TErr (TEBad "incomplete")
      end
  end.

Definition type_size_align (t : c_type) (env : c_type_env) : c_tr (Z * Z) :=
  type_size_align_aux (Z.to_nat 256) t env.

Definition complete_type (t : c_type) (env : c_type_env) : bool :=
  match type_size_align t env with TOk _ => true | TErr _ => false end.

Definition sizeof_size (t : c_type) (env : c_type_env) : c_tr Z :=
  match unqualified t with
  | TVoid | TFunc _ _ _ => TOk 1
  | _ =>
      match type_size_align t env with
      | TOk (sz, _) => TOk sz
      | TErr e => TErr e
      end
  end.

Definition arith_size (elem : c_type) (env : c_type_env) : c_tr Z :=
  match unqualified elem with
  | TVoid => TOk 1
  | _ =>
      match type_size_align elem env with
      | TOk (sz, _) => TOk sz
      | TErr e => TErr e
      end
  end.

Fixpoint holds_ref_aux (fuel : nat) (t : c_type) (env : c_type_env) : bool :=
  match fuel with
  | O => false
  | S f =>
      match t with
      | TPtr _ | TVec _ _ _ => true
      | TArray elem _ | TAtomic elem _ | TQual _ elem => holds_ref_aux f elem env
      | TStruct id | TUnion id =>
          match lookup_su_def env id with
          | Some (SUDef _ ms _ _) =>
              existsb (fun m => holds_ref_aux f (ml_type m) env) ms
          | _ => false
          end
      | _ => false
      end
  end.

Definition holds_ref (t : c_type) (env : c_type_env) : bool :=
  holds_ref_aux (Z.to_nat 128) t env.

Definition atomic_su_type (s : c_type) (env : c_type_env) : option c_type :=
  match s with
  | TStruct _ | TUnion _ =>
      match type_size_align s env with
      | TOk (sz, _) =>
          let p :=
            if sz <=? 1 then Some 1
            else if sz <=? 2 then Some 2
            else if sz <=? 4 then Some 4
            else if sz <=? 8 then Some 8
            else None in
          match p with
          | Some pw => if negb (holds_ref s env) then Some (TAtomic s pw) else None
          | None => None
          end
      | TErr _ => None
      end
  | _ => None
  end.

Definition su_known_members (d : su_def) : option (list c_member_layout) :=
  match d with
  | SUDef _ ms _ _ | SUPartial _ ms => Some ms
  | _ => None
  end.

Fixpoint member_layout_aux (fuel : nat) (su : c_type) (name : string) (env : c_type_env)
  : option (c_type * Z * c_member_bits) :=
  match fuel with
  | O => None
  | S f =>
      let oid := match su with TStruct id | TUnion id => Some id | _ => None end in
      match oid with
      | None => None
      | Some id =>
          match lookup_su_def env id with
          | None => None
          | Some d =>
              match su_known_members d with
              | None => None
              | Some ms =>
                  let fix find_direct (xs : list c_member_layout) :=
                    match xs with
                    | [] => None
                    | m :: rest =>
                        match ml_name m with
                        | Some nm =>
                            if String.eqb nm name then Some (ml_type m, ml_off m, ml_bits m)
                            else find_direct rest
                        | None => find_direct rest
                        end
                    end in
                  match find_direct ms with
                  | Some res => Some res
                  | None =>
                      let fix find_anon (xs : list c_member_layout) :=
                        match xs with
                        | [] => None
                        | m :: rest =>
                            match ml_name m with
                            | None =>
                                match ml_bits m with
                                | MBNone =>
                                    match member_layout_aux f (ml_type m) name env with
                                    | Some (mt, ioff, bits) => Some (mt, ml_off m + ioff, bits)
                                    | None => find_anon rest
                                    end
                                | MBBits _ _ => find_anon rest
                                end
                            | Some _ => find_anon rest
                            end
                        end in
                      find_anon ms
                  end
              end
          end
      end
  end.

Definition member_layout (su : c_type) (name : string) (env : c_type_env)
  : option (c_type * Z * c_member_bits) :=
  member_layout_aux (Z.to_nat 64) su name env.

Definition member_type_offset (su : c_type) (name : string) (env : c_type_env)
  : option (c_type * Z) :=
  match member_layout su name env with
  | Some (t, off, MBNone) => Some (t, off)
  | _ => None
  end.

Fixpoint member_type_aux (fuel : nat) (su : c_type) (name : string) (env : c_type_env)
  : option c_type :=
  match fuel with
  | O => None
  | S f =>
      match su with
      | TQual qs inner =>
          match member_type_aux f inner name env with
          | Some t0 => Some (qualify qs t0)
          | None => None
          end
      | TStruct id | TUnion id =>
          match lookup_qmembers env id with
          | Some qms =>
              let fix find_direct (xs : list (option string * c_type)) :=
                match xs with
                | [] => None
                | (Some nm, t) :: rest =>
                    if String.eqb nm name then Some t else find_direct rest
                | (None, _) :: rest => find_direct rest
                end in
              match find_direct qms with
              | Some t => Some t
              | None =>
                  let fix find_anon (xs : list (option string * c_type)) :=
                    match xs with
                    | [] => None
                    | (None, anon_t) :: rest =>
                        match member_type_aux f anon_t name env with
                        | Some t => Some t
                        | None => find_anon rest
                        end
                    | _ :: rest => find_anon rest
                    end in
                  find_anon qms
              end
          | None =>
              match member_type_offset su name env with
              | Some (t, _) => Some t
              | None => None
              end
          end
      | _ => None
      end
  end.

Definition member_type (su : c_type) (name : string) (env : c_type_env) : option c_type :=
  member_type_aux (Z.to_nat 64) su name env.

Definition transparent_union (t : c_type) (env : c_type_env) : option (list c_type) :=
  match t with
  | TUnion id =>
      if negb (is_transparent_su env id) then None
      else
        match lookup_su_def env id with
        | Some (SUDef KUnion fields _ _) =>
            let ms := fold_right (fun m acc =>
              match ml_bits m with MBNone => ml_type m :: acc | _ => acc end) [] fields in
            match ms with
            | [] => None
            | first :: _ =>
                if float_type first then None
                else
                  match type_size_align first env with
                  | TErr _ => None
                  | TOk (sz, al) =>
                      let ok := forallb (fun m =>
                        match type_size_align m env with
                        | TOk (msz, mal) => Z.eqb msz sz && Z.eqb mal al
                        | TErr _ => false
                        end) ms in
                      if ok then Some ms else None
                  end
            end
        | _ => None
        end
  | _ => None
  end.

Fixpoint unaligned_type_aux (fuel : nat) (t : c_type) (env : c_type_env) : bool :=
  match fuel with
  | O => false
  | S f =>
      match t with
      | TStruct id | TUnion id =>
          match lookup_su_def env id with
          | Some (SUDef _ ms _ _) =>
              existsb (fun m =>
                match ml_bits m with
                | MBNone =>
                    match type_size_align (ml_type m) env with
                    | TOk (_, al) =>
                        negb (Z.eqb (Z.modulo (ml_off m) al) 0) ||
                        unaligned_type_aux f (ml_type m) env
                    | TErr _ => false
                    end
                | MBBits _ _ => false
                end) ms
          | _ => false
          end
      | TArray elem _ => unaligned_type_aux f elem env
      | _ => false
      end
  end.

Definition unaligned_type (t : c_type) (env : c_type_env) : bool :=
  unaligned_type_aux (Z.to_nat 64) t env.

(** ## Compatible and composite types *)

Definition extract_enum_qual (qs : list c_qual) : option (enum_key_t * list c_qual) :=
  let fix go (xs acc : list c_qual) :=
    match xs with
    | [] => None
    | QEnum k :: rest => Some (k, rev_append acc rest)
    | q :: rest => go rest (q :: acc)
    end in
  go qs [].

Definition enum_marked (t : c_type) : option (enum_key_t * c_type) :=
  match t with
  | TQual qs inner =>
      match extract_enum_qual qs with
      | Some (k, rest) => Some (k, qualify rest inner)
      | None => None
      end
  | _ => None
  end.

Definition enum_completed (t0 u0 : c_type) : c_type * c_type :=
  match t0 with
  | TIntK IUInt => (u0, u0)
  | _ => match u0 with TIntK IUInt => (t0, t0) | _ => (t0, u0) end
  end.

Definition composite_size (n m : c_arr_len) : option c_arr_len :=
  match n with
  | ALNone => Some m
  | _ =>
      match m with
      | ALNone => Some n
      | _ =>
          if variable_size n then Some m
          else if variable_size m then Some n
          else if c_arr_len_eqb n m then Some n
          else None
      end
  end.

Fixpoint composite_type_aux (fuel : nat) (t u : c_type) (oenv : option c_type_env)
  : option c_type :=
  match fuel with
  | O => None
  | S f =>
      if c_type_eqb t u then Some t
      else
        match enum_marked t with
        | Some (k, t0) =>
            match enum_marked u with
            | Some (l, u0) =>
                if enum_key_eqb k l then
                  let '(t1, u1) := enum_completed t0 u0 in
                  composite_type_aux f t1 u1 oenv
                else None
            | None => composite_type_aux f t0 u oenv
            end
        | None =>
            match enum_marked u with
            | Some (_, u1) => composite_type_aux f t u1 oenv
            | None =>
                match t with
                | TQual q1 t1 =>
                    match u with
                    | TQual q2 u1 =>
                        if list_eqb c_qual_eqb q1 q2 then
                          match composite_type_aux f t1 u1 oenv with
                          | Some c => Some (TQual q1 c)
                          | None => None
                          end
                        else None
                    | _ => None
                    end
                | TPtr t1 =>
                    match u with
                    | TPtr u1 =>
                        match composite_type_aux f t1 u1 oenv with
                        | Some c => Some (TPtr c)
                        | None => None
                        end
                    | _ => None
                    end
                | TArray t1 n =>
                    match u with
                    | TArray u1 m =>
                        match composite_size n m, composite_type_aux f t1 u1 oenv with
                        | Some k, Some c => Some (TArray c k)
                        | _, _ => None
                        end
                    | _ => None
                    end
                | TFunc r1 ps1 v1 =>
                    match u with
                    | TFunc r2 ps2 v2 =>
                        if negb (Bool.eqb v1 v2) then None
                        else
                          match composite_type_aux f r1 r2 oenv with
                          | None => None
                          | Some rc =>
                              match ps1 with
                              | None => Some (TFunc rc ps2 v1)
                              | Some xs =>
                                  match ps2 with
                                  | None => Some (TFunc rc ps1 v1)
                                  | Some ys =>
                                      let strip_top (x : c_type) :=
                                        match x with TQual _ x1 => x1 | _ => x end in
                                      let comp_param (p q : c_type) : option c_type :=
                                        let p1 := strip_top p in
                                        let q1 := strip_top q in
                                        match composite_type_aux f p1 q1 oenv with
                                        | Some c0 => Some c0
                                        | None =>
                                            match oenv with
                                            | None => None
                                            | Some env =>
                                                let try_tu (tu other : c_type) :=
                                                  match transparent_union tu env with
                                                  | None => None
                                                  | Some ms =>
                                                      let o1 := unqualified other in
                                                      let fix find_m (zs : list c_type) :=
                                                        match zs with
                                                        | [] => None
                                                        | m :: more =>
                                                            match composite_type_aux f m o1 oenv with
                                                            | Some c => Some c
                                                            | None => find_m more
                                                            end
                                                        end in
                                                      find_m ms
                                                  end in
                                                match try_tu p1 q1 with
                                                | Some c => Some c
                                                | None => try_tu q1 p1
                                                end
                                            end
                                        end in
                                      let fix map_params (a b : list c_type) (acc : list c_type) :=
                                        match a with
                                        | [] => match b with [] => Some (rev_append acc []) | _ => None end
                                        | x :: rx =>
                                            match b with
                                            | y :: ry =>
                                                match comp_param x y with
                                                | Some c => map_params rx ry (c :: acc)
                                                | None => None
                                                end
                                            | [] => None
                                            end
                                        end in
                                      match map_params xs ys [] with
                                      | Some cs => Some (TFunc rc (Some cs) v1)
                                      | None => None
                                      end
                                  end
                              end
                          end
                    | _ => None
                    end
                | _ => None
                end
            end
        end
  end.

Definition composite_type (t u : c_type) (oenv : option c_type_env) : option c_type :=
  composite_type_aux (Z.to_nat 128) t u oenv.

Definition compatible_type (t u : c_type) (oenv : option c_type_env) : bool :=
  match composite_type t u oenv with Some _ => true | None => false end.

(** ## Operator typing, assignments, casts, and conditional arms *)

Definition complex_or_arithmetic (a b : c_type) : bool :=
  let ca := match complex_type a with Some _ => true | None => false end in
  let cb := match complex_type b with Some _ => true | None => false end in
  (ca || cb) && (ca || arithmetic_type a) && (cb || arithmetic_type b).

Definition complex_real (t : c_type) : option c_type :=
  match complex_type t with
  | Some f => Some f
  | None => if arithmetic_type t then Some t else None
  end.

Definition complex_side (t r : c_type) : option c_type :=
  match complex_type t with
  | Some _ => complex_of r
  | None => Some r
  end.

Definition vector_bytes (e : c_type) (n : Z) : option Z :=
  match e with
  | TIntK k => let '(sz, _, _) := int_kind_info k in Some (sz * n)
  | TFloatK FFloat => Some (4 * n)
  | TFloatK FDouble => Some (8 * n)
  | _ => None
  end.

Definition unary_operand (op : c_unop) (t0 : c_type) : option c_type :=
  match t0 with
  | TVec e _ _ =>
      match op with
      | UPlus | UNeg => Some t0
      | UBnot => if int_type e then Some t0 else None
      | _ => None
      end
  | _ =>
      match complex_type t0 with
      | Some _ =>
          match op with
          | UPlus | UNeg | UBnot => Some (unqualified t0)
          | _ => None
          end
      | None =>
          match op with
          | UPlus | UNeg =>
              if arithmetic_type t0 then Some (integer_promotion t0) else None
          | UBnot =>
              if int_type t0 then Some (integer_promotion t0) else None
          | UNot =>
              if scalar_type t0 then Some TInt else None
          | _ => None
          end
      end
  end.

Definition is_comparison_op (op : c_binop) : bool :=
  match op with BEq | BNe | BLt | BGt | BLe | BGe => true | _ => false end.

Definition is_int_arith_op (op : c_binop) : bool :=
  match op with BMod | BAnd | BOr | BXor => true | _ => false end.

Definition is_general_arith_op (op : c_binop) : bool :=
  match op with BAdd | BSub | BMul | BDiv => true | _ => false end.

Definition is_shift_op (op : c_binop) : bool :=
  match op with BShl | BShr => true | _ => false end.

Definition vector_scalar_ok (e s : c_type) : bool :=
  if int_type e then int_type s else arithmetic_type s.

Definition vector_operands (op : c_binop) (ta tb : c_type) : option (c_type * c_type) :=
  let oc :=
    match ta with
    | TVec e1 n1 _ =>
        match tb with
        | TVec e2 n2 _ => if c_type_eqb e1 e2 && Z.eqb n1 n2 then Some ta else None
        | _ => if vector_scalar_ok e1 tb then Some ta else None
        end
    | _ =>
        match tb with
        | TVec e2 _ _ => if vector_scalar_ok e2 ta then Some tb else None
        | _ => None
        end
    end in
  match oc with
  | Some (TVec e n a as c) =>
      if is_comparison_op op then
        let ose :=
          match vector_bytes e 1 with
          | Some 1 => Some TSChar
          | Some 2 => Some TShort
          | Some 4 => Some TInt
          | Some 8 => Some TLLong
          | _ => None
          end in
        match ose with
        | Some se => Some (c, TVec se n a)
        | None => None
        end
      else if is_int_arith_op op then
        if int_type e then Some (c, c) else None
      else if is_general_arith_op op then
        if arithmetic_type e then Some (c, c) else None
      else if is_shift_op op then
        if int_type e then Some (c, c) else None
      else None
  | _ => None
  end.

Definition is_vec_type (t : c_type) : bool :=
  match t with TVec _ _ _ => true | _ => false end.

Definition is_ptr_type (t : c_type) : bool :=
  match t with TPtr _ => true | _ => false end.

Definition is_su_type (t : c_type) : bool :=
  match t with TStruct _ | TUnion _ => true | _ => false end.

Definition is_func_type (t : c_type) : bool :=
  match t with TFunc _ _ _ => true | _ => false end.

Definition binary_operands (op : c_binop) (ta tb : c_type)
  : option (c_type * c_type * c_type) :=
  if is_vec_type ta || is_vec_type tb then
    match vector_operands op ta tb with
    | Some (c, t) => Some (c, c, t)
    | None => None
    end
  else
    let is_cx := match complex_type ta with Some _ => true | None =>
                 match complex_type tb with Some _ => true | None => false end end in
    if is_cx then
      match op with
      | BAdd | BSub | BMul | BDiv | BEq | BNe =>
          match complex_real ta, complex_real tb with
          | Some ra, Some rb =>
              match usual_arith_conversion ra rb with
              | Some r =>
                  match complex_side ta r, complex_side tb r with
                  | Some ca, Some cb =>
                      match op with
                      | BEq | BNe => Some (ca, cb, TInt)
                      | _ =>
                          match complex_of r with
                          | Some t => Some (ca, cb, t)
                          | None => None
                          end
                      end
                  | _, _ => None
                  end
              | None => None
              end
          | _, _ => None
          end
      | _ => None
      end
    else if is_shift_op op then
      if int_type ta && int_type tb then
        let ca := integer_promotion ta in
        let cb := integer_promotion tb in
        Some (ca, cb, ca)
      else None
    else
      let dom_ok :=
        if is_int_arith_op op then int_type ta && int_type tb
        else if is_general_arith_op op || is_comparison_op op then
          arithmetic_type ta && arithmetic_type tb
        else false in
      if dom_ok then
        match usual_arith_conversion ta tb with
        | Some c =>
            let res := if is_comparison_op op then TInt else c in
            Some (c, c, res)
        | None => None
        end
      else
        match op with
        | BAdd =>
            match ta with
            | TPtr p => if int_type tb then Some (TPtr p, TLong, TPtr p) else None
            | _ =>
                match tb with
                | TPtr p => if int_type ta then Some (TLong, TPtr p, TPtr p) else None
                | _ => None
                end
            end
        | BSub =>
            match ta with
            | TPtr p =>
                match tb with
                | TPtr _ => Some (TPtr p, TPtr p, TLong)
                | _ => if int_type tb then Some (TPtr p, TLong, TPtr p) else None
                end
            | _ => None
            end
        | _ =>
            if is_comparison_op op && (is_ptr_type ta || is_ptr_type tb) then
              Some (TULong, TULong, TInt)
            else None
        end.

Definition expression_binary_type (op : c_binop) (ta tb : c_type) : option c_type :=
  match op with
  | BLand | BLor =>
      if scalar_type ta && scalar_type tb then Some TInt else None
  | _ =>
      match binary_operands op ta tb with
      | Some (_, _, t) => Some t
      | None => None
      end
  end.

Definition castable (from_t to_t : c_type) : bool :=
  match to_t with
  | TVoid => true
  | _ =>
      if arithmetic_type from_t && arithmetic_type to_t then true
      else if complex_or_arithmetic from_t to_t then true
      else if is_ptr_type from_t then is_ptr_type to_t || int_type to_t
      else if is_ptr_type to_t then int_type from_t
      else if is_su_type from_t then c_type_eqb from_t to_t
      else
        match from_t with
        | TVec e n _ =>
            match to_t with
            | TVec f m _ =>
                match vector_bytes e n, vector_bytes f m with
                | Some b1, Some b2 => Z.eqb b1 b2
                | _, _ => false
                end
            | _ => false
            end
        | _ => false
        end
  end.

Definition assignable (from_t : c_type) (is_null : bool) (to_t : c_type)
  (oenv : option c_type_env) : bool :=
  if arithmetic_type from_t && arithmetic_type to_t then true
  else if complex_or_arithmetic from_t to_t then true
  else if c_type_eqb from_t to_t then true
  else
    match to_t with
    | TAtomic s1 _ => c_type_eqb from_t s1
    | TVec f m _ =>
        match from_t with
        | TVec e n _ =>
            (c_type_eqb e f && Z.eqb n m) ||
            (int_type e && int_type f &&
             match vector_bytes e n, vector_bytes f m with
             | Some b1, Some b2 => Z.eqb b1 b2
             | _, _ => false
             end)
        | _ => false
        end
    | TIntK IBool => is_ptr_type from_t
    | TPtr b =>
        if is_null then true
        else
          match from_t with
          | TPtr a =>
              if is_func_type a && is_func_type b then compatible_type a b oenv
              else true
          | _ => false
          end
    | _ => false
    end.

Definition member_takes (m t : c_type) (is_null : bool) (env : c_type_env) : bool :=
  match m with
  | TPtr a =>
      if is_null then true
      else if c_type_eqb m t then true
      else
        match t with
        | TPtr TVoid => true
        | TPtr b =>
            match a with
            | TVoid => true
            | _ => compatible_type a b (Some env)
            end
        | _ => false
        end
  | _ =>
      c_type_eqb m t || (arithmetic_type m && arithmetic_type t)
  end.

Definition transparent_member (param t : c_type) (is_null : bool) (env : c_type_env)
  : option c_type :=
  match transparent_union param env with
  | None => None
  | Some ms =>
      let fix find_m (xs : list c_type) :=
        match xs with
        | [] => None
        | m :: rest => if member_takes m t is_null env then Some m else find_m rest
        end in
      find_m ms
  end.

Definition parameter_accepts (p t : c_type) (is_null : bool) (env : c_type_env) : bool :=
  assignable t is_null p (Some env) ||
  (negb (c_type_eqb t p) &&
   match transparent_member p t is_null env with Some _ => true | None => false end).

Definition union_cast_member (u t : c_type) (env : c_type_env) : option string :=
  match u with
  | TUnion id =>
      match lookup_su_def env id with
      | Some (SUDef KUnion fields _ _) =>
          let fix find_f (xs : list c_member_layout) :=
            match xs with
            | [] => None
            | m :: rest =>
                match ml_name m with
                | Some nm =>
                    match ml_bits m with
                    | MBNone =>
                        if compatible_type (ml_type m) t None then Some nm
                        else find_f rest
                    | MBBits _ _ => find_f rest
                    end
                | None => find_f rest
                end
            end in
          find_f fields
      | _ => None
      end
  | _ => None
  end.

Definition bit_castable (from_t to_t : c_type) (env : c_type_env) : bool :=
  match to_t with
  | TArray _ _ | TFunc _ _ _ | TVoid => false
  | _ =>
      match type_size_align from_t env, type_size_align to_t env with
      | TOk (s1, _), TOk (s2, _) => Z.eqb s1 s2
      | _, _ => false
      end
  end.

Definition target_quals (t : c_type) : list c_qual * c_type :=
  match t with
  | TQual qs u => (qs, u)
  | u => ([], u)
  end.

Definition pointed_type (a b : c_type) (qs : list c_qual) : c_type :=
  let is_v (x : c_type) := match x with TVoid => true | _ => false end in
  if is_v a || is_v b then qualify qs TVoid
  else
    match composite_type a b None with
    | Some c => qualify qs c
    | None => TVoid
    end.

Definition arms_type (ta : c_type) (na : bool) (tb : c_type) (nb : bool)
  : option c_type :=
  if arithmetic_type ta && arithmetic_type tb then
    usual_arith_conversion ta tb
  else if complex_or_arithmetic ta tb then
    match complex_real ta, complex_real tb with
    | Some ra, Some rb =>
        match usual_arith_conversion ra rb with
        | Some r => complex_of r
        | None => None
        end
    | _, _ => None
    end
  else
    let is_v (x : c_type) := match x with TVoid => true | _ => false end in
    if is_v ta || is_v tb then Some TVoid
    else if is_su_type ta then
      if c_type_eqb ta tb then Some ta else None
    else
      match ta with
      | TPtr p =>
          if nb then Some (TPtr p)
          else match tb with
          | TPtr b =>
              if na then Some (TPtr b)
              else
                let '(qa, a1) := target_quals p in
                let '(qb, b1) := target_quals b in
                Some (TPtr (pointed_type a1 b1 (app qa qb)))
          | _ => if int_type tb then Some (TPtr p) else None
          end
      | _ =>
          match tb with
          | TPtr p => if na || int_type ta then Some (TPtr p) else None
          | _ => None
          end
      end.

(** ## Typed tree accessors and modifiability *)

Definition tree_cat (x : c_typed_node) : c_node_cat :=
  match x with TNode c _ _ => c end.

Definition tree_type (x : c_typed_node) : c_type :=
  match x with TNode _ t _ => t end.

Definition tree_form (x : c_typed_node) : c_typed_form :=
  match x with TNode _ _ f => f end.

Definition lowered_node_type (x : c_typed_node) : c_type :=
  unqualified (tree_type x).

Definition value_node (x : c_typed_node) : c_typed_node :=
  match x with
  | TNode cat t f =>
      match cat with
      | CatObj =>
          match f with
          | TFBitfield _ _ w =>
              let v := bitfield_promotion (value_type t) w in
              TNode CatVal v (TFLoad x)
          | _ =>
              if array_type t then TNode CatVal (value_type t) (TFDecay x)
              else TNode CatVal (value_type t) (TFLoad x)
          end
      | CatFun => TNode CatVal (TPtr t) (TFDecay x)
      | CatVal => TNode CatVal (value_type t) f
      end
  end.

Fixpoint const_within_aux (fuel : nat) (t : c_type) (env : c_type_env) : bool :=
  match fuel with
  | O => false
  | S f =>
      match t with
      | TQual qs inner => has_qual QConst qs || const_within_aux f inner env
      | TArray elem _ => const_within_aux f elem env
      | TStruct id | TUnion id =>
          match lookup_qmembers env id with
          | Some ms => existsb (fun '(_, mt) => const_within_aux f mt env) ms
          | None => false
          end
      | _ => false
      end
  end.

Fixpoint modifiable_type (t : c_type) (env : c_type_env) : bool :=
  match t with
  | TQual qs inner => negb (has_qual QConst qs) && modifiable_type inner env
  | TArray _ _ | TVoid => false
  | _ => negb (const_within_aux (Z.to_nat 64) t env)
  end.

Definition modifiable (x : c_typed_node) (env : c_type_env) : bool :=
  match x with
  | TNode CatObj t _ => modifiable_type t env
  | _ => false
  end.

Fixpoint reflected_shape (rt t : c_type) : c_type :=
  match rt with
  | TQual qs r => TQual qs (reflected_shape r t)
  | TArray r _ =>
      match t with
      | TArray elem n => TArray (reflected_shape r elem) n
      | _ => rt
      end
  | TPtr r =>
      match t with
      | TPtr elem => if vm_type elem then TPtr (reflected_shape r elem) else rt
      | _ => rt
      end
  | _ => rt
  end.

Fixpoint underaligned_member_aux (fuel : nat) (x : c_typed_node)
  (env : c_type_env) (w : Z) : option string :=
  match fuel with
  | O => None
  | S f =>
      match x with
      | TNode CatObj _ (TFMember xs field) =>
          let su := unqualified (tree_type xs) in
          let too_small :=
            match type_size_align su env with
            | TOk (_, a) => a <? w
            | TErr _ => false
            end in
          if too_small then Some field
          else
            match member_layout su field env with
            | Some (_, off, _) =>
                if negb (Z.eqb (Z.modulo off w) 0) then Some field
                else underaligned_member_aux f xs env w
            | None => underaligned_member_aux f xs env w
            end
      | _ => None
      end
  end.

Definition underaligned_member (x : c_typed_node) (env : c_type_env) (w : Z)
  : option string :=
  underaligned_member_aux (Z.to_nat 64) x env w.

Fixpoint member_alignment_node_aux (fuel : nat) (x : c_typed_node)
  (env : c_type_env) : option Z :=
  match fuel with
  | O => None
  | S f =>
      match x with
      | TNode CatObj _ (TFMember xs field) =>
          let su := unqualified (tree_type xs) in
          match type_size_align su env with
          | TOk (_, sa) =>
              let b := match member_alignment_node_aux f xs env with
                       | Some b0 => Z.min b0 sa
                       | None => sa
                       end in
              match member_layout su field env with
              | Some (_, off, _) =>
                  if Z.eqb off 0 then Some b
                  else Some (Z.min b (Z.land off (-off)))
              | None => None
              end
          | TErr _ => None
          end
      | _ => None
      end
  end.

Definition member_alignment_node (x : c_typed_node) (env : c_type_env) : option Z :=
  member_alignment_node_aux (Z.to_nat 64) x env.

Fixpoint has_aligned_array_level (t : c_type) (env : c_type_env) : bool :=
  has_aligned_typedef t env ||
  match t with
  | TArray elem _ => has_aligned_array_level elem env
  | _ => false
  end.

Definition expr_alignment (x : c_typed_node) (env : c_type_env) : c_tr Z :=
  let fallback (_ : unit) :=
    let t1 := unqualified (tree_type x) in
    if has_aligned_array_level t1 env then
      TErr (TEBad "__alignof__ of an expression whose type may be an aligned typedef")
    else
      match type_size_align (innermost_element t1) env with
      | TOk (_, a) => TOk a
      | TErr e => TErr e
      end in
  match x with
  | TNode CatObj _ f =>
      match f with
      | TFMember _ _ | TFBitfield _ _ _ => TErr (TEBad "__alignof__ of a member")
      | TFId name =>
          match lookup_qalign env name with
          | Some (Some a) => TOk a
          | _ => fallback tt
          end
      | _ => fallback tt
      end
  | _ => fallback tt
  end.
