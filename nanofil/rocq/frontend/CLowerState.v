(** This module defines the lowering state, IR term builders, canonical IR text
    printer, ABI eightbyte layouts, type conversions, and scalar, complex, and
    vector operators shared by the Gallina C lowering passes.

    It ports the non-recursive foundation of nanofil/src/c_lower.pl so that
    CLowerInit.v, CLowerAsm.v, CLowerBuiltins.v, and CLower.v build ground
    terms over [Nanofil.Term.term] without axioms or side effects, compiling
    directly through both OCaml extraction and CertiRocq λANF. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Nanofil Require Import Term Maps.
From Backend Require Import Text Order Pizlonate.
From Frontend Require Import CAst CAttrs CLex CIeee CParse CCanon CPp
  CTypeAst CTypeTables CTypes.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** String equality, matching Prolog's `==`. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Compiler lowering options and small helpers

    Command-line and environment flags that affect lowering stay explicit in
    [c_lower_opts] so the Gallina lowering pass performs no I/O or environment
    lookups. *)

Record c_lower_opts : Type := mkCLowerOpts {
  lo_vectors : bool;
  lo_gnu89 : bool;
  lo_common : bool;
  lo_math_errno : bool;
}.

Definition default_lower_opts : c_lower_opts :=
  mkCLowerOpts true false false true.

Definition lower_type_opts (o : c_lower_opts) : c_type_opts :=
  mkCTypeOpts (lo_vectors o) (lo_gnu89 o).

Definition z_mod_pow2 (v bits : Z) : Z :=
  Z.modulo v (Z.shiftl 1 bits).

Definition z_mask (bits : Z) : Z :=
  Z.shiftl 1 bits - 1.

Definition z_not_mask (m bits : Z) : Z :=
  Z.lxor (Z.land m (z_mask bits)) (z_mask bits).

Fixpoint seq_Z_aux (fuel : nat) (cur : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => rev acc
  | S f => seq_Z_aux f (cur + 1) (cur :: acc)
  end.

Definition numlist_Z (lo hi : Z) : list Z :=
  if hi <? lo then [] else seq_Z_aux (Z.to_nat (hi - lo + 1)) lo [].

Definition z_repeat {A : Type} (n : Z) (x : A) : list A :=
  repeat x (Z.to_nat n).

Definition list_last {A : Type} (xs : list A) : option A :=
  let fix go (l : list A) :=
    match l with
    | [] => None
    | [x] => Some x
    | _ :: rest => go rest
    end in
  go xs.

Definition list_split_at {A : Type} (n : nat) (xs : list A) : list A * list A :=
  let fix go (k : nat) (l acc : list A) :=
    match k, l with
    | O, _ => (rev acc, l)
    | S _, [] => (rev acc, [])
    | S k', x :: rest => go k' rest (x :: acc)
    end in
  go n xs [].

Definition bytes_to_string (bs : list Z) : string :=
  string_of_rev (fold_left (fun acc b => byte (Z.to_nat (Z.modulo b 256)) :: acc) bs []).

Definition string_to_bytes (s : string) : list Z :=
  map (fun c => Z.of_nat (code c)) (list_ascii_of_string s).

Definition str_starts_with (pre s : string) : bool :=
  let lp := String.length pre in
  let ls := String.length s in
  if (ls <? lp)%nat then false
  else String.eqb (String.substring 0 lp s) pre.

Definition strip_prefix (pre s : string) : option string :=
  if str_starts_with pre s then
    let lp := String.length pre in
    Some (String.substring lp (String.length s - lp) s)
  else None.

Definition lowercase_ascii (c : ascii) : ascii :=
  let n := code c in
  if (65 <=? n)%nat && (n <=? 90)%nat then byte (n + 32) else c.

Definition lowercase_string (s : string) : string :=
  string_of_rev (fold_left (fun acc c => lowercase_ascii c :: acc) (list_ascii_of_string s) []).

Definition str_mem (x : string) (xs : list string) : bool :=
  existsb (String.eqb x) xs.

Definition opt_bind {A B : Type} (o : option A) (f : A -> option B) : option B :=
  match o with Some x => f x | None => None end.

(** ## IR term constructors and canonical IR text printer

    The constructors build unchecked Fil-C IR terms directly over [term], and
    [ir_module_text] formats a module clause by clause to match
    nanofil/src/ir_text.pl byte for byte. *)

Definition ir_tmp (name : string) : term := TApp "tmp" [TAtom name].
Definition ir_const (n : Z) : term := TApp "const" [Term.TInt n].
Definition ir_global (sym : string) : term := TApp "global" [TAtom sym].
Definition ir_unproto (sym : string) : term := TApp "unproto" [TAtom sym].
Definition ir_sym (sym : string) (off : Z) : term := TApp "sym" [TAtom sym; Term.TInt off].
Definition ir_let (d : term) (k : string) (op : term) (args : list term) : term :=
  TApp "let" [d; TAtom k; op; TList args].
Definition ir_store (w : string) (v a : term) : term :=
  TApp "store" [TAtom w; v; a].
Definition ir_atomic_store (w : string) (v a : term) : term :=
  TApp "atomic_store" [TAtom w; v; a].
Definition ir_phi (d : term) (k : string) (edges : list term) : term :=
  TApp "phi" [d; TAtom k; TList edges].
Definition ir_edge (lbl v : term) : term := TApp "-" [lbl; v].
Definition ir_call (res callee : term) (args : list term) : term :=
  TApp "call" [res; callee; TList args].
Definition ir_arg (k : string) (v : term) : term := TApp "arg" [TAtom k; v].
Definition ir_param (k : string) (v : term) : term := TApp "param" [TAtom k; v].
Definition ir_result (d : term) (k : string) : term := TApp "result" [d; TAtom k].
Definition ir_tuple (rs : list term) : term := TApp "tuple" [TList rs].
Definition ir_access (kind : string) (addr : term) (sz al : Z) : term :=
  TApp "access" [TAtom kind; addr; Term.TInt sz; Term.TInt al].
Definition ir_asm_fixed (mnem : string) (ins outs : list term) : term :=
  TApp "asm_fixed" [TAtom mnem; TList ins; TList outs].
Definition ir_fence : term := TAtom "fence".
Definition ir_goto (lbl : string) : term := TApp "goto" [TAtom lbl].
Definition ir_branch (v : term) (l1 l2 : string) : term :=
  TApp "branch" [v; TAtom l1; TAtom l2].
Definition ir_ret (v : term) : term := TApp "ret" [v].
Definition ir_ret_void : term := TAtom "ret".
Definition ir_rets (vs : list term) : term := TApp "rets" [TList vs].
Definition ir_unreachable : term := TAtom "unreachable".
Definition ir_item (w : string) (v : term) : term := TApp "item" [TAtom w; v].
Definition ir_zero (n : Z) : term := TApp "zero" [Term.TInt n].
Definition ir_byte_atom (b : Z) : term :=
  let n := Z.to_nat (Z.modulo b 256) in
  if (n <? 128)%nat then TAtom (string_of_rev [byte n])
  else TAtom (string_of_rev [byte (128 + n mod 64)%nat; byte (192 + n / 64)%nat]).

Definition ir_str (bytes : list Z) : term :=
  TApp "str" [TList (map ir_byte_atom bytes)].
Definition ir_block (lbl : string) (phis insts : list term) (jmp : term) : term :=
  TApp "block" [TAtom lbl; TList phis; TList insts; jmp].
Definition ir_func (sym linkage : string) (ret : term) (params blocks : list term) : term :=
  TApp "func" [TAtom sym; TAtom linkage; ret; TList params; TList blocks].
Definition ir_data (sym : string) (linkage : term) (align : Z) (items : list term) : term :=
  TApp "data" [TAtom sym; linkage; Term.TInt align; TList items].
Definition ir_alias (sym linkage target : string) : term :=
  TApp "alias" [TAtom sym; TAtom linkage; TAtom target].
Definition ir_context (sym : string) (records : list term) : term :=
  TApp "context" [TAtom sym; TList records].

Definition ir_is_lower (n : nat) : bool :=
  (97 <=? n)%nat && (n <=? 122)%nat.

Definition ir_is_ident (n : nat) : bool :=
  ir_is_lower n || ((65 <=? n)%nat && (n <=? 90)%nat)
  || ((48 <=? n)%nat && (n <=? 57)%nat) || Nat.eqb n 95.

Definition ir_atom_is_bare (s : string) : bool :=
  match list_ascii_of_string s with
  | [] => false
  | c :: rest => ir_is_lower (code c) && forallb (fun x => ir_is_ident (code x)) rest
  end.

Definition ir_hex_digit (n : nat) : string :=
  nth n ["0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"a";"b";"c";"d";"e";"f"] "0".

Definition ir_hex_byte (n : nat) : string :=
  if (n <? 16)%nat then ir_hex_digit n
  else ir_hex_digit (n / 16)%nat ++ ir_hex_digit (n mod 16)%nat.

Fixpoint ir_quote_chars (q : nat) (cs : list ascii) (acc : list string) : list string :=
  match cs with
  | [] => acc
  | c :: rest =>
      let n := code c in
      let part :=
        if Nat.eqb n q then ("\" ++ string_of_rev [c])%string
        else if Nat.eqb n 92 then "\\"
        else if Nat.eqb n 10 then "\n"
        else if Nat.eqb n 9 then "\t"
        else if (n <? 32)%nat || Nat.eqb n 127 then ("\x" ++ ir_hex_byte n ++ "\")%string
        else if (128 <=? n)%nat then
          string_of_rev [byte (128 + n mod 64)%nat; byte (192 + n / 64)%nat]
        else string_of_rev [c] in
      ir_quote_chars q rest (part :: acc)
  end.

Definition ir_emit_atom (s : string) (acc : list string) : list string :=
  if ir_atom_is_bare s then s :: acc
  else "'" :: ir_quote_chars 39 (list_ascii_of_string s) ("'" :: acc).

Definition ir_emit_str_atoms (ts : list term) (acc : list string) : option (list string) :=
  let fix go (l : list term) (a : list string) :=
    match l with
    | [] => Some a
    | TAtom s :: rest =>
        match list_ascii_of_string s with
        | [c] =>
            let n := code c in
            if (n <? 128)%nat then
              let part :=
                if Nat.eqb n 34 then "\"""
                else if Nat.eqb n 92 then "\\"
                else if Nat.eqb n 10 then "\n"
                else if Nat.eqb n 9 then "\t"
                else if (n <? 32)%nat || Nat.eqb n 127 then ("\x" ++ ir_hex_byte n ++ "\")%string
                else s in
              go rest (part :: a)
            else None
        | [c1; c2] =>
            let a1 := code c1 in
            let b1 := code c2 in
            if (192 <=? a1)%nat && (a1 <? 224)%nat && (128 <=? b1)%nat && (b1 <? 192)%nat then
              go rest (s :: a)
            else None
        | _ => None
        end
    | _ => None
    end in
  go ts acc.

Fixpoint ir_emit_term (t : term) (acc : list string) : list string :=
  let fix emit_args (ts : list term) (a : list string) : list string :=
    match ts with
    | [] => a
    | [x] => ir_emit_term x a
    | x :: rest => emit_args rest (", " :: ir_emit_term x a)
    end in
  match t with
  | TList [] => "[]" :: acc
  | Term.TInt n => decimal n :: acc
  | TAtom s => ir_emit_atom s acc
  | TList xs => "]" :: emit_args xs ("[" :: acc)
  | TApp f xs =>
      if f == "str" then
        match xs with
        | [TList cs_terms] =>
            match ir_emit_str_atoms cs_terms ("str(""" :: acc) with
            | Some a1 => """)" :: a1
            | None => ")" :: emit_args xs ("(" :: ir_emit_atom f acc)
            end
        | _ => ")" :: emit_args xs ("(" :: ir_emit_atom f acc)
        end
      else if f == "-" then
        match xs with
        | [a; b] => ir_emit_term b ("-" :: ir_emit_term a acc)
        | _ => ")" :: emit_args xs ("(" :: ir_emit_atom f acc)
        end
      else
        ")" :: emit_args xs ("(" :: ir_emit_atom f acc)
  end.

Definition ir_emit_lines (xs : list term) (acc : list string) : list string :=
  match xs with
  | [] => "[]" :: acc
  | _ =>
      let fix go (l : list term) (a : list string) :=
        match l with
        | [] => a
        | [x] => nl :: ir_emit_term x ("        " :: a)
        | x :: rest => go rest (nl :: "," :: ir_emit_term x ("        " :: a))
        end in
      "    ]" :: go xs (nl :: "[" :: acc)
  end.

Definition ir_emit_block (b : term) (acc : list string) : list string :=
  match b with
  | TApp f [lbl; TList phis; TList insts; jmp] =>
      if f == "block" then
        let a1 := ir_emit_term lbl ("    block(" :: acc) in
        let a2 := ir_emit_lines phis (", " :: a1) in
        let a3 := ir_emit_lines insts (", " :: a2) in
        ")" :: ir_emit_term jmp (", " :: a3)
      else ir_emit_term b acc
  | _ => ir_emit_term b acc
  end.

Definition ir_emit_item (item : term) (acc : list string) : list string :=
  match item with
  | TApp f [nm; lnk; ret; params; TList blks] =>
      if f == "func" then
        let a1 := ir_emit_term nm ("func(" :: acc) in
        let a2 := ir_emit_term lnk (", " :: a1) in
        let a3 := ir_emit_term ret (", " :: a2) in
        let a4 := ir_emit_term params (", " :: a3) in
        let fix go_blks (bs : list term) (a : list string) :=
          match bs with
          | [] => a
          | [b] => nl :: ir_emit_block b a
          | b :: rest => go_blks rest (nl :: "," :: ir_emit_block b a)
          end in
        "])" :: go_blks blks (nl :: ", [" :: a4)
      else ir_emit_term item acc
  | _ => ir_emit_term item acc
  end.

Definition ir_item_line (item : term) : string :=
  String.concat "" (rev_append (nl :: "." :: ir_emit_item item []) []).

Definition ir_module_lines (items : list term) : list string :=
  map ir_item_line items.

(** ## Converting semantic types and shallow nodes to ground terms

    Provenance records inside `context(Sym, Records)` embed semantic C types,
    source locations, and shallow typed-node forms as Prolog terms. *)

Definition su_id_to_term (id : su_id) : term :=
  match id with
  | SUInt n => Term.TInt n
  | SUBuiltin s => TAtom s
  end.

Definition enum_key_to_term (k : enum_key_t) : term :=
  match k with
  | EKTag s => TAtom s
  | EKAnon s => TApp "anon" [TAtom s]
  end.

Definition c_qual_to_term (q : c_qual) : term :=
  match q with
  | QAtomic => TAtom "atomic"
  | QConst => TAtom "const"
  | QRestrict => TAtom "restrict"
  | QVolatile => TAtom "volatile"
  | QEnum k => TApp "enum" [enum_key_to_term k]
  end.

Fixpoint parse_dec_Z_aux (cs : list ascii) (acc : Z) : option Z :=
  match cs with
  | [] => Some acc
  | c :: rest =>
      let n := code c in
      if (48 <=? n)%nat && (n <=? 57)%nat then
        parse_dec_Z_aux rest (acc * 10 + Z.of_nat (n - 48))
      else None
  end.

Definition parse_dec_Z (s : string) : option Z :=
  match list_ascii_of_string s with
  | [] => None
  | c :: rest =>
      if Ascii.eqb c "-"%char then
        match rest with
        | [] => None
        | _ => match parse_dec_Z_aux rest 0 with Some n => Some (- n) | None => None end
        end
      else parse_dec_Z_aux (c :: rest) 0
  end.

Definition dyn_str_to_term (s : string) : term :=
  match strip_prefix "=" s with
  | Some ns =>
      match parse_dec_Z ns with
      | Some n => ir_const n
      | None => ir_tmp s
      end
  | None => ir_tmp s
  end.

Definition term_to_dyn_str (v : term) : string :=
  match v with
  | TApp f [Term.TInt n] => if f == "const" then "=" ++ decimal n else "v0"
  | TApp f [TAtom t] => if f == "tmp" then t else "v0"
  | _ => "v0"
  end.

Definition c_suf_rad_term (s : int_suffix) (r : int_radix) : term :=
  let sn :=
    match s with
    | SufNone => "none"
    | SufU => "u"
    | SufL => "l"
    | SufUL => "ul"
    | SufLL => "ll"
    | SufULL => "ull"
    end in
  let rn := match r with RadDec => "dec" | RadOther => "other" end in
  TApp "-" [TAtom sn; TAtom rn].

Definition c_chars_list_term (s : string) : term :=
  TList (map (fun c => TAtom (string_of_rev [c])) (list_ascii_of_string s)).

Definition c_loc_ast_term (loc : c_loc) : term :=
  match loc with
  | LocEof => TAtom "eof"
  | Loc f l => TApp ":" [TAtom f; Term.TInt l]
  end.

Definition c_opt_some_atom_term (o : option string) : term :=
  match o with Some s => TApp "some" [TAtom s] | None => TAtom "none" end.

Definition c_opt_atom_term (o : option string) : term :=
  match o with Some s => TAtom s | None => TAtom "none" end.

Definition c_pack_op_term (op : pack_op) : term :=
  match op with
  | PackSet None => TApp "set" [TAtom "none"]
  | PackSet (Some n) => TApp "set" [Term.TInt n]
  | PackPush lbl None => TApp "push" [c_opt_atom_term lbl; TAtom "keep"]
  | PackPush lbl (Some n) => TApp "push" [c_opt_atom_term lbl; Term.TInt n]
  | PackPop lbl => TApp "pop" [c_opt_atom_term lbl]
  | PackShow => TAtom "show"
  end.

Definition c_tok_kind_term (k : tok_kind) : term :=
  match k with
  | CAst.TId s => TApp "id" [TAtom s]
  | CAst.TKw s => TApp "kw" [TAtom s]
  | CAst.TInt v s r => TApp "int" [Term.TInt v; c_suf_rad_term s r]
  | CAst.TFloat cs => TApp "float" [c_chars_list_term cs]
  | CAst.TImag cs => TApp "imag" [TApp "float" [c_chars_list_term cs]]
  | CAst.TChr v => TApp "chr" [Term.TInt v]
  | CAst.TStr bs => TApp "str" [TList (map Term.TInt bs)]
  | CAst.TWStr wt vs => TApp "wstr" [TAtom (wt_name wt); TList (map Term.TInt vs)]
  | CAst.TPunct s => TApp "p" [TAtom s]
  | CAst.TPragmaWeak nm tgt => TApp "pragma_weak" [TAtom nm; c_opt_atom_term tgt]
  | CAst.TPragmaPack op => TApp "pragma_pack" [c_pack_op_term op]
  end.

Fixpoint c_attr_tok_term (fuel : nat) (t : attr_tok) {struct fuel} : term :=
  match fuel with
  | O => TAtom "none"
  | S f =>
      match t with
      | ATok k => c_tok_kind_term k
      | AGroup xs => TApp "group" [TList (map (c_attr_tok_term f) xs)]
      end
  end.

Fixpoint c_expr_to_term_f (fuel : nat) (e : c_expr) {struct fuel} : term :=
  match fuel with
  | O => TAtom "expr"
  | S f =>
      match e with
      | EId s => TApp "id" [TAtom s]
      | ENum v s r => TApp "num" [Term.TInt v; c_suf_rad_term s r]
      | EChr v => TApp "chr" [Term.TInt v]
      | EFloat cs => TApp "float" [c_chars_list_term cs]
      | EImag cs => TApp "imag" [TApp "float" [c_chars_list_term cs]]
      | EStr bs => TApp "str" [TList (map Term.TInt bs)]
      | EWStr wt vs => TApp "wstr" [TAtom (wt_name wt); TList (map Term.TInt vs)]
      | EBin op a c => TApp "bin" [TAtom (binop_name op); c_expr_to_term_f f a; c_expr_to_term_f f c]
      | EAssign op a c => TApp "assign" [TAtom op; c_expr_to_term_f f a; c_expr_to_term_f f c]
      | EUn op a => TApp "un" [TAtom (unop_name op); c_expr_to_term_f f a]
      | ECond c a d => TApp "cond" [c_expr_to_term_f f c; c_expr_to_term_f f a; c_expr_to_term_f f d]
      | EGCond c d => TApp "gcond" [c_expr_to_term_f f c; c_expr_to_term_f f d]
      | EComma a c => TApp "comma" [c_expr_to_term_f f a; c_expr_to_term_f f c]
      | ECall fn args => TApp "call" [c_expr_to_term_f f fn; TList (map (c_expr_to_term_f f) args)]
      | EConvertVector a tn =>
          TApp "call" [TApp "id" [TAtom "__builtin_convertvector"];
                       TList [c_expr_to_term_f f a; c_type_name_to_term_f f tn]]
      | EIndex a i => TApp "index" [c_expr_to_term_f f a; c_expr_to_term_f f i]
      | EMember a fld => TApp "member" [c_expr_to_term_f f a; TAtom fld]
      | EArrow a fld => TApp "arrow" [c_expr_to_term_f f a; TAtom fld]
      | ECast tn a => TApp "cast" [c_type_name_to_term_f f tn; c_expr_to_term_f f a]
      | ESizeofType tn => TApp "sizeof_type" [c_type_name_to_term_f f tn]
      | ESizeofExpr a => TApp "sizeof_expr" [c_expr_to_term_f f a]
      | EAlignofType tn => TApp "alignof" [c_type_name_to_term_f f tn]
      | EAlignofExpr a => TApp "alignof_expr" [c_expr_to_term_f f a]
      | ERealPart a => TApp "real_part" [c_expr_to_term_f f a]
      | EImagPart a => TApp "imag_part" [c_expr_to_term_f f a]
      | EComplit tn es =>
          TApp "complit" [c_type_name_to_term_f f tn; TApp "list" [TList (map (c_init_entry_to_term_f f) es)]]
      | EOffsetof tn ds =>
          TApp "offsetof" [c_type_name_to_term_f f tn; TList (map (c_desig_to_term_f f) ds)]
      | EVaArg a tn => TApp "va_arg" [c_expr_to_term_f f a; c_type_name_to_term_f f tn]
      | EBitCast tn a => TApp "bit_cast" [c_type_name_to_term_f f tn; c_expr_to_term_f f a]
      | ETypesCompatible a c =>
          TApp "types_compatible" [c_type_name_to_term_f f a; c_type_name_to_term_f f c]
      | EStmtExpr body => TApp "stmtexpr" [c_stmt_to_term_f f body]
      | ELabelAddr l => TApp "label_addr" [TAtom l]
      | EGeneric c assocs =>
          TApp "generic" [c_expr_to_term_f f c;
                          TList (map (fun ga =>
                                        match ga with
                                        | GAssocType tn ex =>
                                            TApp "assoc" [c_type_name_to_term_f f tn; c_expr_to_term_f f ex]
                                        | GAssocDefault ex =>
                                            TApp "assoc" [TAtom "default"; c_expr_to_term_f f ex]
                                        end) assocs)]
      end
  end

with c_type_name_to_term_f (fuel : nat) (tn : c_type_name) {struct fuel} : term :=
  match fuel with
  | O => TAtom "type"
  | S f =>
      match tn with
      | TypeName sps ty => TApp "type" [TList (map (c_spec_to_term_f f) sps); c_dcl_type_to_term_f f ty]
      end
  end

with c_spec_to_term_f (fuel : nat) (sp : c_spec) {struct fuel} : term :=
  match fuel with
  | O => TAtom "spec"
  | S f =>
      match sp with
      | SpStorage s => TApp "storage" [TAtom s]
      | SpTspec s => TApp "tspec" [TAtom s]
      | SpQual s => TApp "qual" [TAtom s]
      | SpFspec s => TApp "fspec" [TAtom s]
      | SpTname s => TApp "tname" [TAtom s]
      | SpSu k tag oms ats =>
          let kstr := match k with KStruct => "struct" | KUnion => "union" end in
          let ms_t := match oms with None => TAtom "none" | Some ms => TList (map (c_member_to_term_f f) ms) end in
          let ats_t := TList (map (fun xs => TList (map (c_attr_tok_term f) xs)) ats) in
          TApp "su" [TAtom kstr; c_opt_some_atom_term tag; ms_t; ats_t]
      | SpEnum tag es =>
          let es_t :=
            match es with
            | EnumNone => TAtom "none"
            | EnumList xs => TList (map (c_enumerator_to_term_f f) xs)
            | EnumPacked xs => TApp "packed" [TList (map (c_enumerator_to_term_f f) xs)]
            end in
          TApp "enum" [c_opt_some_atom_term tag; es_t]
      | SpSharedBase => TAtom "shared_base"
      | SpAttr ts => TApp "attr" [TList (map (c_attr_tok_term f) ts)]
      | SpAttrTag tag => TApp "attr" [TAtom tag]
      | SpAlignasType tn => TApp "alignas" [TApp "type" [c_type_name_to_term_f f tn]]
      | SpAlignasExpr e => TApp "alignas" [TApp "expr" [c_expr_to_term_f f e]]
      | SpTypeofType tn => TApp "typeof" [TApp "type" [c_type_name_to_term_f f tn]]
      | SpTypeofExpr e => TApp "typeof" [TApp "expr" [c_expr_to_term_f f e]]
      | SpAutoType => TAtom "auto_type"
      | SpAtomic tn => TApp "atomic" [c_type_name_to_term_f f tn]
      end
  end

with c_member_to_term_f (fuel : nat) (m : c_member) {struct fuel} : term :=
  match fuel with
  | O => TAtom "member"
  | S f =>
      match m with
      | MField sps dcl ow =>
          let w_t := match ow with None => TAtom "none" | Some e => c_expr_to_term_f f e end in
          TApp "field" [TList (map (c_spec_to_term_f f) sps); c_dcl_to_term_f f dcl; w_t]
      | MStaticAssert loc cond msg =>
          TApp "static_assert" [c_loc_ast_term loc; c_expr_to_term_f f cond; TList (map Term.TInt msg)]
      end
  end

with c_enumerator_to_term_f (fuel : nat) (e : c_enumerator) {struct fuel} : term :=
  match fuel with
  | O => TAtom "enumerator"
  | S f =>
      match e with
      | Enumerator nm ov =>
          TApp "enumerator" [TAtom nm; match ov with None => TAtom "none" | Some ex => c_expr_to_term_f f ex end]
      end
  end

with c_dcl_to_term_f (fuel : nat) (dcl : c_dcl) {struct fuel} : term :=
  match fuel with
  | O => TAtom "dcl"
  | S f =>
      match dcl with
      | Dcl nm ty asym =>
          let as_t := match asym with None => TAtom "none" | Some s => TApp "asm" [TAtom s] end in
          TApp "dcl" [c_opt_some_atom_term nm; c_dcl_type_to_term_f f ty; as_t]
      end
  end

with c_dcl_type_to_term_f (fuel : nat) (ty : c_dcl_type) {struct fuel} : term :=
  match fuel with
  | O => TAtom "base"
  | S f =>
      match ty with
      | DTBase => TAtom "base"
      | DTPtr inner qs => TApp "ptr" [c_dcl_type_to_term_f f inner; TList (map TAtom qs)]
      | DTArray inner sz =>
          let sz_t :=
            match sz with
            | ASNone => TAtom "none"
            | ASStar => TAtom "star"
            | ASExpr e => c_expr_to_term_f f e
            end in
          TApp "array" [c_dcl_type_to_term_f f inner; sz_t]
      | DTFunc inner ps =>
          let ps_t :=
            match ps with
            | PUnspecified => TAtom "unspecified"
            | PParams xs var =>
                TApp "params" [TList (map (fun p =>
                                             match p with
                                             | Param sps d =>
                                                 TApp "param" [TList (map (c_spec_to_term_f f) sps); c_dcl_to_term_f f d]
                                             end) xs);
                               TAtom (if var then "variadic" else "fixed")]
            | PKnr ns => TApp "knr" [TList (map TAtom ns)]
            | PKnrDef ns ds => TApp "knr" [TList (map TAtom ns); TList (map (c_item_to_term_f f) ds)]
            end in
          TApp "func" [c_dcl_type_to_term_f f inner; ps_t]
      end
  end

with c_init_to_term_f (fuel : nat) (ini : c_init) {struct fuel} : term :=
  match fuel with
  | O => TAtom "none"
  | S f =>
      match ini with
      | InitExpr e => c_expr_to_term_f f e
      | InitList es => TApp "list" [TList (map (c_init_entry_to_term_f f) es)]
      end
  end

with c_init_entry_to_term_f (fuel : nat) (en : c_init_entry) {struct fuel} : term :=
  match fuel with
  | O => TAtom "entry"
  | S f =>
      match en with
      | InitEntry ds ini => TApp "entry" [TList (map (c_desig_to_term_f f) ds); c_init_to_term_f f ini]
      end
  end

with c_desig_to_term_f (fuel : nat) (d : c_designator) {struct fuel} : term :=
  match fuel with
  | O => TAtom "desig"
  | S f =>
      match d with
      | DField fld => TApp "field" [TAtom fld]
      | DIndex e => TApp "index" [c_expr_to_term_f f e]
      | DRange lo hi => TApp "range" [c_expr_to_term_f f lo; c_expr_to_term_f f hi]
      end
  end

with c_item_to_term_f (fuel : nat) (it : c_item) {struct fuel} : term :=
  match fuel with
  | O => TAtom "item"
  | S f =>
      match it with
      | IDecl loc sps inits =>
          TApp "decl" [c_loc_ast_term loc; TList (map (c_spec_to_term_f f) sps);
                       TList (map (fun idcl =>
                                     match idcl with
                                     | InitDecl d oini =>
                                         TApp "init" [c_dcl_to_term_f f d;
                                                      match oini with
                                                      | None => TAtom "none"
                                                      | Some ini => c_init_to_term_f f ini
                                                      end]
                                     end) inits)]
      | IFundef loc sps dcl body =>
          TApp "fundef" [c_loc_ast_term loc; TList (map (c_spec_to_term_f f) sps);
                         c_dcl_to_term_f f dcl; c_stmt_to_term_f f body]
      | IStaticAssert loc cond msg =>
          TApp "static_assert" [c_loc_ast_term loc; c_expr_to_term_f f cond; TList (map Term.TInt msg)]
      | IPragmaWeak loc nm tgt =>
          TApp "pragma_weak" [c_loc_ast_term loc; TAtom nm; c_opt_atom_term tgt]
      | IToplevelAsm loc tpl =>
          TApp "toplevel_asm" [c_loc_ast_term loc; TList (map Term.TInt tpl)]
      end
  end

with c_stmt_to_term_f (fuel : nat) (st : c_stmt) {struct fuel} : term :=
  match fuel with
  | O => TAtom "null"
  | S f =>
      match st with
      | Stmt loc body =>
          let asm_op_t (ao : c_asm_op) :=
            match ao with AsmOp c e => TApp "op" [TAtom c; c_expr_to_term_f f e] end in
          let asm_clob_t (cl : c_asm_clobber) :=
            match cl with ACName s => TAtom s | ACLabels ls => TApp "labels" [TList (map TAtom ls)] end in
          let body_t :=
            match body with
            | SBlock bis =>
                TApp "block" [TList (map (fun bi =>
                                            match bi with
                                            | BIDecl it => c_item_to_term_f f it
                                            | BIStmt s => c_stmt_to_term_f f s
                                            end) bis)]
            | SExpr e => TApp "expr" [c_expr_to_term_f f e]
            | SNull => TAtom "null"
            | SIf c t oe =>
                TApp "if" [c_expr_to_term_f f c; c_stmt_to_term_f f t;
                           match oe with None => TAtom "none" | Some e => c_stmt_to_term_f f e end]
            | SWhile c b => TApp "while" [c_expr_to_term_f f c; c_stmt_to_term_f f b]
            | SDo b c => TApp "do" [c_stmt_to_term_f f b; c_expr_to_term_f f c]
            | SFor fi oc os b =>
                let fi_t :=
                  match fi with
                  | FINone => TAtom "none"
                  | FIExpr e => TApp "expr" [c_expr_to_term_f f e]
                  | FIDecl it => c_item_to_term_f f it
                  end in
                let oc_t := match oc with None => TAtom "none" | Some e => c_expr_to_term_f f e end in
                let os_t := match os with None => TAtom "none" | Some e => c_expr_to_term_f f e end in
                TApp "for" [fi_t; oc_t; os_t; c_stmt_to_term_f f b]
            | SSwitch c b => TApp "switch" [c_expr_to_term_f f c; c_stmt_to_term_f f b]
            | SCase v b => TApp "case" [c_expr_to_term_f f v; c_stmt_to_term_f f b]
            | SCaseRange lo hi b =>
                TApp "case" [TApp "range" [c_expr_to_term_f f lo; c_expr_to_term_f f hi]; c_stmt_to_term_f f b]
            | SDefault b => TApp "default" [c_stmt_to_term_f f b]
            | SBreak => TAtom "break"
            | SContinue => TAtom "continue"
            | SReturn oe =>
                TApp "return" [match oe with None => TAtom "none" | Some e => c_expr_to_term_f f e end]
            | SGoto l => TApp "goto" [TAtom l]
            | SComputedGoto e => TApp "computed_goto" [c_expr_to_term_f f e]
            | SLabel l b => TApp "label" [TAtom l; c_stmt_to_term_f f b]
            | SAsmEmpty outs ins clobs g =>
                TApp "asm_empty" [TList (map asm_op_t outs); TList (map asm_op_t ins);
                                  TList (map asm_clob_t clobs); TAtom (if g then "goto" else "none")]
            | SAsm tpl outs ins clobs g =>
                TApp "asm" [TList (map Term.TInt tpl); TList (map asm_op_t outs);
                            TList (map asm_op_t ins); TList (map asm_clob_t clobs);
                            TAtom (if g then "goto" else "none")]
            | SUnsupportedAsm k =>
                TApp "unsupported_asm" [match k with
                                        | AUMemory tpl => TApp "memory" [TList (map Term.TInt tpl)]
                                        | AUOther => TAtom "other"
                                        end]
            end in
          TApp "at" [c_loc_ast_term loc; body_t]
      end
  end.

Definition c_expr_to_term (e : c_expr) : term :=
  c_expr_to_term_f (Z.to_nat 128) e.

Definition arr_len_to_term (l : c_arr_len) : term :=
  match l with
  | ALNone => TAtom "none"
  | ALConst n => Term.TInt n
  | ALVlaStar => TApp "vla" [TAtom "star"]
  | ALVlaExpr e => TApp "vla" [c_expr_to_term e]
  | ALDyn s => TApp "dyn" [dyn_str_to_term s]
  end.

Fixpoint c_type_to_term (t : c_type) : term :=
  match t with
  | TVoid => TAtom "void"
  | TIntK k => TAtom (c_int_kind_name k)
  | TFloatK k => TAtom (c_float_kind_name k)
  | TPtr inner => TApp "ptr" [c_type_to_term inner]
  | TArray elem len => TApp "array" [c_type_to_term elem; arr_len_to_term len]
  | TFunc ret ops var =>
      let ps_t :=
        match ops with
        | None => TAtom "unspecified"
        | Some ps => TList (map c_type_to_term ps)
        end in
      TApp "func" [c_type_to_term ret; ps_t; TAtom (if var then "variadic" else "fixed")]
  | TStruct id => TApp "struct" [su_id_to_term id]
  | TUnion id => TApp "union" [su_id_to_term id]
  | TAtomic su p => TApp "atomic" [c_type_to_term su; Term.TInt p]
  | TVec elem n al => TApp "vec" [c_type_to_term elem; Term.TInt n; Term.TInt al]
  | TQual qs inner => TApp "qualified" [TList (map c_qual_to_term qs); c_type_to_term inner]
  | TBad why => TApp "bad" [TAtom why]
  end.

Definition source_location_term (loc : c_loc) : term :=
  match loc with
  | LocEof => TAtom "none"
  | Loc file line =>
      if (file == "") || ((file == "unknown") && Z.eqb line 0) then TAtom "none"
      else TApp "at" [TAtom file; Term.TInt line]
  end.

Definition wide_type_atom (wt : wide_type) : string :=
  match wt with
  | WInt => "int"
  | WUShort => "ushort"
  | WUInt => "uint"
  end.

Definition shallow_node_term (form : c_typed_form) (env : c_type_env) : term :=
  match form with
  | TFId name =>
      match lookup_ordinary env name with
      | Some (BVar (VSNamed b) _) => TApp "binding" [TAtom b]
      | Some (BGVar _ sym _ _) => TApp "binding" [ir_global sym]
      | _ => TApp "id" [TAtom name]
      end
  | TFPredefined name => TApp "predefined" [TAtom name]
  | TFInt v => TApp "int" [Term.TInt v]
  | TFFloat _ => TAtom "float"
  | TFImag _ => TAtom "imag"
  | TFStr bs => match bs with [] => TApp "str" [TList []] | _ => TAtom "str" end
  | TFWStr wt cs =>
      match cs with
      | [] => TApp "wstr" [TAtom (wide_type_atom wt); TList []]
      | _ => TApp "wstr" [TAtom (wide_type_atom wt)]
      end
  | TFLoad _ => TAtom "load"
  | TFDecay _ => TAtom "decay"
  | TFAddr _ => TAtom "addr"
  | TFDeref _ => TAtom "deref"
  | TFCast _ _ => TAtom "cast"
  | TFComplit _ _ => TAtom "complit"
  | TFIncDec op _ => TApp "incdec" [TAtom (c_unop_name op)]
  | TFUn op _ => TApp "un" [TAtom (c_unop_name op)]
  | TFBin op _ _ => TApp "bin" [TAtom (c_binop_name op)]
  | TFCond _ _ _ => TAtom "cond"
  | TFGCond _ _ => TAtom "gcond"
  | TFAssign op _ _ => TApp "assign" [TAtom op]
  | TFComma _ _ => TAtom "comma"
  | TFMember _ fld => TApp "member" [TAtom fld]
  | TFBitfield _ _ w => TApp "bitfield" [Term.TInt w]
  | TFVLane _ _ => TAtom "vlane"
  | TFCall _ args => match args with [] => TApp "call" [TList []] | _ => TAtom "call" end
  | TFBuiltin name args =>
      match args with
      | [] => TApp "builtin" [TAtom name; TList []]
      | _ => TApp "builtin" [TAtom name]
      end
  | TFConvertVector _ _ => TApp "builtin" [TAtom "__builtin_convertvector"]
  | TFSizeofExpr _ => TAtom "sizeof"
  | TFSizeofType _ => TAtom "sizeof"
  | TFAlignofType _ => TAtom "alignof"
  | TFAlignofExpr _ => TAtom "alignof_expr"
  | TFOffsetof _ path => match path with [] => TApp "offsetof" [TList []] | _ => TAtom "offsetof" end
  | TFVaArg _ _ => TAtom "va_arg"
  | TFBitCast _ => TAtom "bit_cast"
  | TFStmtExpr _ => TAtom "stmtexpr"
  end.

Definition node_cat_name (cat : c_node_cat) : string :=
  match cat with
  | CatObj => "obj"
  | CatFun => "fun"
  | CatVal => "val"
  end.

(** ## Values, places, lowering context, and state

    Lowering threads a function state [c_func_st] holding the type environment,
    block-scoped lowering metadata, module-wide global tables, open block,
    emitted instructions and blocks, fresh counter, label tables, switch cases,
    and provenance builder. *)

Inductive c_val : Type :=
| CVal (v : term) (ty : c_type).

Inductive c_place : Type :=
| PLv (addr : term) (ty : c_type)
| PFn (callee : term) (ty : c_type)
| PBits (addr : term) (ty : c_type) (pos width : Z).

Record c_lower_ctx : Type := mkCLowerCtx {
  ctx_func : string;
  ctx_ret : c_type;
  ctx_break : option string;
  ctx_cont : option string;
  ctx_loc : c_loc;
}.

Definition ctx_at (c : c_lower_ctx) (loc : c_loc) : c_lower_ctx :=
  mkCLowerCtx (ctx_func c) (ctx_ret c) (ctx_break c) (ctx_cont c) loc.

Definition loop_ctx (c : c_lower_ctx) (lbreak lcont : string) : c_lower_ctx :=
  mkCLowerCtx (ctx_func c) (ctx_ret c) (Some lbreak) (Some lcont) (ctx_loc c).

Definition switch_ctx (c : c_lower_ctx) (lbreak : string) : c_lower_ctx :=
  mkCLowerCtx (ctx_func c) (ctx_ret c) (Some lbreak) (ctx_cont c) (ctx_loc c).

Definition unknown_loc : c_loc := Loc "unknown" 0.

Definition unknown_ctx : c_lower_ctx :=
  mkCLowerCtx "" TVoid None None unknown_loc.

Inductive g_linkage : Type :=
| GLNormal (s : string)
| GLTls (s : string).

Record gdef_entry : Type := mkGDef {
  gd_type : c_type;
  gd_linkage : g_linkage;
  gd_init : option c_init;
  gd_loc : c_loc;
}.

Inductive lit_entry : Type :=
| LitBytes (bs : list Z)
| LitWide (wt : c_type) (vs : list Z).

Record deferred_fn : Type := mkDeferredFn {
  df_loc : c_loc;
  df_name : string;
  df_type : c_type;
  df_dcl : c_dcl_type;
  df_body : c_stmt;
  df_scope : c_scope;
}.

Record init_entry : Type := mkInitEntry {
  ie_order : Z;
  ie_kind : string;
  ie_sym : string;
  ie_prio : option Z;
}.

Record c_lower_globals : Type := mkCLowerGlobals {
  lg_gdefs : smap gdef_entry;
  lg_gdef_syms : list string;
  lg_lits : smap lit_entry;
  lg_lit_syms : list string;
  lg_lit_of : smap string;
  lg_func_names : smap string;
  lg_deferred : smap deferred_fn;
  lg_inline_copy : smap string;
  lg_inline_copy_of : smap string;
  lg_inline_attr : list string;
  lg_readonly : smap bool;
  lg_galign : smap Z;
  lg_qsym : smap c_type;
  lg_initialized : smap (list term);
  lg_inits : list init_entry;
}.

Definition empty_lower_globals : c_lower_globals :=
  mkCLowerGlobals smap_empty [] smap_empty [] smap_empty smap_empty
                  smap_empty smap_empty smap_empty [] smap_empty smap_empty
                  smap_empty smap_empty [].

Inductive vm_scope_id : Type :=
| VMSNormal (k : Z)
| VMSCleanup (k : Z).

Definition vm_scope_id_eqb (a b : vm_scope_id) : bool :=
  match a with
  | VMSNormal x => match b with VMSNormal y => Z.eqb x y | _ => false end
  | VMSCleanup x => match b with VMSCleanup y => Z.eqb x y | _ => false end
  end.

Record c_lower_scope : Type := mkCLowerScope {
  ls_vm_scopes : list vm_scope_id;
  ls_vm_switch : list vm_scope_id;
  ls_cleanup_at : smap (list Z);
  ls_labels_taken : list string;
  ls_va_args : option term;
  ls_sret : option term;
}.

Definition empty_lower_scope : c_lower_scope :=
  mkCLowerScope [] [] smap_empty [] None None.

Inductive switch_case : Type :=
| SCCase (val : Z) (lbl : string)
| SCRange (lo hi : Z) (lbl : string)
| SCDefault (lbl : string).

Record cleanup_info : Type := mkCleanupInfo {
  ci_node : c_typed_node;
  ci_binds : list (string * ord_binding);
  ci_ctx : c_lower_ctx;
}.

Record c_build_st : Type := mkCBuildSt {
  bs_rev_allocs : list (list Z * term);
  bs_active_origins : list Z;
  bs_origin_n : Z;
  bs_rev_records : list term;
  bs_bindings : nmap term;
  bs_hints : nmap term;
  bs_active_loc : term;
}.

Definition open_block : Type := (string * list (list Z * term))%type.
Definition closed_block : Type :=
  (string * list (list Z * term) * list (list Z * term) * (list Z * term))%type.

Record c_func_st : Type := mkCFuncSt {
  fs_env : c_type_env;
  fs_lscope : c_lower_scope;
  fs_globals : c_lower_globals;
  fs_cur : option open_block;
  fs_insts : list (list Z * term);
  fs_blocks : list closed_block;
  fs_n : Z;
  fs_labels : smap string;
  fs_vm_labels : smap (list vm_scope_id);
  fs_vm_gotos : list (string * list vm_scope_id * c_loc);
  fs_cleanups : smap cleanup_info;
  fs_cleanup_gotos : smap (list (string * list Z));
  fs_computed_goto : option (string * term * c_loc);
  fs_cases : list switch_case;
  fs_build : c_build_st;
  fs_opts : c_lower_opts;
}.

Inductive l_res (A : Type) : Type :=
| LOk (v : A) (st : c_func_st)
| LErr (msg : string).

Arguments LOk {A} v st.
Arguments LErr {A} msg.

Definition l_ret {A : Type} (v : A) (st : c_func_st) : l_res A := LOk v st.

Definition l_bind {A B : Type} (m : c_func_st -> l_res A) (f : A -> c_func_st -> l_res B)
  (st : c_func_st) : l_res B :=
  match m st with
  | LOk a st1 => f a st1
  | LErr msg => LErr msg
  end.

Notation "'let!' x ':=' e1 'in' e2" :=
  (l_bind e1 (fun x => e2)) (at level 60, right associativity).

Definition sema_msg (loc : c_loc) (msg : string) : string :=
  match loc with
  | LocEof => "eof: " ++ msg
  | Loc f l =>
      if (f == "constant") && Z.eqb l 0 then "constant: " ++ msg
      else if (f == "unknown") && Z.eqb l 0 then "unknown: " ++ msg
      else loc_to_string loc ++ ": " ++ msg
  end.

Definition l_err {A : Type} (loc : c_loc) (msg : string) (_ : c_func_st) : l_res A :=
  LErr (sema_msg loc msg).

Definition l_fail {A : Type} (msg : string) (_ : c_func_st) : l_res A :=
  LErr msg.

Definition l_tr_msg (loc : c_loc) (e : c_type_err) : string :=
  match e with
  | TESema m => m
  | TEBad why => sema_msg loc why
  | TENotConstant => sema_msg loc "expression is not a constant"
  end.

Definition next_env_id (env0 : c_type_env) : Z * c_type_env :=
  let df := te_defs env0 in
  let n := df_next df in
  let df1 := mkCDefs (df_su df) (df_qmembers df) (df_transparent df)
                     (df_aligned_typedefs df) (df_expr_tags df) (n + 1) in
  (n, with_defs env0 df1).

Definition set_fs_env (env : c_type_env) (st : c_func_st) : c_func_st :=
  mkCFuncSt env (fs_lscope st) (fs_globals st) (fs_cur st) (fs_insts st)
            (fs_blocks st) (fs_n st) (fs_labels st) (fs_vm_labels st)
            (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
            (fs_computed_goto st) (fs_cases st) (fs_build st) (fs_opts st).

Definition set_fs_lscope (ls : c_lower_scope) (st : c_func_st) : c_func_st :=
  mkCFuncSt (fs_env st) ls (fs_globals st) (fs_cur st) (fs_insts st)
            (fs_blocks st) (fs_n st) (fs_labels st) (fs_vm_labels st)
            (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
            (fs_computed_goto st) (fs_cases st) (fs_build st) (fs_opts st).

Definition set_fs_globals (lg : c_lower_globals) (st : c_func_st) : c_func_st :=
  mkCFuncSt (fs_env st) (fs_lscope st) lg (fs_cur st) (fs_insts st)
            (fs_blocks st) (fs_n st) (fs_labels st) (fs_vm_labels st)
            (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
            (fs_computed_goto st) (fs_cases st) (fs_build st) (fs_opts st).

Definition set_fs_build (b : c_build_st) (st : c_func_st) : c_func_st :=
  mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) (fs_cur st) (fs_insts st)
            (fs_blocks st) (fs_n st) (fs_labels st) (fs_vm_labels st)
            (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
            (fs_computed_goto st) (fs_cases st) b (fs_opts st).

Definition set_fs_cur (cur : option open_block) (st : c_func_st) : c_func_st :=
  mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) cur (fs_insts st)
            (fs_blocks st) (fs_n st) (fs_labels st) (fs_vm_labels st)
            (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
            (fs_computed_goto st) (fs_cases st) (fs_build st) (fs_opts st).

Definition set_fs_cases (cs : list switch_case) (st : c_func_st) : c_func_st :=
  mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) (fs_cur st) (fs_insts st)
            (fs_blocks st) (fs_n st) (fs_labels st) (fs_vm_labels st)
            (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
            (fs_computed_goto st) cs (fs_build st) (fs_opts st).

(** ## Type classifiers and small semantic helpers *)

Definition is_su (t : c_type) : bool :=
  match t with TStruct _ | TUnion _ => true | _ => false end.

Definition is_memtype (t : c_type) : bool :=
  match t with TStruct _ | TUnion _ | TVec _ _ _ => true | _ => false end.

Definition is_abi_memory (t : c_type) : bool :=
  match t with
  | TStruct _ | TUnion _ | TVec _ _ _ | TFloatK FLDouble => true
  | _ => false
  end.

Definition is_aggregate (t : c_type) : bool :=
  match t with
  | TArray _ _ | TUnion _ => true
  | TStruct id => match complex_type (TStruct id) with Some _ => false | None => true end
  | _ => false
  end.

Definition is_char_type (t : c_type) : bool :=
  match t with TIntK IChar | TIntK ISChar | TIntK IUChar => true | _ => false end.

Definition qualified_with (t : c_type) (q : c_qual) : bool :=
  match t with
  | TQual qs _ => existsb (c_qual_eqb q) qs
  | _ => false
  end.

Definition atomic_or_volatile (t : c_type) : bool :=
  atomic_qualified t || qualified_with t QVolatile.

Definition narrow_type_atom (size : Z) (sg : c_sign) : option string :=
  match sg with
  | CSigned =>
      if Z.eqb size 4 then Some "sw"
      else if Z.eqb size 2 then Some "sh"
      else if Z.eqb size 1 then Some "sb"
      else None
  | CUnsigned =>
      if Z.eqb size 4 then Some "uw"
      else if Z.eqb size 2 then Some "uh"
      else if Z.eqb size 1 then Some "ub"
      else None
  end.

Definition load_op (t : c_type) : option (string * string) :=
  match int_info t, type_class t with
  | Some (sz, sg), Some cls =>
      if Z.eqb sz 8 then Some (cls, "l")
      else
        match narrow_type_atom sz sg with
        | Some op => Some (cls, op)
        | None => None
        end
  | None, Some cls => Some (cls, cls)
  | _, _ => None
  end.

Definition store_width (t : c_type) : option string :=
  match t with
  | TPtr _ => Some "p"
  | TFloatK FFloat => Some "s"
  | TFloatK FDouble => Some "d"
  | TFloatK FLDouble => Some "x"
  | _ =>
      match int_info t with
      | Some (sz, _) =>
          if Z.eqb sz 1 then Some "b"
          else if Z.eqb sz 2 then Some "h"
          else if Z.eqb sz 4 then Some "w"
          else if Z.eqb sz 8 then Some "l"
          else None
      | None => None
      end
  end.

Definition ir_width_bytes (w : string) : Z :=
  if w == "b" then 1
  else if w == "h" then 2
  else if (w == "w") || (w == "s") then 4
  else if (w == "l") || (w == "p") || (w == "d") then 8
  else if w == "x" then 10
  else 0.

Definition unsupported_type_msg (t : c_type) : option string :=
  match bad_type t with
  | Some why => Some (why ++ " is not supported")
  | None => None
  end.

Definition check_supported (t : c_type) (loc : c_loc) : option string :=
  match unsupported_type_msg t with
  | Some msg => Some (sema_msg loc msg)
  | None => None
  end.

Definition expression_type (e : c_expr) (env : c_type_env) : option c_type :=
  match elaborate e env with
  | TOk (Some x) => Some (tree_type x)
  | _ => None
  end.

Definition is_setjmp_sym (s : string) : bool :=
  (s == "setjmp") || (s == "_setjmp") || (s == "sigsetjmp").

Definition class_bits_Z (k : string) : Z :=
  if k == "w" then 32 else 64.

(** ## Provenance recording and block/instruction primitives

    Each emitted instruction, hoisted allocation, phi, and terminator is paired
    with the active origin list from [c_build_st] so [CLower.function] can
    assemble the exact `context(Sym, Records)` item after lowering the body. *)

Definition l_record (r : term) (st : c_func_st) : c_func_st :=
  let b := fs_build st in
  let '(bs1, hs1) :=
    match r with
    | TApp f (id :: _ :: _ :: _ :: nil) =>
        if f == "binding" then (nm_add id r (bs_bindings b), bs_hints b)
        else (bs_bindings b, bs_hints b)
    | TApp f [t; h] =>
        if f == "hint" then (bs_bindings b, nm_add t h (bs_hints b))
        else (bs_bindings b, bs_hints b)
    | _ => (bs_bindings b, bs_hints b)
    end in
  set_fs_build
    (mkCBuildSt (bs_rev_allocs b) (bs_active_origins b) (bs_origin_n b)
                (r :: bs_rev_records b) bs1 hs1 (bs_active_loc b))
    st.

Definition l_enter_origin (loc0 : c_loc) (desc : term) (st : c_func_st)
  : (list Z * term) * c_func_st :=
  let b := fs_build st in
  let parent := bs_active_origins b in
  let parent_loc := bs_active_loc b in
  let n := bs_origin_n b in
  let loc_t := source_location_term loc0 in
  let b1 := mkCBuildSt (bs_rev_allocs b) [n] (n + 1) (bs_rev_records b)
                       (bs_bindings b) (bs_hints b) loc_t in
  let orig := TApp "origin" [Term.TInt n; loc_t; desc; TList (map Term.TInt parent)] in
  ((parent, parent_loc), l_record orig (set_fs_build b1 st)).

Definition l_restore_origin (saved : list Z * term) (st : c_func_st) : c_func_st :=
  let b := fs_build st in
  set_fs_build
    (mkCBuildSt (bs_rev_allocs b) (fst saved) (bs_origin_n b) (bs_rev_records b)
                (bs_bindings b) (bs_hints b) (snd saved))
    st.

Definition address_binding_of (b_atom : term) (bs hs : nmap term) : option term :=
  if nm_mem b_atom bs then Some b_atom
  else
    match nm_find b_atom hs with
    | Some (TApp f [id; role]) =>
        if (f == "named") && is_atom "address" role then Some id else None
    | _ => None
    end.

Definition l_name_value (v b_term : term) (role : string) (st : c_func_st) : c_func_st :=
  match tmp_name v, tmp_name b_term with
  | [t], [b] =>
      let bld := fs_build st in
      match address_binding_of b (bs_bindings bld) (bs_hints bld) with
      | Some id =>
          if nm_mem t (bs_hints bld) then st
          else l_record (TApp "hint" [t; TApp "named" [id; TAtom role]]) st
      | None => st
      end
  | _, _ => st
  end.

Definition l_name_values (vs : list term) (b_term : term) (role : string)
  (st : c_func_st) : c_func_st :=
  fold_left (fun s v => l_name_value v b_term role s) vs st.

Definition l_binding_context (name : string) (val : ord_binding) (st : c_func_st) : c_func_st :=
  match val with
  | BVar (VSNamed b) _ =>
      let ty :=
        match expression_type (EId name) (fs_env st) with
        | Some t => t
        | None => TVoid
        end in
      let loc_t := bs_active_loc (fs_build st) in
      let st1 := l_record (TApp "binding" [TAtom b; TAtom name; c_type_to_term ty; loc_t]) st in
      l_name_value (ir_tmp b) (ir_tmp b) "address" st1
  | BGVar _ sym _ _ =>
      let key := ir_global sym in
      if nm_mem key (bs_bindings (fs_build st)) then st
      else
        let ty :=
          match expression_type (EId name) (fs_env st) with
          | Some t => t
          | None => TVoid
          end in
        l_record (TApp "binding" [key; TAtom name; c_type_to_term ty; TAtom "none"]) st
  | _ => st
  end.

Definition scalar_store_matches (w : string) (u : c_type) : bool :=
  match store_width u with Some w' => w == w' | None => false end.

Definition scalar_load_matches (k op : string) (u : c_type) : bool :=
  match load_op u with Some (k', op') => (k == k') && (op == op') | None => false end.

Definition c_type_from_binding_term (r : term) (st : c_func_st) : option c_type :=
  match r with
  | TApp _ [_; TAtom nm; _; _] =>
      match lookup_ordinary (fs_env st) nm with
      | Some (BVar _ ty) => Some ty
      | Some (BGVar ty _ _ _) => Some ty
      | _ => None
      end
  | _ => None
  end.

Fixpoint unqual_term (t : term) : term :=
  match t with
  | TApp f [_; inner] => if f == "qualified" then unqual_term inner else t
  | _ => t
  end.

Definition scalar_access_term_store (w : string) (t0 : term) : bool :=
  match unqual_term t0 with
  | TApp f [_] => (f == "ptr") && (w == "p")
  | TAtom a =>
      if (a == "char") || (a == "schar") || (a == "uchar") || (a == "bool") then w == "b"
      else if (a == "short") || (a == "ushort") then w == "h"
      else if (a == "int") || (a == "uint") then w == "w"
      else if (a == "long") || (a == "ulong") || (a == "llong") || (a == "ullong") then w == "l"
      else if a == "float" then w == "s"
      else if a == "double" then w == "d"
      else if a == "ldouble" then w == "x"
      else false
  | _ => false
  end.

Definition scalar_access_term_load (k op : string) (t0 : term) : bool :=
  match unqual_term t0 with
  | TApp f [_] => (f == "ptr") && (k == "p") && (op == "p")
  | TAtom a =>
      if (a == "char") || (a == "schar") then (k == "w") && (op == "sb")
      else if (a == "uchar") || (a == "bool") then (k == "w") && (op == "ub")
      else if a == "short" then (k == "w") && (op == "sh")
      else if a == "ushort" then (k == "w") && (op == "uh")
      else if a == "int" then (k == "w") && (op == "sw")
      else if a == "uint" then (k == "w") && (op == "uw")
      else if (a == "long") || (a == "ulong") || (a == "llong") || (a == "ullong") then
        (k == "l") && (op == "l")
      else if a == "float" then (k == "s") && (op == "s")
      else if a == "double" then (k == "d") && (op == "d")
      else if a == "ldouble" then (k == "x") && (op == "x")
      else false
  | _ => false
  end.

Definition l_stored_name (inst : term) (st : c_func_st) : c_func_st :=
  let bld := fs_build st in
  match inst with
  | TApp f [TAtom w; v; addr] =>
      if f == "store" then
        match tmp_name addr with
        | [a] =>
            match address_binding_of a (bs_bindings bld) (bs_hints bld) with
            | Some b =>
                match nm_find b (bs_bindings bld) with
                | Some (TApp _ [_; _; ty_t; _]) =>
                    if scalar_access_term_store w (unqual_term ty_t) then
                      l_name_value v addr "value" st
                    else st
                | _ => st
                end
            | None => st
            end
        | _ => st
        end
      else st
  | TApp f [v; TAtom k; TApp lf [TAtom op]; TList [addr]] =>
      if (f == "let") && (lf == "load") then
        match tmp_name addr with
        | [a] =>
            match address_binding_of a (bs_bindings bld) (bs_hints bld) with
            | Some b =>
                match nm_find b (bs_bindings bld) with
                | Some (TApp _ [_; _; ty_t; _]) =>
                    if scalar_access_term_load k op ty_t then
                      l_name_value v addr "value" st
                    else st
                | _ => st
                end
            | None => st
            end
        | _ => st
        end
      else st
  | _ => st
  end.

Definition l_typed_origin (x : c_typed_node) (ctx : c_lower_ctx) (st : c_func_st)
  : (list Z * term) * c_func_st :=
  match x with
  | TNode cat ty form =>
      let form_t := shallow_node_term form (fs_env st) in
      let desc := TApp "typed" [TAtom (node_cat_name cat); c_type_to_term ty; form_t] in
      l_enter_origin (ctx_loc ctx) desc st
  end.

Definition l_result_name (x : c_typed_node) (r : c_val) (st : c_func_st) : c_func_st :=
  match x, r with
  | TNode CatVal _ (TFLoad (TNode CatObj _ (TFId name))), CVal v _ =>
      match lookup_ordinary (fs_env st) name with
      | Some (BVar (VSNamed b) _) => l_name_value v (ir_tmp b) "value" st
      | _ => st
      end
  | _, _ => st
  end.

Definition l_fresh (st : c_func_st) : term * c_func_st :=
  let n0 := fs_n st in
  let nm := "v" ++ decimal n0 in
  (ir_tmp nm,
   mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) (fs_cur st) (fs_insts st)
             (fs_blocks st) (n0 + 1) (fs_labels st) (fs_vm_labels st)
             (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
             (fs_computed_goto st) (fs_cases st) (fs_build st) (fs_opts st)).

Definition l_label (st : c_func_st) : string * c_func_st :=
  let n0 := fs_n st in
  let lbl := "L" ++ decimal n0 in
  (lbl,
   mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) (fs_cur st) (fs_insts st)
             (fs_blocks st) (n0 + 1) (fs_labels st) (fs_vm_labels st)
             (fs_vm_gotos st) (fs_cleanups st) (fs_cleanup_gotos st)
             (fs_computed_goto st) (fs_cases st) (fs_build st) (fs_opts st)).

Definition l_ensure_live (st : c_func_st) : c_func_st :=
  match fs_cur st with
  | Some _ => st
  | None =>
      let '(lbl, st1) := l_label st in
      set_fs_cur (Some (lbl, [])) st1
  end.

Definition l_emit (inst : term) (st : c_func_st) : c_func_st :=
  let st1 := l_ensure_live st in
  let st2 := l_stored_name inst st1 in
  let os := bs_active_origins (fs_build st2) in
  mkCFuncSt (fs_env st2) (fs_lscope st2) (fs_globals st2) (fs_cur st2)
            ((os, inst) :: fs_insts st2) (fs_blocks st2) (fs_n st2) (fs_labels st2)
            (fs_vm_labels st2) (fs_vm_gotos st2) (fs_cleanups st2)
            (fs_cleanup_gotos st2) (fs_computed_goto st2) (fs_cases st2)
            (fs_build st2) (fs_opts st2).

Definition l_term (jmp : term) (st : c_func_st) : c_func_st :=
  let st1 := l_ensure_live st in
  let os := bs_active_origins (fs_build st1) in
  match fs_cur st1 with
  | Some (lbl, phis) =>
      let blk : closed_block := (lbl, phis, rev (fs_insts st1), (os, jmp)) in
      mkCFuncSt (fs_env st1) (fs_lscope st1) (fs_globals st1) None []
                (blk :: fs_blocks st1) (fs_n st1) (fs_labels st1)
                (fs_vm_labels st1) (fs_vm_gotos st1) (fs_cleanups st1)
                (fs_cleanup_gotos st1) (fs_computed_goto st1) (fs_cases st1)
                (fs_build st1) (fs_opts st1)
  | None => st1
  end.

Definition l_start (lbl : string) (st : c_func_st) : c_func_st :=
  let st1 :=
    match fs_cur st with
    | None => st
    | Some _ => l_term (ir_goto lbl) st
    end in
  set_fs_cur (Some (lbl, [])) st1.

Definition l_start_phi (lbl : string) (phis : list term) (st : c_func_st) : c_func_st :=
  let os := bs_active_origins (fs_build st) in
  set_fs_cur (Some (lbl, map (fun p => (os, p)) phis)) st.

Definition l_here (st : c_func_st) : string * c_func_st :=
  let st1 := l_ensure_live st in
  match fs_cur st1 with
  | Some (lbl, _) => (lbl, st1)
  | None => ("", st1)
  end.

Definition l_add_alloc (inst : term) (st : c_func_st) : c_func_st :=
  let b := fs_build st in
  set_fs_build
    (mkCBuildSt ((bs_active_origins b, inst) :: bs_rev_allocs b)
                (bs_active_origins b) (bs_origin_n b) (bs_rev_records b)
                (bs_bindings b) (bs_hints b) (bs_active_loc b))
    st.

Definition l_let (cls : string) (op : term) (args : list term) (st : c_func_st)
  : term * c_func_st :=
  let '(d, st1) := l_fresh st in
  (d, l_emit (ir_let d cls op args) st1).

Definition l_offset (addr : term) (off : Z) (st : c_func_st) : term * c_func_st :=
  if Z.eqb off 0 then (addr, st)
  else l_let "p" (TAtom "add") [addr; ir_const off] st.

Definition l_goto_label (name : string) (st : c_func_st) : string * c_func_st :=
  match smap_find name (fs_labels st) with
  | Some lbl => (lbl, st)
  | None =>
      let n0 := fs_n st in
      let lbl := "L" ++ decimal n0 in
      (lbl,
       mkCFuncSt (fs_env st) (fs_lscope st) (fs_globals st) (fs_cur st) (fs_insts st)
                 (fs_blocks st) (n0 + 1) (smap_add name lbl (fs_labels st))
                 (fs_vm_labels st) (fs_vm_gotos st) (fs_cleanups st)
                 (fs_cleanup_gotos st) (fs_computed_goto st) (fs_cases st)
                 (fs_build st) (fs_opts st))
  end.

Definition l_bind_ord (name : string) (val : ord_binding) (st : c_func_st) : c_func_st :=
  let st1 := set_fs_env (bind_ordinary name val (fs_env st)) st in
  l_binding_context name val st1.

Definition l_local_slot_min (ty : c_type) (min_al : Z) (st : c_func_st) : l_res term :=
  match type_size_align ty (fs_env st) with
  | TErr err => LErr (l_tr_msg unknown_loc err)
  | TOk (sz0, al0) =>
      let al := Z.max 4 (Z.max al0 min_al) in
      let sz := Z.max sz0 1 in
      let '(addr, st1) := l_fresh st in
      LOk addr (l_add_alloc (ir_let addr "p" (TApp "alloc" [Term.TInt al]) [ir_const sz]) st1)
  end.

Definition l_local_slot (ty : c_type) (st : c_func_st) : l_res term :=
  l_local_slot_min ty 1 st.

(** ## Global literal table helpers

    Equal string literals share one `str.N` symbol across a translation unit.
    The key encodes byte lists and wide element lists unambiguously so wide and
    narrow literals never collide. *)

Definition lit_key (lit : lit_entry) : string :=
  match lit with
  | LitBytes bs =>
      "b:" ++ String.concat "," (map decimal bs)
  | LitWide wt vs =>
      "w:" ++ c_type_diag_str wt ++ ":" ++ String.concat "," (map decimal vs)
  end.

Definition new_literal_g (lit : lit_entry) (env0 : c_type_env) (lg0 : c_lower_globals)
  : string * c_type_env * c_lower_globals :=
  let key := lit_key lit in
  match smap_find key (lg_lit_of lg0) with
  | Some sym => (sym, env0, lg0)
  | None =>
      let '(n, env1) := next_env_id env0 in
      let sym := "str." ++ decimal n in
      let lg1 :=
        mkCLowerGlobals
          (lg_gdefs lg0) (lg_gdef_syms lg0)
          (smap_add sym lit (lg_lits lg0)) (sym :: lg_lit_syms lg0)
          (smap_add key sym (lg_lit_of lg0)) (lg_func_names lg0)
          (lg_deferred lg0) (lg_inline_copy lg0) (lg_inline_copy_of lg0)
          (lg_inline_attr lg0) (lg_readonly lg0) (lg_galign lg0)
          (lg_qsym lg0) (lg_initialized lg0) (lg_inits lg0) in
      (sym, env1, lg1)
  end.

Definition func_literal_g (func : string) (env0 : c_type_env) (lg0 : c_lower_globals)
  : string * c_type_env * c_lower_globals :=
  match smap_find func (lg_func_names lg0) with
  | Some sym => (sym, env0, lg0)
  | None =>
      let '(sym, env1, lg1) := new_literal_g (LitBytes (string_to_bytes func)) env0 lg0 in
      let lg2 :=
        mkCLowerGlobals
          (lg_gdefs lg1) (lg_gdef_syms lg1) (lg_lits lg1) (lg_lit_syms lg1)
          (lg_lit_of lg1) (smap_add func sym (lg_func_names lg1))
          (lg_deferred lg1) (lg_inline_copy lg1) (lg_inline_copy_of lg1)
          (lg_inline_attr lg1) (lg_readonly lg1) (lg_galign lg1)
          (lg_qsym lg1) (lg_initialized lg1) (lg_inits lg1) in
      (sym, env1, lg2)
  end.

Definition l_new_literal (lit : lit_entry) (st : c_func_st) : string * c_func_st :=
  let '(sym, env1, lg1) := new_literal_g lit (fs_env st) (fs_globals st) in
  (sym, set_fs_globals lg1 (set_fs_env env1 st)).

Definition l_func_literal (func : string) (st : c_func_st) : string * c_func_st :=
  let '(sym, env1, lg1) := func_literal_g func (fs_env st) (fs_globals st) in
  (sym, set_fs_globals lg1 (set_fs_env env1 st)).

Definition l_safety_error (msg_bytes : list Z) (st : c_func_st) : c_func_st :=
  let '(sym, st1) := l_new_literal (LitBytes msg_bytes) st in
  let '(addr, st2) := l_let "p" (TAtom "copy") [ir_global sym] st1 in
  l_emit (ir_call (TAtom "void") (ir_global "zsafety_error") [ir_arg "p" addr]) st2.

(** ## SysV / Fil-C ABI eightbytes, object copies, and memory loads/stores

    Aggregate and long double values cross function boundaries as eightbytes
    classified according to the SysV x86-64 psABI and Fil-C's generic packet
    conventions. *)

Record abi_eb : Type := mkAbiEb {
  eb_off : Z;
  eb_bytes : Z;
  eb_class : string;
}.

Inductive abi_ret_shape : Type :=
| RetSret
| RetWords (ebs : list abi_eb).

Inductive leaf_kind : Type :=
| LKInt | LKPtr | LKFloat | LKDouble | LKX87.

Definition leaf_kind_eqb (a b : leaf_kind) : bool :=
  match a with
  | LKInt => match b with LKInt => true | _ => false end
  | LKPtr => match b with LKPtr => true | _ => false end
  | LKFloat => match b with LKFloat => true | _ => false end
  | LKDouble => match b with LKDouble => true | _ => false end
  | LKX87 => match b with LKX87 => true | _ => false end
  end.

Definition su_members_of (su : c_type) (env : c_type_env) : option (list c_member_layout) :=
  match su with
  | TStruct id =>
      match lookup_su_def env id with
      | Some (SUDef KStruct ms _ _) => Some ms
      | _ => None
      end
  | TUnion id =>
      match lookup_su_def env id with
      | Some (SUDef KUnion ms _ _) => Some ms
      | _ => None
      end
  | _ => None
  end.

Fixpoint ptr_offsets_aux (fuel : nat) (ty : c_type) (env : c_type_env)
  (base : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f =>
      match ty with
      | TPtr _ => base :: acc
      | TArray elem (ALConst n) =>
          let elem_offs := ptr_offsets_aux f elem env 0 [] in
          match elem_offs with
          | [] => acc
          | _ =>
              match type_size_align elem env with
              | TOk (sz, _) =>
                  fold_left (fun a i => ptr_offsets_aux f elem env (base + i * sz) a)
                            (numlist_Z 0 (n - 1)) acc
              | TErr _ => acc
              end
          end
      | TStruct _ | TUnion _ =>
          match su_members_of ty env with
          | Some ms =>
              fold_left
                (fun a m =>
                   match ml_bits m with
                   | MBNone => ptr_offsets_aux f (ml_type m) env (base + ml_off m) a
                   | MBBits _ _ => a
                   end)
                ms acc
          | None => acc
          end
      | _ => acc
      end
  end.

Definition ptr_offsets (ty : c_type) (env : c_type_env) : list Z :=
  ptr_offsets_aux (Z.to_nat 128) ty env 0 [].

Fixpoint leaves_aux (fuel : nat) (ty : c_type) (env : c_type_env)
  (base : Z) (acc : list (Z * leaf_kind)) : list (Z * leaf_kind) :=
  match fuel with
  | O => acc
  | S f =>
      match ty with
      | TFloatK FFloat => (base, LKFloat) :: acc
      | TFloatK FDouble => (base, LKDouble) :: acc
      | TFloatK FLDouble => (base, LKX87) :: acc
      | TPtr _ => (base, LKPtr) :: acc
      | TVec elem n _ => leaves_aux f (TArray elem (ALConst n)) env base acc
      | TArray elem (ALConst n) =>
          if 0 <? n then
            match type_size_align elem env with
            | TOk (sz, _) =>
                fold_left (fun a i => leaves_aux f elem env (base + i * sz) a)
                          (numlist_Z 0 (n - 1)) acc
            | TErr _ => acc
            end
          else acc
      | TArray _ _ => acc
      | TStruct _ | TUnion _ =>
          match su_members_of ty env with
          | Some ms =>
              fold_left
                (fun a m =>
                   match ml_bits m with
                   | MBNone => leaves_aux f (ml_type m) env (base + ml_off m) a
                   | MBBits _ _ => (base + ml_off m, LKInt) :: a
                   end)
                ms acc
          | None => acc
          end
      | _ => (base, LKInt) :: acc
      end
  end.

Definition type_leaves (ty : c_type) (env : c_type_env) : list (Z * leaf_kind) :=
  rev (leaves_aux (Z.to_nat 128) ty env 0 []).

Definition eightbytes (ty : c_type) (env : c_type_env) (loc : c_loc)
  : c_tr (list abi_eb) :=
  match type_size_align ty env with
  | TErr (TEBad why) =>
      sema_err loc (c_type_diag_str ty ++ " has an unsupported type (" ++ why ++ ")")
  | TErr err => TErr err
  | TOk (sz, _) =>
      let poffs := ptr_offsets ty env in
      let last := Z.div (sz + 7) 8 - 1 in
      TOk (map (fun i =>
                  let off := 8 * i in
                  let n := Z.min 8 (sz - off) in
                  let cls := if existsb (Z.eqb off) poffs then "p" else "l" in
                  mkAbiEb off n cls)
               (numlist_Z 0 last))
  end.

Definition byval_type (ty : c_type) (env : c_type_env) : bool :=
  match type_size_align ty env with
  | TOk (sz, _) => (16 <? sz) || unaligned_type ty env
  | TErr _ => false
  end.

Definition x87_type (ty : c_type) (env : c_type_env) : bool :=
  match ty with
  | TFloatK FLDouble => true
  | TStruct _ | TUnion _ =>
      existsb (fun p => leaf_kind_eqb (snd p) LKX87) (type_leaves ty env)
  | _ => false
  end.

Definition eightbyte_class (lvs : list (Z * leaf_kind)) (eb : abi_eb) : abi_eb :=
  if eb_class eb == "p" then eb
  else
    let o := eb_off eb in
    let end_o := o + 8 in
    let inside := filter (fun p => (o <=? fst p) && (fst p <? end_o)) lvs in
    let cls :=
      match inside with
      | [] => "l"
      | _ =>
          if forallb (fun p => leaf_kind_eqb (snd p) LKFloat || leaf_kind_eqb (snd p) LKDouble) inside then
            if existsb (fun p => leaf_kind_eqb (snd p) LKDouble) inside then "d"
            else if forallb (fun p => Z.eqb (fst p) o) inside then "s"
            else "l"
          else "l"
      end in
    mkAbiEb o (eb_bytes eb) cls.

Definition holds_leaf (lvs : list (Z * leaf_kind)) (eb : abi_eb) : bool :=
  let o := eb_off eb in
  let end_o := o + 8 in
  existsb (fun p =>
             let leaf_end :=
               if leaf_kind_eqb (snd p) LKX87 then fst p + 16 else fst p + 1 in
             (fst p <? end_o) && (o <? leaf_end)) lvs.

Definition classed_eightbytes (ty : c_type) (env : c_type_env) (loc : c_loc)
  : c_tr (list (Z * leaf_kind) * list abi_eb) :=
  match eightbytes ty env loc with
  | TErr err => TErr err
  | TOk ebs0 =>
      let lvs := type_leaves ty env in
      TOk (lvs, map (eightbyte_class lvs) ebs0)
  end.

Definition abi_eightbytes (ty : c_type) (env : c_type_env) (loc : c_loc)
  : c_tr (list abi_eb) :=
  match classed_eightbytes ty env loc with
  | TErr err => TErr err
  | TOk (lvs, ebs0) => TOk (filter (holds_leaf lvs) ebs0)
  end.

Definition arg_words (ty : c_type) (env : c_type_env) (loc : c_loc)
  : c_tr (list abi_eb) :=
  match ty with
  | TFloatK FLDouble => TOk [mkAbiEb 0 8 "l"; mkAbiEb 8 8 "l"]
  | _ =>
      if byval_type ty env then eightbytes ty env loc
      else abi_eightbytes ty env loc
  end.

Definition variadic_words (ty : c_type) (env : c_type_env) (loc : c_loc)
  : c_tr (list abi_eb) :=
  match ty with
  | TFloatK FLDouble => arg_words ty env loc
  | _ =>
      if byval_type ty env then arg_words ty env loc
      else
        match classed_eightbytes ty env loc with
        | TErr err => TErr err
        | TOk (_, ebs) => TOk ebs
        end
  end.

Definition ret_shape (ty : c_type) (env : c_type_env) (loc : c_loc)
  : c_tr abi_ret_shape :=
  match ty with
  | TFloatK FLDouble => TOk (RetWords [mkAbiEb 0 8 "l"; mkAbiEb 8 8 "l"])
  | _ =>
      if byval_type ty env then TOk RetSret
      else
        match abi_eightbytes ty env loc with
        | TErr err => TErr err
        | TOk ebs => TOk (RetWords ebs)
        end
  end.

Definition float_pair_type (ty : c_type) (env : c_type_env) : bool :=
  if byval_type ty env then false
  else
    match eightbytes ty env unknown_loc with
    | TErr _ => false
    | TOk ebs =>
        let lvs := type_leaves ty env in
        existsb
          (fun eb =>
             let o := eb_off eb in
             let end_o := o + 8 in
             let ts := filter (fun p => (o <=? fst p) && (fst p <? end_o)) lvs in
             match ts with
             | _ :: _ :: _ => forallb (fun p => leaf_kind_eqb (snd p) LKFloat) ts
             | _ => false
             end)
          ebs
    end.

Definition generic_only_type (ty : c_type) (env : c_type_env) : bool :=
  x87_type ty env || byval_type ty env || float_pair_type ty env.

Definition va_cells (ebs0 : list abi_eb) (lvs : list (Z * leaf_kind))
  (ty : c_type) (loc : c_loc) : c_tr (list abi_eb) :=
  let has_x87 := existsb (fun p => leaf_kind_eqb (snd p) LKX87) lvs in
  let x87_at (o : Z) :=
    existsb (fun p => Z.eqb (fst p) o && leaf_kind_eqb (snd p) LKX87) lvs in
  match ebs0 with
  | eb0 :: _ =>
      if has_x87 && negb (x87_at (eb_off eb0)) then
        sema_err loc ("va_arg of " ++ c_type_diag_str ty ++
                      ", which does not start with its long double, is not supported")
      else
        let fix go (es : list abi_eb) : list abi_eb :=
          match es with
          | [] => []
          | e1 :: tail =>
              match tail with
              | _ :: rest =>
                  if x87_at (eb_off e1) then mkAbiEb (eb_off e1) 10 "x" :: go rest
                  else
                    let k := if eb_class e1 == "p" then "p" else "l" in
                    mkAbiEb (eb_off e1) (eb_bytes e1) k :: go tail
              | [] =>
                  let k := if eb_class e1 == "p" then "p" else "l" in
                  [mkAbiEb (eb_off e1) (eb_bytes e1) k]
              end
          end in
        TOk (go ebs0)
  | [] => TOk []
  end.

Inductive pad_item : Type :=
| PIPad16
| PITerm (t : term).

Definition pad16_mark (ty : c_type) (env : c_type_env) (items : list term)
  : list pad_item :=
  let wrapped := map PITerm items in
  if x87_type ty env then PIPad16 :: wrapped else wrapped.

Fixpoint pad_args_aux (items : list pad_item) (n : Z) (acc : list term) : list term :=
  match items with
  | [] => rev acc
  | PIPad16 :: rest =>
      if Z.eqb (Z.modulo n 2) 1 then
        pad_args_aux rest (n + 1) (ir_arg "l" (ir_const 0) :: acc)
      else pad_args_aux rest n acc
  | PITerm t :: rest => pad_args_aux rest (n + 1) (t :: acc)
  end.

Fixpoint pad_params_aux (items : list pad_item) (n : Z) (acc : list term)
  (st : c_func_st) : list term * c_func_st :=
  match items with
  | [] => (rev acc, st)
  | PIPad16 :: rest =>
      if Z.eqb (Z.modulo n 2) 1 then
        let '(p, st1) := l_fresh st in
        pad_params_aux rest (n + 1) (ir_param "l" p :: acc) st1
      else pad_params_aux rest n acc st
  | PITerm t :: rest => pad_params_aux rest (n + 1) (t :: acc) st
  end.

Record copy_piece : Type := mkCopyPiece {
  cp_off : Z;
  cp_bytes : Z;
  cp_load : string;
  cp_store : string;
}.

Fixpoint pieces_aux (fuel : nat) (n off : Z) : list copy_piece :=
  match fuel with
  | O => []
  | S f =>
      if n <=? 0 then []
      else if 8 <=? n then mkCopyPiece off 8 "l" "l" :: pieces_aux f (n - 8) (off + 8)
      else if 4 <=? n then mkCopyPiece off 4 "uw" "w" :: pieces_aux f (n - 4) (off + 4)
      else if 2 <=? n then mkCopyPiece off 2 "uh" "h" :: pieces_aux f (n - 2) (off + 2)
      else mkCopyPiece off 1 "ub" "b" :: pieces_aux f (n - 1) (off + 1)
  end.

Definition split_pieces (n : Z) : list copy_piece :=
  pieces_aux 8 n 0.

Definition copy_object (ty : c_type) (src dst : term) (st : c_func_st) : l_res unit :=
  let env := fs_env st in
  match eightbytes ty env unknown_loc with
  | TErr err => LErr (l_tr_msg unknown_loc err)
  | TOk ebs =>
      match type_size_align ty env with
      | TErr err => LErr (l_tr_msg unknown_loc err)
      | TOk (sz, al) =>
          let use_memmove :=
            (40 <? sz) || ((al <? 8) && match ptr_offsets ty env with _ :: _ => true | [] => false end) in
          if use_memmove then
            LOk tt (l_emit (ir_call (TAtom "void") (ir_global "zmemmove")
                              [ir_arg "p" dst; ir_arg "p" src; ir_arg "l" (ir_const sz)]) st)
          else
            let st_end :=
              fold_left
                (fun s eb =>
                   let '(s_ptr, s1) := l_offset src (eb_off eb) s in
                   let '(d_ptr, s2) := l_offset dst (eb_off eb) s1 in
                   if eb_class eb == "p" then
                     let '(v, s3) := l_let "p" (TApp "load" [TAtom "p"]) [s_ptr] s2 in
                     l_emit (ir_store "p" v d_ptr) s3
                   else
                     fold_left
                       (fun sc cp =>
                          let '(sp, sc1) := l_offset s_ptr (cp_off cp) sc in
                          let '(dp, sc2) := l_offset d_ptr (cp_off cp) sc1 in
                          let '(v, sc3) := l_let "l" (TApp "load" [TAtom (cp_load cp)]) [sp] sc2 in
                          l_emit (ir_store (cp_store cp) v dp) sc3)
                       (split_pieces (eb_bytes eb)) s2)
                ebs st in
            LOk tt st_end
      end
  end.

Definition load_words (ebs : list abi_eb) (addr : term) (st : c_func_st)
  : list term * c_func_st :=
  let '(ws_rev, st1) :=
    fold_left
      (fun acc eb =>
         let '(ws, s) := acc in
         let '(p, s1) := l_offset addr (eb_off eb) s in
         let cls := eb_class eb in
         if (cls == "p") || (cls == "s") || (cls == "d") || (cls == "x") then
           let '(w, s2) := l_let cls (TApp "load" [TAtom cls]) [p] s1 in
           (w :: ws, s2)
         else
           let '(ow, s2) :=
             fold_left
               (fun pacc cp =>
                  let '(cur, sc) := pacc in
                  let '(p1, sc1) := l_offset p (cp_off cp) sc in
                  let '(pc0, sc2) := l_let "l" (TApp "load" [TAtom (cp_load cp)]) [p1] sc1 in
                  let '(pc, sc3) :=
                    if Z.eqb (cp_off cp) 0 then (pc0, sc2)
                    else l_let "l" (TAtom "shl") [pc0; ir_const (8 * cp_off cp)] sc2 in
                  match cur with
                  | None => (Some pc, sc3)
                  | Some prev =>
                      let '(joined, sc4) := l_let "l" (TAtom "or") [prev; pc] sc3 in
                      (Some joined, sc4)
                  end)
               (split_pieces (eb_bytes eb)) (None, s1) in
           (match ow with Some w => w | None => ir_const 0 end :: ws, s2))
      ebs ([], st) in
  (rev ws_rev, st1).

Definition store_words (ebs : list abi_eb) (ws : list term) (addr : term)
  (st : c_func_st) : c_func_st :=
  let fix go (es : list abi_eb) (vs : list term) (s : c_func_st) : c_func_st :=
    match es, vs with
    | eb :: er, w :: vr =>
        let '(p, s1) := l_offset addr (eb_off eb) s in
        let cls := eb_class eb in
        let s2 :=
          if (cls == "p") || (cls == "s") || (cls == "d") || (cls == "x") then
            l_emit (ir_store cls w p) s1
          else
            fold_left
              (fun sc cp =>
                 let '(p1, sc1) := l_offset p (cp_off cp) sc in
                 let '(pc, sc2) :=
                   if Z.eqb (cp_off cp) 0 then (w, sc1)
                   else l_let "l" (TAtom "shr") [w; ir_const (8 * cp_off cp)] sc1 in
                 l_emit (ir_store (cp_store cp) pc p1) sc2)
              (split_pieces (eb_bytes eb)) s1 in
        go er vr s2
    | _, _ => s
    end in
  go ebs ws st.

Definition vector_access (kind : string) (vt : c_type) (addr : term)
  (st : c_func_st) : l_res unit :=
  match type_size_align vt (fs_env st) with
  | TErr err => LErr (l_tr_msg unknown_loc err)
  | TOk (sz, al) =>
      LOk tt (l_emit (ir_access kind addr sz (Z.min al 8)) st)
  end.

Definition load_typed (ty : c_type) (addr : term) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res term :=
  match load_op ty with
  | Some (cls, op) =>
      let '(v, st1) := l_let cls (TApp "load" [TAtom op]) [addr] st in
      LOk v st1
  | None =>
      l_err (ctx_loc ctx) ("loading a " ++ c_type_diag_str ty ++ " value is not supported yet") st
  end.

Definition store_typed (ty : c_type) (v addr : term) (st : c_func_st) : l_res unit :=
  match ty with
  | TVec _ _ _ =>
      match eightbytes ty (fs_env st) unknown_loc with
      | TErr err => LErr (l_tr_msg unknown_loc err)
      | TOk ebs =>
          if forallb (fun eb => Z.eqb (eb_bytes eb) 8) ebs then
            let '(xs_rev, st1) :=
              fold_left
                (fun acc eb =>
                   let '(xs, s) := acc in
                   let '(sp, s1) := l_offset v (eb_off eb) s in
                   let '(x, s2) := l_let "l" (TApp "load" [TAtom "l"]) [sp] s1 in
                   (x :: xs, s2))
                ebs ([], st) in
            match vector_access "write" ty addr st1 with
            | LErr m => LErr m
            | LOk _ st2 =>
                let fix store_chunks (es : list abi_eb) (xs : list term) (s : c_func_st) :=
                  match es, xs with
                  | eb :: er, x :: xr =>
                      let '(dp, s1) := l_offset addr (eb_off eb) s in
                      store_chunks er xr (l_emit (ir_store "l" x dp) s1)
                  | _, _ => s
                  end in
                LOk tt (store_chunks ebs (rev xs_rev) st2)
            end
          else
            match vector_access "write" ty addr st with
            | LErr m => LErr m
            | LOk _ st1 => copy_object ty v addr st1
            end
      end
  | TStruct _ | TUnion _ => copy_object ty v addr st
  | _ =>
      match store_width ty with
      | Some w => LOk tt (l_emit (ir_store w v addr) st)
      | None => LErr ("cannot store " ++ c_type_diag_str ty)
      end
  end.

Definition loaded_val (u : c_type) (addr : term) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res c_val :=
  match u with
  | TVec _ _ _ =>
      match l_local_slot u st with
      | LErr m => LErr m
      | LOk cp st1 =>
          match vector_access "read" u addr st1 with
          | LErr m => LErr m
          | LOk _ st2 =>
              match copy_object u addr cp st2 with
              | LErr m => LErr m
              | LOk _ st3 => LOk (CVal cp u) st3
              end
          end
      end
  | TStruct _ | TUnion _ => LOk (CVal addr u) st
  | _ =>
      match load_typed u addr ctx st with
      | LErr m => LErr m
      | LOk v st1 => LOk (CVal v u) st1
      end
  end.

Definition abi_source (ty : c_type) (v : term) (st : c_func_st) : l_res term :=
  match ty with
  | TFloatK FLDouble =>
      match l_local_slot TLDouble st with
      | LErr m => LErr m
      | LOk addr st1 => LOk addr (l_emit (ir_store "x" v addr) st1)
      end
  | _ => LOk v st
  end.

Definition arm_value (ty : c_type) (v : term) (st : c_func_st) : l_res term :=
  match ty with
  | TFloatK FLDouble => abi_source TLDouble v st
  | _ => LOk v st
  end.

Definition lanes_loaded (vt : c_type) (addr : term) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res (list term) :=
  match vt with
  | TVec elem n _ =>
      match type_size_align elem (fs_env st) with
      | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
      | TOk (es, _) =>
          let fix go (is_ : list Z) (acc : list term) (s : c_func_st) : l_res (list term) :=
            match is_ with
            | [] => LOk (rev acc) s
            | i :: rest =>
                let '(p, s1) := l_offset addr (i * es) s in
                match load_typed elem p ctx s1 with
                | LErr m => LErr m
                | LOk x s2 => go rest (x :: acc) s2
                end
            end in
          go (numlist_Z 0 (n - 1)) [] st
      end
  | _ => LErr "lanes_loaded on non-vector"
  end.

Definition lanes_stored (vt : c_type) (addr : term) (i0 : Z) (xs : list term)
  (st : c_func_st) : l_res unit :=
  match vt with
  | TVec elem _ _ =>
      match type_size_align elem (fs_env st) with
      | TErr err => LErr (l_tr_msg unknown_loc err)
      | TOk (es, _) =>
          let fix go (i : Z) (vs : list term) (s : c_func_st) : l_res unit :=
            match vs with
            | [] => LOk tt s
            | x :: rest =>
                let '(p, s1) := l_offset addr (i * es) s in
                match store_typed elem x p s1 with
                | LErr m => LErr m
                | LOk _ s2 => go (i + 1) rest s2
                end
            end in
          go i0 xs st
      end
  | _ => LErr "lanes_stored on non-vector"
  end.

Fixpoint zero_bytes_aux (fuel : nat) (addr : term) (off sz al : Z)
  (st : c_func_st) : c_func_st :=
  match fuel with
  | O => st
  | S f =>
      if sz <=? off then st
      else
        let left := sz - off in
        let '(w, n) :=
          if (8 <=? left) && (8 <=? al) && Z.eqb (Z.modulo off 8) 0 then ("l", 8)
          else if (4 <=? left) && (4 <=? al) && Z.eqb (Z.modulo off 4) 0 then ("w", 4)
          else if (2 <=? left) && (2 <=? al) && Z.eqb (Z.modulo off 2) 0 then ("h", 2)
          else ("b", 1) in
        let '(p, st1) := l_offset addr off st in
        let st2 := l_emit (ir_store w (ir_const 0) p) st1 in
        zero_bytes_aux f addr (off + n) sz al st2
  end.

Definition zero_object (addr : term) (ty : c_type) (st : c_func_st) : l_res unit :=
  match type_size_align ty (fs_env st) with
  | TErr err => LErr (l_tr_msg unknown_loc err)
  | TOk (sz, al) =>
      LOk tt (zero_bytes_aux (Z.to_nat (sz + 1)) addr 0 sz al st)
  end.

Definition normalize_call_result (ty : c_type) (v0 : term) (st : c_func_st)
  : term * c_func_st :=
  match int_info ty with
  | Some (sz, sg) =>
      if sz <? 4 then
        match narrow_type_atom sz sg with
        | Some op => l_let "w" (TApp "ext" [TAtom op]) [v0] st
        | None => (v0, st)
        end
      else (v0, st)
  | None => (v0, st)
  end.

(** ## VLA extents, truth tests, conversions, and scalar/complex/vector ops

    Scalar, pointer, complex, and vector conversions and operators live here
    together because complex and vector operations recurse mutually with
    conversions and binary operators. *)

Definition l_product (a b : term) (st : c_func_st) : term * c_func_st :=
  match a, b with
  | TApp fa [Term.TInt na], TApp fb [Term.TInt nb] =>
      if (fa == "const") && (fb == "const") then (ir_const (na * nb), st)
      else l_let "l" (TAtom "mul") [a; b] st
  | _, TApp fb [Term.TInt 1] =>
      if fb == "const" then (a, st) else l_let "l" (TAtom "mul") [a; b] st
  | _, _ => l_let "l" (TAtom "mul") [a; b] st
  end.

Fixpoint extent_aux (fuel : nat) (ty : c_type) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res term :=
  match fuel with
  | O => l_err (ctx_loc ctx) "extent recursion limit" st
  | S f =>
      if vla_type ty then
        match ty with
        | TArray elem len =>
            match extent_aux f elem ctx st with
            | LErr m => LErr m
            | LOk esz st1 =>
                match len with
                | ALDyn s =>
                    let '(res, st2) := l_product (dyn_str_to_term s) esz st1 in
                    LOk res st2
                | ALConst n =>
                    let '(res, st2) := l_product (ir_const n) esz st1 in
                    LOk res st2
                | _ => l_err (ctx_loc ctx) "the length of a variable length array is not known here" st1
                end
            end
        | _ => l_err (ctx_loc ctx) "invalid VLA type" st
        end
      else
        match type_size_align ty (fs_env st) with
        | TOk (sz, _) => LOk (ir_const sz) st
        | TErr (TEBad why) =>
            l_err (ctx_loc ctx) ("size of " ++ c_type_diag_str ty ++ " (" ++ why ++ ")") st
        | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
        end
  end.

Definition extent (ty : c_type) (ctx : c_lower_ctx) (st : c_func_st) : l_res term :=
  extent_aux (Z.to_nat 128) ty ctx st.

Definition truth_val (cv : c_val) (ctx : c_lower_ctx) (st : c_func_st) : l_res term :=
  let '(CVal v ty) := cv in
  match type_class ty with
  | Some k =>
      if k == "w" then LOk v st
      else if k == "l" then
        let '(w, st1) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom "l"]) [v; ir_const 0] st in
        LOk w st1
      else if float_type ty then
        let '(w, st1) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom k]) [v; ir_const 0] st in
        LOk w st1
      else
        match ty with
        | TPtr _ =>
            let '(iv, st1) := l_let "l" (TAtom "ptoi") [v] st in
            let '(w, st2) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom "l"]) [iv; ir_const 0] st1 in
            LOk w st2
        | _ => l_err (ctx_loc ctx) ("a " ++ c_type_diag_str ty ++ " value is not a scalar") st
        end
  | None => l_err (ctx_loc ctx) ("a " ++ c_type_diag_str ty ++ " value is not a scalar") st
  end.

Definition representable (sz_from : Z) (sg_from : c_sign) (sz_to : Z) (sg_to : c_sign) : bool :=
  if sz_from <? sz_to then
    match sg_to, sg_from with
    | CSigned, _ => true
    | CUnsigned, CUnsigned => true
    | _, _ => false
    end
  else Z.eqb sz_from sz_to && c_sign_eqb sg_from sg_to.

Definition int_convert (from_t to_t : c_type) (v : term) (st : c_func_st)
  : term * c_func_st :=
  match int_info from_t, int_info to_t with
  | Some (sz_f, sg_f), Some (sz_t, sg_t) =>
      if Z.eqb sz_t 8 && (sz_f <? 8) then
        match narrow_type_atom 4 sg_f with
        | Some op => l_let "l" (TApp "ext" [TAtom op]) [v] st
        | None => (v, st)
        end
      else if (sz_t <? 4) && negb (representable sz_f sg_f sz_t sg_t) then
        match narrow_type_atom sz_t sg_t with
        | Some op => l_let "w" (TApp "ext" [TAtom op]) [v] st
        | None => (v, st)
        end
      else (v, st)
  | _, _ => (v, st)
  end.

Definition int_float_op (ik : string) (sg : c_sign) : string :=
  match sg with
  | CSigned => if ik == "w" then "swtof" else "sltof"
  | CUnsigned => if ik == "w" then "uwtof" else "ultof"
  end.

Definition float_int_op (fk : string) (sg : c_sign) : string :=
  match sg with
  | CSigned => if fk == "s" then "stosi" else if fk == "d" then "dtosi" else "xtosi"
  | CUnsigned => if fk == "s" then "stoui" else if fk == "d" then "dtoui" else "xtoui"
  end.

Definition conversion_int_type (ik : string) (sg : c_sign) : c_type :=
  match sg with
  | CSigned => if ik == "w" then TInt else TLong
  | CUnsigned => if ik == "w" then TUInt else TULong
  end.

Definition cmp_op_names (op : c_binop) : option (string * string) :=
  match op with
  | BEq => Some ("eq", "eq")
  | BNe => Some ("ne", "ne")
  | BLt => Some ("slt", "ult")
  | BGt => Some ("sgt", "ugt")
  | BLe => Some ("sle", "ule")
  | BGe => Some ("sge", "uge")
  | _ => None
  end.

Definition arith_op_name (op : c_binop) (sg : c_sign) : string :=
  match op with
  | BAdd => "add"
  | BSub => "sub"
  | BMul => "mul"
  | BDiv => match sg with CSigned => "div" | CUnsigned => "udiv" end
  | BMod => match sg with CSigned => "rem" | CUnsigned => "urem" end
  | BAnd => "and"
  | BOr => "or"
  | BXor => "xor"
  | BShl => "shl"
  | BShr => match sg with CSigned => "sar" | CUnsigned => "shr" end
  | _ => "add"
  end.

Definition cx_parts (cv : c_val) (ctx : c_lower_ctx) (st : c_func_st)
  : l_res (c_val * c_val) :=
  let '(CVal addr ct) := cv in
  match complex_type ct with
  | Some f =>
      match type_size_align f (fs_env st) with
      | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
      | TOk (sz, _) =>
          match load_typed f addr ctx st with
          | LErr m => LErr m
          | LOk x st1 =>
              let '(p, st2) := l_offset addr sz st1 in
              match load_typed f p ctx st2 with
              | LErr m => LErr m
              | LOk y st3 => LOk (CVal x f, CVal y f) st3
              end
          end
      end
  | None => l_err (ctx_loc ctx) "not a complex value" st
  end.

Definition ptr_offset (op : c_binop) (vp : c_val) (elem : c_type)
  (vi : c_val) (conv_fn : c_val -> c_type -> c_func_st -> l_res c_val)
  (ctx : c_lower_ctx) (st : c_func_st) : l_res c_val :=
  let '(CVal p ptr_ty) := vp in
  let op_s := match op with BSub => "sub" | _ => "add" end in
  if vla_type elem then
    match extent elem ctx st with
    | LErr m => LErr m
    | LOk sz st1 =>
        match conv_fn vi TLong st1 with
        | LErr m => LErr m
        | LOk (CVal iv _) st2 =>
            let '(offv, st3) := l_product iv sz st2 in
            let '(r, st4) := l_let "p" (TAtom op_s) [p; offv] st3 in
            LOk (CVal r ptr_ty) st4
        end
    end
  else
    match arith_size elem (fs_env st) with
    | TErr (TEBad why) =>
        l_err (ctx_loc ctx) ("pointer arithmetic on " ++ c_type_diag_str elem ++ " (" ++ why ++ ")") st
    | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
    | TOk sz =>
        match conv_fn vi TLong st with
        | LErr m => LErr m
        | LOk (CVal iv _) st1 =>
            let '(offv, st2) :=
              match iv with
              | TApp f [Term.TInt n] =>
                  if f == "const" then (ir_const (n * sz), st1)
                  else if Z.eqb sz 1 then (iv, st1)
                  else l_let "l" (TAtom "mul") [iv; ir_const sz] st1
              | _ =>
                  if Z.eqb sz 1 then (iv, st1)
                  else l_let "l" (TAtom "mul") [iv; ir_const sz] st1
              end in
            let '(r, st3) := l_let "p" (TAtom op_s) [p; offv] st2 in
            LOk (CVal r ptr_ty) st3
        end
    end.

Definition ptr_diff (va vb : c_val) (elem : c_type) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res c_val :=
  let '(CVal a _) := va in
  let '(CVal b _) := vb in
  if vla_type elem then
    match extent elem ctx st with
    | LErr m => LErr m
    | LOk sz st1 =>
        let '(ia, st2) := l_let "l" (TAtom "ptoi") [a] st1 in
        let '(ib, st3) := l_let "l" (TAtom "ptoi") [b] st2 in
        let '(diff, st4) := l_let "l" (TAtom "sub") [ia; ib] st3 in
        let '(v, st5) := l_let "l" (TAtom "div") [diff; sz] st4 in
        LOk (CVal v TLong) st5
    end
  else
    match arith_size elem (fs_env st) with
    | TErr (TEBad why) =>
        l_err (ctx_loc ctx) ("pointer subtraction on " ++ c_type_diag_str elem ++ " (" ++ why ++ ")") st
    | TErr err => LErr (l_tr_msg (ctx_loc ctx) err)
    | TOk sz =>
        let '(ia, st1) := l_let "l" (TAtom "ptoi") [a] st in
        let '(ib, st2) := l_let "l" (TAtom "ptoi") [b] st1 in
        let '(diff, st3) := l_let "l" (TAtom "sub") [ia; ib] st2 in
        let '(v, st4) :=
          if Z.eqb sz 1 then (diff, st3)
          else l_let "l" (TAtom "div") [diff; ir_const sz] st3 in
        LOk (CVal v TLong) st4
    end.

Fixpoint convert_f (fuel : nat) (v0 : c_val) (to_t : c_type) (st : c_func_st) : l_res c_val :=
  match fuel with
  | O => LErr "convert recursion limit"
  | S f =>
      let '(CVal v from_t) := v0 in
      if c_type_eqb from_t to_t then LOk v0 st
      else
        match complex_type from_t, complex_type to_t with
        | Some _, _ =>
            match cx_parts v0 unknown_ctx st with
            | LErr m => LErr m
            | LOk (re, im) st1 =>
                match complex_type to_t with
                | Some _ => cx_made_f f to_t re im st1
                | None =>
                    match to_t with
                    | TVoid => LOk (CVal (ir_const 0) TVoid) st1
                    | TIntK IBool =>
                        match binary_f f BNe re (CVal (ir_const 0) TInt) unknown_ctx st1 with
                        | LErr m => LErr m
                        | LOk a st2 =>
                            match binary_f f BNe im (CVal (ir_const 0) TInt) unknown_ctx st2 with
                            | LErr m => LErr m
                            | LOk b st3 =>
                                match binary_f f BOr a b unknown_ctx st3 with
                                | LErr m => LErr m
                                | LOk c st4 => convert_f f c TBool st4
                                end
                            end
                        end
                    | _ => convert_f f re to_t st1
                    end
                end
            end
        | None, Some _ =>
            cx_made_f f to_t v0 (CVal (ir_const 0) TInt) st
        | None, None =>
            let is_from_vec := match from_t with TVec _ _ _ => true | _ => false end in
            let fallback (u : unit) : l_res c_val :=
              let const_float_done :=
                match v with
                | TApp fn [Term.TInt n] =>
                    if (fn == "const") && (float_type from_t || float_type to_t)
                       && arithmetic_type from_t && arithmetic_type to_t then
                      match const_convert (CVInt n) from_t to_t with
                      | Some (CVInt w) => Some (CVal (ir_const w) to_t)
                      | _ => None
                      end
                    else None
                | _ => None
                end in
              match const_float_done with
              | Some r => LOk r st
              | None =>
                  match from_t with
                  | TFloatK fk =>
                      match to_t with
                      | TFloatK FDouble =>
                          let op := match fk with FFloat => TApp "ext" [TAtom "s"] | _ => TAtom "truncx" end in
                          let '(r, st1) := l_let "d" op [v] st in
                          LOk (CVal r TDouble) st1
                      | TFloatK FFloat =>
                          let op := match fk with FDouble => TAtom "truncd" | _ => TAtom "truncx" end in
                          let '(r, st1) := l_let "s" op [v] st in
                          LOk (CVal r TFloat) st1
                      | TFloatK FLDouble =>
                          let op := match fk with FFloat => TApp "ext" [TAtom "s"] | _ => TApp "ext" [TAtom "d"] end in
                          let '(r, st1) := l_let "x" op [v] st in
                          LOk (CVal r TLDouble) st1
                      | _ =>
                          match type_class from_t, int_info to_t, type_class to_t with
                          | Some fk_s, Some (_, sg), Some ik =>
                              let op := float_int_op fk_s sg in
                              let base := conversion_int_type ik sg in
                              let '(iv, st1) := l_let ik (TAtom op) [v] st in
                              let '(r, st2) := int_convert base to_t iv st1 in
                              LOk (CVal r to_t) st2
                          | _, _, _ => LOk (CVal v to_t) st
                          end
                      end
                  | TPtr _ =>
                      if int_type to_t then
                        let '(iv, st1) := l_let "l" (TAtom "ptoi") [v] st in
                        convert_f f (CVal iv TULong) to_t st1
                      else LOk (CVal v to_t) st
                  | _ =>
                      if int_type from_t && float_type to_t then
                        match type_class from_t, int_info from_t, type_class to_t with
                        | Some ik, Some (_, sg), Some fk_s =>
                            let '(r, st1) := l_let fk_s (TAtom (int_float_op ik sg)) [v] st in
                            LOk (CVal r to_t) st1
                        | _, _, _ => LOk (CVal v to_t) st
                        end
                      else if int_type from_t && int_type to_t then
                        match v with
                        | TApp fn [Term.TInt n] =>
                            if fn == "const" then
                              match convert_int n to_t with
                              | Some w => LOk (CVal (ir_const w) to_t) st
                              | None => LOk (CVal v to_t) st
                              end
                            else
                              let '(v1, st1) := int_convert from_t to_t v st in
                              LOk (CVal v1 to_t) st1
                        | _ =>
                            let '(v1, st1) := int_convert from_t to_t v st in
                            LOk (CVal v1 to_t) st1
                        end
                      else if int_type from_t && is_ptr_type to_t then
                        match v with
                        | TApp fn [Term.TInt n] =>
                            if fn == "const" then
                              match convert_int n TULong with
                              | Some w => LOk (CVal (ir_const w) to_t) st
                              | None => LOk (CVal v to_t) st
                              end
                            else
                              let '(v2, st1) := int_convert from_t TULong v st in
                              let '(v1, st2) := l_let "p" (TAtom "itop") [v2] st1 in
                              LOk (CVal v1 to_t) st2
                        | _ =>
                            let '(v2, st1) := int_convert from_t TULong v st in
                            let '(v1, st2) := l_let "p" (TAtom "itop") [v2] st1 in
                            LOk (CVal v1 to_t) st2
                        end
                      else LOk (CVal v to_t) st
                  end
              end in
            match to_t with
            | TVec elem n _ =>
                if is_from_vec then LOk (CVal v to_t) st
                else
                  match convert_f f v0 elem st with
                  | LErr m => LErr m
                  | LOk (CVal x _) st1 =>
                      match l_local_slot to_t st1 with
                      | LErr m => LErr m
                      | LOk addr st2 =>
                          match lanes_stored to_t addr 0 (z_repeat n x) st2 with
                          | LErr m => LErr m
                          | LOk _ st3 => LOk (CVal addr to_t) st3
                          end
                      end
                  end
            | TVoid => LOk (CVal v TVoid) st
            | TIntK k =>
                match k with
                | IBool =>
                    match truth_val v0 unknown_ctx st with
                    | LErr m => LErr m
                    | LOk w st1 =>
                        let need_cmp :=
                          match type_class from_t with
                          | Some kc => (kc == "w") && negb (c_type_eqb from_t TBool)
                          | None => false
                          end in
                        if need_cmp then
                          let '(b, st2) := l_let "w" (TApp "cmp" [TAtom "ne"; TAtom "w"]) [w; ir_const 0] st1 in
                          LOk (CVal b TBool) st2
                        else LOk (CVal w TBool) st1
                    end
                | _ => fallback tt
                end
            | _ => fallback tt
            end
        end
  end

with cx_made_f (fuel : nat) (ct0 : c_type) (re im : c_val) (st : c_func_st) : l_res c_val :=
  match fuel with
  | O => LErr "cx_made recursion limit"
  | S f =>
      let ct := unqualified ct0 in
      match complex_type ct with
      | Some ft =>
          match type_size_align ft (fs_env st) with
          | TErr err => LErr (l_tr_msg unknown_loc err)
          | TOk (sz, _) =>
              match convert_f f re ft st with
              | LErr m => LErr m
              | LOk (CVal x _) st1 =>
                  match convert_f f im ft st1 with
                  | LErr m => LErr m
                  | LOk (CVal y _) st2 =>
                      match l_local_slot ct st2 with
                      | LErr m => LErr m
                      | LOk addr st3 =>
                          match store_typed ft x addr st3 with
                          | LErr m => LErr m
                          | LOk _ st4 =>
                              let '(p, st5) := l_offset addr sz st4 in
                              match store_typed ft y p st5 with
                              | LErr m => LErr m
                              | LOk _ st6 => LOk (CVal addr ct) st6
                              end
                          end
                      end
                  end
              end
          end
      | None => LErr "cx_made on non-complex"
      end
  end

with unary_f (fuel : nat) (op : c_unop) (v0 : c_val) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res c_val :=
  match fuel with
  | O => LErr "unary recursion limit"
  | S f =>
      let '(CVal _ from_t) := v0 in
      match unary_operand op from_t with
      | None =>
          l_err (ctx_loc ctx) ("invalid operand to " ++ c_unop_name op ++ ": " ++ c_type_diag_str from_t) st
      | Some ty =>
          match complex_type ty with
          | Some _ =>
              match cx_parts v0 ctx st with
              | LErr m => LErr m
              | LOk (re, im) st1 =>
                  match op with
                  | UPlus => LOk v0 st1
                  | UNeg =>
                      match unary_f f UNeg re ctx st1 with
                      | LErr m => LErr m
                      | LOk re1 st2 =>
                          match unary_f f UNeg im ctx st2 with
                          | LErr m => LErr m
                          | LOk im1 st3 => cx_made_f f ty re1 im1 st3
                          end
                      end
                  | _ =>
                      match unary_f f UNeg im ctx st1 with
                      | LErr m => LErr m
                      | LOk im1 st2 => cx_made_f f ty re im1 st2
                      end
                  end
              end
          | None =>
              match ty with
              | TVec elem _ _ =>
                  let '(CVal addr _) := v0 in
                  match lanes_loaded ty addr ctx st with
                  | LErr m => LErr m
                  | LOk xs st1 =>
                      let fix go_u (ls : list term) (acc : list term) (s : c_func_st) : l_res (list term) :=
                        match ls with
                        | [] => LOk (rev acc) s
                        | x :: rest =>
                            match unary_f f op (CVal x elem) ctx s with
                            | LErr m => LErr m
                            | LOk z0 s1 =>
                                match convert_f f z0 elem s1 with
                                | LErr m => LErr m
                                | LOk (CVal z _) s2 => go_u rest (z :: acc) s2
                                end
                            end
                        end in
                      match go_u xs [] st1 with
                      | LErr m => LErr m
                      | LOk zs st2 =>
                          match l_local_slot ty st2 with
                          | LErr m => LErr m
                          | LOk dst st3 =>
                              match lanes_stored ty dst 0 zs st3 with
                              | LErr m => LErr m
                              | LOk _ st4 => LOk (CVal dst ty) st4
                              end
                          end
                      end
                  end
              | _ =>
                  match op with
                  | UNot =>
                      match truth_val v0 ctx st with
                      | LErr m => LErr m
                      | LOk w st1 =>
                          let '(r, st2) := l_let "w" (TApp "cmp" [TAtom "eq"; TAtom "w"]) [w; ir_const 0] st1 in
                          LOk (CVal r TInt) st2
                      end
                  | _ =>
                      match convert_f f v0 ty st with
                      | LErr m => LErr m
                      | LOk (CVal v1 _) st1 =>
                          match type_class ty with
                          | None => l_err (ctx_loc ctx) ("invalid unary class for " ++ c_type_diag_str ty) st1
                          | Some k =>
                              match op with
                              | UPlus => LOk (CVal v1 ty) st1
                              | UNeg =>
                                  let '(r, st2) := l_let k (TAtom "neg") [v1] st1 in
                                  LOk (CVal r ty) st2
                              | UBnot =>
                                  let '(r, st2) := l_let k (TAtom "xor") [v1; ir_const (-1)] st1 in
                                  LOk (CVal r ty) st2
                              | _ => LOk (CVal v1 ty) st1
                              end
                          end
                      end
                  end
              end
          end
      end
  end

with binary_f (fuel : nat) (op : c_binop) (va vb : c_val) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res c_val :=
  match fuel with
  | O => LErr "binary recursion limit"
  | S f =>
      let '(CVal _ ta) := va in
      let '(CVal _ tb) := vb in
      match binary_operands op ta tb with
      | None =>
          l_err (ctx_loc ctx) ("invalid operands to " ++ c_binop_name op ++ ": " ++
                               c_type_diag_str ta ++ " and " ++ c_type_diag_str tb) st
      | Some (ca, cb, res_t) =>
          match complex_type ca, complex_type cb with
          | Some _, _ | _, Some _ =>
              match convert_f f va ca st with
              | LErr m => LErr m
              | LOk a st1 =>
                  match convert_f f vb cb st1 with
                  | LErr m => LErr m
                  | LOk b st2 =>
                      let split_cx (cv : c_val) (s : c_func_st) : l_res (c_val * option c_val) :=
                        let '(CVal _ t) := cv in
                        match complex_type t with
                        | Some _ =>
                            match cx_parts cv ctx s with
                            | LErr m => LErr m
                            | LOk (re, im) s1 => LOk (re, Some im) s1
                            end
                        | None => LOk (cv, None) s
                        end in
                      match split_cx a st2 with
                      | LErr m => LErr m
                      | LOk (ar, oai) st3 =>
                          match split_cx b st3 with
                          | LErr m => LErr m
                          | LOk (br, obi) st4 =>
                              let is_mul_div := match op with BMul | BDiv => true | _ => false end in
                              let bad_cx :=
                                is_mul_div &&
                                match obi with
                                | None => false
                                | Some _ =>
                                    match op with
                                    | BDiv => true
                                    | _ => match oai with Some _ => true | None => false end
                                    end
                                end in
                              if bad_cx then
                                let fl :=
                                  match complex_type res_t with
                                  | Some (TFloatK FFloat) => "s"
                                  | Some (TFloatK FDouble) => "d"
                                  | _ => "x"
                                  end in
                                let w := match op with BMul => "multiplying a _Complex value by" | _ => "dividing by" end in
                                l_err (ctx_loc ctx)
                                  (w ++ " a _Complex value is not supported: clang calls compiler-rt's native __" ++
                                   c_binop_name op ++ fl ++ "c3") st4
                              else if match op with BEq | BNe => true | _ => false end then
                                match binary_f f op ar br ctx st4 with
                                | LErr m => LErr m
                                | LOk e1 st5 =>
                                    let im_cmp :=
                                      match oai, obi with
                                      | Some ai, Some bi => binary_f f op ai bi ctx st5
                                      | Some ai, None => binary_f f op ai (CVal (ir_const 0) TInt) ctx st5
                                      | None, Some bi => binary_f f op bi (CVal (ir_const 0) TInt) ctx st5
                                      | None, None => LOk (CVal (ir_const 0) TInt) st5
                                      end in
                                    match im_cmp with
                                    | LErr m => LErr m
                                    | LOk e2 st6 =>
                                        let j := match op with BEq => BAnd | _ => BOr end in
                                        binary_f f j e1 e2 ctx st6
                                    end
                                end
                              else
                                match binary_f f op ar br ctx st4 with
                                | LErr m => LErr m
                                | LOk re st5 =>
                                    let im_res :=
                                      match oai, obi with
                                      | Some ai, Some bi => binary_f f op ai bi ctx st5
                                      | Some ai, None =>
                                          match op with
                                          | BAdd | BSub => LOk ai st5
                                          | _ => binary_f f op ai br ctx st5
                                          end
                                      | None, Some bi =>
                                          match op with
                                          | BAdd => LOk bi st5
                                          | BSub => unary_f f UNeg bi ctx st5
                                          | _ => binary_f f BMul ar bi ctx st5
                                          end
                                      | None, None => LOk (CVal (ir_const 0) TInt) st5
                                      end in
                                    match im_res with
                                    | LErr m => LErr m
                                    | LOk im st6 => cx_made_f f res_t re im st6
                                    end
                                end
                          end
                      end
                  end
              end
          | None, None =>
              match ca with
              | TVec elem _ _ =>
                  match convert_f f va ca st with
                  | LErr m => LErr m
                  | LOk (CVal aa _) st1 =>
                      match convert_f f vb ca st1 with
                      | LErr m => LErr m
                      | LOk (CVal ba _) st2 =>
                          match lanes_loaded ca aa ctx st2 with
                          | LErr m => LErr m
                          | LOk xs st3 =>
                              match lanes_loaded ca ba ctx st3 with
                              | LErr m => LErr m
                              | LOk ys st4 =>
                                  match res_t with
                                  | TVec re_elem _ _ =>
                                      let fix go_b (lx ly acc : list term) (s : c_func_st) : l_res (list term) :=
                                        match lx, ly with
                                        | x :: rx, y :: ry =>
                                            match binary_f f op (CVal x elem) (CVal y elem) ctx s with
                                            | LErr m => LErr m
                                            | LOk z0 s1 =>
                                                let z1_res :=
                                                  match cmp_op_names op with
                                                  | Some _ => binary_f f BSub (CVal (ir_const 0) TInt) z0 ctx s1
                                                  | None => LOk z0 s1
                                                  end in
                                                match z1_res with
                                                | LErr m => LErr m
                                                | LOk z1 s2 =>
                                                    match convert_f f z1 re_elem s2 with
                                                    | LErr m => LErr m
                                                    | LOk (CVal z _) s3 => go_b rx ry (z :: acc) s3
                                                    end
                                                end
                                            end
                                        | _, _ => LOk (rev acc) s
                                        end in
                                      match go_b xs ys [] st4 with
                                      | LErr m => LErr m
                                      | LOk zs st5 =>
                                          match l_local_slot res_t st5 with
                                          | LErr m => LErr m
                                          | LOk dst st6 =>
                                              match lanes_stored res_t dst 0 zs st6 with
                                              | LErr m => LErr m
                                              | LOk _ st7 => LOk (CVal dst res_t) st7
                                              end
                                          end
                                      end
                                  | _ => LErr "vector binary non-vector result"
                                  end
                              end
                          end
                      end
                  end
              | TPtr elem =>
                  match cb with
                  | TIntK ILong => ptr_offset op va elem vb (convert_f f) ctx st
                  | TPtr _ =>
                      match op with
                      | BSub => ptr_diff va vb elem ctx st
                      | _ =>
                          match convert_f f va ca st with
                          | LErr m => LErr m
                          | LOk (CVal a _) st1 =>
                              match convert_f f vb cb st1 with
                              | LErr m => LErr m
                              | LOk (CVal b _) st2 =>
                                  match cmp_op_names op with
                                  | Some (_, ucmp) =>
                                      let '(v, st3) := l_let "w" (TApp "cmp" [TAtom ucmp; TAtom "p"]) [a; b] st2 in
                                      LOk (CVal v res_t) st3
                                  | None => LErr "invalid pointer binary op"
                                  end
                              end
                          end
                      end
                  | _ => LErr "invalid pointer binary rhs"
                  end
              | _ =>
                  let add_long_ptr :=
                    match op with
                    | BAdd =>
                        match ca, cb with
                        | TIntK ILong, TPtr elem => Some elem
                        | _, _ => None
                        end
                    | _ => None
                    end in
                  match add_long_ptr with
                  | Some elem =>
                      ptr_offset BAdd vb elem va (convert_f f) ctx st
                  | None =>
                      match convert_f f va ca st with
                      | LErr m => LErr m
                      | LOk (CVal a _) st1 =>
                          match convert_f f vb cb st1 with
                          | LErr m => LErr m
                          | LOk (CVal b _) st2 =>
                              match type_class ca with
                              | None => LErr ("no class for " ++ c_type_diag_str ca)
                              | Some k =>
                                  let sg :=
                                    if float_type ca then CSigned
                                    else
                                      match int_info ca with
                                      | Some (_, s) => s
                                      | None => CUnsigned
                                      end in
                                  match cmp_op_names op with
                                  | Some (scmp, ucmp) =>
                                      let cmp_s :=
                                        if float_type ca then c_binop_name op
                                        else match sg with CSigned => scmp | CUnsigned => ucmp end in
                                      let '(v, st3) := l_let "w" (TApp "cmp" [TAtom cmp_s; TAtom k]) [a; b] st2 in
                                      LOk (CVal v res_t) st3
                                  | None =>
                                      let '(v, st3) := l_let k (TAtom (arith_op_name op sg)) [a; b] st2 in
                                      LOk (CVal v res_t) st3
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end
  end.

Definition op_fuel : nat := Z.to_nat 128.

Definition convert_val (v0 : c_val) (to_t : c_type) (st : c_func_st) : l_res c_val :=
  convert_f op_fuel v0 to_t st.

Definition cx_made (ct : c_type) (re im : c_val) (st : c_func_st) : l_res c_val :=
  cx_made_f op_fuel ct re im st.

Definition unary_op (op : c_unop) (v0 : c_val) (ctx : c_lower_ctx) (st : c_func_st) : l_res c_val :=
  unary_f op_fuel op v0 ctx st.

Definition binary_op (op : c_binop) (va vb : c_val) (ctx : c_lower_ctx) (st : c_func_st) : l_res c_val :=
  binary_f op_fuel op va vb ctx st.

Definition converted_val (v0 : c_val) (to_t : c_type) (st : c_func_st) : l_res c_val :=
  match to_t with
  | TVoid => LOk (CVal (ir_const 0) TVoid) st
  | _ =>
      let '(CVal addr from_t) := v0 in
      match complex_type to_t, complex_type from_t with
      | Some _, _ | _, Some _ => convert_val v0 to_t st
      | None, None =>
          if is_su to_t then LOk (CVal addr to_t) st
          else convert_val v0 to_t st
      end
  end.

Definition assign_convert (expr : c_expr) (v0 : c_val) (to_t : c_type)
  (loc : c_loc) (st : c_func_st) : l_res c_val :=
  match assigned expr (fs_env st) to_t loc with
  | TErr err => LErr (l_tr_msg loc err)
  | TOk _ => converted_val v0 to_t st
  end.

Definition join_arms (ty : c_type) (ljoin la : string) (va : term) (lb : string)
  (vb : term) (st : c_func_st) : l_res c_val :=
  match ty with
  | TVoid => LOk (CVal (ir_const 0) TVoid) (l_start ljoin st)
  | TFloatK FLDouble =>
      let '(a, st1) := l_fresh st in
      let st2 := l_start_phi ljoin [ir_phi a "p" [ir_edge (TAtom la) va; ir_edge (TAtom lb) vb]] st1 in
      let '(v, st3) := l_let "x" (TApp "load" [TAtom "x"]) [a] st2 in
      LOk (CVal v ty) st3
  | _ =>
      let ocls := if is_memtype ty then Some "p" else type_class ty in
      match ocls with
      | Some cls =>
          let '(v, st1) := l_fresh st in
          let st2 := l_start_phi ljoin [ir_phi v cls [ir_edge (TAtom la) va; ir_edge (TAtom lb) vb]] st1 in
          LOk (CVal v ty) st2
      | None => LErr ("join_arms unsupported type " ++ c_type_diag_str ty)
      end
  end.

(** ## Place reading, writing, and bit-field manipulation

    Scalar, aggregate, vector, and bit-field lvalues share uniform [place_read],
    [place_write], and [place_loaded] entry points. *)

Definition l_shifted (k op : string) (v : term) (n : Z) (st : c_func_st)
  : term * c_func_st :=
  if Z.eqb n 0 then (v, st)
  else l_let k (TAtom op) [v; ir_const n] st.

Definition bits_extended (t : c_type) (w : Z) (v : term) (st : c_func_st)
  : l_res c_val :=
  match type_class t, int_info t with
  | Some k, Some (_, sg) =>
      let kb := class_bits_Z k in
      let down := kb - w in
      let op := match sg with CSigned => "sar" | CUnsigned => "shr" end in
      let p := bitfield_promotion t w in
      let '(v1, st1) := l_shifted k op v down st in
      convert_val (CVal v1 t) p st1
  | _, _ => LErr "bits_extended non-integer"
  end.

Definition place_read (p : c_place) (ctx : c_lower_ctx) (st : c_func_st) : l_res c_val :=
  match p with
  | PLv addr u =>
      match u with
      | TVec _ _ _ => loaded_val u addr ctx st
      | _ =>
          match complex_type u with
          | Some _ => LOk (CVal addr u) st
          | None =>
              match load_typed u addr ctx st with
              | LErr m => LErr m
              | LOk cur st1 => LOk (CVal cur u) st1
              end
          end
      end
  | PBits addr t pos w =>
      match load_typed t addr ctx st with
      | LErr m => LErr m
      | LOk unit_v st1 =>
          match type_class t with
          | Some k =>
              let kb := class_bits_Z k in
              let up := kb - pos - w in
              let '(v1, st2) := l_shifted k "shl" unit_v up st1 in
              bits_extended t w v1 st2
          | None => LErr "bitfield non-integer class"
          end
      end
  | PFn _ _ => l_err (ctx_loc ctx) "cannot read a function designator" st
  end.

Definition place_loaded (p : c_place) (u : c_type) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res c_val :=
  match p with
  | PLv addr pu =>
      match pu with
      | TVec _ _ _ =>
          match loaded_val pu addr ctx st with
          | LErr m => LErr m
          | LOk (CVal v _) st1 => LOk (CVal v u) st1
          end
      | _ => loaded_val u addr ctx st
      end
  | PBits _ _ _ _ => place_read p ctx st
  | PFn _ _ => l_err (ctx_loc ctx) "cannot load a function designator" st
  end.

Definition place_write (p : c_place) (v0 : c_val) (ctx : c_lower_ctx)
  (st : c_func_st) : l_res c_val :=
  match p with
  | PLv addr u =>
      match converted_val v0 u st with
      | LErr m => LErr m
      | LOk (CVal v _) st1 =>
          match store_typed u v addr st1 with
          | LErr m => LErr m
          | LOk _ st2 => LOk (CVal v u) st2
          end
      end
  | PBits addr t pos w =>
      match convert_val v0 t st with
      | LErr m => LErr m
      | LOk (CVal v _) st1 =>
          match load_typed t addr ctx st1 with
          | LErr m => LErr m
          | LOk unit_v st2 =>
              match type_class t with
              | Some k =>
                  let kb := class_bits_Z k in
                  let mask := Z.shiftl (Z.shiftl 1 w - 1) pos in
                  let keep := z_not_mask mask kb in
                  let '(kept, st3) := l_let k (TAtom "and") [unit_v; ir_const keep] st2 in
                  let '(v1, st4) := l_shifted k "shl" v pos st3 in
                  let '(fld, st5) := l_let k (TAtom "and") [v1; ir_const mask] st4 in
                  let '(nw, st6) := l_let k (TAtom "or") [kept; fld] st5 in
                  match store_typed t nw addr st6 with
                  | LErr m => LErr m
                  | LOk _ st7 =>
                      let up := kb - w in
                      let '(v2, st8) := l_shifted k "shl" v up st7 in
                      bits_extended t w v2 st8
                  end
              | None => LErr "bitfield write non-integer"
              end
          end
      end
  | PFn _ _ => l_err (ctx_loc ctx) "cannot write to a function designator" st
  end.
