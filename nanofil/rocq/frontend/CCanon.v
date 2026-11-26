(** The canonical printer serializes tokens and syntax trees from CLex and
    CParse into SWI-Prolog `write_canonical` format using a reversed list of
    string fragments. Keeping printing in pure Gallina lets both OCaml
    extraction and the λANF arena build emit identical terms without
    duplicating serializer code in C. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Frontend Require Import CAst CAttrs CLex.
Import ListNotations.
Local Open Scope string_scope.

(** ## Prolog atom quoting

    Atoms follow SWI-Prolog's exact `write_canonical` rules: lowercase
    identifiers, graphic-character sequences without `/*`, and the four
    punctuation atoms `[]`, `{}`, `!`, and `;` print unquoted; all other
    atoms are single-quoted with standard escapes. *)

Definition is_graphic (c : ascii) : bool :=
  Ascii.eqb c "#"%char || Ascii.eqb c "$"%char || Ascii.eqb c "&"%char ||
  Ascii.eqb c "*"%char || Ascii.eqb c "+"%char || Ascii.eqb c "-"%char ||
  Ascii.eqb c "."%char || Ascii.eqb c "/"%char || Ascii.eqb c ":"%char ||
  Ascii.eqb c "<"%char || Ascii.eqb c "="%char || Ascii.eqb c ">"%char ||
  Ascii.eqb c "?"%char || Ascii.eqb c "@"%char || Ascii.eqb c "\"%char ||
  Ascii.eqb c "^"%char || Ascii.eqb c "~"%char.

Definition is_atom_tail (c : ascii) : bool :=
  in_range "a"%char "z"%char c || in_range "A"%char "Z"%char c ||
  in_range "0"%char "9"%char c || Ascii.eqb c "_"%char.

Fixpoint has_slash_star (cs : list ascii) : bool :=
  match cs with
  | a :: ((b :: _) as rest) =>
      if Ascii.eqb a "/"%char && Ascii.eqb b "*"%char then true
      else has_slash_star rest
  | _ => false
  end.

Definition is_bare_atom (s : string) : bool :=
  if String.eqb s "" then false
  else if String.eqb s "[]" || String.eqb s "{}" ||
          String.eqb s "!" || String.eqb s ";" then true
  else if String.eqb s "." then false
  else
    match list_ascii_of_string s with
    | [] => false
    | c0 :: rest =>
        if in_range "a"%char "z"%char c0 then forallb is_atom_tail rest
        else if is_graphic c0 then
          forallb is_graphic rest && negb (has_slash_star (c0 :: rest))
        else false
    end.

Definition hex_digit_char (n : nat) : ascii :=
  if (n <? 10)%nat then byte (code "0"%char + n)
  else byte (code "a"%char + (n - 10)).

Fixpoint escape_atom_chars (cs acc : list ascii) : list ascii :=
  match cs with
  | [] => "'"%char :: acc
  | c :: rest =>
      let k := code c in
      if Ascii.eqb c "'"%char then
        escape_atom_chars rest ("'"%char :: "\"%char :: acc)
      else if Ascii.eqb c "\"%char then
        escape_atom_chars rest ("\"%char :: "\"%char :: acc)
      else if Ascii.eqb c "010"%char then
        escape_atom_chars rest ("n"%char :: "\"%char :: acc)
      else if Ascii.eqb c "009"%char then
        escape_atom_chars rest ("t"%char :: "\"%char :: acc)
      else if Ascii.eqb c "013"%char then
        escape_atom_chars rest ("r"%char :: "\"%char :: acc)
      else if (k <? code " "%char)%nat || (code "~"%char <? k)%nat then
        let acc1 :=
          if (k <? 16)%nat then
            "\"%char :: hex_digit_char k :: "x"%char :: "\"%char :: acc
          else
            "\"%char :: hex_digit_char (k mod 16) ::
            hex_digit_char (k / 16) :: "x"%char :: "\"%char :: acc in
        escape_atom_chars rest acc1
      else
        escape_atom_chars rest (c :: acc)
  end.

Definition format_atom (s : string) : string :=
  if is_bare_atom s then s
  else string_of_rev (escape_atom_chars (list_ascii_of_string s) ["'"%char]).

(** ## Accumulator helpers

    Every printer appends string fragments to a reversed [list string]
    accumulator so serialization runs in linear time with no nested
    concatenation. *)

Definition emit (s : string) (acc : list string) : list string := s :: acc.

Definition emit_atom (s : string) (acc : list string) : list string :=
  emit (format_atom s) acc.

Definition emit_z (z : Z) (acc : list string) : list string :=
  emit (z_to_string z) acc.

Definition emit_list {A : Type} (f : A -> list string -> list string)
  (xs : list A) (acc : list string) : list string :=
  let fix go (ys : list A) (first : bool) (a : list string) : list string :=
    match ys with
    | [] => emit "]" a
    | y :: rest =>
        let a1 := if first then a else emit "," a in
        go rest false (f y a1)
    end in
  go xs true (emit "[" acc).

Definition emit_chars_atom_list (s : string) (acc : list string) : list string :=
  emit_list (fun c a => emit_atom (string_of_rev [c]) a)
    (list_ascii_of_string s) acc.

Definition emit_opt_atom (o : option string) (acc : list string) : list string :=
  match o with
  | None => emit "none" acc
  | Some s => emit_atom s acc
  end.

Definition emit_opt_some {A : Type} (f : A -> list string -> list string)
  (o : option A) (acc : list string) : list string :=
  match o with
  | None => emit "none" acc
  | Some x => emit ")" (f x (emit "some(" acc))
  end.

(** ## Token and location printers *)

Definition emit_loc (l : c_loc) (acc : list string) : list string :=
  match l with
  | Loc f n => emit ")" (emit_z n (emit "," (emit_atom f (emit ":(" acc))))
  | LocEof => emit "eof" acc
  end.

Definition suf_name (s : int_suffix) : string :=
  match s with
  | SufNone => "none"
  | SufU => "u"
  | SufL => "l"
  | SufUL => "ul"
  | SufLL => "ll"
  | SufULL => "ull"
  end.

Definition rad_name (r : int_radix) : string :=
  match r with
  | RadDec => "dec"
  | RadOther => "other"
  end.

Definition wt_name (wt : wide_type) : string :=
  match wt with
  | WInt => "int"
  | WUShort => "ushort"
  | WUInt => "uint"
  end.

Definition emit_suf_rad (s : int_suffix) (r : int_radix) (acc : list string)
  : list string :=
  emit ")" (emit (rad_name r) (emit "," (emit (suf_name s) (emit "-(" acc)))).

Definition emit_pack_op (op : pack_op) (acc : list string) : list string :=
  match op with
  | PackSet None => emit "set(none)" acc
  | PackSet (Some n) => emit ")" (emit_z n (emit "set(" acc))
  | PackPush lbl None =>
      emit ",keep)" (emit_opt_atom lbl (emit "push(" acc))
  | PackPush lbl (Some n) =>
      emit ")" (emit_z n (emit "," (emit_opt_atom lbl (emit "push(" acc))))
  | PackPop lbl => emit ")" (emit_opt_atom lbl (emit "pop(" acc))
  | PackShow => emit "show" acc
  end.

Definition emit_tok_kind (k : tok_kind) (acc : list string) : list string :=
  match k with
  | TId s => emit ")" (emit_atom s (emit "id(" acc))
  | TKw s => emit ")" (emit_atom s (emit "kw(" acc))
  | TInt v s r =>
      emit ")" (emit_suf_rad s r (emit "," (emit_z v (emit "int(" acc))))
  | TFloat cs => emit ")" (emit_chars_atom_list cs (emit "float(" acc))
  | TImag cs => emit "))" (emit_chars_atom_list cs (emit "imag(float(" acc))
  | TChr v => emit ")" (emit_z v (emit "chr(" acc))
  | TStr bs => emit ")" (emit_list emit_z bs (emit "str(" acc))
  | TWStr wt vs =>
      emit ")" (emit_list emit_z vs (emit "," (emit (wt_name wt) (emit "wstr(" acc))))
  | TPunct s => emit ")" (emit_atom s (emit "p(" acc))
  | TPragmaWeak nm tgt =>
      emit ")" (emit_opt_atom tgt (emit "," (emit_atom nm (emit "pragma_weak(" acc))))
  | TPragmaPack op => emit ")" (emit_pack_op op (emit "pragma_pack(" acc))
  end.

Definition emit_token (t : token) (acc : list string) : list string :=
  emit ")" (emit_loc (tok_loc t) (emit "," (emit_tok_kind (tok_val t) (emit "tok(" acc)))).

Fixpoint emit_attr_tok (t : attr_tok) (acc : list string) : list string :=
  match t with
  | ATok k => emit_tok_kind k acc
  | AGroup xs =>
      let fix go (ys : list attr_tok) (first : bool) (a : list string) : list string :=
        match ys with
        | [] => emit "])" a
        | y :: rest =>
            let a1 := if first then a else emit "," a in
            go rest false (emit_attr_tok y a1)
        end in
      go xs true (emit "group([" acc)
  end.

(** ## Syntax tree printers *)

Definition unop_name (op : c_unop) : string :=
  match op with
  | UNeg => "neg"
  | UPlus => "plus"
  | UBnot => "bnot"
  | UNot => "not"
  | UDeref => "deref"
  | UAddr => "addr"
  | UPreInc => "preinc"
  | UPreDec => "predec"
  | UPostInc => "postinc"
  | UPostDec => "postdec"
  end.

Definition binop_name (op : c_binop) : string :=
  match op with
  | BLor => "lor"
  | BLand => "land"
  | BOr => "or"
  | BXor => "xor"
  | BAnd => "and"
  | BEq => "eq"
  | BNe => "ne"
  | BLt => "lt"
  | BGt => "gt"
  | BLe => "le"
  | BGe => "ge"
  | BShl => "shl"
  | BShr => "shr"
  | BAdd => "add"
  | BSub => "sub"
  | BMul => "mul"
  | BDiv => "div"
  | BMod => "mod"
  end.

Definition emit_asm_clobber (c : c_asm_clobber) (acc : list string) : list string :=
  match c with
  | ACName s => emit_atom s acc
  | ACLabels ls => emit ")" (emit_list emit_atom ls (emit "labels(" acc))
  end.

Definition emit_asm_unsupported (u : c_asm_unsupported) (acc : list string)
  : list string :=
  match u with
  | AUMemory tpl => emit ")" (emit_list emit_z tpl (emit "memory(" acc))
  | AUOther => emit "other" acc
  end.

Fixpoint emit_item (it : c_item) (acc : list string) : list string :=
  match it with
  | IDecl loc sps inits =>
      let a1 := emit_loc loc (emit "decl(" acc) in
      let a2 := emit_list emit_spec sps (emit "," a1) in
      emit ")" (emit_list emit_init_decl inits (emit "," a2))
  | IFundef loc sps dcl body =>
      let a1 := emit_loc loc (emit "fundef(" acc) in
      let a2 := emit_list emit_spec sps (emit "," a1) in
      let a3 := emit_dcl dcl (emit "," a2) in
      emit ")" (emit_stmt body (emit "," a3))
  | IStaticAssert loc cond msg =>
      let a1 := emit_loc loc (emit "static_assert(" acc) in
      let a2 := emit_expr cond (emit "," a1) in
      emit ")" (emit_list emit_z msg (emit "," a2))
  | IPragmaWeak loc nm tgt =>
      let a1 := emit_loc loc (emit "pragma_weak(" acc) in
      let a2 := emit_atom nm (emit "," a1) in
      emit ")" (emit_opt_atom tgt (emit "," a2))
  | IToplevelAsm loc tpl =>
      let a1 := emit_loc loc (emit "toplevel_asm(" acc) in
      emit ")" (emit_list emit_z tpl (emit "," a1))
  end

with emit_init_decl (idcl : c_init_decl) (acc : list string) : list string :=
  match idcl with
  | InitDecl dcl oini =>
      let a1 := emit_dcl dcl (emit "init(" acc) in
      let a2 :=
        match oini with
        | None => emit "none" (emit "," a1)
        | Some ini => emit_init ini (emit "," a1)
        end in
      emit ")" a2
  end

with emit_dcl (dcl : c_dcl) (acc : list string) : list string :=
  match dcl with
  | Dcl nm ty asym =>
      let a1 := emit_opt_some emit_atom nm (emit "dcl(" acc) in
      let a2 := emit_dcl_type ty (emit "," a1) in
      let a3 :=
        match asym with
        | None => emit "none" (emit "," a2)
        | Some s => emit ")" (emit_atom s (emit "asm(" (emit "," a2)))
        end in
      emit ")" a3
  end

with emit_dcl_type (ty : c_dcl_type) (acc : list string) : list string :=
  match ty with
  | DTBase => emit "base" acc
  | DTPtr inner qs =>
      let a1 := emit_dcl_type inner (emit "ptr(" acc) in
      emit ")" (emit_list emit_atom qs (emit "," a1))
  | DTArray inner sz =>
      let a1 := emit_dcl_type inner (emit "array(" acc) in
      emit ")" (emit_array_size sz (emit "," a1))
  | DTFunc inner ps =>
      let a1 := emit_dcl_type inner (emit "func(" acc) in
      emit ")" (emit_params ps (emit "," a1))
  end

with emit_array_size (sz : c_array_size) (acc : list string) : list string :=
  match sz with
  | ASNone => emit "none" acc
  | ASStar => emit "star" acc
  | ASExpr e => emit_expr e acc
  end

with emit_params (ps : c_params) (acc : list string) : list string :=
  match ps with
  | PUnspecified => emit "unspecified" acc
  | PParams xs var =>
      let a1 := emit_list emit_param xs (emit "params(" acc) in
      emit ")" (emit (if var then "variadic" else "fixed") (emit "," a1))
  | PKnr ns => emit ")" (emit_list emit_atom ns (emit "knr(" acc))
  | PKnrDef ns ds =>
      let a1 := emit_list emit_atom ns (emit "knr(" acc) in
      emit ")" (emit_list emit_item ds (emit "," a1))
  end

with emit_param (p : c_param) (acc : list string) : list string :=
  match p with
  | Param sps dcl =>
      let a1 := emit_list emit_spec sps (emit "param(" acc) in
      emit ")" (emit_dcl dcl (emit "," a1))
  end

with emit_type_name (tn : c_type_name) (acc : list string) : list string :=
  match tn with
  | TypeName sps ty =>
      let a1 := emit_list emit_spec sps (emit "type(" acc) in
      emit ")" (emit_dcl_type ty (emit "," a1))
  end

with emit_spec (sp : c_spec) (acc : list string) : list string :=
  match sp with
  | SpStorage s => emit ")" (emit_atom s (emit "storage(" acc))
  | SpTspec s => emit ")" (emit_atom s (emit "tspec(" acc))
  | SpQual s => emit ")" (emit_atom s (emit "qual(" acc))
  | SpFspec s => emit ")" (emit_atom s (emit "fspec(" acc))
  | SpTname s => emit ")" (emit_atom s (emit "tname(" acc))
  | SpSu k tag oms ats =>
      let a1 := emit (match k with KStruct => "struct" | KUnion => "union" end) (emit "su(" acc) in
      let a2 := emit_opt_some emit_atom tag (emit "," a1) in
      let a3 :=
        match oms with
        | None => emit "none" (emit "," a2)
        | Some ms => emit_list emit_member ms (emit "," a2)
        end in
      emit ")" (emit_list (emit_list emit_attr_tok) ats (emit "," a3))
  | SpEnum tag es =>
      let a1 := emit_opt_some emit_atom tag (emit "enum(" acc) in
      emit ")" (emit_enums es (emit "," a1))
  | SpSharedBase => emit "shared_base" acc
  | SpAttr ts => emit ")" (emit_list emit_attr_tok ts (emit "attr(" acc))
  | SpAttrTag tag => emit ")" (emit_atom tag (emit "attr(" acc))
  | SpAlignasType tn => emit "))" (emit_type_name tn (emit "alignas(type(" acc))
  | SpAlignasExpr e => emit "))" (emit_expr e (emit "alignas(expr(" acc))
  | SpTypeofType tn => emit "))" (emit_type_name tn (emit "typeof(type(" acc))
  | SpTypeofExpr e => emit "))" (emit_expr e (emit "typeof(expr(" acc))
  | SpAutoType => emit "auto_type" acc
  | SpAtomic tn => emit ")" (emit_type_name tn (emit "atomic(" acc))
  end

with emit_member (m : c_member) (acc : list string) : list string :=
  match m with
  | MField sps dcl ow =>
      let a1 := emit_list emit_spec sps (emit "field(" acc) in
      let a2 := emit_dcl dcl (emit "," a1) in
      let a3 :=
        match ow with
        | None => emit "none" (emit "," a2)
        | Some e => emit_expr e (emit "," a2)
        end in
      emit ")" a3
  | MStaticAssert loc cond msg =>
      let a1 := emit_loc loc (emit "static_assert(" acc) in
      let a2 := emit_expr cond (emit "," a1) in
      emit ")" (emit_list emit_z msg (emit "," a2))
  end

with emit_enums (es : c_enumerators) (acc : list string) : list string :=
  match es with
  | EnumNone => emit "none" acc
  | EnumList xs => emit_list emit_enumerator xs acc
  | EnumPacked xs => emit ")" (emit_list emit_enumerator xs (emit "packed(" acc))
  end

with emit_enumerator (e : c_enumerator) (acc : list string) : list string :=
  match e with
  | Enumerator nm ov =>
      let a1 := emit_atom nm (emit "enumerator(" acc) in
      let a2 :=
        match ov with
        | None => emit "none" (emit "," a1)
        | Some ex => emit_expr ex (emit "," a1)
        end in
      emit ")" a2
  end

with emit_init (ini : c_init) (acc : list string) : list string :=
  match ini with
  | InitExpr e => emit_expr e acc
  | InitList es => emit ")" (emit_list emit_init_entry es (emit "list(" acc))
  end

with emit_init_entry (en : c_init_entry) (acc : list string) : list string :=
  match en with
  | InitEntry ds ini =>
      let a1 := emit_list emit_desig ds (emit "entry(" acc) in
      emit ")" (emit_init ini (emit "," a1))
  end

with emit_desig (d : c_designator) (acc : list string) : list string :=
  match d with
  | DField f => emit ")" (emit_atom f (emit "field(" acc))
  | DIndex e => emit ")" (emit_expr e (emit "index(" acc))
  | DRange lo hi =>
      let a1 := emit_expr lo (emit "range(" acc) in
      emit ")" (emit_expr hi (emit "," a1))
  end

with emit_stmt (st : c_stmt) (acc : list string) : list string :=
  match st with
  | Stmt loc body =>
      let a1 := emit_loc loc (emit "at(" acc) in
      emit ")" (emit_stmt_body body (emit "," a1))
  end

with emit_block_item (bi : c_block_item) (acc : list string) : list string :=
  match bi with
  | BIDecl it => emit_item it acc
  | BIStmt st => emit_stmt st acc
  end

with emit_for_init (fi : c_for_init) (acc : list string) : list string :=
  match fi with
  | FINone => emit "none" acc
  | FIExpr e => emit ")" (emit_expr e (emit "expr(" acc))
  | FIDecl it => emit_item it acc
  end

with emit_asm_op (ao : c_asm_op) (acc : list string) : list string :=
  match ao with
  | AsmOp c e =>
      let a1 := emit_atom c (emit "op(" acc) in
      emit ")" (emit_expr e (emit "," a1))
  end

with emit_stmt_body (sb : c_stmt_body) (acc : list string) : list string :=
  match sb with
  | SBlock bis => emit ")" (emit_list emit_block_item bis (emit "block(" acc))
  | SExpr e => emit ")" (emit_expr e (emit "expr(" acc))
  | SNull => emit "null" acc
  | SIf c t oe =>
      let a1 := emit_expr c (emit "if(" acc) in
      let a2 := emit_stmt t (emit "," a1) in
      let a3 :=
        match oe with
        | None => emit "none" (emit "," a2)
        | Some e => emit_stmt e (emit "," a2)
        end in
      emit ")" a3
  | SWhile c body =>
      let a1 := emit_expr c (emit "while(" acc) in
      emit ")" (emit_stmt body (emit "," a1))
  | SDo body c =>
      let a1 := emit_stmt body (emit "do(" acc) in
      emit ")" (emit_expr c (emit "," a1))
  | SFor fi oc os body =>
      let a1 := emit_for_init fi (emit "for(" acc) in
      let a2 :=
        match oc with
        | None => emit "none" (emit "," a1)
        | Some e => emit_expr e (emit "," a1)
        end in
      let a3 :=
        match os with
        | None => emit "none" (emit "," a2)
        | Some e => emit_expr e (emit "," a2)
        end in
      emit ")" (emit_stmt body (emit "," a3))
  | SSwitch c body =>
      let a1 := emit_expr c (emit "switch(" acc) in
      emit ")" (emit_stmt body (emit "," a1))
  | SCase v body =>
      let a1 := emit_expr v (emit "case(" acc) in
      emit ")" (emit_stmt body (emit "," a1))
  | SCaseRange lo hi body =>
      let a1 := emit_expr lo (emit "case(range(" acc) in
      let a2 := emit ")" (emit_expr hi (emit "," a1)) in
      emit ")" (emit_stmt body (emit "," a2))
  | SDefault body => emit ")" (emit_stmt body (emit "default(" acc))
  | SBreak => emit "break" acc
  | SContinue => emit "continue" acc
  | SReturn oe =>
      let a1 :=
        match oe with
        | None => emit "none" (emit "return(" acc)
        | Some e => emit_expr e (emit "return(" acc)
        end in
      emit ")" a1
  | SGoto l => emit ")" (emit_atom l (emit "goto(" acc))
  | SComputedGoto e => emit ")" (emit_expr e (emit "computed_goto(" acc))
  | SLabel l body =>
      let a1 := emit_atom l (emit "label(" acc) in
      emit ")" (emit_stmt body (emit "," a1))
  | SAsmEmpty outs ins clobs g =>
      let a1 := emit_list emit_asm_op outs (emit "asm_empty(" acc) in
      let a2 := emit_list emit_asm_op ins (emit "," a1) in
      let a3 := emit_list emit_asm_clobber clobs (emit "," a2) in
      emit ")" (emit (if g then "goto" else "none") (emit "," a3))
  | SAsm tpl outs ins clobs g =>
      let a1 := emit_list emit_z tpl (emit "asm(" acc) in
      let a2 := emit_list emit_asm_op outs (emit "," a1) in
      let a3 := emit_list emit_asm_op ins (emit "," a2) in
      let a4 := emit_list emit_asm_clobber clobs (emit "," a3) in
      emit ")" (emit (if g then "goto" else "none") (emit "," a4))
  | SUnsupportedAsm k =>
      emit ")" (emit_asm_unsupported k (emit "unsupported_asm(" acc))
  end

with emit_generic_assoc (ga : c_generic_assoc) (acc : list string) : list string :=
  match ga with
  | GAssocType tn e =>
      let a1 := emit_type_name tn (emit "assoc(" acc) in
      emit ")" (emit_expr e (emit "," a1))
  | GAssocDefault e =>
      emit ")" (emit_expr e (emit "assoc(default," acc))
  end

with emit_expr (e : c_expr) (acc : list string) : list string :=
  match e with
  | EId s => emit ")" (emit_atom s (emit "id(" acc))
  | ENum v s r =>
      emit ")" (emit_suf_rad s r (emit "," (emit_z v (emit "num(" acc))))
  | EChr v => emit ")" (emit_z v (emit "chr(" acc))
  | EFloat cs => emit ")" (emit_chars_atom_list cs (emit "float(" acc))
  | EImag cs => emit "))" (emit_chars_atom_list cs (emit "imag(float(" acc))
  | EStr bs => emit ")" (emit_list emit_z bs (emit "str(" acc))
  | EWStr wt vs =>
      emit ")" (emit_list emit_z vs (emit "," (emit (wt_name wt) (emit "wstr(" acc))))
  | EBin op a c =>
      let a1 := emit (binop_name op) (emit "bin(" acc) in
      let a2 := emit_expr a (emit "," a1) in
      emit ")" (emit_expr c (emit "," a2))
  | EAssign op a c =>
      let a1 := emit_atom op (emit "assign(" acc) in
      let a2 := emit_expr a (emit "," a1) in
      emit ")" (emit_expr c (emit "," a2))
  | EUn op a =>
      let a1 := emit (unop_name op) (emit "un(" acc) in
      emit ")" (emit_expr a (emit "," a1))
  | ECond c a d =>
      let a1 := emit_expr c (emit "cond(" acc) in
      let a2 := emit_expr a (emit "," a1) in
      emit ")" (emit_expr d (emit "," a2))
  | EGCond c d =>
      let a1 := emit_expr c (emit "gcond(" acc) in
      emit ")" (emit_expr d (emit "," a1))
  | EComma a c =>
      let a1 := emit_expr a (emit "comma(" acc) in
      emit ")" (emit_expr c (emit "," a1))
  | ECall fn args =>
      let a1 := emit_expr fn (emit "call(" acc) in
      emit ")" (emit_list emit_expr args (emit "," a1))
  | EConvertVector a tn =>
      let a1 := emit_expr a (emit "call(id('__builtin_convertvector'),[" acc) in
      emit "])" (emit_type_name tn (emit "," a1))
  | EIndex a i =>
      let a1 := emit_expr a (emit "index(" acc) in
      emit ")" (emit_expr i (emit "," a1))
  | EMember a f =>
      let a1 := emit_expr a (emit "member(" acc) in
      emit ")" (emit_atom f (emit "," a1))
  | EArrow a f =>
      let a1 := emit_expr a (emit "arrow(" acc) in
      emit ")" (emit_atom f (emit "," a1))
  | ECast tn a =>
      let a1 := emit_type_name tn (emit "cast(" acc) in
      emit ")" (emit_expr a (emit "," a1))
  | ESizeofType tn => emit ")" (emit_type_name tn (emit "sizeof_type(" acc))
  | ESizeofExpr a => emit ")" (emit_expr a (emit "sizeof_expr(" acc))
  | EAlignofType tn => emit ")" (emit_type_name tn (emit "alignof(" acc))
  | EAlignofExpr a => emit ")" (emit_expr a (emit "alignof_expr(" acc))
  | ERealPart a => emit ")" (emit_expr a (emit "real_part(" acc))
  | EImagPart a => emit ")" (emit_expr a (emit "imag_part(" acc))
  | EComplit tn es =>
      let a1 := emit_type_name tn (emit "complit(" acc) in
      emit "))" (emit_list emit_init_entry es (emit ",list(" a1))
  | EOffsetof tn ds =>
      let a1 := emit_type_name tn (emit "offsetof(" acc) in
      emit ")" (emit_list emit_desig ds (emit "," a1))
  | EVaArg a tn =>
      let a1 := emit_expr a (emit "va_arg(" acc) in
      emit ")" (emit_type_name tn (emit "," a1))
  | EBitCast tn a =>
      let a1 := emit_type_name tn (emit "bit_cast(" acc) in
      emit ")" (emit_expr a (emit "," a1))
  | ETypesCompatible a c =>
      let a1 := emit_type_name a (emit "types_compatible(" acc) in
      emit ")" (emit_type_name c (emit "," a1))
  | EStmtExpr body => emit ")" (emit_stmt body (emit "stmtexpr(" acc))
  | ELabelAddr l => emit ")" (emit_atom l (emit "label_addr(" acc))
  | EGeneric c assocs =>
      let a1 := emit_expr c (emit "generic(" acc) in
      emit ")" (emit_list emit_generic_assoc assocs (emit "," a1))
  end.
