(** The C frontend transforms preprocessed source text into a syntax tree
    before type checking and lowering to nanofil IR. This module defines the
    token and syntax-tree types shared by the Gallina C lexer and parser,
    mirroring the ground terms built by c_lex.pl and c_parse.pl.

    Keeping these definitions independent of the IR proofs lets the frontend
    compile in seconds and extract cleanly under both standard OCaml
    extraction and the custom λANF pipeline. *)

From Stdlib Require Import String ZArith List Bool Ascii.
Import ListNotations.

(** ## Results and source locations

    Lexing and parsing report either a value or a diagnostic message tied to
    the file and line where the error occurred. *)

(** A fallible frontend step returns either a value or an error message. *)
Inductive c_result (A : Type) : Type :=
| COk (v : A)
| CErr (msg : string).

Arguments COk {A} v.
Arguments CErr {A} msg.

(** A source location pairs a filename with its one-based line number, or
    marks the end of the token stream. *)
Inductive c_loc : Type :=
| Loc (file : string) (line : Z)
| LocEof.

(** ## Lexer tokens

    Each token carries its payload alongside the source location where it
    began, matching the `tok(T, File:Line)` terms produced by c_lex.pl. *)

(** Integer literal suffixes collapse case and letter order to six canonical
    forms. *)
Inductive int_suffix : Type :=
| SufNone
| SufU
| SufL
| SufUL
| SufLL
| SufULL.

(** Decimal constants follow different C integer typing rules from hexadecimal,
    octal, and binary constants. *)
Inductive int_radix : Type :=
| RadDec
| RadOther.

(** Wide string and character prefixes select the element integer type. *)
Inductive wide_type : Type :=
| WInt
| WUShort
| WUInt.

(** Supported `#pragma pack` directives manipulate a labeled stack of
    alignment caps. *)
Inductive pack_op : Type :=
| PackSet (n : option Z)
| PackPush (label : option string) (val : option Z)
| PackPop (label : option string)
| PackShow.

(** A token kind distinguishes identifiers, normalized keywords, numeric and
    string literals, punctuators, and retained pragmas. *)
Inductive tok_kind : Type :=
| TId (name : string)
| TKw (kw : string)
| TInt (val : Z) (suf : int_suffix) (rad : int_radix)
| TFloat (chars : string)
| TImag (chars : string)
| TChr (val : Z)
| TStr (bytes : list Z)
| TWStr (wt : wide_type) (codes : list Z)
| TPunct (sym : string)
| TPragmaWeak (name : string) (target : option string)
| TPragmaPack (op : pack_op).

(** A located token pairs a token kind with its source location. *)
Record token : Type := mkTok {
  tok_val : tok_kind;
  tok_loc : c_loc;
}.

(** GNU attribute lists store balanced token trees whose nested parentheses
    become [AGroup] nodes. *)
Inductive attr_tok : Type :=
| ATok (k : tok_kind)
| AGroup (inner : list attr_tok).

(** ## C syntax tree

    The parser builds declarations, declarators, statements, and expressions
    with only typedef names resolved. Types, struct layouts, and constant
    values are resolved in later passes. *)

(** Struct and union specifiers share one syntax node distinguished by
    [su_kind]. *)
Inductive su_kind : Type :=
| KStruct
| KUnion.

(** Unary operators cover prefix and postfix increments, dereference,
    address-of, and arithmetic or logical negation. *)
Inductive c_unop : Type :=
| UNeg | UPlus | UBnot | UNot | UDeref | UAddr
| UPreInc | UPreDec | UPostInc | UPostDec.

(** Binary operators cover logical, bitwise, comparison, shift, and
    arithmetic operations in C precedence order. *)
Inductive c_binop : Type :=
| BLor | BLand | BOr | BXor | BAnd
| BEq | BNe | BLt | BGt | BLe | BGe
| BShl | BShr | BAdd | BSub | BMul | BDiv | BMod.

(** Inline assembly clobbers list register or memory names plus any `asm goto`
    label targets. *)
Inductive c_asm_clobber : Type :=
| ACName (name : string)
| ACLabels (labels : list string).

(** Unsupported inline assembly keeps whether any operand carries a memory
    constraint so lowering can emit the right runtime diagnostic. *)
Inductive c_asm_unsupported : Type :=
| AUMemory (tpl : list Z)
| AUOther.

(** The syntax tree forms a single mutually inductive family covering
    translation-unit items, specifiers, declarators, initializers, statements,
    and expressions. *)
Inductive c_item : Type :=
| IDecl (loc : c_loc) (specs : list c_spec) (inits : list c_init_decl)
| IFundef (loc : c_loc) (specs : list c_spec) (dcl : c_dcl) (body : c_stmt)
| IStaticAssert (loc : c_loc) (cond : c_expr) (msg : list Z)
| IPragmaWeak (loc : c_loc) (name : string) (target : option string)
| IToplevelAsm (loc : c_loc) (tpl : list Z)

with c_init_decl : Type :=
| InitDecl (dcl : c_dcl) (init : option c_init)

with c_dcl : Type :=
| Dcl (name : option string) (ty : c_dcl_type) (asm_sym : option string)

with c_dcl_type : Type :=
| DTBase
| DTPtr (inner : c_dcl_type) (quals : list string)
| DTArray (inner : c_dcl_type) (sz : c_array_size)
| DTFunc (inner : c_dcl_type) (ps : c_params)

with c_array_size : Type :=
| ASNone
| ASStar
| ASExpr (e : c_expr)

with c_params : Type :=
| PUnspecified
| PParams (ps : list c_param) (variadic : bool)
| PKnr (names : list string)
| PKnrDef (names : list string) (decls : list c_item)

with c_param : Type :=
| Param (specs : list c_spec) (dcl : c_dcl)

with c_type_name : Type :=
| TypeName (specs : list c_spec) (ty : c_dcl_type)

with c_spec : Type :=
| SpStorage (s : string)
| SpTspec (k : string)
| SpQual (q : string)
| SpFspec (f : string)
| SpTname (name : string)
| SpSu (kind : su_kind) (tag : option string) (members : option (list c_member))
       (attrs : list (list attr_tok))
| SpEnum (tag : option string) (enums : c_enumerators)
| SpSharedBase
| SpAttr (ts : list attr_tok)
| SpAttrTag (tag : string)
| SpAlignasType (ty : c_type_name)
| SpAlignasExpr (e : c_expr)
| SpTypeofType (ty : c_type_name)
| SpTypeofExpr (e : c_expr)
| SpAutoType
| SpAtomic (ty : c_type_name)

with c_member : Type :=
| MField (specs : list c_spec) (dcl : c_dcl) (width : option c_expr)
| MStaticAssert (loc : c_loc) (cond : c_expr) (msg : list Z)

with c_enumerators : Type :=
| EnumNone
| EnumList (es : list c_enumerator)
| EnumPacked (es : list c_enumerator)

with c_enumerator : Type :=
| Enumerator (name : string) (val : option c_expr)

with c_init : Type :=
| InitExpr (e : c_expr)
| InitList (entries : list c_init_entry)

with c_init_entry : Type :=
| InitEntry (ds : list c_designator) (init : c_init)

with c_designator : Type :=
| DField (name : string)
| DIndex (e : c_expr)
| DRange (lo hi : c_expr)

with c_stmt : Type :=
| Stmt (loc : c_loc) (body : c_stmt_body)

with c_block_item : Type :=
| BIDecl (item : c_item)
| BIStmt (stmt : c_stmt)

with c_for_init : Type :=
| FINone
| FIExpr (e : c_expr)
| FIDecl (item : c_item)

with c_asm_op : Type :=
| AsmOp (constraint : string) (e : c_expr)

with c_stmt_body : Type :=
| SBlock (items : list c_block_item)
| SExpr (e : c_expr)
| SNull
| SIf (cond : c_expr) (thn : c_stmt) (els : option c_stmt)
| SWhile (cond : c_expr) (body : c_stmt)
| SDo (body : c_stmt) (cond : c_expr)
| SFor (init : c_for_init) (cond : option c_expr) (step : option c_expr) (body : c_stmt)
| SSwitch (cond : c_expr) (body : c_stmt)
| SCase (val : c_expr) (body : c_stmt)
| SCaseRange (lo hi : c_expr) (body : c_stmt)
| SDefault (body : c_stmt)
| SBreak
| SContinue
| SReturn (e : option c_expr)
| SGoto (label : string)
| SComputedGoto (e : c_expr)
| SLabel (label : string) (body : c_stmt)
| SAsmEmpty (outs ins : list c_asm_op) (clobbers : list c_asm_clobber) (is_goto : bool)
| SAsm (tpl : list Z) (outs ins : list c_asm_op) (clobbers : list c_asm_clobber) (is_goto : bool)
| SUnsupportedAsm (kind : c_asm_unsupported)

with c_generic_assoc : Type :=
| GAssocType (ty : c_type_name) (e : c_expr)
| GAssocDefault (e : c_expr)

with c_expr : Type :=
| EId (name : string)
| ENum (val : Z) (suf : int_suffix) (rad : int_radix)
| EChr (val : Z)
| EFloat (chars : string)
| EImag (chars : string)
| EStr (bytes : list Z)
| EWStr (wt : wide_type) (codes : list Z)
| EBin (op : c_binop) (lhs rhs : c_expr)
| EAssign (op : string) (lhs rhs : c_expr)
| EUn (op : c_unop) (e : c_expr)
| ECond (cond thn els : c_expr)
| EGCond (cond els : c_expr)
| EComma (lhs rhs : c_expr)
| ECall (fn : c_expr) (args : list c_expr)
| EConvertVector (e : c_expr) (ty : c_type_name)
| EIndex (arr idx : c_expr)
| EMember (e : c_expr) (field : string)
| EArrow (e : c_expr) (field : string)
| ECast (ty : c_type_name) (e : c_expr)
| ESizeofType (ty : c_type_name)
| ESizeofExpr (e : c_expr)
| EAlignofType (ty : c_type_name)
| EAlignofExpr (e : c_expr)
| ERealPart (e : c_expr)
| EImagPart (e : c_expr)
| EComplit (ty : c_type_name) (entries : list c_init_entry)
| EOffsetof (ty : c_type_name) (path : list c_designator)
| EVaArg (e : c_expr) (ty : c_type_name)
| EBitCast (ty : c_type_name) (e : c_expr)
| ETypesCompatible (a b : c_type_name)
| EStmtExpr (body : c_stmt)
| ELabelAddr (label : string)
| EGeneric (ctrl : c_expr) (assocs : list c_generic_assoc).
