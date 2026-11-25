(* Typed AST mirroring nanofil/web/rocq/rocq_syntax.pl 1-to-1. *)

type span = { lo : int; hi : int }

type assoc = Left | Right | NonAssoc

type tok_kind =
  | Id of string
  | Kw of string
  | Num of string
  | Str of string
  | Sym of string
  | P of string
  | Dot

type token = { kind : tok_kind; lo : int; hi : int }

type comment = { cm_lo : int; cm_hi : int; cm_text : string }

type name = { n_span : span; n_text : string }

type focus =
  | FocusNum of string
  | FocusBullet of string

type binder_kind =
  | BParen
  | BStruct
  | BBrace
  | BBare
  | BPattern of expr
  | BGen of string * gen_item list

and gen_item =
  | GenBangCast of span * string * expr
  | GenBang of expr
  | GenExpr of expr

and binder = {
  b_span : span;
  b_kind : binder_kind;
  b_names : name list;
  b_ty : expr option;
}

and mixfix_part =
  | MStr of string
  | MExpr of expr

and pointsto_mod =
  | PmName of expr
  | PmDfrac of expr
  | PmOwn of expr
  | PmPersistent

and wp_at =
  | WpNone
  | WpAt of expr option * expr

and wp_post = { wp_binder : name option; wp_body : expr }

and big_binds = { bb_key : name option; bb_vals : name list }

and let_lhs =
  | LetTuple of name list
  | LetName of name * binder list

and rec_field_val =
  | RFld of span * string * expr
  | RFldB of span * string * binder list * expr

and scrutinee =
  | ScrutExpr of expr
  | ScrutAs of expr * name

and branch = { br_alts : expr list list; br_rhs : expr }

and ir_operand =
  | IrVal of expr
  | IrTmp of expr
  | IrGlobal of expr
  | IrConst of expr

and ir_edge =
  | IrEdgeExpr of expr
  | IrPoll of expr
  | IrTo of expr

and ir_param = { irp_ty : expr; irp_name : expr }

and ir_arg = { ira_ty : expr; ira_val : ir_operand }

and ir_incoming = { iri_lab : expr; iri_val : ir_operand }

and ir_phi =
  | IrPhiEscape of expr
  | IrPhi of span * expr * expr * ir_incoming list

and ir_insts =
  | IrInsts of ir_ssa list
  | IrCode of expr

and ir_block =
  | IrBlockEscape of expr
  | IrBlock of span * expr * ir_phi list * ir_insts * ir_ssa

and ir_body =
  | IrBodyExpr of expr
  | IrBodyBlocks of ir_block list

and ir_ret =
  | IrRetVoid
  | IrRetVal of ir_operand

and ir_call_res =
  | IrCallVoid
  | IrCallRes of expr * expr

and ir_ssa_kind =
  | IrSsaEscape of expr
  | IrLet of expr * expr * expr * ir_operand list
  | IrFlight of expr * ir_operand * ir_operand
  | IrStore of expr * ir_operand * expr * ir_operand
  | IrStorePtr of ir_operand * expr * ir_operand
  | IrAlloca of expr * expr
  | IrGoto of ir_edge
  | IrBr of ir_operand * ir_edge * ir_edge
  | IrRet of ir_ret
  | IrUnreachable
  | IrCall of string * ir_call_res * ir_operand * ir_arg list

and ir_ssa = { irs_span : span; irs_kind : ir_ssa_kind }

and expr =
  | EId of span * string
  | EHole of span
  | EMeta of span * string
  | ELtac of span * tactic
  | ENum of span * string
  | EStr of span * string
  | EExplicit of span * string
  | EApp of span * expr * expr list
  | EBin of span * string * expr * expr
  | EChain of span * string list * expr list
  | EPre of span * string * expr
  | EParen of span * expr
  | ECast of span * expr * expr
  | ETuple of span * expr list
  | EOrPat of span * expr list
  | EForall of span * binder list * expr
  | EExists of span * binder list * expr
  | EFun of span * binder list * expr
  | ELet of span * let_lhs * expr option * expr * expr
  | ELetStar of span * name * expr * expr
  | ELetQ of span * expr * expr * expr
  | ELetPat of span * expr * expr * expr
  | ELetFix of span * name * binder list * expr option * expr * expr
  | EFix of span * name * binder list * expr option * expr
  | ENamed of span * string * expr
  | EAsPat of span * expr * name
  | EBits of span * expr * string
  | EIf of span * expr * expr * expr
  | EIfIs of span * expr * expr * expr * expr
  | EMatch of span * scrutinee list * expr option * branch list
  | EList of span * expr list
  | ERecord of span * rec_field_val list
  | EScope of span * expr * string
  | EMixfix of span * mixfix_part list
  | EIrInst of span * ir_ssa
  | EIrBlk of span * ir_block
  | EIrList of span * ir_ssa list
  | EIrFn of span * expr * expr * ir_param list * expr * ir_body
  | EBraces of span * expr
  | EPure of span * expr
  | EConst of span * string
  | EUnit of span
  | EInsert of span * expr * expr
  | EProj of span * expr * string
  | EGFunctors of span * expr list
  | EFupd of span * expr list * expr
  | EFupdw of span * expr list * expr * expr
  | EStepUpd of span * expr list * expr option * expr
  | EStepUpdw of span * expr list * expr option * expr * expr
  | ELaterN of span * expr * expr
  | EPointsTo of span * string * expr * pointsto_mod list * expr
  | EIndexed of span * string * expr * expr option * expr
  | EWp of span * expr * wp_at * wp_post
  | ETriple of span * expr * expr * wp_at * binder list * expr * expr
  | EBigOp of span * string * string * big_binds * expr list * expr
  | EBigAll of span * string * expr
  | EEval of span * string list * expr
  | ESig of span * name * expr * expr

and intro_pat =
  | IpInj of intro_pat list
  | IpOr of intro_pat list list
  | IpAnd of intro_pat list
  | IpFresh of name
  | IpName of name
  | IpRewrite of string
  | IpAuto of string

and ipm_intro_item =
  | IpmCoq of intro_pat list
  | IpmStr of string

and ipm_pat =
  | IpmPatStr of string
  | IpmPatPure of intro_pat

and ipm_head =
  | IpmHyp of string
  | IpmExpr of expr

and tactic_subject =
  | TSubGoal
  | TSubType of expr
  | TSubTerm of expr

and tactic_part =
  | TPIntro of intro_pat list
  | TPIpmIntros of ipm_intro_item list
  | TPIpmAs of intro_pat list * ipm_pat
  | TPIpm of ipm_head * expr list * string option
  | TPTerms of expr list
  | TPClause of string * tactic_part list
  | TPTerm of expr
  | TPTactic of tactic
  | TPBinding of name * string * expr
  | TPContext of expr
  | TPHypCtx of name * expr
  | TPHypExpr of name * expr
  | TPGroup of string * tactic_part list * string
  | TPToken of tok_kind

and tactic_branch = { tbr_pats : tactic_part list; tbr_rhs : tactic }

and tactic =
  | TBin of string * tactic * tactic
  | TPrefix of string * tactic
  | TDo of string * tactic
  | TSelect of string * tactic
  | TGroup of tactic
  | TChoices of string * tactic list
  | TDispatch of tactic * tactic list
  | TMatch of string * tactic_subject * tactic_branch list
  | TCall of string * tactic_part list
  | TLet of name * tactic * tactic
  | TLetRec of name * name list * tactic * tactic
  | TEval of string list * expr
  | TEmpty
  | TRest of tactic

type ctor_decl = {
  c_span : span;
  c_name : string;
  c_binders : binder list;
  c_ty : expr option;
}

type ind_body = {
  ib_name : name;
  ib_binders : binder list;
  ib_ty : expr option;
  ib_ctors : ctor_decl list;
}

type field_decl = {
  fd_span : span;
  fd_name : string;
  fd_binders : binder list;
  fd_ty : expr option;
  fd_def : expr option;
}

type rec_ctor =
  | RecCtorNone
  | RecCtorSingleton
  | RecCtorNamed of name

type decl_group =
  | DeclTyped of name list * expr
  | DeclBinders of binder list

type def_body = {
  d_span : span;
  d_kw : string;
  d_name : name;
  d_binders : binder list;
  d_ty : expr option;
  d_body : expr option;
}

type tac_not_part =
  | TnpLit of string
  | TnpArg of string * name

type module_kind = ModModule | ModType | ModSection

type module_open =
  | ModOpen
  | ModOpenSig of string * string list
  | ModDefined of string list * (string * string list) option

type vernac =
  | VDir of span * string list
  | VCmd of span * string list * token list
  | VInd of span * string * ind_body list
  | VRec of span * string * name * binder list * expr option * rec_ctor * field_decl list
  | VDef of def_body
  | VMutual of span * def_body list
  | VThm of span * string * name option * binder list * expr
  | VTacDef of span * name * name list * tactic
  | VTacNotation of span * tac_not_part list * tactic
  | VDecl of span * string * decl_group list
  | VNotation of span * string * string * expr * string list
  | VModule of span * module_kind * name * binder list * module_open
  | VEnd of span * name
  | VProofStart of span
  | VRaw of span * string

type proof_step =
  | PStep of span * focus list * token list
  | PBullets of focus list

type proof_end = QedEnd of span * string

type proof_body = { pf_steps : proof_step list; pf_end : proof_end option }

type item =
  | IBlock of vernac * item list * vernac option
  | IProved of vernac * proof_body
  | ISent of vernac

type fragment =
  | FSentence of vernac
  | FAlts of name * expr list
  | FFields of name * field_decl list
  | FTyped of name * expr
  | FContext of name list * expr option * expr
  | FTerm of expr

let expr_span = function
  | EId (s, _) | EHole s | EMeta (s, _) | ELtac (s, _) | ENum (s, _)
  | EStr (s, _) | EExplicit (s, _) | EApp (s, _, _) | EBin (s, _, _, _)
  | EChain (s, _, _) | EPre (s, _, _) | EParen (s, _) | ECast (s, _, _)
  | ETuple (s, _) | EOrPat (s, _) | EForall (s, _, _) | EExists (s, _, _)
  | EFun (s, _, _) | ELet (s, _, _, _, _) | ELetStar (s, _, _, _)
  | ELetQ (s, _, _, _) | ELetPat (s, _, _, _) | ELetFix (s, _, _, _, _, _)
  | EFix (s, _, _, _, _) | ENamed (s, _, _) | EAsPat (s, _, _)
  | EBits (s, _, _) | EIf (s, _, _, _) | EIfIs (s, _, _, _, _)
  | EMatch (s, _, _, _) | EList (s, _) | ERecord (s, _) | EScope (s, _, _)
  | EMixfix (s, _) | EIrInst (s, _) | EIrBlk (s, _) | EIrList (s, _)
  | EIrFn (s, _, _, _, _, _) | EBraces (s, _) | EPure (s, _) | EConst (s, _)
  | EUnit s | EInsert (s, _, _) | EProj (s, _, _) | EGFunctors (s, _)
  | EFupd (s, _, _) | EFupdw (s, _, _, _) | EStepUpd (s, _, _, _)
  | EStepUpdw (s, _, _, _, _) | ELaterN (s, _, _) | EPointsTo (s, _, _, _, _)
  | EIndexed (s, _, _, _, _) | EWp (s, _, _, _) | ETriple (s, _, _, _, _, _, _)
  | EBigOp (s, _, _, _, _, _) | EBigAll (s, _, _) | EEval (s, _, _)
  | ESig (s, _, _, _) -> s

let vernac_span = function
  | VDir (s, _) | VCmd (s, _, _) | VInd (s, _, _) | VRec (s, _, _, _, _, _, _)
  | VMutual (s, _) | VThm (s, _, _, _, _) | VTacDef (s, _, _, _)
  | VTacNotation (s, _, _) | VDecl (s, _, _) | VNotation (s, _, _, _, _)
  | VModule (s, _, _, _, _) | VEnd (s, _) | VProofStart s | VRaw (s, _) -> s
  | VDef d -> d.d_span

let tok_text = function
  | Id s | Kw s | Sym s | P s | Num s | Str s -> s
  | Dot -> "."
