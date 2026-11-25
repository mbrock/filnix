(* Exact 1-to-1 OCaml port of nanofil/web/rocq/tests/reprint.pl using Buffer.t. *)

open Ast

let is_copied_raw = function
  | "Check" | "Compute" | "Print" | "Eval" | "Search" | "About" | "Locate" | "Extraction"
  | "Extract" | "Crane" | "CertiRocq" | "Recursive" | "Next" | "Obligation" | "Opaque"
  | "Transparent" ->
      true
  | _ -> false

let rec collect_raws acc = function
  | [] -> List.rev acc
  | IBlock (s, body, _) :: rest ->
      let acc = match s with VRaw (sp, kw) when not (is_copied_raw kw) -> (sp, kw) :: acc | _ -> acc in
      let acc = List.rev_append (collect_raws [] body) acc in
      collect_raws acc rest
  | IProved (s, _) :: rest ->
      let acc = match s with VRaw (sp, kw) when not (is_copied_raw kw) -> (sp, kw) :: acc | _ -> acc in
      collect_raws acc rest
  | ISent (VRaw (sp, kw)) :: rest when not (is_copied_raw kw) ->
      collect_raws ((sp, kw) :: acc) rest
  | ISent _ :: rest -> collect_raws acc rest

let line_of_offset (text : string) (off : int) : int =
  let lim = min off (String.length text) in
  let n = ref 1 in
  for i = 0 to lim - 1 do
    if text.[i] = '\n' then incr n
  done;
  !n

let starts_with_at (text : string) (off : int) (prefix : string) : bool =
  let plen = String.length prefix in
  off + plen <= String.length text && String.sub text off plen = prefix

let escape_double_quotes s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c -> if c = '"' then Buffer.add_string b "\"\"" else Buffer.add_char b c) s;
  Buffer.contents b

let reprint ~(strict : bool) ~(file : string) (pf : Parse_vernac.parsed_file) :
    (string, string) result =
  let text = pf.text in
  let ops = pf.ops in
  match (strict, collect_raws [] pf.items) with
  | true, (_ :: _ as raws) ->
      Error
        (String.concat "\n"
           (List.map
              (fun ((sp : span), kw) ->
                Printf.sprintf "%s:%d: the grammar does not read this %s" file
                  (line_of_offset text sp.lo) kw)
              raws))
  | _ ->
      let buf = Buffer.create (String.length text * 2) in
      let w s = Buffer.add_string buf s in
      let wc c = Buffer.add_char buf c in
      let src (sp : span) =
        Buffer.add_substring buf text sp.lo (sp.hi - sp.lo);
        wc '\n'
      in
      let rec sep_by f s = function
        | [] -> ()
        | [ x ] -> f x
        | x :: xs ->
            f x;
            w s;
            sep_by f s xs
      in
      let rec names = function
        | [] -> ()
        | [ n ] -> w n.n_text
        | n :: ns ->
            w n.n_text;
            wc ' ';
            names ns
      and names_c = function
        | [] -> ()
        | [ n ] -> w n.n_text
        | n :: ns ->
            w n.n_text;
            w ", ";
            names_c ns
      and opt_type = function
        | None -> ()
        | Some t ->
            w " : ";
            pr t
      and binders bs =
        List.iter
          (fun b ->
            wc ' ';
            binder b)
          bs
      and binder b =
        match b.b_kind with
        | BPattern pat ->
            wc '\'';
            pr pat
        | BGen (open_d, items) ->
            let close_d = if open_d = "{" then "}" else ")" in
            wc '`';
            w open_d;
            sep_by gen_item ", " items;
            w close_d
        | BStruct ->
            w "{struct ";
            w (List.hd b.b_names).n_text;
            wc '}'
        | BBrace -> (
            wc '{';
            names b.b_names;
            (match b.b_ty with None -> () | Some t -> w " : "; pr t);
            wc '}')
        | BBare | BParen -> (
            match b.b_ty with
            | None -> names b.b_names
            | Some t ->
                wc '(';
                names b.b_names;
                w " : ";
                pr t;
                wc ')')
      and gen_item = function
        | GenBangCast (_, n, e) ->
            w n;
            w " : !";
            pr e
        | GenBang e ->
            wc '!';
            pr e
        | GenExpr e -> pr e
      and wp_at = function
        | WpNone -> ()
        | WpAt (None, m) ->
            w " @ ";
            pr m
        | WpAt (Some s, m) ->
            w " @ ";
            pr s;
            w "; ";
            pr m
      and wp_post post =
        match post.wp_binder with
        | None ->
            w "{{ ";
            pr post.wp_body;
            w " }}"
        | Some n ->
            w "{{ ";
            w n.n_text;
            w ", ";
            pr post.wp_body;
            w " }}"
      and count = function
        | None -> ()
        | Some n ->
            w "^(";
            pr n;
            wc ')'
      and pr = function
        | EId (_, x) -> w x
        | EHole _ -> wc '_'
        | EMeta (_, x) ->
            wc '?';
            w x
        | ELtac (_, t) ->
            w "ltac:(";
            pt t;
            wc ')'
        | ENum (_, n) -> w n
        | EStr (_, s) ->
            wc '"';
            w s;
            wc '"'
        | EExplicit (_, x) ->
            wc '@';
            w x
        | EApp (_, f, args) ->
            wc '(';
            pr f;
            List.iter
              (fun a ->
                wc ' ';
                pr a)
              args;
            wc ')'
        | EBin (_, op, l, r) ->
            wc '(';
            pr l;
            wc ' ';
            w op;
            wc ' ';
            pr r;
            wc ')'
        | EChain (_, [ o1; o2 ], [ a; b; c ]) ->
            wc '(';
            pr a;
            wc ' ';
            w o1;
            wc ' ';
            pr b;
            wc ' ';
            w o2;
            wc ' ';
            pr c;
            wc ')'
        | EChain _ -> assert false
        | EPre (_, op, e) ->
            wc '(';
            w op;
            wc ' ';
            pr e;
            wc ')'
        | EParen (_, e) ->
            wc '(';
            pr e;
            wc ')'
        | ECast (_, e, t) ->
            wc '(';
            pr e;
            w " : ";
            pr t;
            wc ')'
        | ETuple (_, es) ->
            wc '(';
            sep_by pr ", " es;
            wc ')'
        | EOrPat (_, ps) ->
            wc '(';
            sep_by pr " | " ps;
            wc ')'
        | EForall (sp, bs, b) ->
            let q = if starts_with_at text sp.lo "∀" then "∀" else "forall" in
            wc '(';
            w q;
            binders bs;
            w ", ";
            pr b;
            wc ')'
        | EExists (sp, bs, b) ->
            let q = if starts_with_at text sp.lo "∃" then "∃" else "exists" in
            wc '(';
            w q;
            binders bs;
            w ", ";
            pr b;
            wc ')'
        | EFun (_, bs, b) ->
            w "(fun";
            binders bs;
            w " => ";
            pr b;
            wc ')'
        | ELet (_, lhs, ty, v, b) ->
            w "(let ";
            (match lhs with
            | LetTuple ns ->
                wc '(';
                names_c ns;
                wc ')'
            | LetName (n, bs) ->
                w n.n_text;
                binders bs);
            opt_type ty;
            w " := ";
            pr v;
            w " in ";
            pr b;
            wc ')'
        | ELetStar (_, n, v, b) ->
            w "(let* ";
            w n.n_text;
            w " := ";
            pr v;
            w " in ";
            pr b;
            wc ')'
        | ELetQ (_, pat, v, b) ->
            w "(let? ";
            pr pat;
            w " := ";
            pr v;
            w " in ";
            pr b;
            wc ')'
        | ELetPat (_, pat, v, b) ->
            w "(let '";
            pr pat;
            w " := ";
            pr v;
            w " in ";
            pr b;
            wc ')'
        | ELetFix (_, n, bs, ty, v, b) ->
            w "(let fix ";
            w n.n_text;
            binders bs;
            opt_type ty;
            w " := ";
            pr v;
            w " in ";
            pr b;
            wc ')'
        | EFix (_, n, bs, ty, b) ->
            w "(fix ";
            w n.n_text;
            binders bs;
            opt_type ty;
            w " := ";
            pr b;
            wc ')'
        | ENamed (_, x, e) ->
            wc '(';
            w x;
            w " := ";
            pr e;
            wc ')'
        | EAsPat (_, pat, n) ->
            wc '(';
            pr pat;
            w " as ";
            w n.n_text;
            wc ')'
        | EBits (_, e, ds) ->
            wc '(';
            pr e;
            wc ')';
            String.iter
              (fun c ->
                wc '~';
                wc c)
              ds
        | EIf (_, c, t, e) ->
            w "(if ";
            pr c;
            w " then ";
            pr t;
            w " else ";
            pr e;
            wc ')'
        | EIfIs (_, c, pat, t, e) ->
            w "(if ";
            pr c;
            w " is ";
            pr pat;
            w " then ";
            pr t;
            w " else ";
            pr e;
            wc ')'
        | EMatch (_, ss, ret, brs) ->
            w "(match ";
            sep_by
              (function
                | ScrutExpr e -> pr e
                | ScrutAs (e, n) ->
                    pr e;
                    w " as ";
                    w n.n_text)
              ", " ss;
            (match ret with None -> () | Some r -> w " return "; pr r);
            w " with";
            List.iter
              (fun br ->
                w "\n    | ";
                sep_by (sep_by pr ", ") " | " br.br_alts;
                w " => ";
                pr br.br_rhs)
              brs;
            w "\n  end)"
        | EList (_, es) ->
            wc '[';
            sep_by pr "; " es;
            wc ']'
        | ERecord (_, fs) ->
            w "{| ";
            sep_by
              (function
                | RFld (_, n, e) ->
                    w n;
                    w " := ";
                    pr e
                | RFldB (_, n, bs, e) ->
                    w n;
                    binders bs;
                    w " := ";
                    pr e)
              "; " fs;
            w " |}"
        | EScope (_, e, k) ->
            wc '(';
            pr e;
            w ")%";
            w k
        | EMixfix (_, parts) ->
            wc '(';
            List.iter (function MStr s -> w s | MExpr e -> pr e) parts;
            wc ')'
        | EIrInst (_, i) ->
            w "(ir{ ";
            pr_ir_ssa i;
            w " })"
        | EIrBlk (_, b) ->
            w "(ir_blk{ ";
            pr_ir_block b;
            w " })"
        | EIrList (_, is) ->
            w "(ir[ ";
            sep_by pr_ir_ssa "; " is;
            w " ])"
        | EIrFn (_, lk, nm, ps, ret, bs) ->
            w "(ir_fn{ ";
            pr lk;
            wc ' ';
            pr nm;
            pr_ir_formals ps;
            w " -> ";
            pr ret;
            wc ' ';
            pr_ir_body bs;
            w " })"
        | EBraces (_, e) ->
            wc '{';
            pr e;
            wc '}'
        | EPure (_, e) ->
            w "⌜";
            pr e;
            w "⌝"
        | EConst (_, c) -> w c
        | EUnit _ -> w "()"
        | EInsert (_, k, v) ->
            w "<[";
            pr k;
            w " := ";
            pr v;
            w "]>"
        | EProj (_, e, op) ->
            w "((";
            pr e;
            w ") ";
            w op;
            wc ')'
        | EGFunctors (_, es) ->
            w "#[";
            sep_by pr "; " es;
            wc ']'
        | EFupd (_, ms, a) ->
            w "(|={";
            sep_by pr "," ms;
            w "}=> ";
            pr a;
            wc ')'
        | EFupdw (_, ms, l, r) ->
            wc '(';
            pr l;
            w " ={";
            sep_by pr "," ms;
            w "}=∗ ";
            pr r;
            wc ')'
        | EStepUpd (_, ms, n, a) ->
            w "(|={";
            sep_by pr "," ms;
            w "}▷=>";
            count n;
            wc ' ';
            pr a;
            wc ')'
        | EStepUpdw (_, ms, n, l, r) ->
            wc '(';
            pr l;
            w " ={";
            sep_by pr "," ms;
            w "}▷=∗";
            count n;
            wc ' ';
            pr r;
            wc ')'
        | ELaterN (_, n, a) ->
            w "(▷^(";
            pr n;
            w ") ";
            pr a;
            wc ')'
        | EPointsTo (_, op, l, ms, r) ->
            wc '(';
            pr l;
            wc ' ';
            w op;
            List.iter
              (function
                | PmName g ->
                    wc '[';
                    pr g;
                    wc ']'
                | PmDfrac d ->
                    wc '{';
                    pr d;
                    wc '}'
                | PmOwn q ->
                    w "{#";
                    pr q;
                    wc '}'
                | PmPersistent -> w "□")
              ms;
            wc ' ';
            pr r;
            wc ')'
        | EIndexed (_, "✓", n, None, a) ->
            w "(✓{";
            pr n;
            w "} ";
            pr a;
            wc ')'
        | EIndexed (_, op, n, Some l, r) ->
            wc '(';
            pr l;
            wc ' ';
            w op;
            wc '{';
            pr n;
            wc '}';
            if op = "≡" then w "≡";
            wc ' ';
            pr r;
            wc ')'
        | EIndexed _ -> assert false
        | EWp (_, e, at, post) ->
            w "(WP ";
            pr e;
            wp_at at;
            wc ' ';
            wp_post post;
            wc ')'
        | ETriple (_, pre, e, at, bs, ret, post) ->
            w "{{{ ";
            pr pre;
            w " }}} ";
            pr e;
            wp_at at;
            w " {{{";
            if bs <> [] then (
              binders bs;
              wc ',');
            w " RET ";
            pr ret;
            w "; ";
            pr post;
            w " }}}"
        | EBigOp (_, op, kind, bb, cs, b) ->
            w "([";
            w op;
            wc ' ';
            w kind;
            w "] ";
            (match bb.bb_key with
            | None -> ()
            | Some kn ->
                w kn.n_text;
                w " ↦ ");
            w (String.concat ";" (List.map (fun n -> n.n_text) bb.bb_vals));
            w " ∈ ";
            sep_by pr ";" cs;
            w ", ";
            pr b;
            wc ')'
        | EBigAll (_, op, e) ->
            w "([";
            w op;
            w "] ";
            pr e;
            wc ')'
        | EEval (_, ws, e) ->
            w "Eval ";
            w (String.concat " " ws);
            w " in ";
            pr e
        | ESig (_, x, t, q) ->
            wc '{';
            w x.n_text;
            w " : ";
            pr t;
            w " | ";
            pr q;
            wc '}'
      and pr_ir_formals = function
        | [] -> w "()"
        | ps ->
            wc '(';
            sep_by
              (fun p ->
                pr p.irp_ty;
                w " %";
                pr p.irp_name)
              ", " ps;
            wc ')'
      and pr_ir_body = function
        | IrBodyExpr xs ->
            w "blocks(";
            pr xs;
            wc ')'
        | IrBodyBlocks [] -> w "{}"
        | IrBodyBlocks bs ->
            w "{\n  ";
            sep_by pr_ir_block ";\n  " bs;
            w "\n}"
      and pr_ir_block = function
        | IrBlockEscape x ->
            wc '(';
            pr x;
            wc ')'
        | IrBlock (_, l, phis, ins, j) ->
            wc '@';
            pr l;
            (match phis with
            | [] -> wc ':'
            | _ ->
                w " [";
                sep_by pr_ir_phi "; " phis;
                w "]:");
            (match ins with
            | IrInsts [] -> w " => "
            | IrCode xs ->
                w " code(";
                pr xs;
                w ") => "
            | IrInsts is ->
                w "\n    ";
                sep_by pr_ir_ssa ";\n    " is;
                w "\n    => ");
            pr_ir_ssa j
      and pr_ir_phi = function
        | IrPhiEscape x ->
            wc '(';
            pr x;
            wc ')'
        | IrPhi (_, d, k, incs) ->
            wc '%';
            pr d;
            w " : ";
            pr k;
            w " = phi(";
            sep_by
              (fun inc ->
                pr inc.iri_lab;
                w " => ";
                pr_ir_opnd inc.iri_val)
              ", " incs;
            wc ')'
      and pr_ir_opnd = function
        | IrVal x ->
            w "val(";
            pr x;
            wc ')'
        | IrTmp x ->
            wc '%';
            pr x
        | IrGlobal x ->
            wc '$';
            pr x
        | IrConst x ->
            wc '#';
            pr x
      and pr_ir_edge = function
        | IrEdgeExpr x ->
            w "edge(";
            pr x;
            wc ')'
        | IrPoll l ->
            w "poll ";
            pr l
        | IrTo l -> pr l
      and pr_ir_args = function
        | [] -> w "()"
        | args ->
            wc '(';
            sep_by
              (fun a ->
                pr a.ira_ty;
                wc ' ';
                pr_ir_opnd a.ira_val)
              ", " args;
            wc ')'
      and pr_ir_ssa s =
        match s.irs_kind with
        | IrSsaEscape x ->
            wc '(';
            pr x;
            wc ')'
        | IrLet (d, k, op, args) ->
            wc '%';
            pr d;
            w " : ";
            pr k;
            w " = ";
            pr op;
            if args <> [] then (
              wc ' ';
              sep_by pr_ir_opnd ", " args)
        | IrFlight (d, base, off) ->
            wc '%';
            pr d;
            w " = ";
            pr_ir_opnd base;
            w " +p ";
            pr_ir_opnd off
        | IrStore (sz, a, off, v) ->
            w "store ";
            pr sz;
            w " [";
            pr_ir_opnd a;
            w " + ";
            pr off;
            w "] <- ";
            pr_ir_opnd v
        | IrStorePtr (a, off, v) ->
            w "store.ptr [";
            pr_ir_opnd a;
            w " + ";
            pr off;
            w "] <- ";
            pr_ir_opnd v
        | IrAlloca (x, sz) ->
            w "alloca ";
            pr x;
            wc ' ';
            pr sz
        | IrGoto dst ->
            w "goto ";
            pr_ir_edge dst
        | IrBr (x, y, n) ->
            w "br ";
            pr_ir_opnd x;
            w " ? ";
            pr_ir_edge y;
            w " : ";
            pr_ir_edge n
        | IrRet IrRetVoid -> w "ret void"
        | IrRet (IrRetVal v) ->
            w "ret ";
            pr_ir_opnd v
        | IrUnreachable -> w "unreachable"
        | IrCall (kw, res, fn, args) ->
            w kw;
            wc ' ';
            (match res with
            | IrCallRes (d, k) ->
                wc '%';
                pr d;
                w " : ";
                pr k;
                w " = "
            | IrCallVoid -> w "void ");
            pr_ir_opnd fn;
            pr_ir_args args
      and pt = function
        | TBin (op, l, r) ->
            wc '(';
            pt l;
            wc ' ';
            w op;
            wc ' ';
            pt r;
            wc ')'
        | TPrefix (k, t) ->
            wc '(';
            w k;
            wc ' ';
            pt t;
            wc ')'
        | TDo (n, t) ->
            w "(do ";
            w n;
            wc ' ';
            pt t;
            wc ')'
        | TSelect (s, t) ->
            w s;
            w ": ";
            pt t
        | TGroup t ->
            wc '(';
            pt t;
            wc ')'
        | TChoices (k, ts) ->
            w k;
            w " [";
            sep_by pt " | " ts;
            wc ']'
        | TDispatch (t, ts) ->
            wc '(';
            pt t;
            w "; [";
            sep_by pt " | " ts;
            w "])"
        | TMatch (k, subj, bs) ->
            w k;
            wc ' ';
            (match subj with
            | TSubGoal -> w "goal"
            | TSubType e ->
                w "type of ";
                pr e
            | TSubTerm e -> pr e);
            w " with ";
            List.iter
              (fun br ->
                w " | ";
                pt_parts br.tbr_pats;
                w " => ";
                pt br.tbr_rhs)
              bs;
            w " end"
        | TCall (n, ps) ->
            w n;
            wc ' ';
            pt_parts ps
        | TLet (n, v, b) ->
            w "(let ";
            w n.n_text;
            w " := ";
            pt v;
            w " in ";
            pt b;
            wc ')'
        | TLetRec (n, args, v, b) ->
            w "(let rec ";
            w n.n_text;
            wc ' ';
            names args;
            w " := ";
            pt v;
            w " in ";
            pt b;
            wc ')'
        | TEval (ws, e) ->
            w "eval ";
            w (String.concat " " ws);
            w " in ";
            pr e
        | TEmpty -> ()
        | TRest t ->
            pt t;
            w " .."
      and pt_parts ps =
        List.iter
          (fun p ->
            pt_part p;
            wc ' ')
          ps
      and pt_part = function
        | TPIntro ps -> pt_intro_seq ps
        | TPIpmIntros is ->
            List.iter
              (function
                | IpmCoq ps ->
                    wc '(';
                    pt_intro_seq ps;
                    w ") "
                | IpmStr s ->
                    wc '"';
                    w s;
                    w "\" ")
              is
        | TPIpmAs (ps, pat) ->
            if ps <> [] then (
              wc '(';
              pt_intro_seq ps;
              w ") ");
            (match pat with
            | IpmPatStr s ->
                wc '"';
                w s;
                wc '"'
            | IpmPatPure p ->
                wc '%';
                pt_intro p)
        | TPIpm (h, args, spat) ->
            wc '(';
            (match h with
            | IpmHyp s ->
                wc '"';
                w s;
                wc '"'
            | IpmExpr e -> pr e);
            if args <> [] then (
              w " $!";
              List.iter
                (fun a ->
                  wc ' ';
                  pr a)
                args);
            (match spat with
            | None -> ()
            | Some s ->
                w " with \"";
                w s;
                wc '"');
            wc ')'
        | TPTerms es -> sep_by pr ", " es
        | TPClause (k, ps) ->
            w k;
            w (if k = "eqn" then ": " else " ");
            pt_parts ps
        | TPTerm e -> pr e
        | TPTactic t ->
            wc '(';
            pt t;
            wc ')'
        | TPBinding (n, op, e) ->
            wc '(';
            w n.n_text;
            wc ' ';
            w op;
            wc ' ';
            pr e;
            wc ')'
        | TPContext e ->
            w "context [";
            pr e;
            wc ']'
        | TPHypCtx (n, e) ->
            w n.n_text;
            w " : context [";
            pr e;
            wc ']'
        | TPHypExpr (n, e) ->
            w n.n_text;
            w " : ";
            pr e
        | TPGroup (o, ps, c) ->
            w o;
            pt_parts ps;
            w c
        | TPToken (Str s) ->
            wc '"';
            w s;
            wc '"'
        | TPToken k -> w (tok_text k)
      and pt_intro = function
        | IpName n -> w n.n_text
        | IpRewrite op -> w op
        | IpAuto k -> w k
        | IpFresh n ->
            wc '?';
            w n.n_text
        | IpAnd ps ->
            wc '(';
            sep_by pt_intro " & " ps;
            wc ')'
        | IpOr arms ->
            wc '[';
            sep_by pt_intro_seq " | " arms;
            wc ']'
        | IpInj ps ->
            w "[= ";
            pt_intro_seq ps;
            wc ']'
      and pt_intro_seq ps = sep_by pt_intro " " ps in
      let print_def d =
        w d.d_kw;
        wc ' ';
        w d.d_name.n_text;
        binders d.d_binders;
        opt_type d.d_ty;
        match d.d_body with
        | None -> ()
        | Some b ->
            w " :=\n  ";
            pr b
      in
      let print_ind_body b =
        w b.ib_name.n_text;
        binders b.ib_binders;
        opt_type b.ib_ty;
        w " :=";
        List.iter
          (fun c ->
            w "\n  | ";
            w c.c_name;
            binders c.c_binders;
            opt_type c.c_ty)
          b.ib_ctors
      in
      let rec print_fields = function
        | [] -> ()
        | f :: fs ->
            w "  ";
            w f.fd_name;
            binders f.fd_binders;
            opt_type f.fd_ty;
            (match f.fd_def with None -> () | Some d -> w " := "; pr d);
            w (if fs = [] then "\n" else ";\n");
            print_fields fs
      in
      let print_sent = function
        | VInd (_, kw, bodies) ->
            w kw;
            wc ' ';
            sep_by print_ind_body "\nwith " bodies;
            w ".\n"
        | VRec (_, "Class", n, bs, sort, RecCtorSingleton, [ fld ])
          when fld.fd_binders = [] && fld.fd_def = None && fld.fd_ty <> None ->
            w "Class ";
            w n.n_text;
            binders bs;
            opt_type sort;
            w " := ";
            w fld.fd_name;
            w " : ";
            pr (Option.get fld.fd_ty);
            w ".\n"
        | VRec (_, kw, n, bs, sort, ctor, fs) ->
            w kw;
            wc ' ';
            w n.n_text;
            binders bs;
            opt_type sort;
            w " :=";
            (match ctor with
            | RecCtorNamed c ->
                wc ' ';
                w c.n_text
            | RecCtorNone | RecCtorSingleton -> ());
            w " {\n";
            print_fields fs;
            w "}.\n"
        | VDef d ->
            print_def d;
            w ".\n"
        | VMutual (_, d :: ds) ->
            print_def d;
            List.iter
              (fun e ->
                wc '\n';
                print_def e)
              ds;
            w ".\n"
        | VMutual (_, []) -> ()
        | VThm (_, "Goal", None, [], ty) ->
            w "Goal ";
            pr ty;
            w ".\n"
        | VThm (_, kw, Some n, bs, ty) ->
            w kw;
            wc ' ';
            w n.n_text;
            binders bs;
            w " : ";
            pr ty;
            w ".\n"
        | VThm (sp, _, _, _, _) -> src sp
        | VTacDef (_, n, args, t) ->
            w "Ltac ";
            w n.n_text;
            wc ' ';
            names args;
            w " := ";
            pt t;
            w ".\n"
        | VTacNotation (_, parts, t) ->
            w "Tactic Notation ";
            List.iter
              (function
                | TnpLit s ->
                    wc '"';
                    w (escape_double_quotes s);
                    w "\" "
                | TnpArg (k, n) ->
                    w k;
                    wc '(';
                    w n.n_text;
                    w ") ")
              parts;
            w " := ";
            pt t;
            w ".\n"
        | VDecl (_, "Context", gs) when not (match gs with [ DeclBinders _ ] -> true | _ -> false) ->
            w "Context";
            List.iter
              (function
                | DeclTyped (ns, ty) ->
                    w " (";
                    names ns;
                    w " : ";
                    pr ty;
                    wc ')'
                | DeclBinders bs -> binders bs)
              gs;
            w ".\n"
        | VDecl (_, kw, [ DeclTyped (ns, ty) ]) ->
            w kw;
            wc ' ';
            names ns;
            w " : ";
            pr ty;
            w ".\n"
        | VDecl (_, kw, [ DeclBinders bs ]) ->
            w kw;
            binders bs;
            w ".\n"
        | VDecl (_, kw, gs) ->
            w kw;
            List.iter
              (function
                | DeclTyped (ns, ty) ->
                    w " (";
                    names ns;
                    w " : ";
                    pr ty;
                    wc ')'
                | DeclBinders bs -> binders bs)
              gs;
            w ".\n"
        | s -> src (vernac_span s)
      in
      let print_focus = function
        | FocusNum n ->
            w n;
            w ": { "
        | FocusBullet b ->
            w b;
            wc ' '
      in
      let unparsed_tac = ref None in
      let print_step = function
        | PStep (sp, bs, ts) -> (
            List.iter print_focus bs;
            match Parse_tactic.parse_tactic_tokens ~ops ts with
            | Some t ->
                pt t;
                w ".\n"
            | None ->
                if strict then unparsed_tac := Some sp
                else src sp)
        | PBullets bs ->
            List.iter print_focus bs;
            wc '\n'
      in
      let rec print_item = function
        | IBlock (s, body, e) ->
            print_sent s;
            List.iter print_item body;
            Option.iter print_sent e
        | IProved (s, pf_body) ->
            print_sent s;
            List.iter print_step pf_body.pf_steps;
            (match pf_body.pf_end with Some (QedEnd (sp, _)) -> src sp | None -> ())
        | ISent s -> print_sent s
      in
      List.iter print_item pf.items;
      match !unparsed_tac with
      | Some sp -> Error (Printf.sprintf "%s:%d: unparsed tactic" file (line_of_offset text sp.lo))
      | None -> Ok (Buffer.contents buf)
