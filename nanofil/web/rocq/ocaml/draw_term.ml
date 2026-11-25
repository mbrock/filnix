(* Terms, blocks, inference rules, and vernacular sentences renderer
   mirroring rocq_draw.pl lines 239-704 and 1358-1648. *)

open Ast
open Draw_env
open Html

let nbsp = "\xc2\xa0"

let kw b s = el_text b "span" (Some "kw") s
let defeq b = el_a b "span" (Some "op wide defeq") [ ("title", ":=") ] (fun b -> raw b "≔")

let op_glyph = function
  | "->" -> "→"
  | "<->" -> "↔"
  | "/\\" -> "∧"
  | "\\/" -> "∨"
  | "~" -> "¬"
  | "<>" -> "≠"
  | "<=" -> "≤"
  | ">=" -> "≥"
  | "<=?" -> "≤?"
  | ">=?" -> "≥?"
  | "*" -> "×"
  | "-" -> "−"
  | "=>" -> "⇒"
  | "-∗" -> "−∗"
  | "∗-∗" -> "∗−∗"
  | "|==>" -> "|⇛"
  | "==∗" -> "⇛"
  | "~~>" -> "⇝"
  | "-d>" -> "→ᵈ"
  | "-n>" -> "→ⁿᵉ"
  | op -> op

let op_ b op = el_a b "span" (Some "op wide") [ ("title", op) ] (fun b -> esc b (op_glyph op))

let is_spaced_prefix op =
  match op with
  | "⊢" | "|==>" | "●" | "◯" | "✓" | "£" -> true
  | _ -> String.starts_with ~prefix:"<" op

let var_text b x =
  let n = String.length x in
  let p_end = ref n in
  while !p_end > 0 && x.[!p_end - 1] = '\'' do
    decr p_end
  done;
  let n_primes = n - !p_end in
  let d_start = ref !p_end in
  while !d_start > 0 && x.[!d_start - 1] >= '0' && x.[!d_start - 1] <= '9' do
    decr d_start
  done;
  if !d_start = 0 then esc b (String.sub x 0 !p_end)
  else (
    esc b (String.sub x 0 !d_start);
    if !d_start < !p_end then el_text b "sub" None (String.sub x !d_start (!p_end - !d_start)));
  for _ = 1 to n_primes do
    raw b "′"
  done

let var_ b x = el_a b "span" (Some "v") [ ("data-v", x) ] (fun b -> var_text b x)
let var_def b x = el_a b "span" (Some "v def") [ ("data-v", x) ] (fun b -> var_text b x)

let name_ref ctx b x env pos =
  if List.mem x env then var_ b x
  else
    let k = name_kind ctx x in
    let c0 = kind_class k in
    let cls = if pos = `Head && k = KOther then "f" else c0 in
    if not ctx.in_button then
      match global_ref ctx x with
      | Some (href, _) -> el_a b "a" (Some cls) [ ("href", href) ] (fun b -> esc b x)
      | None -> el_text b "span" (Some cls) x
    else el_text b "span" (Some cls) x

let rec vars b = function
  | [] -> ()
  | [ n ] -> var_def b n.n_text
  | n :: ns ->
      var_def b n.n_text;
      raw_char b ' ';
      vars b ns

let rec seq_defs b = function
  | [] -> ()
  | [ n ] -> el_text b "span" (Some "f def") n.n_text
  | n :: ns ->
      el_text b "span" (Some "f def") n.n_text;
      raw_char b ' ';
      seq_defs b ns

let rec pat_vars ctx acc = function
  | EId (_, x) when x <> "_" && (not (is_ctor ctx x)) && not (String.contains x '.') -> x :: acc
  | EApp (_, _, args) | EOrPat (_, args) | ETuple (_, args) | EList (_, args) ->
      List.fold_left (pat_vars ctx) acc args
  | EParen (_, e) | EScope (_, e, _) -> pat_vars ctx acc e
  | EBin (_, _, l, r) -> pat_vars ctx (pat_vars ctx acc l) r
  | EAsPat (_, p, n) -> pat_vars ctx (n.n_text :: acc) p
  | _ -> acc

let alts_vars ctx alts =
  List.fold_left (List.fold_left (pat_vars ctx)) [] alts |> List.sort_uniq String.compare

let binders_env ctx bs env0 =
  List.fold_left
    (fun env b ->
      match b.b_kind with
      | BPattern p -> alts_vars ctx [ [ p ] ] @ env
      | _ ->
          List.fold_left
            (fun a n -> if n.n_text = "_" then a else n.n_text :: a)
            env b.b_names)
    env0 bs

type split_binder =
  | SBOrig of binder
  | SBInst of span * string * expr

let split_gen bs =
  List.concat_map
    (fun b ->
      match b.b_kind with
      | BGen (open_d, items) ->
          List.map
            (function
              | GenBang e -> SBInst (b.b_span, open_d, e)
              | GenBangCast (sp, n, e) ->
                  SBInst (b.b_span, open_d, ECast (sp, EId ({ lo = sp.lo; hi = sp.lo + String.length n }, n), e))
              | GenExpr e -> SBInst (b.b_span, open_d, e))
            items
      | _ -> [ SBOrig b ])
    bs

let lhs_names = function
  | LetName (n, _) -> [ n.n_text ]
  | LetTuple ns -> List.map (fun n -> n.n_text) ns

let esc_words b ws =
  let s0 = String.concat " " ws in
  let replace_all s sub rep =
    let slen = String.length s and sublen = String.length sub in
    let out = Buffer.create slen in
    let rec go i =
      if i > slen - sublen then Buffer.add_substring out s i (slen - i)
      else if String.sub s i sublen = sub then (
        Buffer.add_string out rep;
        go (i + sublen))
      else (
        Buffer.add_char out s.[i];
        go (i + 1))
    in
    go 0;
    Buffer.contents out
  in
  let s1 = replace_all s0 "( " "(" in
  let s2 = replace_all s1 " )" ")" in
  esc b s2

let notation_pattern b s e =
  let ws = String.split_on_char ' ' s in
  let xs = Draw_prose.collect_sub_ids [] e in
  el_a b "span" (Some "notation") [ ("title", s) ] (fun b ->
      let rec go = function
        | [] -> ()
        | [ w ] ->
            if List.mem w xs then var_ b w else el_text b "span" (Some "op wide") w
        | w :: rest ->
            if List.mem w xs then var_ b w else el_text b "span" (Some "op wide") w;
            raw_char b ' ';
            go rest
      in
      go ws)

(* ── Inline terms ──────────────────────────────────────────────────────── *)

let rec term ctx b e env =
  match e with
  | EId (_, x) -> name_ref ctx b x env `Arg
  | EHole _ -> el_a b "span" (Some "v anon") [ ("title", "_") ] (fun b -> raw b "_")
  | EMeta (_, x) ->
      el b "span" (Some "rq-meta") (fun b ->
          raw_char b '?';
          var_def b x)
  | ELtac (_, t) ->
      if !Draw_hooks.tactic_structural_ref t then (
        kw b "ltac:";
        raw_char b '(';
        !Draw_hooks.draw_tactic_block_ref ctx b t env;
        raw_char b ')')
      else (
        kw b "ltac:";
        el b "span" (Some "paren") (fun b -> !Draw_hooks.draw_tactic_inline_ref ctx b t env))
  | ENum (_, n) -> el_text b "span" (Some "n") n
  | EStr (_, s) ->
      el b "span" (Some "s") (fun b ->
          raw_char b '"';
          esc b s;
          raw_char b '"')
  | EExplicit (_, x) ->
      el b "span" (Some "explicit") (fun b ->
          el_raw b "span" (Some "at") "@";
          name_ref ctx b x env `Arg)
  | EApp (sp, EId (_, f), [ a; b_arg ]) when Hashtbl.mem ctx.folds f ->
      let op = Hashtbl.find ctx.folds f in
      term ctx b (EBin (sp, op, a, b_arg)) env
  | EApp (_, f, args) ->
      el_a b "span" (Some "c app") [ ("data-d", "args") ] (fun b ->
          head_ ctx b f env;
          el b "span" (Some "args") (fun b -> items ctx b args env))
  | EBin (_, "^", l, ((ENum _ | EId _) as r)) ->
      el_a b "span" (Some "o rq-pow") [ ("title", "^") ] (fun b ->
          term ctx b l env;
          el b "sup" (Some "rq-exp") (fun b -> term ctx b r env))
  | EBin (_, op, l, r) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          term ctx b l env;
          raw b nbsp;
          op_ b op;
          raw_char b ' ';
          term ctx b r env)
  | EChain (_, [ o1; o2 ], [ x; y; z ]) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          term ctx b x env;
          raw b nbsp;
          op_ b o1;
          raw_char b ' ';
          term ctx b y env;
          raw b nbsp;
          op_ b o2;
          raw_char b ' ';
          term ctx b z env)
  | EChain _ -> assert false
  | EPre (_, op, a) ->
      el b "span" (Some "o pre") (fun b ->
          op_ b op;
          if is_spaced_prefix op then raw b nbsp;
          term ctx b a env)
  | EParen (_, e0) -> el b "span" (Some "paren") (fun b -> term ctx b e0 env)
  | ECast (_, e0, t) ->
      el b "span" (Some "paren") (fun b ->
          term ctx b e0 env;
          raw b nbsp;
          el_a b "span" (Some "op wide") [ ("title", ":") ] (fun b -> raw_char b ':');
          raw_char b ' ';
          term ctx b t env)
  | ETuple (_, es) ->
      el_a b "span" (Some "c tuple") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args") (fun b -> sep_items ctx b es env ","))
  | EForall (_, bs, body) -> quant ctx b "∀" "forall" bs "," body env
  | EExists (_, bs, body) -> quant ctx b "∃" "exists" bs "," body env
  | EFun (_, bs, body) -> quant ctx b "λ" "fun" bs (nbsp ^ "⇒") body env
  | ELet (_, lhs, ty, v, body) ->
      let env1 = lhs_names lhs @ env in
      el b "span" (Some "o let") (fun b ->
          kw b "let";
          raw_char b ' ';
          draw_lhs ctx b lhs env;
          opt_type ctx b ty env;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b v env;
          raw_char b ' ';
          kw b "in";
          raw_char b ' ';
          term ctx b body env1)
  | ELetStar (_, n, v, body) ->
      el b "span" (Some "o let") (fun b ->
          kw b "let*";
          raw_char b ' ';
          var_def b n.n_text;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b v env;
          raw_char b ' ';
          kw b "in";
          raw_char b ' ';
          term ctx b body (n.n_text :: env))
  | ELetPat (_, pat, v, body) ->
      let env1 = alts_vars ctx [ [ pat ] ] @ env in
      el b "span" (Some "o let") (fun b ->
          kw b "let";
          raw_char b ' ';
          el_raw b "span" (Some "tick") "'";
          term ctx b pat env1;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b v env;
          raw_char b ' ';
          kw b "in";
          raw_char b ' ';
          term ctx b body env1)
  | ELetQ (_, pat, v, body) ->
      let env1 = alts_vars ctx [ [ pat ] ] @ env in
      el b "span" (Some "o let") (fun b ->
          kw b "let?";
          raw_char b ' ';
          term ctx b pat env1;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b v env;
          raw_char b ' ';
          kw b "in";
          raw_char b ' ';
          term ctx b body env1)
  | ELetFix (_, f, bs, ty, v, body) ->
      let env_v = binders_env ctx bs (f.n_text :: env) in
      el b "span" (Some "o let") (fun b ->
          kw b "let fix";
          raw_char b ' ';
          var_def b f.n_text;
          binders_ ctx b bs env;
          opt_type ctx b ty env_v;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b v env_v;
          raw_char b ' ';
          kw b "in";
          raw_char b ' ';
          term ctx b body (f.n_text :: env))
  | EFix (_, f, bs, ty, body) ->
      let env_b = binders_env ctx bs (f.n_text :: env) in
      el b "span" (Some "o let") (fun b ->
          kw b "fix";
          raw_char b ' ';
          var_def b f.n_text;
          binders_ ctx b bs env;
          opt_type ctx b ty env_b;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b body env_b)
  | ENamed (_, x, e0) ->
      el b "span" (Some "paren rq-named") (fun b ->
          el_text b "span" (Some "rq-arg-name") x;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b e0 env)
  | EAsPat (_, pat, n) ->
      term ctx b pat env;
      raw_char b ' ';
      kw b "as";
      raw_char b ' ';
      var_def b n.n_text
  | EBits (_, e0, ds) ->
      term ctx b e0 env;
      let buf = Buffer.create (String.length ds * 2) in
      String.iter
        (fun c ->
          Buffer.add_char buf '~';
          Buffer.add_char buf c)
        ds;
      el_a b "span" (Some "rq-bits")
        [ ("title", "a positive's binary digits: p~0 is 2p, p~1 is 2p + 1") ]
        (fun b -> esc b (Buffer.contents buf))
  | EOrPat (_, ps) -> el b "span" (Some "paren") (fun b -> bar_items ctx b ps env)
  | EIfIs (_, c, pat, t, e0) ->
      el b "span" (Some "o if") (fun b ->
          kw b "if";
          raw_char b ' ';
          term ctx b c env;
          raw_char b ' ';
          kw b "is";
          raw_char b ' ';
          term ctx b pat env;
          raw_char b ' ';
          kw b "then";
          raw_char b ' ';
          term ctx b t env;
          raw_char b ' ';
          kw b "else";
          raw_char b ' ';
          term ctx b e0 env)
  | EIf (_, c, t, e0) ->
      el b "span" (Some "o if") (fun b ->
          kw b "if";
          raw_char b ' ';
          term ctx b c env;
          raw_char b ' ';
          kw b "then";
          raw_char b ' ';
          term ctx b t env;
          raw_char b ' ';
          kw b "else";
          raw_char b ' ';
          term ctx b e0 env)
  | EMatch (_, ss, _, brs) ->
      el b "span" (Some "o match") (fun b ->
          kw b "match";
          raw_char b ' ';
          scrutinees ctx b ss env;
          raw_char b ' ';
          kw b "with";
          raw_char b ' ';
          inline_branches ctx b brs env;
          raw_char b ' ';
          kw b "end")
  | EList (_, []) -> el_raw b "span" (Some "l empty") "[ ]"
  | EList (_, es) ->
      el_a b "span" (Some "l") [ ("data-d", "args") ] (fun b -> sep_items ctx b es env ";")
  | ERecord (_, fs) ->
      el_a b "span" (Some "c rec") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args recbr") (fun b -> rec_fields ctx b fs env))
  | EScope (_, e0, k) ->
      term ctx b e0 env;
      el_a b "span" (Some "scope") [ ("title", "scope") ] (fun b ->
          raw_char b '%';
          esc b k)
  | EMixfix (_, parts) ->
      List.iter (function MStr s -> esc b s | MExpr e0 -> term ctx b e0 env) parts
  | EIrInst (_, i) ->
      el b "span" (Some "rq-ir-inline") (fun b -> !Draw_hooks.draw_ir_ssa_ref ctx b i env)
  | EIrList (_, is) ->
      el_a b "span" (Some "c rq-ir-inline rq-ir-inline-list") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args l") (fun b ->
              !Draw_hooks.draw_ir_inline_ssa_items_ref ctx b is env))
  | EIrBlk (_, blk) ->
      el b "span" (Some "rq-ir-inline rq-ir-inline-blk") (fun b ->
          !Draw_hooks.draw_ir_blk_inline_ref ctx b blk env)
  | EIrFn (_, lk, nm, ps, ret, bs) ->
      el b "span" (Some "rq-ir-inline rq-ir-inline-fn") (fun b ->
          !Draw_hooks.draw_ir_fn_inline_ref ctx b lk nm ps ret bs env)
  | EBraces (_, e0) -> el b "span" (Some "braces") (fun b -> term ctx b e0 env)
  | ESig (_, x, t, q) ->
      el b "span" (Some "braces sig") (fun b ->
          var_def b x.n_text;
          raw b nbsp;
          el_raw b "span" (Some "op wide") ":";
          raw_char b ' ';
          term ctx b t env;
          raw_char b ' ';
          el_raw b "span" (Some "op wide") "|";
          raw_char b ' ';
          term ctx b q (x.n_text :: env))
  | EPure (_, e0) ->
      el b "span" (Some "rq-pure") (fun b ->
          el_raw b "span" (Some "op") "⌜";
          term ctx b e0 env;
          el_raw b "span" (Some "op") "⌝")
  | EConst (_, c) -> el_text b "span" (Some "rq-const") c
  | EUnit _ -> el_raw b "span" (Some "a") "()"
  | EInsert (_, k, v) ->
      el b "span" (Some "rq-insert") (fun b ->
          el_text b "span" (Some "op") "<[";
          term ctx b k env;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b v env;
          el_text b "span" (Some "op") "]>")
  | EProj (_, e0, op) ->
      term ctx b e0 env;
      el_a b "span" (Some "rq-proj") [ ("title", op) ] (fun b -> esc b op)
  | EGFunctors (_, es) ->
      el b "span" (Some "rq-gfunctors") (fun b ->
          el_raw b "span" (Some "op") "#";
          term ctx b (EList ({ lo = 0; hi = 0 }, es)) env)
  | EFupd (_, ms, a) ->
      el b "span" (Some "o pre rq-upd") (fun b ->
          draw_update ctx b ms "|⇛" None env;
          raw b nbsp;
          term ctx b a env)
  | ELaterN (_, n, a) ->
      el b "span" (Some "o pre") (fun b ->
          el b "span" (Some "op") (fun b -> step_later ctx b (Some n) env);
          term ctx b a env)
  | EStepUpd (_, ms, n, a) ->
      el b "span" (Some "o pre rq-upd") (fun b ->
          draw_update ctx b ms "|⇛" (Some (fun b -> step_later ctx b n env)) env;
          raw b nbsp;
          term ctx b a env)
  | EStepUpdw (_, ms, n, l, r) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          term ctx b l env;
          raw b nbsp;
          draw_update ctx b ms "⇛" (Some (fun b -> step_later ctx b n env)) env;
          raw_char b ' ';
          term ctx b r env)
  | EFupdw (_, ms, l, r) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          term ctx b l env;
          raw b nbsp;
          draw_update ctx b ms "⇛" None env;
          raw_char b ' ';
          term ctx b r env)
  | EPointsTo (_, op, l, ms, r) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          term ctx b l env;
          raw b nbsp;
          el_a b "span" (Some "op wide rq-pointsto") [ ("title", op) ] (fun b ->
              esc b op;
              List.iter (pointsto_mod ctx b env) ms);
          raw_char b ' ';
          term ctx b r env)
  | EIndexed (_, op, n, None, a) ->
      el b "span" (Some "o pre") (fun b ->
          el b "span" (Some "op") (fun b ->
              esc b op;
              el b "sub" None (fun b -> term ctx b n env));
          raw b nbsp;
          term ctx b a env)
  | EIndexed (_, op, n, Some l, r) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          term ctx b l env;
          raw b nbsp;
          el b "span" (Some "op wide") (fun b ->
              esc b op;
              el b "sub" None (fun b -> term ctx b n env));
          raw_char b ' ';
          term ctx b r env)
  | EWp (_, e0, at, post) ->
      el_a b "span" (Some "c app rq-wp") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "rq-wp-head") (fun b ->
              kw b "WP";
              draw_wp_at ctx b at env);
          el b "span" (Some "args") (fun b ->
              el b "span" (Some "arg") (fun b -> term ctx b e0 env);
              raw_char b ' ';
              el b "span" (Some "arg") (fun b -> draw_post ctx b post env)))
  | ETriple (_, pre, e0, at, bs, ret, q) ->
      let env_q = binders_env ctx bs env in
      el_a b "span" (Some "c app rq-triple") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args") (fun b ->
              el b "span" (Some "arg") (fun b ->
                  el_raw b "span" (Some "op rq-triple-brace") "⦃";
                  term ctx b pre env;
                  el_raw b "span" (Some "op rq-triple-brace") "⦄");
              raw_char b ' ';
              el b "span" (Some "arg") (fun b ->
                  term ctx b e0 env;
                  draw_wp_at ctx b at env);
              raw_char b ' ';
              el b "span" (Some "arg") (fun b ->
                  el_raw b "span" (Some "op rq-triple-brace") "⦃";
                  if bs <> [] then (
                    binders_ ctx b bs env;
                    el_raw b "span" (Some "sep") ".";
                    raw_char b ' ');
                  kw b "RET";
                  raw_char b ' ';
                  term ctx b ret env_q;
                  el_raw b "span" (Some "sep") ";";
                  raw_char b ' ';
                  term ctx b q env_q;
                  el_raw b "span" (Some "op rq-triple-brace") "⦄")))
  | EBigOp (_, op, kind, bb, cs, body) ->
      let vs =
        (match bb.bb_key with Some n when n.n_text <> "_" -> [ n.n_text ] | _ -> [])
        @ List.filter_map (fun n -> if n.n_text = "_" then None else Some n.n_text) bb.bb_vals
      in
      let env1 = vs @ env in
      let title = Printf.sprintf "[%s %s]" op kind in
      el_a b "span" (Some "c quant rq-big") [ ("data-d", "args") ] (fun b ->
          el_a b "span" (Some "q rq-big-op") [ ("title", title) ] (fun b ->
              esc b op;
              el b "sub" (Some "rq-big-binds") (fun b ->
                  Option.iter
                    (fun k ->
                      var_def b k.n_text;
                      el_raw b "span" (Some "op") "↦")
                    bb.bb_key;
                  sep_defs b bb.bb_vals;
                  el_raw b "span" (Some "op") "∈";
                  sep_terms ctx b cs env));
          el b "span" (Some "args") (fun b ->
              el b "span" (Some "arg") (fun b -> term ctx b body env1)))
  | EBigAll (_, op, e0) ->
      el b "span" (Some "o pre rq-big") (fun b ->
          el_a b "span" (Some "q rq-big-op") [ ("title", op) ] (fun b -> esc b op);
          raw b nbsp;
          term ctx b e0 env)
  | EEval (_, ws, e0) ->
      kw b "Eval";
      raw_char b ' ';
      el b "span" (Some "rq-mods") (fun b -> esc_words b ws);
      raw_char b ' ';
      kw b "in";
      raw_char b ' ';
      term ctx b e0 env

and step_later ctx b n env =
  match n with
  | None -> raw b "▷"
  | Some e ->
      raw b "▷";
      el b "sup" (Some "rq-mask") (fun b -> term ctx b e env)

and draw_update ctx b ms arrow tail env =
  let emit_tail () = Option.iter (fun f -> f b) tail in
  match ms with
  | [] ->
      el b "span" (Some "op wide rq-upd-arrow") (fun b ->
          esc b arrow;
          emit_tail ())
  | [ e ] ->
      el b "span" (Some "op wide rq-upd-arrow") (fun b ->
          esc b arrow;
          el b "sup" (Some "rq-mask") (fun b -> term ctx b e env);
          emit_tail ())
  | [ e1; e2 ] ->
      el b "span" (Some "op wide rq-upd-arrow") (fun b ->
          el b "sup" (Some "rq-mask") (fun b -> term ctx b e1 env);
          esc b arrow;
          el b "sup" (Some "rq-mask") (fun b -> term ctx b e2 env);
          emit_tail ())
  | _ -> ()

and pointsto_mod ctx b env = function
  | PmName g -> el b "sub" (Some "rq-mask") (fun b -> term ctx b g env)
  | PmOwn q -> el b "sup" (Some "rq-mask") (fun b -> term ctx b q env)
  | PmDfrac d -> el b "sup" (Some "rq-mask") (fun b -> term ctx b d env)
  | PmPersistent -> el_raw b "sup" (Some "rq-mask") "□"

and draw_wp_at ctx b at env =
  match at with
  | WpNone -> ()
  | WpAt (s, m) ->
      el b "sub" (Some "rq-mask") (fun b ->
          Option.iter
            (fun se ->
              term ctx b se env;
              raw b "; ")
            s;
          term ctx b m env)

and draw_post ctx b post env =
  match post.wp_binder with
  | None ->
      el b "span" (Some "rq-post") (fun b ->
          el_raw b "span" (Some "op") "{";
          term ctx b post.wp_body env;
          el_raw b "span" (Some "op") "}")
  | Some x ->
      let env1 = if x.n_text = "_" then env else x.n_text :: env in
      el b "span" (Some "rq-post") (fun b ->
          el_raw b "span" (Some "op") "{";
          var_def b x.n_text;
          el_raw b "span" (Some "sep") ".";
          raw_char b ' ';
          term ctx b post.wp_body env1;
          el_raw b "span" (Some "op") "}")

and sep_defs b = function
  | [] -> ()
  | [ n ] -> var_def b n.n_text
  | n :: rest ->
      var_def b n.n_text;
      raw_char b ';';
      sep_defs b rest

and sep_terms ctx b cs env =
  match cs with
  | [] -> ()
  | [ c ] -> term ctx b c env
  | c :: rest ->
      term ctx b c env;
      raw_char b ';';
      sep_terms ctx b rest env

and bar_items ctx b ps env =
  match ps with
  | [] -> ()
  | [ p ] -> term ctx b p env
  | p :: rest ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          term ctx b p env;
          raw_char b ' ';
          el_a b "span" (Some "op wide bar") [ ("title", "|") ] (fun b -> raw_char b '|');
          raw_char b ' ';
          bar_items ctx b rest env)

and items ctx b es env =
  match es with
  | [] -> ()
  | [ e ] -> el b "span" (Some "arg") (fun b -> term ctx b e env)
  | e :: rest ->
      el b "span" (Some "arg") (fun b -> term ctx b e env);
      raw_char b ' ';
      items ctx b rest env

and sep_items ctx b es env sep =
  match es with
  | [] -> ()
  | [ e ] -> el b "span" (Some "arg") (fun b -> term ctx b e env)
  | e :: rest ->
      el b "span" (Some "arg") (fun b ->
          term ctx b e env;
          el_text b "span" (Some "sep") sep);
      raw_char b ' ';
      sep_items ctx b rest env sep

and rec_fields ctx b fs env =
  match fs with
  | [] -> ()
  | f :: rest ->
      (match f with
      | RFld (_, n, e) ->
          el b "span" (Some "arg") (fun b ->
              name_ref ctx b n [] `Arg;
              raw b nbsp;
              defeq b;
              raw_char b ' ';
              term ctx b e env;
              if rest <> [] then el_raw b "span" (Some "sep") ";")
      | RFldB (_, n, bs, e) ->
          let env1 = binders_env ctx bs env in
          el b "span" (Some "arg") (fun b ->
              name_ref ctx b n [] `Arg;
              binders_ ctx b bs env;
              raw b nbsp;
              defeq b;
              raw_char b ' ';
              term ctx b e env1;
              if rest <> [] then el_raw b "span" (Some "sep") ";"));
      if rest <> [] then raw_char b ' ';
      rec_fields ctx b rest env

and head_ ctx b f env =
  match f with EId (_, x) -> name_ref ctx b x env `Head | _ -> term ctx b f env

and quant ctx b sym title bs sep body env =
  let env1 = binders_env ctx bs env in
  el_a b "span" (Some "c quant") [ ("data-d", "args") ] (fun b ->
      el_a b "span" (Some "q") [ ("title", title) ] (fun b -> esc b sym);
      el b "span" (Some "args") (fun b ->
          quant_binders ctx b bs env sep;
          el b "span" (Some "arg") (fun b -> term ctx b body env1)))

and quant_binders ctx b bs env sep =
  match bs with
  | [] -> ()
  | b0 :: rest ->
      el b "span" (Some "arg") (fun b ->
          binder_ ctx b b0 env;
          if rest = [] then el_text b "span" (Some "sep qsep") sep);
      raw_char b ' ';
      quant_binders ctx b rest env sep

and opt_type ctx b ty env =
  match ty with
  | None -> ()
  | Some t ->
      raw b nbsp;
      el_a b "span" (Some "op wide colon") [ ("title", ":") ] (fun b -> raw_char b ':');
      raw_char b ' ';
      term ctx b t env

and draw_split_binder ctx b sb env =
  match sb with
  | SBInst (_, open_d, e) ->
      let cls = if open_d = "(" then "paren binder rq-inst" else "braces binder rq-inst" in
      el_a b "span" (Some cls) [ ("title", "an instance of this class") ] (fun b -> term ctx b e env)
  | SBOrig b0 -> binder_ ctx b b0 env

and binder_ ctx b b0 env =
  match b0.b_kind with
  | BPattern p ->
      el_raw b "span" (Some "tick") "'";
      term ctx b p env
  | BGen _ -> (
      match split_gen [ b0 ] with
      | [] -> ()
      | first :: rest ->
          draw_split_binder ctx b first env;
          List.iter
            (fun sb ->
              raw_char b ' ';
              draw_split_binder ctx b sb env)
            rest)
  | BStruct ->
      el b "span" (Some "struct") (fun b ->
          raw_char b '{';
          kw b "struct";
          raw_char b ' ';
          esc b (List.hd b0.b_names).n_text;
          raw_char b '}')
  | BBrace ->
      el b "span" (Some "braces binder") (fun b ->
          vars b b0.b_names;
          opt_type ctx b b0.b_ty env)
  | BBare ->
      vars b b0.b_names;
      opt_type ctx b b0.b_ty env
  | BParen -> (
      match b0.b_ty with
      | None -> vars b b0.b_names
      | Some _ ->
          el b "span" (Some "paren binder") (fun b ->
              vars b b0.b_names;
              opt_type ctx b b0.b_ty env))

and binders_ ctx b bs0 env =
  List.iter
    (fun sb ->
      raw_char b ' ';
      draw_split_binder ctx b sb env)
    (split_gen bs0)

and sig_items ctx b bs0 ty env =
  let rec go = function
    | [] -> (
        match ty with
        | None -> ()
        | Some t ->
            el b "span" (Some "arg") (fun b ->
                el_a b "span" (Some "op wide colon") [ ("title", ":") ] (fun b -> raw_char b ':');
                raw_char b ' ';
                term ctx b t env))
    | sb :: rest ->
        el b "span" (Some "arg") (fun b -> draw_split_binder ctx b sb env);
        if rest <> [] || ty <> None then (
          raw_char b ' ';
          go rest)
  in
  go (split_gen bs0)

and sig_ ctx b kw_s cls n bs ty env =
  if bs = [] && ty = None then (
    kw b kw_s;
    raw_char b ' ';
    el_text b "span" (Some cls) n)
  else
    el_a b "span" (Some "c sig") [ ("data-d", "args") ] (fun b ->
        kw b kw_s;
        raw_char b ' ';
        el_text b "span" (Some cls) n;
        el b "span" (Some "args binders") (fun b -> sig_items ctx b bs ty env))

and draw_lhs ctx b lhs env =
  match lhs with
  | LetName (n, bs) ->
      var_def b n.n_text;
      binders_ ctx b bs env
  | LetTuple ns ->
      el b "span" (Some "c tuple") (fun b ->
          el b "span" (Some "args") (fun b ->
              let rec go = function
                | [] -> ()
                | [ n ] -> el b "span" (Some "arg") (fun b -> var_def b n.n_text)
                | n :: rest ->
                    el b "span" (Some "arg") (fun b ->
                        var_def b n.n_text;
                        el_raw b "span" (Some "sep") ",");
                    raw_char b ' ';
                    go rest
              in
              go ns))

and scrutinees ctx b ss env =
  let draw_one = function
    | ScrutAs (e, n) ->
        term ctx b e env;
        raw_char b ' ';
        kw b "as";
        raw_char b ' ';
        var_def b n.n_text
    | ScrutExpr e -> term ctx b e env
  in
  match ss with
  | [] -> ()
  | [ s ] -> draw_one s
  | s :: rest ->
      draw_one s;
      el_raw b "span" (Some "sep") ",";
      raw_char b ' ';
      scrutinees ctx b rest env

and inline_branches ctx b brs env =
  match brs with
  | [] -> ()
  | br :: rest ->
      let env1 = alts_vars ctx br.br_alts @ env in
      el b "span" (Some "branch") (fun b ->
          alts_ ctx b br.br_alts env1;
          raw b nbsp;
          el_a b "span" (Some "op wide") [ ("title", "=>") ] (fun b -> raw b "⇒");
          raw_char b ' ';
          term ctx b br.br_rhs env1);
      if rest <> [] then (
        raw_char b ' ';
        el_raw b "span" (Some "op wide bar") "|";
        raw_char b ' ';
        inline_branches ctx b rest env)

and alts_ ctx b alts env =
  match alts with
  | [] -> ()
  | [ a ] -> pats_ ctx b a env
  | a :: rest ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          pats_ ctx b a env;
          raw_char b ' ';
          el_a b "span" (Some "op wide bar") [ ("title", "|") ] (fun b -> raw_char b '|');
          raw_char b ' ';
          alts_ ctx b rest env)

and pats_ ctx b ps env =
  match ps with
  | [] -> ()
  | [ p ] -> term ctx b p env
  | p :: rest ->
      term ctx b p env;
      el_raw b "span" (Some "sep") ",";
      raw_char b ' ';
      pats_ ctx b rest env

(* ── Block terms ───────────────────────────────────────────────────────── *)

let rec is_block = function
  | EMatch _ | EIf _ | ELet _ | ELetStar _ | ELetPat _ | ELetQ _ | ELetFix _ | EFix _
  | EIrFn _ | EIrBlk _ ->
      true
  | EIrList (_, _ :: _) -> true
  | EFun (_, _, body) | EForall (_, _, body) | EExists (_, _, body) -> is_block body
  | EApp (_, EParen (_, f), _) when is_block f -> true
  | EApp (_, _, args) -> List.exists is_block args
  | ETuple (_, es) -> List.exists is_block es
  | EBin (_, _, l, r) -> is_block l || is_block r
  | EParen (_, e) | EScope (_, e, _) -> is_block e
  | _ -> false

type if_case = IfCond of expr * expr | IfElse of expr

let rec if_chain = function
  | EIf (_, c, t, (EIf _ as e)) -> IfCond (c, t) :: if_chain e
  | EIf (_, c, t, e) -> [ IfCond (c, t); IfElse e ]
  | _ -> []

let rec blk ctx b e env =
  if is_block e then blk_ ctx b e env
  else (
    let sp = expr_span e in
    el b "div" (Some "goal") (fun b -> term ctx b e env);
    !Draw_hooks.aside_after_ref ctx b sp.hi)

and blk_ ctx b e env =
  match e with
  | EParen (_, e0) | EScope (_, e0, _) -> blk ctx b e0 env
  | EIrFn (_, lk, nm, ps, ret, bs) ->
      !Draw_hooks.draw_ir_fn_block_ref ctx b lk nm ps ret bs env
  | EIrBlk (_, bl) -> !Draw_hooks.draw_ir_blk_standalone_ref ctx b bl env
  | EIrList (_, is) -> !Draw_hooks.draw_ir_list_block_ref ctx b is env
  | EBin (_, op, l, r) ->
      el b "div" (Some "rq-equation") (fun b ->
          blk ctx b l env;
          el b "div" (Some "goal") (fun b -> op_ b op);
          blk ctx b r env)
  | ETuple (_, es) ->
      el b "div" (Some "rq-tuple") (fun b ->
          List.iter (fun x -> el b "div" (Some "tuple-part") (fun b -> blk ctx b x env)) es)
  | EApp (_, EParen (_, f), args) when is_block f ->
      el b "div" (Some "rq-app") (fun b ->
          el b "div" (Some "rq-tuple") (fun b -> blk ctx b f env);
          el b "div" (Some "goal app-tail") (fun b -> items ctx b args env))
  | EApp (_, f, args) ->
      let rec split_first_block acc = function
        | [] -> (List.rev acc, [])
        | a :: rest when is_block a -> (List.rev acc, a :: rest)
        | a :: rest -> split_first_block (a :: acc) rest
      in
      let inl, rest = split_first_block [] args in
      el b "div" (Some "rq-app") (fun b ->
          el b "div" (Some "goal app-head") (fun b ->
              if inl = [] then head_ ctx b f env
              else
                el_a b "span" (Some "c app") [ ("data-d", "args") ] (fun b ->
                    head_ ctx b f env;
                    el b "span" (Some "args") (fun b -> items ctx b inl env)));
          el b "div" (Some "app-args") (fun b ->
              List.iter (fun a -> el b "div" (Some "app-arg") (fun b -> blk ctx b a env)) rest))
  | EMatch (_, ss, _, brs) ->
      el b "div" (Some "rq-match") (fun b ->
          el b "div" (Some "goal match-head") (fun b ->
              kw b "match";
              raw_char b ' ';
              scrutinees ctx b ss env;
              raw_char b ' ';
              kw b "with");
          el b "div" (Some "cases match") (fun b -> branch_rows ctx b brs env))
  | EIf _ ->
      let cases = if_chain e in
      el b "div" (Some "cases stack rq-if") (fun b ->
          List.iter
            (function
              | IfCond (c, t) ->
                  el b "div" (Some "case") (fun b ->
                      el b "div" (Some "cond") (fun b ->
                          el b "div" (Some "goals") (fun b -> blk ctx b c env));
                      el_raw b "div" (Some "arrow") "→";
                      el b "div" (Some "then") (fun b ->
                          el b "div" (Some "goals") (fun b -> blk ctx b t env)))
              | IfElse e0 ->
                  el b "div" (Some "case plain") (fun b ->
                      el b "div" (Some "cond") (fun b -> kw b "else");
                      el_empty b "div" (Some "arrow");
                      el b "div" (Some "then") (fun b ->
                          el b "div" (Some "goals") (fun b -> blk ctx b e0 env))))
            cases)
  | ELet (_, lhs, ty, v, body) ->
      let env1 = lhs_names lhs @ env in
      let_block ctx b
        (fun b ->
          kw b "let";
          raw_char b ' ';
          draw_lhs ctx b lhs env;
          opt_type ctx b ty env)
        v env body env1
  | ELetStar (_, n, v, body) ->
      let_block ctx b
        (fun b ->
          kw b "let*";
          raw_char b ' ';
          var_def b n.n_text)
        v env body (n.n_text :: env)
  | ELetPat (_, pat, v, body) ->
      let env1 = alts_vars ctx [ [ pat ] ] @ env in
      let_block ctx b
        (fun b ->
          kw b "let";
          raw_char b ' ';
          el_raw b "span" (Some "tick") "'";
          term ctx b pat env1)
        v env body env1
  | ELetQ (_, pat, v, body) ->
      let env1 = alts_vars ctx [ [ pat ] ] @ env in
      let_block ctx b
        (fun b ->
          kw b "let?";
          raw_char b ' ';
          term ctx b pat env1)
        v env body env1
  | ELetFix (_, f, bs, ty, v, body) ->
      let env_v = binders_env ctx bs (f.n_text :: env) in
      let_block ctx b
        (fun b ->
          kw b "let fix";
          raw_char b ' ';
          var_def b f.n_text;
          binders_ ctx b bs env;
          opt_type ctx b ty env_v)
        v env_v body (f.n_text :: env)
  | EFix (_, f, bs, ty, body) ->
      let env_b = binders_env ctx bs (f.n_text :: env) in
      el b "div" (Some "rq-fun") (fun b ->
          el b "div" (Some "goal fun-head") (fun b ->
              kw b "fix";
              raw_char b ' ';
              var_def b f.n_text;
              binders_ ctx b bs env;
              opt_type ctx b ty env_b;
              raw b nbsp;
              defeq b);
          el b "div" (Some "fun-body") (fun b -> blk ctx b body env_b))
  | EFun (_, bs, body) -> quant_block ctx b "λ" bs "⇒" body env
  | EForall (_, bs, body) -> quant_block ctx b "∀" bs "," body env
  | EExists (_, bs, body) -> quant_block ctx b "∃" bs "," body env
  | _ -> blk ctx b e env

and quant_block ctx b sym bs sep body env =
  let env1 = binders_env ctx bs env in
  el b "div" (Some "rq-fun") (fun b ->
      el b "div" (Some "goal fun-head") (fun b ->
          el_text b "span" (Some "q") sym;
          binders_ ctx b bs env;
          raw_char b ' ';
          raw b nbsp;
          el_text b "span" (Some "sep qsep") sep);
      el b "div" (Some "fun-body") (fun b -> blk ctx b body env1))

and let_block ctx b head_fn v env_v body env_b =
  el b "div" (Some "rq-let") (fun b ->
      if is_block v then (
        el b "div" (Some "goal let-head") (fun b ->
            head_fn b;
            raw b nbsp;
            defeq b);
        el b "div" (Some "let-value") (fun b -> blk ctx b v env_v);
        el b "div" (Some "goal let-in") (fun b -> kw b "in"))
      else
        el b "div" (Some "goal let-head") (fun b ->
            head_fn b;
            raw b nbsp;
            defeq b;
            raw_char b ' ';
            term ctx b v env_v;
            raw_char b ' ';
            kw b "in");
      el b "div" (Some "let-body") (fun b -> blk ctx b body env_b))

and branch_rows ctx b brs env =
  List.iter
    (fun br ->
      let p0 = List.hd (List.hd br.br_alts) in
      let env1 = alts_vars ctx br.br_alts @ env in
      !Draw_hooks.notes_before_ref ctx b (expr_span p0).lo;
      el b "div" (Some "case") (fun b ->
          el b "div" (Some "cond") (fun b ->
              el b "div" (Some "goals") (fun b ->
                  el b "div" (Some "goal") (fun b -> alts_ ctx b br.br_alts env1)));
          el_a b "div" (Some "arrow") [ ("title", "=>") ] (fun b -> raw b "⇒");
          el b "div" (Some "then") (fun b ->
              el b "div" (Some "goals") (fun b -> blk ctx b br.br_rhs env1))))
    brs

(* ── Statements as inference rules & vernacular items ──────────────────── *)

let rec rule_parts = function
  | EForall (_, bs0, b) ->
      let bs1, ps, c = rule_parts b in
      (bs0 @ bs1, ps, c)
  | EBin (_, ("->" | "→"), l, r) ->
      let bs, ps, c = rule_parts r in
      (bs, l :: ps, c)
  | EParen (_, (EForall _ as e)) -> rule_parts e
  | c -> ([], [], c)

let draw_rule ctx b label_fn bs0 ty env0 =
  let bs1, ps, c = rule_parts ty in
  let bs = bs0 @ bs1 in
  let env = binders_env ctx bs env0 in
  el b "div" (Some "rule") (fun b ->
      if bs <> [] then
        el b "div" (Some "rule-vars") (fun b ->
            el_a b "span" (Some "q") [ ("title", "forall") ] (fun b -> raw b "∀");
            binders_ ctx b bs env0);
      if ps = [] then
        el b "div" (Some "rule-concl alone") (fun b ->
            blk ctx b c env;
            label_fn b)
      else (
        el b "div" (Some "premises") (fun b ->
            List.iter
              (fun p ->
                let sp = expr_span p in
                !Draw_hooks.notes_before_ref ctx b sp.lo;
                blk ctx b p env;
                !Draw_hooks.aside_after_ref ctx b sp.hi)
              ps);
        el b "div" (Some "rule-line") label_fn;
        el b "div" (Some "rule-concl") (fun b -> blk ctx b c env)))

let line_link ctx b off =
  match ctx.file with
  | None -> ()
  | Some file ->
      let l = line_of ctx off in
      let href = Printf.sprintf "%s%s#L%d" github_blob file l in
      el_a b "a" (Some "ln") [ ("href", href); ("title", "source line") ] (fun b -> esc_int b l)

let is_dir_keyword = function
  | "From" | "Require" | "Import" | "Export" | "Open" | "Close" | "Scope" | "Set" | "Unset"
  | "Arguments" | "Hint" | "Local" | "Global" | "Declare" | "Delimit" | "Bind" | "Implicit"
  | "Types" | "Generalizable" | "Create" | "HintDb" | "Opaque" | "Transparent" | "Typeclasses"
  | "Coercion" ->
      true
  | _ -> false

let rec dir_words b = function
  | [] -> ()
  | w :: rest ->
      if is_dir_keyword w then kw b w else el_text b "span" (Some "module") w;
      if rest <> [] then raw_char b ' ';
      dir_words b rest

let draw_dir ctx b (sp : span) ws =
  el b "div" (Some "rq-dir") (fun b -> dir_words b ws);
  !Draw_hooks.aside_after_ref ctx b sp.hi

let cmd_words toks =
  let rec group = function
    | [] -> []
    | t :: rest ->
        let rec cont hi acc = function
          | t2 :: r when t2.lo = hi -> cont t2.hi (t2 :: acc) r
          | r -> (List.rev acc, r)
        in
        let w, rem = cont t.hi [ t ] rest in
        w :: group rem
  in
  group toks

let draw_cmd_tok ctx b tok =
  match tok.kind with
  | Id (("From" | "Include") as x) -> kw b x
  | Id x -> name_ref ctx b x [] `Arg
  | Num _ -> el_text b "span" (Some "n") (src_text ctx { lo = tok.lo; hi = tok.hi })
  | Str _ -> el_text b "span" (Some "s rq-code") (src_text ctx { lo = tok.lo; hi = tok.hi })
  | Sym "=>" -> el_a b "span" (Some "op wide") [ ("title", "=>") ] (fun b -> raw b "⇒")
  | _ -> el_text b "span" (Some "op") (src_text ctx { lo = tok.lo; hi = tok.hi })

let draw_cmd_word ctx b w =
  match w with
  | t0 :: _ when (match t0.kind with Sym s -> String.starts_with ~prefix:"-" s | _ -> false) ->
      let last_t = List.nth w (List.length w - 1) in
      el_text b "span" (Some "rq-flag") (src_text ctx { lo = t0.lo; hi = last_t.hi })
  | _ -> List.iter (draw_cmd_tok ctx b) w

let rec draw_cmd_args ctx b = function
  | [] -> ()
  | [ w ] -> el b "span" (Some "arg") (fun b -> draw_cmd_word ctx b w)
  | w :: rest ->
      el b "span" (Some "arg") (fun b -> draw_cmd_word ctx b w);
      raw_char b ' ';
      draw_cmd_args ctx b rest

let draw_raw ctx b (sp : span) =
  let s = src_text ctx sp in
  el b "pre" (Some "rq-raw") (fun b ->
      line_link ctx b sp.lo;
      esc b s);
  !Draw_hooks.notes_before_ref ctx b sp.hi

let rec param_names ctx b = function
  | [] -> ()
  | n :: rest ->
      let id = anchor ctx n.n_text in
      el_a b "span" (Some "f def") [ ("id", id) ] (fun b -> esc b n.n_text);
      if rest <> [] then (
        raw_char b ' ';
        param_names ctx b rest)

let draw_ctor_row ctx b env c =
  !Draw_hooks.notes_rows_ref ctx b c.c_span.lo 4;
  let id = anchor ctx c.c_name in
  let aside = !Draw_hooks.aside_text_ref ctx c.c_span.hi in
  el_a b "tr" None [ ("id", id) ] (fun b ->
      el_raw b "td" (Some "bar") "|";
      el b "td" (Some "ctor") (fun b -> el_text b "span" (Some "a def") c.c_name);
      el b "td" (Some "ctor-args") (fun b ->
          el b "div" (Some "goal") (fun b ->
              el_a b "span" (Some "c sig") [ ("data-d", "args") ] (fun b ->
                  el b "span" (Some "args binders") (fun b ->
                      sig_items ctx b c.c_binders c.c_ty env))));
      el b "td" (Some "ctor-aside") (fun b ->
          Option.iter
            (fun s -> el b "span" (Some "aside") (fun b -> !Draw_hooks.draw_prose_inline_ref ctx b s))
            aside))

let draw_ctor_rule ctx b env c =
  !Draw_hooks.notes_before_ref ctx b c.c_span.lo;
  let id = anchor ctx c.c_name in
  el_a b "div" (Some "clause rq-rule") [ ("id", id) ] (fun b ->
      match c.c_ty with
      | None ->
          el b "div" (Some "rule-concl alone") (fun b ->
              el b "div" (Some "goal") (fun b ->
                  el_text b "span" (Some "a def") c.c_name;
                  binders_ ctx b c.c_binders env))
      | Some ty ->
          draw_rule ctx b
            (fun b -> el b "span" (Some "rule-name") (fun b -> el_text b "span" (Some "a def") c.c_name))
            c.c_binders ty env);
  !Draw_hooks.aside_after_ref ctx b c.c_span.hi

let draw_ind_body ctx b ib =
  let id = anchor ctx ib.ib_name.n_text in
  let env = binders_env ctx ib.ib_binders [] in
  let has_premises =
    List.exists
      (fun c ->
        match c.c_ty with
        | Some ct -> (
            match rule_parts ct with _, _ :: _, _ -> true | _ -> false)
        | None -> false)
      ib.ib_ctors
  in
  el_a b "div" (Some "clause rq-ind") [ ("id", id) ] (fun b ->
      el b "div" (Some "head rq-ind-head") (fun b ->
          line_link ctx b ib.ib_name.n_span.lo;
          sig_ ctx b "Inductive" "ty def" ib.ib_name.n_text ib.ib_binders ib.ib_ty env;
          raw b nbsp;
          defeq b);
      if has_premises then
        el b "div" (Some "rules") (fun b -> List.iter (draw_ctor_rule ctx b env) ib.ib_ctors)
      else
        el b "table" (Some "rq-ctors") (fun b ->
            el b "tbody" None (fun b -> List.iter (draw_ctor_row ctx b env) ib.ib_ctors)))

let draw_field_row ctx b env f =
  !Draw_hooks.notes_rows_ref ctx b f.fd_span.lo 3;
  let id = anchor ctx f.fd_name in
  let aside = !Draw_hooks.aside_text_ref ctx f.fd_span.hi in
  el_a b "tr" None [ ("id", id) ] (fun b ->
      el b "td" (Some "field-name") (fun b -> el_text b "span" (Some "f def") f.fd_name);
      el b "td" (Some "field-type") (fun b ->
          el b "div" (Some "goal") (fun b ->
              el_a b "span" (Some "c sig") [ ("data-d", "args") ] (fun b ->
                  el b "span" (Some "args binders") (fun b ->
                      sig_items ctx b f.fd_binders f.fd_ty env));
              Option.iter
                (fun d ->
                  raw b nbsp;
                  defeq b;
                  raw_char b ' ';
                  term ctx b d env)
                f.fd_def));
      el b "td" (Some "field-aside") (fun b ->
          Option.iter
            (fun s -> el b "span" (Some "aside") (fun b -> !Draw_hooks.draw_prose_inline_ref ctx b s))
            aside))

let module_arg ctx b a =
  raw_char b ' ';
  name_ref ctx b a [] `Arg

type item_run =
  | RunDirs of (span * string list) list
  | RunItem of item

let group_runs items =
  let rec go acc = function
    | [] -> List.rev acc
    | ISent (VDir (sp, ws)) :: rest ->
        let rec take_dirs dacc = function
          | ISent (VDir (sp2, ws2)) :: r -> take_dirs ((sp2, ws2) :: dacc) r
          | r -> (List.rev dacc, r)
        in
        let ds, rem = take_dirs [ (sp, ws) ] rest in
        go (RunDirs ds :: acc) rem
    | i :: rest -> go (RunItem i :: acc) rest
  in
  go [] items

let item_from = function
  | IProved (s, _) | IBlock (s, _, _) | ISent s -> (vernac_span s).lo

let rec rocq_items ctx b items =
  List.iter
    (function
      | RunDirs ((sp0, _) :: _ as ds) ->
          !Draw_hooks.notes_before_ref ctx b sp0.lo;
          el b "div" (Some "rq-dirs") (fun b ->
              List.iter (fun (sp, ws) -> draw_dir ctx b sp ws) ds)
      | RunDirs [] -> ()
      | RunItem i ->
          !Draw_hooks.notes_before_ref ctx b (item_from i);
          draw_item ctx b i)
    (group_runs items)

and draw_item ctx b = function
  | IBlock (VModule (sp, kind, n, bs, open_), body, end_opt) ->
      let mod0 = ctx.mod_path in
      let q = qualify mod0 n.n_text in
      let mod1 = if kind = ModSection then mod0 else mod0 @ [ n.n_text ] in
      let kws = Draw_prose.module_kw_str kind in
      let env = binders_env ctx bs [] in
      el_a b "section" (Some "rq-module") [ ("id", q) ] (fun b ->
          el b "div" (Some "clause rq-module-head") (fun b ->
              el b "div" (Some "head") (fun b ->
                  line_link ctx b sp.lo;
                  kw b kws;
                  raw_char b ' ';
                  el_text b "span" (Some "module-name") n.n_text;
                  binders_ ctx b bs [];
                  (match open_ with
                  | ModOpenSig (sig_n, args) ->
                      raw b nbsp;
                      el_raw b "span" (Some "op wide colon") ":";
                      raw_char b ' ';
                      name_ref ctx b sig_n env `Arg;
                      List.iter (module_arg ctx b) args
                  | _ -> ())));
          ctx.mod_path <- mod1;
          Fun.protect
            ~finally:(fun () -> ctx.mod_path <- mod0)
            (fun () -> el b "div" (Some "rq-module-body") (fun b -> rocq_items ctx b body));
          match end_opt with
          | Some (VEnd (esp, _)) -> !Draw_hooks.notes_before_ref ctx b esp.hi
          | _ -> ())
  | IBlock (s, _, _) -> draw_sent ctx b s
  | IProved (s, { pf_steps = []; pf_end = None }) -> draw_sent ctx b s
  | IProved (s, pf) ->
      draw_sent ctx b s;
      !Draw_hooks.draw_proof_ref ctx b s pf
  | ISent s -> draw_sent ctx b s

and draw_sent ctx b = function
  | VProofStart _ -> ()
  | VInd (_, _, bodies) -> List.iter (draw_ind_body ctx b) bodies
  | VRec (sp, k, n, bs, sort, ctor, fs) ->
      let id = anchor ctx n.n_text in
      let env = binders_env ctx bs [] in
      el_a b "div" (Some "clause rq-rec") [ ("id", id) ] (fun b ->
          el b "div" (Some "head") (fun b ->
              line_link ctx b sp.lo;
              sig_ ctx b k "ty def" n.n_text bs sort env;
              match ctor with
              | RecCtorNamed c ->
                  raw b nbsp;
                  defeq b;
                  raw_char b ' ';
                  let cid = anchor ctx c.n_text in
                  el_a b "span" (Some "a def") [ ("id", cid) ] (fun b -> esc b c.n_text)
              | RecCtorNone | RecCtorSingleton -> ());
          el b "table" (Some "rq-fields") (fun b ->
              el b "tbody" None (fun b -> List.iter (draw_field_row ctx b env) fs)));
      !Draw_hooks.notes_before_ref ctx b sp.hi
  | VMutual (_, d :: ds) ->
      draw_sent ctx b (VDef d);
      List.iter
        (fun d2 ->
          !Draw_hooks.notes_before_ref ctx b d2.d_span.lo;
          draw_sent ctx b (VDef d2))
        ds
  | VMutual (_, []) -> ()
  | VDef { d_span; d_kw = "Example"; d_name; d_binders; d_ty = Some ty; d_body = None } ->
      draw_sent ctx b (VThm (d_span, "Example", Some d_name, d_binders, ty))
  | VDef d ->
      let id = anchor ctx d.d_name.n_text in
      let env = binders_env ctx d.d_binders [] in
      el_a b "div" (Some "clause rq-def") [ ("id", id) ] (fun b ->
          el b "div" (Some "head") (fun b ->
              line_link ctx b d.d_span.lo;
              sig_ ctx b d.d_kw "f def" d.d_name.n_text d.d_binders d.d_ty env;
              if d.d_body <> None then (
                raw b nbsp;
                defeq b));
          Option.iter
            (fun body -> el b "div" (Some "rq-body") (fun b -> blk ctx b body env))
            d.d_body);
      !Draw_hooks.notes_before_ref ctx b d.d_span.hi
  | VTacDef (sp, n, args, body) ->
      let id = anchor ctx n.n_text in
      let env = List.map (fun a -> a.n_text) args in
      el_a b "div" (Some "clause rq-ltac") [ ("id", id) ] (fun b ->
          el b "div" (Some "head") (fun b ->
              line_link ctx b sp.lo;
              kw b "Ltac";
              raw_char b ' ';
              el_text b "span" (Some "f def") n.n_text;
              raw_char b ' ';
              vars b args;
              raw b nbsp;
              defeq b);
          el b "div" (Some "rq-body") (fun b -> !Draw_hooks.draw_tactic_block_ref ctx b body env));
      !Draw_hooks.notes_before_ref ctx b sp.hi
  | VThm (sp, k, name_opt, bs, ty) ->
      let n_text, attrs =
        match name_opt with
        | Some n -> (n.n_text, [ ("id", anchor ctx n.n_text) ])
        | None -> ("", [])
      in
      el_a b "div" (Some "clause rq-thm") attrs (fun b ->
          el b "div" (Some "rq-thm-head") (fun b ->
              line_link ctx b sp.lo;
              kw b k;
              raw_char b ' ';
              el_text b "span" (Some "lem def") n_text);
          draw_rule ctx b (fun _ -> ()) bs ty []);
      !Draw_hooks.notes_before_ref ctx b sp.hi
  | VDecl (sp, k, gs) when is_axiom_kw k ->
      List.iter
        (function
          | DeclTyped (n0 :: _, ty) ->
              let id = anchor ctx n0.n_text in
              el_a b "div" (Some "clause rq-thm rq-axiom") [ ("id", id) ] (fun b ->
                  el b "div" (Some "rq-thm-head") (fun b ->
                      line_link ctx b sp.lo;
                      kw b k;
                      raw_char b ' ';
                      el_text b "span" (Some "lem def") n0.n_text);
                  draw_rule ctx b (fun _ -> ()) [] ty [])
          | _ -> ())
        gs;
      !Draw_hooks.notes_before_ref ctx b sp.hi
  | VDecl (sp, k, gs) ->
      let draw_param_items () =
        match gs with
        | [ DeclTyped (ns, ty) ] ->
            kw b k;
            raw_char b ' ';
            param_names ctx b ns;
            opt_type ctx b (Some ty) []
        | [ DeclBinders bs0 ] ->
            let sbs = split_gen bs0 in
            el_a b "span" (Some "c sig rq-ctx") [ ("data-d", "args") ] (fun b ->
                kw b k;
                el b "span" (Some "args binders") (fun b ->
                    let rec go = function
                      | [] -> ()
                      | sb :: rest ->
                          el b "span" (Some "arg") (fun b ->
                              match sb with
                              | SBOrig b0 when b0.b_kind = BParen && b0.b_ty <> None ->
                                  el b "span" (Some "paren binder") (fun b ->
                                      seq_defs b b0.b_names;
                                      opt_type ctx b b0.b_ty [])
                              | SBOrig b0 when b0.b_kind = BBrace ->
                                  el b "span" (Some "braces binder") (fun b ->
                                      seq_defs b b0.b_names;
                                      opt_type ctx b b0.b_ty [])
                              | _ -> draw_split_binder ctx b sb []);
                          if rest <> [] then (
                            raw_char b ' ';
                            go rest)
                    in
                    go sbs))
        | _ ->
            el_a b "span" (Some "c sig rq-ctx") [ ("data-d", "args") ] (fun b ->
                kw b k;
                el b "span" (Some "args binders") (fun b ->
                    let rec go = function
                      | [] -> ()
                      | DeclTyped (ns, ty) :: rest ->
                          el b "span" (Some "arg") (fun b ->
                              el b "span" (Some "paren binder") (fun b ->
                                  param_names ctx b ns;
                                  opt_type ctx b (Some ty) []));
                          if rest <> [] then (
                            raw_char b ' ';
                            go rest)
                      | DeclBinders _ :: rest -> go rest
                    in
                    go gs))
      in
      el b "div" (Some "clause rq-param") (fun b ->
          el b "div" (Some "head") (fun b ->
              line_link ctx b sp.lo;
              draw_param_items ()));
      !Draw_hooks.notes_before_ref ctx b sp.hi
  | VNotation (sp, k, s, e, mods) ->
      let e1 = match e with EParen (_, inner) -> inner | _ -> e in
      el b "div" (Some "clause rq-notation") (fun b ->
          el b "div" (Some "head") (fun b ->
              line_link ctx b sp.lo;
              kw b k;
              raw_char b ' ';
              notation_pattern b s e;
              raw b nbsp;
              defeq b;
              raw_char b ' ';
              term ctx b e1 [];
              if mods <> [] then (
                raw_char b ' ';
                el b "span" (Some "rq-mods") (fun b -> esc_words b mods))));
      !Draw_hooks.notes_before_ref ctx b sp.hi
  | VModule (sp, kind, n, bs, ModDefined (m :: as_, sig_opt)) ->
      let q = qualify ctx.mod_path n.n_text in
      let kws = Draw_prose.module_kw_str kind in
      el_a b "div" (Some "clause rq-module-def") [ ("id", q) ] (fun b ->
          el b "div" (Some "head") (fun b ->
              line_link ctx b sp.lo;
              kw b kws;
              raw_char b ' ';
              el_text b "span" (Some "module-name") n.n_text;
              binders_ ctx b bs [];
              (match sig_opt with
              | Some (sig_n, args) ->
                  raw b nbsp;
                  el_raw b "span" (Some "op wide colon") ":";
                  raw_char b ' ';
                  name_ref ctx b sig_n [] `Arg;
                  List.iter (module_arg ctx b) args
              | None -> ());
              raw b nbsp;
              defeq b;
              raw_char b ' ';
              name_ref ctx b m [] `Arg;
              List.iter (module_arg ctx b) as_));
      !Draw_hooks.notes_before_ref ctx b sp.hi
  | VCmd (sp, kws, toks) ->
      let kw_s = String.concat " " kws in
      let ws0 = cmd_words toks in
      let ws, code_opt =
        match List.rev ws0 with
        | [ t ] :: rev_rest when (match t.kind with Str _ -> true | _ -> false) ->
            let s = src_text ctx { lo = t.lo; hi = t.hi } in
            if String.contains s '\n' then
              match String.split_on_char '\n' s with
              | l :: ls -> (List.rev rev_rest, Some (String.concat "\n" (l :: Markdown.dedent ls)))
              | [] -> (ws0, None)
            else (ws0, None)
        | _ -> (ws0, None)
      in
      el b "div" (Some "clause rq-cmd") (fun b ->
          el b "div" (Some "head") (fun b ->
              line_link ctx b sp.lo;
              if ws = [] then kw b kw_s
              else
                el_a b "span" (Some "c rq-cmd-args") [ ("data-d", "args") ] (fun b ->
                    kw b kw_s;
                    el b "span" (Some "args") (fun b -> draw_cmd_args ctx b ws)));
          Option.iter (fun code -> el_text b "pre" (Some "s rq-code rq-code-block") code) code_opt);
      !Draw_hooks.notes_before_ref ctx b sp.hi
  | VEnd (sp, _) -> draw_raw ctx b sp
  | s -> draw_raw ctx b (vernac_span s)

let () =
  Draw_hooks.draw_term_ref := term;
  Draw_hooks.draw_blk_ref := blk;
  Draw_hooks.draw_name_ref_ref := name_ref;
  Draw_hooks.draw_var_ref := var_;
  Draw_hooks.draw_var_def_ref := var_def;
  Draw_hooks.draw_kw_ref := kw;
  Draw_hooks.draw_defeq_ref := defeq;
  Draw_hooks.draw_items_ref := rocq_items;
  Draw_hooks.draw_expr_items_ref := items;
  Draw_hooks.draw_sep_items_ref := sep_items;
  Draw_hooks.draw_binders_ref := binders_;
  Draw_hooks.draw_opt_type_ref := opt_type;
  Draw_hooks.draw_vars_ref := vars;
  Draw_hooks.draw_seq_defs_ref := seq_defs;
  Draw_hooks.draw_notation_pat_ref := notation_pattern
