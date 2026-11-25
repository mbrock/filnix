(* Proof, Ltac, intro-pattern, and Iris Proof Mode renderer mirroring
   rocq_draw.pl lines 1649-2101. *)

open Ast
open Draw_env
open Html

let nbsp = "\xc2\xa0"

let term ctx b e env = !Draw_hooks.draw_term_ref ctx b e env
let name_ref ctx b x env pos = !Draw_hooks.draw_name_ref_ref ctx b x env pos
let var_ b x = !Draw_hooks.draw_var_ref b x
let var_def b x = !Draw_hooks.draw_var_def_ref b x
let kw b s = !Draw_hooks.draw_kw_ref b s
let defeq b = !Draw_hooks.draw_defeq_ref b
let expr_items ctx b es env = !Draw_hooks.draw_expr_items_ref ctx b es env
let sep_items ctx b es env s = !Draw_hooks.draw_sep_items_ref ctx b es env s
let vars b ns = !Draw_hooks.draw_vars_ref b ns
let notes_before ctx b off = !Draw_hooks.notes_before_ref ctx b off
let aside_after ctx b off = !Draw_hooks.aside_after_ref ctx b off

let rec tactic_structural = function
  | TMatch _ | TSelect _ | TLetRec _ -> true
  | TChoices (_, ts) -> List.exists tactic_structural ts
  | TDispatch (t, ts) -> tactic_structural t || List.exists tactic_structural ts
  | TPrefix (_, t) | TDo (_, t) | TGroup t | TLet (_, _, t) -> tactic_structural t
  | TBin (_, l, r) -> tactic_structural l || tactic_structural r
  | _ -> false

let is_ipm_tactic s =
  String.length s >= 2 && s.[0] = 'i' && s.[1] >= 'A' && s.[1] <= 'Z'

let is_csym_ascii c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'

let is_ipm_name_uchar u =
  (u < 128 && (is_csym_ascii (Char.unsafe_chr u) || u = 0x27))
  || (u >= 0x80 && u <> 0x25A1 (* □ *) && u <> 0x2217 (* ∗ *))

let ipm_pattern b s =
  el b "span" (Some "rq-ipm") (fun b ->
      let n = String.length s in
      let rec go i =
        if i >= n then ()
        else
          let u, step = Lexer.decode_uchar s i in
          if is_ipm_name_uchar u then (
            let rec scan j =
              if j >= n then j
              else
                let u2, st2 = Lexer.decode_uchar s j in
                if is_ipm_name_uchar u2 then scan (j + st2) else j
            in
            let hi = scan (i + step) in
            let w = String.sub s i (hi - i) in
            if w = "_" then el_raw b "span" (Some "v anon") "_" else var_ b w;
            go hi)
          else if u = 0x20 then (
            raw_char b ' ';
            go (i + step))
          else (
            el b "span" (Some "op rq-ipm-mark") (fun b ->
                if step = 1 then esc_char b s.[i] else raw_sub b s i step);
            go (i + step))
      in
      go 0)

let rec tactic_chain : 'a. ctx -> Html.t -> 'a list -> string -> (ctx -> Html.t -> 'a -> string list -> unit) -> string list -> unit =
 fun ctx b xs op draw env ->
  match xs with
  | [] -> ()
  | [ x ] -> draw ctx b x env
  | x :: rest ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          draw ctx b x env;
          raw_char b ' ';
          el_a b "span" (Some "op wide") [ ("title", op) ] (fun b -> esc b op);
          raw_char b ' ';
          tactic_chain ctx b rest op draw env)

let rec intro_pattern ctx b pat env =
  match pat with
  | IpName { n_text = "_"; _ } -> el_a b "span" (Some "v anon") [ ("title", "_") ] (fun b -> raw b "_")
  | IpName n -> var_ b n.n_text
  | IpRewrite op ->
      let g = if op = "->" then "→" else "←" in
      el_a b "span" (Some "op rq-rewrite") [ ("title", op) ] (fun b -> esc b g)
  | IpAuto k -> el_text b "span" (Some "v anon") k
  | IpFresh n ->
      el b "span" (Some "rq-meta") (fun b ->
          raw_char b '?';
          var_ b n.n_text)
  | IpInj [] ->
      el b "span" (Some "l rq-pattern") (fun b -> el_raw b "span" (Some "op") "=")
  | IpInj ps ->
      el b "span" (Some "l rq-pattern") (fun b ->
          el_raw b "span" (Some "op") "=";
          raw_char b ' ';
          intro_items ctx b ps env)
  | IpAnd ps ->
      el b "span" (Some "paren rq-pattern rq-intro-and") (fun b ->
          tactic_chain ctx b ps "&"
            (fun ctx b p env -> el b "span" (Some "arg") (fun b -> intro_pattern ctx b p env))
            env)
  | IpOr arms ->
      el b "span" (Some "l rq-pattern rq-intro-or") (fun b ->
          tactic_chain ctx b arms "|" intro_sequence env)

and intro_sequence ctx b ps env =
  match ps with
  | [] -> el_empty b "span" (Some "rq-empty")
  | _ ->
      el_a b "span" (Some "c rq-intros") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args rq-tac-args") (fun b -> intro_items ctx b ps env))

and intro_items ctx b ps env =
  match ps with
  | [] -> ()
  | [ p ] -> el b "span" (Some "arg") (fun b -> intro_pattern ctx b p env)
  | p :: rest ->
      el b "span" (Some "arg") (fun b -> intro_pattern ctx b p env);
      raw_char b ' ';
      intro_items ctx b rest env

let rec ipm_items ctx b is env =
  let draw_one = function
    | IpmCoq ps ->
        el b "span" (Some "paren rq-pattern") (fun b -> intro_items ctx b ps env)
    | IpmStr s -> ipm_pattern b s
  in
  match is with
  | [] -> ()
  | [ i ] -> el b "span" (Some "arg") (fun _ -> draw_one i)
  | i :: rest ->
      el b "span" (Some "arg") (fun _ -> draw_one i);
      raw_char b ' ';
      ipm_items ctx b rest env

(* Collect meta and hyp names bound in a match-goal pattern *)
let rec pat_bound_names_expr acc = function
  | EMeta (_, x) -> x :: acc
  | EApp (_, f, args) -> List.fold_left pat_bound_names_expr (pat_bound_names_expr acc f) args
  | EBin (_, _, l, r) -> pat_bound_names_expr (pat_bound_names_expr acc l) r
  | EChain (_, _, es) | ETuple (_, es) | EOrPat (_, es) | EList (_, es) | EGFunctors (_, es) ->
      List.fold_left pat_bound_names_expr acc es
  | EPre (_, _, e) | EParen (_, e) | EBits (_, e, _) | EScope (_, e, _) | EBraces (_, e)
  | EPure (_, e) | EProj (_, e, _) | EBigAll (_, _, e) | EEval (_, _, e) | ENamed (_, _, e)
  | EAsPat (_, e, _) ->
      pat_bound_names_expr acc e
  | ECast (_, a, b) | EInsert (_, a, b) | ELaterN (_, a, b) ->
      pat_bound_names_expr (pat_bound_names_expr acc a) b
  | EForall (_, bs, body) | EExists (_, bs, body) | EFun (_, bs, body) ->
      let acc = List.fold_left pat_bound_names_binder acc bs in
      pat_bound_names_expr acc body
  | ELet (_, _, ty, v, body) ->
      let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) ty in
      pat_bound_names_expr (pat_bound_names_expr acc v) body
  | ELetStar (_, _, v, body) -> pat_bound_names_expr (pat_bound_names_expr acc v) body
  | ELetQ (_, pat, v, body) | ELetPat (_, pat, v, body) ->
      pat_bound_names_expr (pat_bound_names_expr (pat_bound_names_expr acc pat) v) body
  | ELetFix (_, _, bs, ty, v, body) ->
      let acc = List.fold_left pat_bound_names_binder acc bs in
      let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) ty in
      pat_bound_names_expr (pat_bound_names_expr acc v) body
  | EFix (_, _, bs, ty, body) ->
      let acc = List.fold_left pat_bound_names_binder acc bs in
      let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) ty in
      pat_bound_names_expr acc body
  | EIf (_, c, t, e) ->
      pat_bound_names_expr (pat_bound_names_expr (pat_bound_names_expr acc c) t) e
  | EIfIs (_, c, pat, t, e) ->
      pat_bound_names_expr
        (pat_bound_names_expr (pat_bound_names_expr (pat_bound_names_expr acc c) pat) t)
        e
  | EMatch (_, ss, ret, brs) ->
      let acc =
        List.fold_left
          (fun acc -> function ScrutExpr e | ScrutAs (e, _) -> pat_bound_names_expr acc e)
          acc ss
      in
      let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) ret in
      List.fold_left
        (fun acc br ->
          let acc = List.fold_left (List.fold_left pat_bound_names_expr) acc br.br_alts in
          pat_bound_names_expr acc br.br_rhs)
        acc brs
  | ERecord (_, fs) ->
      List.fold_left
        (fun acc -> function
          | RFld (_, _, e) -> pat_bound_names_expr acc e
          | RFldB (_, _, bs, e) ->
              pat_bound_names_expr (List.fold_left pat_bound_names_binder acc bs) e)
        acc fs
  | EMixfix (_, parts) ->
      List.fold_left (fun acc -> function MStr _ -> acc | MExpr e -> pat_bound_names_expr acc e) acc parts
  | EFupd (_, ms, a) -> pat_bound_names_expr (List.fold_left pat_bound_names_expr acc ms) a
  | EFupdw (_, ms, l, r) ->
      pat_bound_names_expr (pat_bound_names_expr (List.fold_left pat_bound_names_expr acc ms) l) r
  | EStepUpd (_, ms, n, a) ->
      let acc = List.fold_left pat_bound_names_expr acc ms in
      let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) n in
      pat_bound_names_expr acc a
  | EStepUpdw (_, ms, n, l, r) ->
      let acc = List.fold_left pat_bound_names_expr acc ms in
      let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) n in
      pat_bound_names_expr (pat_bound_names_expr acc l) r
  | EPointsTo (_, _, l, ms, r) ->
      let acc = pat_bound_names_expr acc l in
      let acc =
        List.fold_left
          (fun acc -> function
            | PmName e | PmDfrac e | PmOwn e -> pat_bound_names_expr acc e
            | PmPersistent -> acc)
          acc ms
      in
      pat_bound_names_expr acc r
  | EIndexed (_, _, n, l, r) ->
      let acc = pat_bound_names_expr acc n in
      let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) l in
      pat_bound_names_expr acc r
  | EWp (_, e, at, post) ->
      let acc = pat_bound_names_expr acc e in
      let acc =
        match at with
        | WpNone -> acc
        | WpAt (s, m) ->
            let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) s in
            pat_bound_names_expr acc m
      in
      pat_bound_names_expr acc post.wp_body
  | ETriple (_, pre, e, at, bs, ret, post) ->
      let acc = pat_bound_names_expr (pat_bound_names_expr acc pre) e in
      let acc =
        match at with
        | WpNone -> acc
        | WpAt (s, m) ->
            let acc = Option.fold ~none:acc ~some:(pat_bound_names_expr acc) s in
            pat_bound_names_expr acc m
      in
      let acc = List.fold_left pat_bound_names_binder acc bs in
      pat_bound_names_expr (pat_bound_names_expr acc ret) post
  | EBigOp (_, _, _, _, cs, body) ->
      pat_bound_names_expr (List.fold_left pat_bound_names_expr acc cs) body
  | ESig (_, _, t, q) -> pat_bound_names_expr (pat_bound_names_expr acc t) q
  | _ -> acc

and pat_bound_names_binder acc b =
  let acc =
    match b.b_kind with
    | BPattern e -> pat_bound_names_expr acc e
    | BGen (_, items) ->
        List.fold_left
          (fun acc -> function
            | GenBangCast (_, _, e) | GenBang e | GenExpr e -> pat_bound_names_expr acc e)
          acc items
    | _ -> acc
  in
  Option.fold ~none:acc ~some:(pat_bound_names_expr acc) b.b_ty

let rec pat_bound_names_parts acc = function
  | [] -> acc
  | p :: rest ->
      let acc =
        match p with
        | TPHypCtx (n, e) | TPHypExpr (n, e) -> pat_bound_names_expr (n.n_text :: acc) e
        | TPTerm e | TPContext e | TPBinding (_, _, e) -> pat_bound_names_expr acc e
        | TPTerms es -> List.fold_left pat_bound_names_expr acc es
        | TPGroup (_, ps, _) | TPClause (_, ps) -> pat_bound_names_parts acc ps
        | TPIpm (h, args, _) ->
            let acc = match h with IpmExpr e -> pat_bound_names_expr acc e | IpmHyp _ -> acc in
            List.fold_left pat_bound_names_expr acc args
        | _ -> acc
      in
      pat_bound_names_parts acc rest

let rec tactic_block ctx b tac env =
  match tac with
  | TMatch (k, subj, bs) ->
      el b "span" (Some "rq-tac-match") (fun b ->
          el b "span" (Some "goal rq-tac-head") (fun b ->
              kw b k;
              raw_char b ' ';
              tactic_subject ctx b subj env;
              raw_char b ' ';
              kw b "with");
          el b "span" (Some "cases match") (fun b -> tactic_branches ctx b bs env);
          el b "span" (Some "rq-tac-end") (fun b -> kw b "end"))
  | TBin (op, l, r) when tactic_structural l || tactic_structural r ->
      el b "span" (Some "rq-tac-seq") (fun b ->
          el b "span" (Some "rq-tac-left") (fun b -> tactic_block ctx b l env);
          el_text b "span" (Some "rq-tac-sep") op;
          el b "span" (Some "rq-tac-right") (fun b -> tactic_block ctx b r env))
  | TPrefix (k, t) when tactic_structural t ->
      el b "span" (Some "rq-tac-prefix") (fun b ->
          kw b k;
          raw_char b ' ';
          tactic_block ctx b t env)
  | TDo (n, t) when tactic_structural t ->
      el b "span" (Some "rq-tac-prefix") (fun b ->
          el b "span" None (fun b ->
              kw b "do";
              raw_char b ' ';
              esc b n);
          raw_char b ' ';
          tactic_block ctx b t env)
  | TSelect (s, t) ->
      el b "span" (Some "rq-tac-select") (fun b ->
          el b "span" (Some "rq-selector") (fun b ->
              esc b s;
              raw_char b ':');
          raw_char b ' ';
          tactic_block ctx b t env)
  | TChoices (k, ts) when List.exists tactic_structural ts ->
      el b "span" (Some "rq-tac-choices") (fun b ->
          kw b k;
          el b "span" (Some "l rq-tac-options") (fun b -> tactic_options ctx b ts env))
  | TDispatch (t, ts) when tactic_structural t || List.exists tactic_structural ts ->
      el b "span" (Some "rq-tac-seq") (fun b ->
          el b "span" (Some "rq-tac-left") (fun b -> tactic_block ctx b t env);
          el_raw b "span" (Some "rq-tac-sep") ";";
          el b "span" (Some "l rq-tac-options") (fun b -> tactic_options ctx b ts env))
  | TLet (n, v, body) when tactic_structural body ->
      el b "span" (Some "rq-tac-let") (fun b ->
          el b "span" (Some "goal rq-tac-head") (fun b ->
              kw b "let";
              raw_char b ' ';
              var_def b n.n_text;
              raw b nbsp;
              defeq b;
              raw_char b ' ';
              tactic_inline ctx b v env;
              raw_char b ' ';
              kw b "in");
          tactic_block ctx b body (n.n_text :: env))
  | TLetRec (n, args, v, body) ->
      let inner = List.map (fun a -> a.n_text) args @ (n.n_text :: env) in
      el b "span" (Some "rq-tac-let") (fun b ->
          el b "span" (Some "goal rq-tac-head") (fun b ->
              kw b "let rec";
              raw_char b ' ';
              var_def b n.n_text;
              raw_char b ' ';
              vars b args;
              raw b nbsp;
              defeq b);
          tactic_block ctx b v inner;
          el b "span" (Some "goal rq-tac-head") (fun b -> kw b "in");
          tactic_block ctx b body (n.n_text :: env))
  | TGroup t when tactic_structural t ->
      el b "span" (Some "rq-tac-group") (fun b ->
          raw_char b '(';
          tactic_block ctx b t env;
          raw_char b ')')
  | t -> el b "span" (Some "goal rq-tac-inline") (fun b -> tactic_inline ctx b t env)

and tactic_inline ctx b tac env =
  match tac with
  | TMatch _ | TLetRec _ -> tactic_block ctx b tac env
  | TBin (op, l, r) ->
      el_a b "span" (Some "o rq-tac-chain") [ ("data-d", "op") ] (fun b ->
          tactic_inline ctx b l env;
          raw_char b ' ';
          el_a b "span" (Some "op wide") [ ("title", op) ] (fun b -> esc b op);
          raw_char b ' ';
          tactic_inline ctx b r env)
  | TPrefix (k, t) ->
      el_a b "span" (Some "c rq-tac-call") [ ("data-d", "args") ] (fun b ->
          kw b k;
          raw_char b ' ';
          el b "span" (Some "args rq-tac-args") (fun b ->
              el b "span" (Some "arg") (fun b -> tactic_inline ctx b t env)))
  | TDo (n, t) ->
      el_a b "span" (Some "c rq-tac-call") [ ("data-d", "args") ] (fun b ->
          kw b "do";
          raw_char b ' ';
          el b "span" (Some "args rq-tac-args") (fun b ->
              el_text b "span" (Some "arg") n;
              raw_char b ' ';
              el b "span" (Some "arg") (fun b -> tactic_inline ctx b t env)))
  | TSelect _ -> tactic_block ctx b tac env
  | TGroup t -> el b "span" (Some "paren") (fun b -> tactic_inline ctx b t env)
  | TChoices (k, ts) ->
      el_a b "span" (Some "c rq-tac-call") [ ("data-d", "args") ] (fun b ->
          kw b k;
          raw_char b ' ';
          el b "span" (Some "args rq-tac-args") (fun b ->
              el b "span" (Some "arg") (fun b -> tactic_alternatives ctx b ts env)))
  | TDispatch (t, ts) ->
      el_a b "span" (Some "o rq-tac-chain") [ ("data-d", "op") ] (fun b ->
          tactic_inline ctx b t env;
          raw_char b ' ';
          el_a b "span" (Some "op wide") [ ("title", ";") ] (fun b -> raw_char b ';');
          raw_char b ' ';
          tactic_alternatives ctx b ts env)
  | TLet (n, v, body) ->
      el_a b "span" (Some "o rq-tac-chain") [ ("data-d", "op") ] (fun b ->
          kw b "let";
          raw_char b ' ';
          var_def b n.n_text;
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          tactic_inline ctx b v env;
          raw_char b ' ';
          kw b "in";
          raw_char b ' ';
          tactic_inline ctx b body (n.n_text :: env))
  | TEval (ws, e) ->
      let strategy = String.concat " " ws in
      el_a b "span" (Some "o rq-tac-chain") [ ("data-d", "op") ] (fun b ->
          kw b "eval";
          raw_char b ' ';
          esc b strategy;
          raw_char b ' ';
          kw b "in";
          raw_char b ' ';
          term ctx b e env)
  | TCall (n, []) -> name_ref ctx b n env `Head
  | TCall ("pose", TPToken (Id "proof") :: ps) ->
      el_a b "span" (Some "c rq-tac-call") [ ("data-d", "args") ] (fun b ->
          name_ref ctx b "pose" env `Head;
          raw_char b ' ';
          kw b "proof";
          if ps <> [] then (
            raw_char b ' ';
            el b "span" (Some "args rq-tac-args") (fun b -> tactic_parts ctx b ps env)))
  | TCall (n, ps) ->
      let prev = ctx.in_ipm in
      if is_ipm_tactic n then ctx.in_ipm <- true;
      Fun.protect ~finally:(fun () -> ctx.in_ipm <- prev) @@ fun () ->
      el_a b "span" (Some "c rq-tac-call") [ ("data-d", "args") ] (fun b ->
          name_ref ctx b n env `Head;
          raw_char b ' ';
          el b "span" (Some "args rq-tac-args") (fun b -> tactic_parts ctx b ps env))
  | TEmpty -> el_empty b "span" (Some "rq-empty")
  | TRest t ->
      tactic_inline ctx b t env;
      raw b ".."

and tactic_alternatives ctx b ts env =
  el b "span" (Some "l rq-tac-alternatives") (fun b ->
      tactic_chain ctx b ts "|" tactic_inline env)

and tactic_options ctx b ts env =
  List.iter
    (fun t ->
      el b "span" (Some "rq-tac-option") (fun b ->
          el_raw b "span" (Some "rq-choice-bar") "|";
          tactic_block ctx b t env))
    ts

and tactic_subject ctx b subj env =
  match subj with
  | TSubGoal -> kw b "goal"
  | TSubType e ->
      kw b "type of";
      raw_char b ' ';
      term ctx b e env
  | TSubTerm e -> term ctx b e env

and tactic_branches ctx b bs env =
  List.iter
    (fun br ->
      let env1 = pat_bound_names_parts [] br.tbr_pats @ env in
      el b "span" (Some "case") (fun b ->
          el b "span" (Some "cond") (fun b ->
              el b "span" (Some "goals") (fun b ->
                  el b "span" (Some "goal rq-tac-pattern") (fun b ->
                      el_a b "span" (Some "c rq-tac-call") [ ("data-d", "args") ] (fun b ->
                          el b "span" (Some "args rq-tac-args") (fun b ->
                              tactic_parts ctx b br.tbr_pats env1)))));
          el_raw b "span" (Some "arrow") "⇒";
          el b "span" (Some "then") (fun b ->
              el b "span" (Some "goals") (fun b -> tactic_block ctx b br.tbr_rhs env1))))
    bs

and tactic_parts ctx b ps env =
  match ps with
  | [] -> ()
  | [ p ] -> el b "span" (Some "arg") (fun b -> tactic_part ctx b p env)
  | p :: rest ->
      el b "span" (Some "arg") (fun b -> tactic_part ctx b p env);
      raw_char b ' ';
      tactic_parts ctx b rest env

and tactic_part ctx b part env =
  match part with
  | TPIpmIntros is ->
      el_a b "span" (Some "c rq-intros") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args rq-tac-args") (fun b -> ipm_items ctx b is env))
  | TPIpmAs (ps, pat) ->
      if ps <> [] then (
        el b "span" (Some "paren rq-pattern") (fun b -> intro_items ctx b ps env);
        raw_char b ' ');
      (match pat with
      | IpmPatStr s -> ipm_pattern b s
      | IpmPatPure p ->
          el b "span" (Some "rq-ipm-pure") (fun b ->
              el_raw b "span" (Some "op") "%";
              intro_pattern ctx b p env))
  | TPIpm (h, args, spat) ->
      el b "span" (Some "paren rq-ipm-term") (fun b ->
          (match h with IpmHyp s -> ipm_pattern b s | IpmExpr e -> term ctx b e env);
          if args <> [] then (
            raw_char b ' ';
            el_a b "span" (Some "op wide") [ ("title", "$!") ] (fun b -> raw b "$!");
            raw_char b ' ';
            expr_items ctx b args env);
          Option.iter
            (fun s ->
              raw_char b ' ';
              kw b "with";
              raw_char b ' ';
              ipm_pattern b s)
            spat)
  | TPTerms es ->
      el b "span" (Some "c tuple") (fun b ->
          el b "span" (Some "args rq-tac-args") (fun b -> sep_items ctx b es env ","))
  | TPIntro ps ->
      el_a b "span" (Some "c rq-intros") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args rq-tac-args") (fun b -> intro_items ctx b ps env))
  | TPClause ("by", [ TPTactic t ]) ->
      el_a b "span" (Some "c rq-tac-clause") [ ("data-d", "args") ] (fun b ->
          kw b "by";
          raw_char b ' ';
          el b "span" (Some "args rq-tac-args") (fun b ->
              el b "span" (Some "arg") (fun b ->
                  if tactic_structural t then tactic_block ctx b t env
                  else tactic_inline ctx b t env)))
  | TPClause (k, ps) ->
      el_a b "span" (Some "c rq-tac-clause") [ ("data-d", "args") ] (fun b ->
          kw b k;
          if k = "eqn" then raw_char b ':';
          raw_char b ' ';
          el b "span" (Some "args rq-tac-args") (fun b -> tactic_parts ctx b ps env))
  | TPTerm e -> term ctx b e env
  | TPTactic t -> el b "span" (Some "paren") (fun b -> tactic_block ctx b t env)
  | TPBinding (n, op, e) ->
      el b "span" (Some "paren") (fun b ->
          var_def b n.n_text;
          raw b nbsp;
          el_a b "span" (Some "op wide") [ ("title", op) ] (fun b -> esc b op);
          raw_char b ' ';
          term ctx b e env)
  | TPContext e ->
      kw b "context";
      raw b " [";
      term ctx b e env;
      raw_char b ']'
  | TPHypCtx (n, e) ->
      var_def b n.n_text;
      raw b " : ";
      tactic_part ctx b (TPContext e) env
  | TPHypExpr (n, e) ->
      var_def b n.n_text;
      raw b " : ";
      term ctx b e env
  | TPGroup (open_d, ps, close_d) ->
      el_a b "span" (Some "l rq-token-group") [ ("data-d", "args") ] (fun b ->
          el_text b "span" (Some "sep") open_d;
          raw_char b ' ';
          tactic_parts ctx b ps env;
          raw_char b ' ';
          el_text b "span" (Some "sep") close_d)
  | TPToken (Id x) -> name_ref ctx b x env `Arg
  | TPToken (Kw x) -> kw b x
  | TPToken (Str s) when ctx.in_ipm -> ipm_pattern b s
  | TPToken (Str s) -> term ctx b (EStr ({ lo = 0; hi = 0 }, s)) env
  | TPToken k -> el_text b "span" (Some "rq-token") (tok_text k)

(* ── Proof tree, bullet focus stack, and tactic rows ───────────────────── *)

let rec tactic_intro_vars_intro acc = function
  | IpName n when n.n_text <> "_" -> n.n_text :: acc
  | IpInj ps | IpAnd ps -> List.fold_left tactic_intro_vars_intro acc ps
  | IpOr arms -> List.fold_left (List.fold_left tactic_intro_vars_intro) acc arms
  | _ -> acc

let rec tactic_intro_vars_expr acc = function
  | ELtac (_, t) -> tactic_intro_vars acc t
  | EApp (_, f, args) -> List.fold_left tactic_intro_vars_expr (tactic_intro_vars_expr acc f) args
  | EBin (_, _, l, r) -> tactic_intro_vars_expr (tactic_intro_vars_expr acc l) r
  | EChain (_, _, es) | ETuple (_, es) | EOrPat (_, es) | EList (_, es) | EGFunctors (_, es) ->
      List.fold_left tactic_intro_vars_expr acc es
  | EPre (_, _, e) | EParen (_, e) | EBits (_, e, _) | EScope (_, e, _) | EBraces (_, e)
  | EPure (_, e) | EProj (_, e, _) | EBigAll (_, _, e) | EEval (_, _, e) | ENamed (_, _, e)
  | EAsPat (_, e, _) ->
      tactic_intro_vars_expr acc e
  | ECast (_, a, b) | EInsert (_, a, b) | ELaterN (_, a, b) ->
      tactic_intro_vars_expr (tactic_intro_vars_expr acc a) b
  | EForall (_, _, body) | EExists (_, _, body) | EFun (_, _, body) ->
      tactic_intro_vars_expr acc body
  | ELet (_, _, ty, v, body) ->
      let acc = Option.fold ~none:acc ~some:(tactic_intro_vars_expr acc) ty in
      tactic_intro_vars_expr (tactic_intro_vars_expr acc v) body
  | ELetStar (_, _, v, body) -> tactic_intro_vars_expr (tactic_intro_vars_expr acc v) body
  | ELetQ (_, pat, v, body) | ELetPat (_, pat, v, body) ->
      tactic_intro_vars_expr (tactic_intro_vars_expr (tactic_intro_vars_expr acc pat) v) body
  | ELetFix (_, _, _, ty, v, body) ->
      let acc = Option.fold ~none:acc ~some:(tactic_intro_vars_expr acc) ty in
      tactic_intro_vars_expr (tactic_intro_vars_expr acc v) body
  | EFix (_, _, _, ty, body) ->
      let acc = Option.fold ~none:acc ~some:(tactic_intro_vars_expr acc) ty in
      tactic_intro_vars_expr acc body
  | EIf (_, c, t, e) ->
      tactic_intro_vars_expr (tactic_intro_vars_expr (tactic_intro_vars_expr acc c) t) e
  | EIfIs (_, c, pat, t, e) ->
      tactic_intro_vars_expr
        (tactic_intro_vars_expr (tactic_intro_vars_expr (tactic_intro_vars_expr acc c) pat) t)
        e
  | EMatch (_, ss, ret, brs) ->
      let acc =
        List.fold_left
          (fun a -> function ScrutExpr e | ScrutAs (e, _) -> tactic_intro_vars_expr a e)
          acc ss
      in
      let acc = Option.fold ~none:acc ~some:(tactic_intro_vars_expr acc) ret in
      List.fold_left (fun a br -> tactic_intro_vars_expr a br.br_rhs) acc brs
  | ERecord (_, fs) ->
      List.fold_left
        (fun a -> function RFld (_, _, e) | RFldB (_, _, _, e) -> tactic_intro_vars_expr a e)
        acc fs
  | EMixfix (_, parts) ->
      List.fold_left (fun a -> function MStr _ -> a | MExpr e -> tactic_intro_vars_expr a e) acc parts
  | EFupd (_, ms, a) -> tactic_intro_vars_expr (List.fold_left tactic_intro_vars_expr acc ms) a
  | EFupdw (_, ms, l, r) ->
      tactic_intro_vars_expr (tactic_intro_vars_expr (List.fold_left tactic_intro_vars_expr acc ms) l) r
  | EPointsTo (_, _, l, _, r) -> tactic_intro_vars_expr (tactic_intro_vars_expr acc l) r
  | EWp (_, e, _, post) -> tactic_intro_vars_expr (tactic_intro_vars_expr acc e) post.wp_body
  | ESig (_, _, t, q) -> tactic_intro_vars_expr (tactic_intro_vars_expr acc t) q
  | _ -> acc

and tactic_intro_vars_part acc = function
  | TPIntro ps -> List.fold_left tactic_intro_vars_intro acc ps
  | TPIpmIntros is ->
      List.fold_left
        (fun acc -> function IpmCoq ps -> List.fold_left tactic_intro_vars_intro acc ps | IpmStr _ -> acc)
        acc is
  | TPIpmAs (ps, pat) ->
      let acc = List.fold_left tactic_intro_vars_intro acc ps in
      (match pat with IpmPatPure p -> tactic_intro_vars_intro acc p | IpmPatStr _ -> acc)
  | TPClause ("eqn", [ TPToken (Id x) ]) -> x :: acc
  | TPClause (_, ps) | TPGroup (_, ps, _) -> List.fold_left tactic_intro_vars_part acc ps
  | TPTactic t -> tactic_intro_vars acc t
  | TPTerm e | TPContext e | TPBinding (_, _, e) -> tactic_intro_vars_expr acc e
  | TPTerms es -> List.fold_left tactic_intro_vars_expr acc es
  | TPIpm (h, args, _) ->
      let acc = match h with IpmExpr e -> tactic_intro_vars_expr acc e | IpmHyp _ -> acc in
      List.fold_left tactic_intro_vars_expr acc args
  | TPHypCtx (n, e) | TPHypExpr (n, e) -> tactic_intro_vars_expr (n.n_text :: acc) e
  | _ -> acc

and tactic_intro_vars acc = function
  | TBin (_, l, r) -> tactic_intro_vars (tactic_intro_vars acc l) r
  | TPrefix (_, t) | TDo (_, t) | TSelect (_, t) | TGroup t | TRest t -> tactic_intro_vars acc t
  | TChoices (_, ts) -> List.fold_left tactic_intro_vars acc ts
  | TDispatch (t, ts) -> List.fold_left tactic_intro_vars (tactic_intro_vars acc t) ts
  | TMatch (_, subj, bs) ->
      let acc =
        match subj with TSubGoal -> acc | TSubType e | TSubTerm e -> tactic_intro_vars_expr acc e
      in
      List.fold_left
        (fun acc br -> tactic_intro_vars (List.fold_left tactic_intro_vars_part acc br.tbr_pats) br.tbr_rhs)
        acc bs
  | TCall (_, ps) -> List.fold_left tactic_intro_vars_part acc ps
  | TLet (n, v, body) ->
      tactic_intro_vars (tactic_intro_vars (n.n_text :: acc) v) body
  | TLetRec (_, _, v, body) -> tactic_intro_vars (tactic_intro_vars acc v) body
  | TEval (_, e) -> tactic_intro_vars_expr acc e
  | TEmpty -> acc

let rec rule_binders_of = function
  | EForall (_, bs0, b) -> bs0 @ rule_binders_of b
  | EBin (_, ("->" | "→"), _, r) -> rule_binders_of r
  | EParen (_, (EForall _ as e)) -> rule_binders_of e
  | _ -> []

let rec binder_names_for_env ctx bs acc =
  List.fold_left
    (fun acc b ->
      match b.b_kind with
      | BPattern pat ->
          (* Same pattern var extraction as draw_term.alts_vars *)
          let rec pv a = function
            | EId (_, x) when x <> "_" && (not (is_ctor ctx x)) && not (String.contains x '.') -> x :: a
            | EApp (_, _, args) | EOrPat (_, args) | ETuple (_, args) | EList (_, args) ->
                List.fold_left pv a args
            | EParen (_, e) | EScope (_, e, _) -> pv a e
            | EBin (_, _, l, r) -> pv (pv a l) r
            | EAsPat (_, p, n) -> pv (n.n_text :: a) p
            | _ -> a
          in
          pv acc pat
      | _ ->
          List.fold_left
            (fun a n -> if n.n_text = "_" then a else n.n_text :: a)
            acc b.b_names)
    acc bs

let proof_env ctx stmt steps =
  let e0 =
    match stmt with
    | VThm (_, _, _, bs, ty) ->
        let e = binder_names_for_env ctx bs [] in
        binder_names_for_env ctx (rule_binders_of ty) e
    | VDef d ->
        let e = binder_names_for_env ctx d.d_binders [] in
        (match d.d_ty with
        | Some ty -> binder_names_for_env ctx (rule_binders_of ty) e
        | None -> e)
    | _ -> []
  in
  let xs =
    List.fold_left
      (fun acc -> function
        | PStep (_, _, ts) -> (
            match Parse_tactic.parse_tactic_tokens ~ops:ctx.ops ts with
            | Some t -> tactic_intro_vars acc t
            | None -> acc)
        | PBullets _ -> acc)
      e0 steps
  in
  List.sort_uniq String.compare xs

type focus_row =
  | RowOpen of int * focus list * span * token list
  | RowClose of focus list

type focus_node =
  | FGroup of string * focus_node list
  | FLeaf of focus_row

let bullet_focus stack = function
  | FocusBullet "}" ->
      let rec drop_brace = function
        | [] -> []
        | "{" :: tl -> tl
        | _ :: tl -> drop_brace tl
      in
      drop_brace stack
  | FocusBullet "{" | FocusNum _ -> "{" :: stack
  | FocusBullet b ->
      let rec pop_same = function
        | [] -> None
        | x :: tl when x = b -> Some tl
        | _ :: tl -> pop_same tl
      in
      let s1 = match pop_same stack with Some tl -> tl | None -> stack in
      b :: s1

let compute_rows steps =
  let rec go stack acc = function
    | [] -> List.rev acc
    | PStep (sp, bs, ts) :: rest ->
        let s' = List.fold_left bullet_focus stack bs in
        go s' (RowOpen (List.length s', bs, sp, ts) :: acc) rest
    | PBullets bs :: rest ->
        let s' = List.fold_left bullet_focus stack bs in
        go s' (RowClose bs :: acc) rest
  in
  go [] [] steps

let row_depth_bs = function
  | RowOpen (d, bs, _, _) -> (d, bs)
  | RowClose bs -> (0, bs)

let is_close_brace = function FocusBullet "}" -> true | _ -> false

let rec focus_tree level = function
  | [] -> []
  | x :: xs ->
      let d, bs = row_depth_bs x in
      if d > level then
        let kind =
          if
            List.exists
              (function FocusBullet "{" | FocusNum _ -> true | _ -> false)
              bs
          then "rq-focus rq-braced"
          else "rq-focus"
        in
        let rec take_members acc = function
          | y :: ys ->
              let dy, bys = row_depth_bs y in
              if dy > d || (dy = d && List.for_all is_close_brace bys) then
                take_members (y :: acc) ys
              else (List.rev acc, y :: ys)
          | [] -> (List.rev acc, [])
        in
        let more, rest = take_members [] xs in
        FGroup (kind, focus_tree d (x :: more)) :: focus_tree level rest
      else FLeaf x :: focus_tree level xs

let bullet_glyph = function
  | FocusBullet "-" -> "–"
  | FocusBullet "+" -> "+"
  | FocusBullet "*" -> "∗"
  | FocusNum n -> n ^ ": {"
  | FocusBullet s -> s

let rec tac_tokens ctx b ts cur_o stop_t =
  match ts with
  | [] ->
      if stop_t > cur_o then esc b (String.sub ctx.text cur_o (stop_t - cur_o))
  | tok :: rest ->
      if tok.lo > cur_o then esc b (String.sub ctx.text cur_o (tok.lo - cur_o));
      (match tok.kind with
      | Id x -> (
          match global_ref ctx x with
          | Some (href, kind) ->
              el_a b "a" (Some (kind_class kind)) [ ("href", href) ] (fun b -> esc b x)
          | None -> esc b (String.sub ctx.text tok.lo (tok.hi - tok.lo)))
      | _ -> esc b (String.sub ctx.text tok.lo (tok.hi - tok.lo)));
      tac_tokens ctx b rest tok.hi stop_t

let tactic_text ctx b (sp : span) ts =
  match Parse_tactic.parse_tactic_tokens ~ops:ctx.ops ts with
  | Some t ->
      let raw_s = src_text ctx sp in
      let env = match ctx.proof_env with Some e -> e | None -> [] in
      el_a b "span" (Some "tactic") [ ("title", raw_s) ] (fun b -> tactic_block ctx b t env)
  | None ->
      el b "span" (Some "tactic rq-unparsed") (fun b -> tac_tokens ctx b ts sp.lo sp.hi)

let tac_row ctx b = function
  | RowClose _ -> ()
  | RowOpen (d, bs, sp, ts) ->
      let style = Printf.sprintf "--depth:%d" d in
      let shown = List.filter (fun x -> not (is_close_brace x)) bs in
      notes_before ctx b sp.lo;
      el_a b "div" (Some "tac clause") [ ("style", style) ] (fun b ->
          el b "span" (Some "bullet") (fun b ->
              List.iter (fun x -> esc b (bullet_glyph x)) shown);
          tactic_text ctx b sp ts);
      aside_after ctx b sp.hi

let rec focus_nodes ctx b draw = function
  | [] -> ()
  | FGroup (kind, children) :: rest ->
      el b "div" (Some kind) (fun b -> focus_nodes ctx b draw children);
      focus_nodes ctx b draw rest
  | FLeaf x :: rest ->
      draw ctx b x;
      focus_nodes ctx b draw rest

let draw_proof ctx b stmt pf =
  let n_tacs =
    List.fold_left (fun acc -> function PStep _ -> acc + 1 | PBullets _ -> acc) 0 pf.pf_steps
  in
  let kw_end = match pf.pf_end with Some (QedEnd (_, kw)) -> kw | None -> "" in
  let count_s = if n_tacs = 1 then "1 step" else Printf.sprintf "%d steps" n_tacs in
  let env = proof_env ctx stmt pf.pf_steps in
  let rows = compute_rows pf.pf_steps in
  let open_rows = List.filter (function RowClose _ -> false | RowOpen _ -> true) rows in
  let script = focus_tree 0 open_rows in
  el b "details" (Some "rq-proof") (fun b ->
      el b "summary" None (fun b ->
          kw b "Proof";
          raw_char b ' ';
          el_text b "span" (Some "proof-count") count_s;
          raw_char b ' ';
          kw b kw_end);
      let prev = ctx.proof_env in
      ctx.proof_env <- Some env;
      Fun.protect ~finally:(fun () -> ctx.proof_env <- prev) @@ fun () ->
      el b "div" (Some "proof-steps") (fun b -> focus_nodes ctx b tac_row script))

let () =
  Draw_hooks.draw_proof_ref := draw_proof;
  Draw_hooks.draw_tactic_block_ref := tactic_block;
  Draw_hooks.draw_tactic_inline_ref := tactic_inline;
  Draw_hooks.tactic_structural_ref := tactic_structural
