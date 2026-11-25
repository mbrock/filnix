(* Comments, coqdoc/Markdown prose, concept cards/embeds, Prolog refs,
   inline Rocq fragments and fences — mirroring rocq_draw.pl lines 2102-2447. *)

open Ast
open Draw_env
open Html

let nbsp = "\xc2\xa0"

let term ctx b e env = !Draw_hooks.draw_term_ref ctx b e env
let kw b s = !Draw_hooks.draw_kw_ref b s
let defeq b = !Draw_hooks.draw_defeq_ref b
let var_ b x = !Draw_hooks.draw_var_ref b x
let binders_ ctx b bs env = !Draw_hooks.draw_binders_ref ctx b bs env
let opt_type ctx b ty env = !Draw_hooks.draw_opt_type_ref ctx b ty env
let seq_defs b ns = !Draw_hooks.draw_seq_defs_ref b ns
let notation_pattern b s e = !Draw_hooks.draw_notation_pat_ref b s e
let rocq_items ctx b items = !Draw_hooks.draw_items_ref ctx b items

let is_csym c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'

let is_digit c = c >= '0' && c <= '9'

let comment_heading text =
  let n = String.length text in
  if n >= 5 && String.starts_with ~prefix:"(**" text then
    let body0 = String.sub text 3 (n - 5) in
    let first = match String.split_on_char '\n' body0 with h :: _ -> h | [] -> "" in
    let l0 = Markdown.trim_spaces first in
    let ln = String.length l0 in
    if ln >= 2 && (l0.[0] = '*' || l0.[0] = '#') then (
      let m = l0.[0] in
      let i = ref 0 in
      while !i < ln && l0.[!i] = m do
        incr i
      done;
      if !i < ln && l0.[!i] = ' ' then
        let marks = !i in
        let n_lvl = if m = '#' then marks - 1 else marks in
        if n_lvl >= 1 && n_lvl + 1 <= 4 then
          let title = Markdown.trim_spaces (String.sub l0 (!i + 1) (ln - !i - 1)) in
          Some (n_lvl + 1, title)
        else None
      else None)
    else None
  else None

let is_unicode_alnum cp =
  (cp >= 0x30 && cp <= 0x39)
  || (cp >= 0x41 && cp <= 0x5A)
  || (cp >= 0x61 && cp <= 0x7A)
  || (cp >= 0xC0 && cp <= 0x2AF && cp <> 0xD7 && cp <> 0xF7)
  || (cp >= 0x370 && cp <= 0x3FF)

let heading_id title =
  let b = Buffer.create (String.length title + 4) in
  Buffer.add_string b "sec";
  let n = String.length title in
  let in_word = ref false in
  let i = ref 0 in
  while !i < n do
    let d = String.get_utf_8_uchar title !i in
    let len = Uchar.utf_decode_length d in
    let cp = Uchar.to_int (Uchar.utf_decode_uchar d) in
    if is_unicode_alnum cp then (
      if not !in_word then (
        Buffer.add_char b '-';
        in_word := true);
      if cp >= 0x41 && cp <= 0x5A then Buffer.add_char b (Char.chr (cp + 32))
      else Buffer.add_substring b title !i len)
    else in_word := false;
    i := !i + len
  done;
  Buffer.contents b

let comment_prose_lines text =
  let n = String.length text in
  let k = if String.starts_with ~prefix:"(**" text then 3 else 2 in
  let body = if n >= k + 2 then String.sub text k (n - k - 2) else "" in
  let ls0 = List.map Markdown.rtrim (String.split_on_char '\n' body) in
  let ls1 =
    match ls0 with
    | first0 :: more ->
        let first = Markdown.trim_spaces first0 in
        if first <> "" then first :: Markdown.dedent more else ls0
    | [] -> []
  in
  Markdown.dedent (Markdown.trim_blank_ends ls1)

(* ── Fragment helpers ──────────────────────────────────────────────────── *)

let rec collect_sub_ids acc = function
  | EId (_, x) -> x :: acc
  | EApp (_, f, args) -> List.fold_left collect_sub_ids (collect_sub_ids acc f) args
  | EBin (_, _, l, r) -> collect_sub_ids (collect_sub_ids acc l) r
  | EChain (_, _, es) | ETuple (_, es) | EOrPat (_, es) | EList (_, es) | EGFunctors (_, es) ->
      List.fold_left collect_sub_ids acc es
  | EPre (_, _, e) | EParen (_, e) | EBits (_, e, _) | EScope (_, e, _) | EBraces (_, e)
  | EPure (_, e) | EProj (_, e, _) | EBigAll (_, _, e) | EEval (_, _, e) | ENamed (_, _, e)
  | EAsPat (_, e, _) ->
      collect_sub_ids acc e
  | ECast (_, a, b) | EInsert (_, a, b) | ELaterN (_, a, b) ->
      collect_sub_ids (collect_sub_ids acc a) b
  | EForall (_, bs, body) | EExists (_, bs, body) | EFun (_, bs, body) ->
      collect_sub_ids (List.fold_left collect_sub_ids_binder acc bs) body
  | ELet (_, _, ty, v, body) ->
      let acc = Option.fold ~none:acc ~some:(collect_sub_ids acc) ty in
      collect_sub_ids (collect_sub_ids acc v) body
  | ELetStar (_, _, v, body) -> collect_sub_ids (collect_sub_ids acc v) body
  | ELetQ (_, pat, v, body) | ELetPat (_, pat, v, body) ->
      collect_sub_ids (collect_sub_ids (collect_sub_ids acc pat) v) body
  | ELetFix (_, _, bs, ty, v, body) ->
      let acc = List.fold_left collect_sub_ids_binder acc bs in
      let acc = Option.fold ~none:acc ~some:(collect_sub_ids acc) ty in
      collect_sub_ids (collect_sub_ids acc v) body
  | EFix (_, _, bs, ty, body) ->
      let acc = List.fold_left collect_sub_ids_binder acc bs in
      let acc = Option.fold ~none:acc ~some:(collect_sub_ids acc) ty in
      collect_sub_ids acc body
  | EIf (_, c, t, e) ->
      collect_sub_ids (collect_sub_ids (collect_sub_ids acc c) t) e
  | EIfIs (_, c, pat, t, e) ->
      collect_sub_ids (collect_sub_ids (collect_sub_ids (collect_sub_ids acc c) pat) t) e
  | EMatch (_, ss, ret, brs) ->
      let acc =
        List.fold_left
          (fun a -> function ScrutExpr e | ScrutAs (e, _) -> collect_sub_ids a e)
          acc ss
      in
      let acc = Option.fold ~none:acc ~some:(collect_sub_ids acc) ret in
      List.fold_left
        (fun a br ->
          let a = List.fold_left (List.fold_left collect_sub_ids) a br.br_alts in
          collect_sub_ids a br.br_rhs)
        acc brs
  | ERecord (_, fs) ->
      List.fold_left
        (fun a -> function
          | RFld (_, _, e) -> collect_sub_ids a e
          | RFldB (_, _, bs, e) -> collect_sub_ids (List.fold_left collect_sub_ids_binder a bs) e)
        acc fs
  | EMixfix (_, parts) ->
      List.fold_left (fun a -> function MStr _ -> a | MExpr e -> collect_sub_ids a e) acc parts
  | EFupd (_, ms, a) -> collect_sub_ids (List.fold_left collect_sub_ids acc ms) a
  | EFupdw (_, ms, l, r) ->
      collect_sub_ids (collect_sub_ids (List.fold_left collect_sub_ids acc ms) l) r
  | EStepUpd (_, ms, n, a) ->
      let acc = List.fold_left collect_sub_ids acc ms in
      let acc = Option.fold ~none:acc ~some:(collect_sub_ids acc) n in
      collect_sub_ids acc a
  | EStepUpdw (_, ms, n, l, r) ->
      let acc = List.fold_left collect_sub_ids acc ms in
      let acc = Option.fold ~none:acc ~some:(collect_sub_ids acc) n in
      collect_sub_ids (collect_sub_ids acc l) r
  | EPointsTo (_, _, l, ms, r) ->
      let acc = collect_sub_ids acc l in
      let acc =
        List.fold_left
          (fun a -> function
            | PmName e | PmDfrac e | PmOwn e -> collect_sub_ids a e
            | PmPersistent -> a)
          acc ms
      in
      collect_sub_ids acc r
  | EIndexed (_, _, n, l, r) ->
      let acc = collect_sub_ids acc n in
      let acc = Option.fold ~none:acc ~some:(collect_sub_ids acc) l in
      collect_sub_ids acc r
  | EWp (_, e, at, post) ->
      let acc = collect_sub_ids acc e in
      let acc =
        match at with
        | WpNone -> acc
        | WpAt (s, m) ->
            collect_sub_ids (Option.fold ~none:acc ~some:(collect_sub_ids acc) s) m
      in
      collect_sub_ids acc post.wp_body
  | ETriple (_, pre, e, at, bs, ret, post) ->
      let acc = collect_sub_ids (collect_sub_ids acc pre) e in
      let acc =
        match at with
        | WpNone -> acc
        | WpAt (s, m) ->
            collect_sub_ids (Option.fold ~none:acc ~some:(collect_sub_ids acc) s) m
      in
      let acc = List.fold_left collect_sub_ids_binder acc bs in
      collect_sub_ids (collect_sub_ids acc ret) post
  | EBigOp (_, _, _, _, cs, body) -> collect_sub_ids (List.fold_left collect_sub_ids acc cs) body
  | ESig (_, _, t, q) -> collect_sub_ids (collect_sub_ids acc t) q
  | ELtac (_, t) -> collect_sub_ids_tactic acc t
  | _ -> acc

and collect_sub_ids_tactic acc = function
  | TBin (_, l, r) -> collect_sub_ids_tactic (collect_sub_ids_tactic acc l) r
  | TPrefix (_, t) | TDo (_, t) | TSelect (_, t) | TGroup t | TRest t ->
      collect_sub_ids_tactic acc t
  | TChoices (_, ts) -> List.fold_left collect_sub_ids_tactic acc ts
  | TDispatch (t, ts) -> List.fold_left collect_sub_ids_tactic (collect_sub_ids_tactic acc t) ts
  | TMatch (_, subj, bs) ->
      let acc =
        match subj with
        | TSubGoal -> acc
        | TSubType e | TSubTerm e -> collect_sub_ids acc e
      in
      List.fold_left
        (fun a br ->
          collect_sub_ids_tactic (List.fold_left collect_sub_ids_part a br.tbr_pats) br.tbr_rhs)
        acc bs
  | TCall (_, ps) -> List.fold_left collect_sub_ids_part acc ps
  | TLet (_, v, body) | TLetRec (_, _, v, body) ->
      collect_sub_ids_tactic (collect_sub_ids_tactic acc v) body
  | TEval (_, e) -> collect_sub_ids acc e
  | TEmpty -> acc

and collect_sub_ids_part acc = function
  | TPTerm e | TPContext e | TPBinding (_, _, e) | TPHypCtx (_, e) | TPHypExpr (_, e) ->
      collect_sub_ids acc e
  | TPTerms es -> List.fold_left collect_sub_ids acc es
  | TPTactic t -> collect_sub_ids_tactic acc t
  | TPClause (_, ps) | TPGroup (_, ps, _) -> List.fold_left collect_sub_ids_part acc ps
  | TPIpm (h, args, _) ->
      let acc = match h with IpmExpr e -> collect_sub_ids acc e | IpmHyp _ -> acc in
      List.fold_left collect_sub_ids acc args
  | _ -> acc

and collect_sub_ids_binder acc b =
  let acc =
    match b.b_kind with
    | BPattern e -> collect_sub_ids acc e
    | BGen (_, items) ->
        List.fold_left
          (fun a -> function
            | GenBangCast (_, _, e) | GenBang e | GenExpr e -> collect_sub_ids a e)
          acc items
    | _ -> acc
  in
  Option.fold ~none:acc ~some:(collect_sub_ids acc) b.b_ty

let rec collect_app_heads acc = function
  | EApp (_, EId (_, x), args) -> List.fold_left collect_app_heads (x :: acc) args
  | EApp (_, f, args) -> List.fold_left collect_app_heads (collect_app_heads acc f) args
  | EBin (_, _, l, r) -> collect_app_heads (collect_app_heads acc l) r
  | EChain (_, _, es) | ETuple (_, es) | EOrPat (_, es) | EList (_, es) | EGFunctors (_, es) ->
      List.fold_left collect_app_heads acc es
  | EPre (_, _, e) | EParen (_, e) | EBits (_, e, _) | EScope (_, e, _) | EBraces (_, e)
  | EPure (_, e) | EProj (_, e, _) | EBigAll (_, _, e) | EEval (_, _, e) | ENamed (_, _, e)
  | EAsPat (_, e, _) ->
      collect_app_heads acc e
  | ECast (_, a, b) | EInsert (_, a, b) | ELaterN (_, a, b) ->
      collect_app_heads (collect_app_heads acc a) b
  | EForall (_, bs, body) | EExists (_, bs, body) | EFun (_, bs, body) ->
      collect_app_heads (List.fold_left collect_app_heads_binder acc bs) body
  | ELet (_, _, ty, v, body) ->
      let acc = Option.fold ~none:acc ~some:(collect_app_heads acc) ty in
      collect_app_heads (collect_app_heads acc v) body
  | ELetStar (_, _, v, body) -> collect_app_heads (collect_app_heads acc v) body
  | ELetQ (_, pat, v, body) | ELetPat (_, pat, v, body) ->
      collect_app_heads (collect_app_heads (collect_app_heads acc pat) v) body
  | ELetFix (_, _, bs, ty, v, body) ->
      let acc = List.fold_left collect_app_heads_binder acc bs in
      let acc = Option.fold ~none:acc ~some:(collect_app_heads acc) ty in
      collect_app_heads (collect_app_heads acc v) body
  | EFix (_, _, bs, ty, body) ->
      let acc = List.fold_left collect_app_heads_binder acc bs in
      let acc = Option.fold ~none:acc ~some:(collect_app_heads acc) ty in
      collect_app_heads acc body
  | EIf (_, c, t, e) ->
      collect_app_heads (collect_app_heads (collect_app_heads acc c) t) e
  | EIfIs (_, c, pat, t, e) ->
      collect_app_heads (collect_app_heads (collect_app_heads (collect_app_heads acc c) pat) t) e
  | EMatch (_, ss, ret, brs) ->
      let acc =
        List.fold_left
          (fun a -> function ScrutExpr e | ScrutAs (e, _) -> collect_app_heads a e)
          acc ss
      in
      let acc = Option.fold ~none:acc ~some:(collect_app_heads acc) ret in
      List.fold_left
        (fun a br ->
          let a = List.fold_left (List.fold_left collect_app_heads) a br.br_alts in
          collect_app_heads a br.br_rhs)
        acc brs
  | ERecord (_, fs) ->
      List.fold_left
        (fun a -> function
          | RFld (_, _, e) -> collect_app_heads a e
          | RFldB (_, _, bs, e) ->
              collect_app_heads (List.fold_left collect_app_heads_binder a bs) e)
        acc fs
  | EMixfix (_, parts) ->
      List.fold_left (fun a -> function MStr _ -> a | MExpr e -> collect_app_heads a e) acc parts
  | EFupd (_, ms, a) -> collect_app_heads (List.fold_left collect_app_heads acc ms) a
  | EFupdw (_, ms, l, r) ->
      collect_app_heads (collect_app_heads (List.fold_left collect_app_heads acc ms) l) r
  | EStepUpd (_, ms, n, a) ->
      let acc = List.fold_left collect_app_heads acc ms in
      let acc = Option.fold ~none:acc ~some:(collect_app_heads acc) n in
      collect_app_heads acc a
  | EStepUpdw (_, ms, n, l, r) ->
      let acc = List.fold_left collect_app_heads acc ms in
      let acc = Option.fold ~none:acc ~some:(collect_app_heads acc) n in
      collect_app_heads (collect_app_heads acc l) r
  | EPointsTo (_, _, l, ms, r) ->
      let acc = collect_app_heads acc l in
      let acc =
        List.fold_left
          (fun a -> function
            | PmName e | PmDfrac e | PmOwn e -> collect_app_heads a e
            | PmPersistent -> a)
          acc ms
      in
      collect_app_heads acc r
  | EIndexed (_, _, n, l, r) ->
      let acc = collect_app_heads acc n in
      let acc = Option.fold ~none:acc ~some:(collect_app_heads acc) l in
      collect_app_heads acc r
  | EWp (_, e, at, post) ->
      let acc = collect_app_heads acc e in
      let acc =
        match at with
        | WpNone -> acc
        | WpAt (s, m) ->
            collect_app_heads (Option.fold ~none:acc ~some:(collect_app_heads acc) s) m
      in
      collect_app_heads acc post.wp_body
  | ETriple (_, pre, e, at, bs, ret, post) ->
      let acc = collect_app_heads (collect_app_heads acc pre) e in
      let acc =
        match at with
        | WpNone -> acc
        | WpAt (s, m) ->
            collect_app_heads (Option.fold ~none:acc ~some:(collect_app_heads acc) s) m
      in
      let acc = List.fold_left collect_app_heads_binder acc bs in
      collect_app_heads (collect_app_heads acc ret) post
  | EBigOp (_, _, _, _, cs, body) ->
      collect_app_heads (List.fold_left collect_app_heads acc cs) body
  | ESig (_, _, t, q) -> collect_app_heads (collect_app_heads acc t) q
  | _ -> acc

and collect_app_heads_binder acc b =
  let acc =
    match b.b_kind with
    | BPattern e -> collect_app_heads acc e
    | BGen (_, items) ->
        List.fold_left
          (fun a -> function
            | GenBangCast (_, _, e) | GenBang e | GenExpr e -> collect_app_heads a e)
          acc items
    | _ -> acc
  in
  Option.fold ~none:acc ~some:(collect_app_heads acc) b.b_ty

let fragment_vars ctx = function
  | EId (_, x) ->
      if
        (not (String.contains x '_'))
        && (not (is_ctor ctx x))
        && (not (is_std_type x))
        && global_ref ctx x = None
      then [ x ]
      else []
  | e ->
      let heads = collect_app_heads [] e in
      collect_sub_ids [] e
      |> List.filter (fun x ->
             (not (is_ctor ctx x))
             && (not (is_std_type x))
             && global_ref ctx x = None
             && not (List.mem x heads))
      |> List.sort_uniq String.compare

let module_kw_str = function
  | ModType -> "Module Type"
  | ModModule -> "Module"
  | ModSection -> "Section"

let rec draw_items_vars ctx b es =
  let var_or_term e =
    match e with
    | EId (_, x) when not (is_ctor ctx x) -> var_ b x
    | _ -> term ctx b e []
  in
  match es with
  | [] -> ()
  | [ e ] -> el b "span" (Some "arg") (fun _ -> var_or_term e)
  | e :: rest ->
      el b "span" (Some "arg") (fun _ -> var_or_term e);
      raw_char b ' ';
      draw_items_vars ctx b rest

let rec draw_alt_terms ctx b = function
  | [] -> ()
  | [ c ] -> draw_alt_term ctx b c
  | c :: rest ->
      draw_alt_term ctx b c;
      raw_char b ' ';
      el_raw b "span" (Some "op wide bar") "|";
      raw_char b ' ';
      draw_alt_terms ctx b rest

and draw_alt_term ctx b = function
  | EApp (_, EId (_, c), args) ->
      el_a b "span" (Some "c app") [ ("data-d", "args") ] (fun b ->
          el_text b "span" (Some "a") c;
          el b "span" (Some "args") (fun b -> draw_items_vars ctx b args))
  | e -> term ctx b e []

let rec draw_inline_fields ctx b = function
  | [] -> ()
  | f :: fs ->
      el b "span" (Some "arg") (fun b ->
          el_text b "span" (Some "f def") f.fd_name;
          opt_type ctx b f.fd_ty [];
          if fs <> [] then el_raw b "span" (Some "sep") ";");
      if fs <> [] then (
        raw_char b ' ';
        draw_inline_fields ctx b fs)

let rec draw_seq_bar ctx b = function
  | [] -> ()
  | [ c ] ->
      el_text b "span" (Some "a") c.c_name;
      binders_ ctx b c.c_binders [];
      opt_type ctx b c.c_ty []
  | c :: rest ->
      el_text b "span" (Some "a") c.c_name;
      binders_ ctx b c.c_binders [];
      opt_type ctx b c.c_ty [];
      raw_char b ' ';
      el_raw b "span" (Some "op wide bar") "|";
      raw_char b ' ';
      draw_seq_bar ctx b rest

let draw_sentence_inline ctx b = function
  | VThm (_, k, Some n, bs, ty) ->
      let env = Draw_tactic.binder_names_for_env ctx bs [] in
      kw b k;
      raw_char b ' ';
      el_text b "span" (Some "lem def") n.n_text;
      binders_ ctx b bs [];
      raw b nbsp;
      el_raw b "span" (Some "op wide colon") ":";
      raw_char b ' ';
      term ctx b ty env
  | VDef d ->
      let env = Draw_tactic.binder_names_for_env ctx d.d_binders [] in
      kw b d.d_kw;
      raw_char b ' ';
      el_text b "span" (Some "f def") d.d_name.n_text;
      binders_ ctx b d.d_binders [];
      opt_type ctx b d.d_ty env;
      Option.iter
        (fun body ->
          raw b nbsp;
          defeq b;
          raw_char b ' ';
          term ctx b body env)
        d.d_body
  | VModule (_, kind, n, bs, _) ->
      kw b (module_kw_str kind);
      raw_char b ' ';
      el_text b "span" (Some "module-name") n.n_text;
      binders_ ctx b bs []
  | VDecl (_, k, [ DeclTyped (ns, ty) ]) ->
      kw b k;
      raw_char b ' ';
      seq_defs b ns;
      opt_type ctx b (Some ty) []
  | VInd (_, k, [ ib ]) ->
      kw b k;
      raw_char b ' ';
      el_text b "span" (Some "ty def") ib.ib_name.n_text;
      binders_ ctx b ib.ib_binders [];
      opt_type ctx b ib.ib_ty [];
      raw b nbsp;
      defeq b;
      raw_char b ' ';
      draw_seq_bar ctx b ib.ib_ctors
  | VRec (_, k, n, bs, _, _, fs) ->
      kw b k;
      raw_char b ' ';
      el_text b "span" (Some "ty def") n.n_text;
      binders_ ctx b bs [];
      raw b nbsp;
      defeq b;
      raw_char b ' ';
      el b "span" (Some "c rec") (fun b ->
          el b "span" (Some "args recbr curly") (fun b -> draw_inline_fields ctx b fs))
  | VNotation (_, k, s, e, _) ->
      kw b k;
      raw_char b ' ';
      notation_pattern b s e;
      raw b nbsp;
      defeq b;
      raw_char b ' ';
      term ctx b e []
  | _ -> ()

let draw_fragment ctx b = function
  | FTerm e -> term ctx b e (fragment_vars ctx e)
  | FTyped (n, t) ->
      el_text b "span" (Some "f def") n.n_text;
      opt_type ctx b (Some t) []
  | FAlts (n, cs) ->
      el_text b "span" (Some "ty def") n.n_text;
      raw b nbsp;
      defeq b;
      raw_char b ' ';
      draw_alt_terms ctx b cs
  | FFields (n, fs) ->
      el_text b "span" (Some "ty def") n.n_text;
      raw b nbsp;
      defeq b;
      raw_char b ' ';
      el_a b "span" (Some "c rec") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args recbr curly") (fun b -> draw_inline_fields ctx b fs))
  | FSentence s -> draw_sentence_inline ctx b s
  | FContext _ -> ()

(* ── Prose href, concepts, Prolog refs, inline code ────────────────────── *)

let prose_href ctx url =
  let pre = ctx.corpus.concepts_prefix in
  if ctx.in_embedding then Concepts.concept_url ctx.corpus.concepts ~prefix:pre url
  else
    match ctx.file with
    | Some file
      when Filename.check_suffix file ".v"
           && (not (String.contains url ':'))
           && not (String.starts_with ~prefix:"#" url) ->
        let path, frag =
          match String.index_opt url '#' with
          | Some i -> (String.sub url 0 i, String.sub url i (String.length url - i))
          | None -> (url, "")
        in
        let dir0 = String.split_on_char '/' file in
        let dir_rev = match List.rev dir0 with _ :: tl -> tl | [] -> [] in
        let rev =
          List.fold_left
            (fun acc step ->
              if step = ".." then match acc with _ :: tl -> tl | [] -> []
              else if step = "." then acc
              else step :: acc)
            dir_rev
            (String.split_on_char '/' path)
        in
        let repo = List.rev rev in
        let rel =
          match repo with
          | [ "nanofil"; "docs"; d ] -> [ ".."; d ]
          | "nanofil" :: rest -> ".." :: ".." :: rest
          | _ -> ".." :: ".." :: ".." :: repo
        in
        let concept_url = String.concat "/" rel ^ frag in
        Concepts.concept_url ctx.corpus.concepts ~prefix:pre concept_url
    | _ -> url

let prolog_href ctx m n ds =
  match ctx.corpus.prolog_prefix with
  | None -> None
  | Some pre -> (
      match Hashtbl.find_opt ctx.corpus.prolog_preds n with
      | Some mods when List.mem m mods ->
          let frag = uri_encode_fragment (n ^ "/" ^ ds) in
          Some (Printf.sprintf "%s%s.html#%s" pre m frag)
      | _ -> None)

let prolog_ref ctx code =
  let m_opt, rest =
    match String.index_opt code ':' with
    | Some i when i > 0 ->
        (Some (String.sub code 0 i), String.sub code (i + 1) (String.length code - i - 1))
    | _ -> (None, code)
  in
  match String.index_opt rest '/' with
  | Some i when i > 0 && i + 1 < String.length rest -> (
      let w = String.sub rest 0 i in
      let ds = String.sub rest (i + 1) (String.length rest - i - 1) in
      let all_digits =
        let ok = ref true in
        String.iter (fun c -> if not (is_digit c) then ok := false) ds;
        !ok
      in
      if not all_digits then None
      else
        match m_opt with
        | Some m -> prolog_href ctx m w ds
        | None -> (
            match Hashtbl.find_opt ctx.corpus.prolog_preds w with
            | Some (m :: _) -> prolog_href ctx m w ds
            | _ -> None))
  | _ -> None

let has_csym_before_lparen s =
  let n = String.length s in
  let rec go i =
    if i + 1 >= n then false
    else if is_csym s.[i] && s.[i + 1] = '(' then true
    else go (i + 1)
  in
  go 0

let rq_kind ctx b id =
  match (Concepts.get ctx.corpus.concepts id).kind with
  | Some (k, _) ->
      let cls, label =
        match k with
        | Concepts.FilC -> ("kind kind-filc", "Fil-C")
        | Concepts.Iris -> ("kind kind-iris", "Iris")
        | Concepts.Nanofil -> ("kind kind-nanofil", "nanofil")
      in
      raw_char b ' ';
      el_text b "span" (Some cls) label
  | None -> ()

let rec concept_ref ctx b name shown =
  if not (Concepts.is_loaded ctx.corpus.concepts) then esc b shown
  else
    match Concepts.resolve ctx.corpus.concepts name with
    | Some id ->
        let href = ctx.corpus.concepts_prefix ^ Concepts.page id in
        let title = Concepts.title ctx.corpus.concepts id in
        let sum = Concepts.plain (Concepts.summary ctx.corpus.concepts id) in
        el b "span" (Some "pref cref") (fun b ->
            el_a b "a" (Some "concept") [ ("href", href) ] (fun b -> esc b shown);
            if not ctx.in_card then
              el_a b "span" (Some "sigcard concept-card") [ ("aria-hidden", "true") ] (fun b ->
                  el b "span" (Some "card-mod") (fun b ->
                      esc b title;
                      rq_kind ctx b id);
                  el b "span" (Some "card-text") (fun b ->
                      let prev_btn = ctx.in_button in
                      let prev_card = ctx.in_card in
                      ctx.in_card <- true;
                      ctx.in_button <- true;
                      Fun.protect
                        ~finally:(fun () ->
                          ctx.in_card <- prev_card;
                          ctx.in_button <- prev_btn)
                        (fun () -> rocq_prose_inline ctx b sum))))
    | None ->
        let f = Option.value ~default:"none" ctx.file in
        Printf.eprintf "dterm-rocq: %s: [[%s]] names no concept\n%!" f name;
        el_text b "span" (Some "broken") shown

and concept_embed ctx b name =
  if not (Concepts.is_loaded ctx.corpus.concepts) then el_text b "p" None name
  else if ctx.in_embedding then el b "p" None (fun b -> concept_ref ctx b name name)
  else
    match Concepts.resolve ctx.corpus.concepts name with
    | Some id ->
        let href = ctx.corpus.concepts_prefix ^ Concepts.page id in
        let title = Concepts.title ctx.corpus.concepts id in
        let lines = (Concepts.get ctx.corpus.concepts id).body in
        el b "aside" (Some "concept-embed") (fun b ->
            el_a b "a" (Some "concept-embed-title") [ ("href", href) ] (fun b ->
                esc b title;
                rq_kind ctx b id);
            let prev = ctx.in_embedding in
            ctx.in_embedding <- true;
            Fun.protect
              ~finally:(fun () -> ctx.in_embedding <- prev)
              (fun () -> rocq_prose ctx b lines))
    | None -> el b "p" None (fun b -> concept_ref ctx b name name)

and strip_c_prefix code =
  if String.starts_with ~prefix:"c:" code then
    let rest =
      if String.length code >= 3 && code.[2] = ' ' then
        String.sub code 3 (String.length code - 3)
      else String.sub code 2 (String.length code - 2)
    in
    if rest = "" then None else Some rest
  else None

and draw_code ctx b code =
  match strip_c_prefix code with
  | Some rest -> (
      match ctx.corpus.c_drawer with
      | Some cd -> (
          match cd.c_inline code with
          | Some html -> raw b html
          | None -> el_text b "code" None rest)
      | None -> el_text b "code" None rest)
  | None -> (
      let c_auto =
        match ctx.corpus.c_drawer with
        | Some cd -> cd.c_inline_auto code
        | None -> None
      in
      match c_auto with
      | Some html -> raw b html
      | None -> (
          match prolog_ref ctx code with
          | Some href ->
              el_a b "a" (Some "ref pl") [ ("href", href) ] (fun b -> el_text b "code" None code)
          | None ->
              if has_csym_before_lparen code then el_text b "code" None code
              else if (not (String.contains code ' ')) && String.contains code '/' then
                el_text b "code" None code
              else
                match Parse_vernac.parse_fragment ~ops:ctx.ops code with
                | Some (FContext _) | None -> el_text b "code" None code
                | Some frag -> el b "code" (Some "term rq") (fun b -> draw_fragment ctx b frag)))

and rocq_prose_inline ctx b text =
  let n = String.length text in
  let rec scan_bracketed j depth =
    if j >= n || text.[j] = '\n' then None
    else if text.[j] = ']' then if depth = 1 then Some j else scan_bracketed (j + 1) (depth - 1)
    else if text.[j] = '[' then scan_bracketed (j + 1) (depth + 1)
    else scan_bracketed (j + 1) depth
  in
  let rec go i =
    if i >= n then ()
    else
      match text.[i] with
      | '[' when i + 1 < n && text.[i + 1] = '[' -> (
          match Concepts.parse_link_after_open text (i + 2) with
          | Some (name, shown, next_i) ->
              concept_ref ctx b name shown;
              go next_i
          | None -> go_bracket i)
      | '[' -> go_bracket i
      | '`' -> (
          match String.index_from_opt text (i + 1) '`' with
          | Some k ->
              draw_code ctx b (String.sub text (i + 1) (k - i - 1));
              go (k + 1)
          | None ->
              raw_char b '`';
              go (i + 1))
      | c when is_csym c ->
          let j = ref (i + 1) in
          while !j < n && is_csym text.[!j] do
            incr j
          done;
          let w = String.sub text i (!j - i) in
          handle_word w !j
      | c ->
          esc_char b c;
          go (i + 1)
  and go_bracket i =
    let md_link =
      match String.index_from_opt text (i + 1) ']' with
      | Some rb when rb + 1 < n && text.[rb + 1] = '(' -> (
          match String.index_from_opt text (rb + 2) ')' with
          | Some rp ->
              let u = String.sub text (rb + 2) (rp - rb - 2) in
              if not (String.contains u ' ') then
                Some (String.sub text (i + 1) (rb - i - 1), u, rp + 1)
              else None
          | None -> None)
      | _ -> None
    in
    match md_link with
    | Some (ts, u, next_i) ->
        let href = prose_href ctx u in
        el_a b "a" None [ ("href", href) ] (fun b -> rocq_prose_inline ctx b ts);
        go next_i
    | None -> (
        match scan_bracketed (i + 1) 1 with
        | Some rb ->
            draw_code ctx b (String.sub text (i + 1) (rb - i - 1));
            go (rb + 1)
        | None ->
            raw_char b '[';
            go (i + 1))
  and handle_word w j =
    let try_mod_pred () =
      if j < n && text.[j] = ':' then
        let k = ref (j + 1) in
        while !k < n && is_csym text.[!k] do
          incr k
        done;
        if !k > j + 1 && !k < n && text.[!k] = '/' then (
          let d = ref (!k + 1) in
          while !d < n && is_digit text.[!d] do
            incr d
          done;
          if !d > !k + 1 then
            let pred = String.sub text (j + 1) (!k - j - 1) in
            let ds = String.sub text (!k + 1) (!d - !k - 1) in
            match prolog_href ctx w pred ds with
            | Some href ->
                let shown = Printf.sprintf "%s:%s/%s" w pred ds in
                el_a b "a" (Some "ref pl") [ ("href", href) ] (fun b ->
                    el_text b "code" None shown);
                Some !d
            | None -> None
          else None)
        else None
      else None
    in
    let try_bare_pred () =
      if j < n && text.[j] = '/' then
        let d = ref (j + 1) in
        while !d < n && is_digit text.[!d] do
          incr d
        done;
        if !d > j + 1 then
          let ds = String.sub text (j + 1) (!d - j - 1) in
          match Hashtbl.find_opt ctx.corpus.prolog_preds w with
          | Some (m :: _) -> (
              match prolog_href ctx m w ds with
              | Some href ->
                  let shown = Printf.sprintf "%s/%s" w ds in
                  el_a b "a" (Some "ref pl") [ ("href", href) ] (fun b ->
                      el_text b "code" None shown);
                  Some !d
              | None -> None)
          | _ -> None
        else None
      else None
    in
    let try_pl_file () =
      if
        j + 3 <= n
        && text.[j] = '.'
        && text.[j + 1] = 'p'
        && text.[j + 2] = 'l'
        && (j + 3 = n || not (is_csym text.[j + 3]))
        && Hashtbl.mem ctx.corpus.prolog_mods w
      then
        match ctx.corpus.prolog_prefix with
        | Some pre ->
            let href = pre ^ w ^ ".html" in
            el_a b "a" (Some "ref pl") [ ("href", href) ] (fun b ->
                esc b w;
                raw b ".pl");
            Some (j + 3)
        | None -> None
      else None
    in
    match try_mod_pred () with
    | Some next_i -> go next_i
    | None -> (
        match try_bare_pred () with
        | Some next_i -> go next_i
        | None -> (
            match try_pl_file () with
            | Some next_i -> go next_i
            | None ->
                esc b w;
                go j))
  in
  go 0

and rocq_fence ctx b lines =
  let text = String.concat "\n" lines in
  let parsed =
    match Parse_vernac.parse_string text with
    | exception Lexer.Lex_error _ -> None
    | pf ->
        if List.exists (function ISent (VRaw _) -> true | _ -> false) pf.items then None
        else Some pf
  in
  match parsed with
  | Some pf ->
      let notes = List.map (note_kind text) pf.comments in
      let sub_ctx =
        make_ctx ~corpus:ctx.corpus ~page:None ~file:None ~text ~notes ~ops:pf.ops ~folds:pf.folds
      in
      el b "div" (Some "dterm-rocq rq-fence") (fun b -> rocq_items sub_ctx b pf.items)
  | None -> el_text b "pre" (Some "fence lang-rocq") text

and draw_block ctx b = function
  | Markdown.P t -> el b "p" None (fun b -> rocq_prose_inline ctx b t)
  | Markdown.Ul items ->
      el b "ul" None (fun b ->
          List.iter (fun t -> el b "li" None (fun b -> rocq_prose_inline ctx b t)) items)
  | Markdown.Pre lines ->
      let t = String.concat "\n" (Markdown.dedent lines) in
      el_text b "pre" None t
  | Markdown.H (n, t) ->
      el b (Printf.sprintf "h%d" n) (Some "prose-h") (fun b -> rocq_prose_inline ctx b t)
  | Markdown.Table (head, rows) ->
      el b "table" (Some "prose-table") (fun b ->
          el b "thead" None (fun b ->
              el b "tr" None (fun b ->
                  List.iter (fun c -> el b "th" None (fun b -> rocq_prose_inline ctx b c)) head));
          el b "tbody" None (fun b ->
              List.iter
                (fun r ->
                  el b "tr" None (fun b ->
                      List.iter
                        (fun c -> el b "td" None (fun b -> rocq_prose_inline ctx b c))
                        r))
                rows))
  | Markdown.Embed name -> concept_embed ctx b name
  | Markdown.Fence (("rocq" | "coq" | ""), lines) -> rocq_fence ctx b lines
  | Markdown.Fence ("c", lines) -> (
      match ctx.corpus.c_drawer with
      | Some cd -> (
          let seq = ctx.c_fence_seq + 1 in
          match cd.c_fence ~seq lines with
          | Some html ->
              ctx.c_fence_seq <- seq;
              raw b html
          | None -> el_text b "pre" (Some "fence") (String.concat "\n" lines))
      | None -> el_text b "pre" (Some "fence") (String.concat "\n" lines))
  | Markdown.Fence (_, lines) -> el_text b "pre" (Some "fence") (String.concat "\n" lines)

and rocq_prose ctx b lines0 =
  let bs = Markdown.blocks (Markdown.dedent lines0) in
  el b "div" (Some "prose") (fun b -> List.iter (draw_block ctx b) bs)

(* ── Comment consumption: notes_before, notes_rows, aside_after ────────── *)

let draw_note ctx b (nt : note) =
  match comment_heading nt.nt_text with
  | Some (level, title) ->
      let id = heading_id title in
      let h = Printf.sprintf "h%d" level in
      let rest =
        match comment_prose_lines nt.nt_text with _ :: tl -> tl | [] -> []
      in
      el_a b h (Some "rq-sec") [ ("id", id) ] (fun b -> rocq_prose_inline ctx b title);
      if List.exists (fun l -> not (Markdown.is_blank l)) rest then
        el b "div" (Some "rq-doc") (fun b -> rocq_prose ctx b rest)
  | None ->
      let lines = comment_prose_lines nt.nt_text in
      if String.starts_with ~prefix:"(**" nt.nt_text then
        el b "div" (Some "rq-doc") (fun b -> rocq_prose ctx b lines)
      else el b "div" (Some "note") (fun b -> rocq_prose ctx b lines)

let take_notes_before ctx off =
  let now, later = List.partition (fun nt -> nt.nt_lo < off) ctx.notes in
  ctx.notes <- later;
  now

let notes_before ctx b off =
  List.iter (draw_note ctx b) (take_notes_before ctx off)

let notes_rows ctx b off cols =
  let cols_s = string_of_int cols in
  List.iter
    (fun nt ->
      el b "tr" (Some "note") (fun b ->
          el_a b "td" None [ ("colspan", cols_s) ] (fun b -> draw_note ctx b nt)))
    (take_notes_before ctx off)

let aside_text ctx to_ =
  match ctx.notes with
  | nt :: rest when nt.nt_kind = Trailing && nt.nt_lo >= to_ ->
      let gap = String.sub ctx.text to_ (nt.nt_lo - to_) in
      if (not (String.contains gap '\n')) && not (String.contains gap '|') then (
        ctx.notes <- rest;
        Some (String.concat " " (comment_prose_lines nt.nt_text)))
      else None
  | _ -> None

let rec aside_after ctx b to_ =
  match aside_text ctx to_ with
  | Some s ->
      el b "span" (Some "aside") (fun b -> rocq_prose_inline ctx b s);
      aside_after ctx b to_
  | None -> ()

let rocq_layout b =
  el_a b "div" (Some "rq-layout") [ ("hidden", "hidden") ] (fun b ->
      el_a b "label" None [ ("for", "rq-layout") ] (fun b -> raw b "Rocq layout");
      el_a b "select" None [ ("id", "rq-layout") ] (fun b ->
          el_a b "option" None [ ("value", "auto") ] (fun b -> raw b "Adaptive");
          el_a b "option" None [ ("value", "stack") ] (fun b -> raw b "Stacked");
          el_a b "option" None [ ("value", "table") ] (fun b -> raw b "Side by side")))

let () =
  Draw_hooks.notes_before_ref := notes_before;
  Draw_hooks.notes_rows_ref := notes_rows;
  Draw_hooks.aside_after_ref := aside_after;
  Draw_hooks.aside_text_ref := aside_text;
  Draw_hooks.draw_prose_inline_ref := rocq_prose_inline;
  Draw_hooks.draw_prose_ref := rocq_prose;
  Draw_hooks.draw_rocq_layout_ref := rocq_layout
