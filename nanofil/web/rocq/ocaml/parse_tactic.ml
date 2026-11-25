(* Ltac, intro-pattern, and Iris Proof Mode tactic parser. *)

open Ast
open Parser_core
open Parse_term

let is_tactic_token = function
  | P (";" | "(" | ")" | "[" | "]") | Sym ("|" | "=>" | "||" | ".." | ".") | Kw "end" ->
      false
  | _ -> true

let is_tactic_prefix = function
  | "try" | "repeat" | "progress" | "now" | "once" | "timeout" -> true
  | _ -> false

let parse_tactic_params p =
  let rec loop acc =
    match try_ p parse_name with
    | Some n -> loop (n :: acc)
    | None -> List.rev acc
  in
  loop []

let parse_tactic_notation_parts p =
  let rec loop acc =
    match peek_kind p with
    | Some (Str s) ->
        ignore (bump p);
        loop (TnpLit s :: acc)
    | Some (Id k) -> (
        match
          try_ p (fun p ->
              ignore (bump p);
              ignore (eat_p p "(");
              let n = parse_name p in
              ignore (eat_p p ")");
              TnpArg (k, n))
        with
        | Some part -> loop (part :: acc)
        | None -> List.rev acc)
    | _ -> List.rev acc
  in
  loop []

let rec intro_patterns p =
  let rec loop acc =
    match try_ p intro_pattern with
    | Some pat -> loop (pat :: acc)
    | None -> List.rev acc
  in
  loop []

and intro_pattern p =
  match peek p with
  | None -> raise Fail
  | Some t0 -> (
      match t0.kind with
      | P "[" when peek2_kind p = Some (P "[", Sym "=") ->
          ignore (bump p);
          ignore (bump p);
          let ps = intro_patterns p in
          ignore (eat_p p "]");
          IpInj ps
      | P "[" ->
          ignore (bump p);
          let arms = intro_arms p in
          ignore (eat_p p "]");
          IpOr arms
      | P "(" ->
          ignore (bump p);
          let p0 = intro_pattern p in
          let ps = intro_pairs p in
          ignore (eat_p p ")");
          IpAnd (p0 :: ps)
      | Sym "?"
        when p.pos + 1 < p.len && p.toks.(p.pos + 1).lo = t0.hi -> (
          match p.toks.(p.pos + 1).kind with
          | Id x ->
              ignore (bump p);
              let t1 = bump p in
              IpFresh { n_span = { lo = t1.lo; hi = t1.hi }; n_text = x }
          | _ ->
              ignore (bump p);
              IpAuto "?")
      | Sym (("->" | "<-") as op) ->
          ignore (bump p);
          IpRewrite op
      | Sym (("?" | "*" | "**") as k) ->
          ignore (bump p);
          IpAuto k
      | Id _ ->
          let n = parse_name_or_hole p in
          (match n.n_text with
          | "eqn" | "using" | "by" | "until" -> raise Fail
          | _ -> IpName n)
      | _ -> raise Fail)

and intro_arms p =
  let ps = intro_patterns p in
  match peek_kind p with
  | Some (Sym "|") ->
      ignore (bump p);
      ps :: intro_arms p
  | _ -> [ ps ]

and intro_pairs p =
  match peek_kind p with
  | Some (Sym "&") ->
      ignore (bump p);
      let pat = intro_pattern p in
      pat :: intro_pairs p
  | _ -> []

let ipm_pat p =
  match peek_kind p with
  | Some (Str s) ->
      ignore (bump p);
      IpmPatStr s
  | Some (Sym "%") ->
      ignore (bump p);
      IpmPatPure (intro_pattern p)
  | Some (Sym "%->") ->
      ignore (bump p);
      IpmPatPure (IpRewrite "->")
  | Some (Sym "%<-") ->
      ignore (bump p);
      IpmPatPure (IpRewrite "<-")
  | _ -> raise Fail

let ipm_intro_items p =
  let rec loop acc =
    match
      try_ p (fun p ->
          ignore (eat_p p "(");
          let ps = intro_patterns p in
          ignore (eat_p p ")");
          IpmCoq ps)
    with
    | Some it -> loop (it :: acc)
    | None -> (
        match peek_kind p with
        | Some (Str s) ->
            ignore (bump p);
            loop (IpmStr s :: acc)
        | _ -> List.rev acc)
  in
  loop []

let tactic_name p =
  match peek_kind p with
  | Some (Id n) ->
      ignore (bump p);
      n
  | Some (Kw (("exists" | "fix" | "cofix") as n)) ->
      ignore (bump p);
      n
  | _ -> raise Fail

let parse_tactic_selector p =
  match peek_kind p with
  | Some (Id "all") ->
      ignore (bump p);
      "all"
  | Some (Num n) ->
      ignore (bump p);
      let rec more acc =
        match peek2_kind p with
        | Some (P ",", Num m) ->
            ignore (bump p);
            ignore (bump p);
            more (m :: acc)
        | _ -> String.concat "," (List.rev acc)
      in
      more [ n ]
  | _ -> raise Fail

let parse_tactic_clause p =
  match peek_kind p with
  | Some (Kw "in") ->
      ignore (bump p);
      "in"
  | Some (Kw "with") ->
      ignore (bump p);
      "with"
  | Some (Id "using") ->
      ignore (bump p);
      "using"
  | Some (Id "eqn") when peek2_kind p = Some (Id "eqn", Sym ":") ->
      ignore (bump p);
      ignore (bump p);
      "eqn"
  | _ -> raise Fail

let peek_tactic_clause p =
  match peek_kind p with
  | Some (Kw "in" | Kw "with" | Id "using" | Kw "as" | Id "by") -> true
  | Some (Id "eqn") -> peek2_kind p = Some (Id "eqn", Sym ":")
  | _ -> false

let ipm_head p =
  match peek_kind p with
  | Some (Str s) ->
      ignore (bump p);
      IpmHyp s
  | _ -> IpmExpr (term p)

let ipm_args p =
  let rec loop acc =
    if starts_atom p then loop (atom p :: acc) else List.rev acc
  in
  loop []

let rec tactic p =
  let l = tactic_choice p in
  tactic_then p l

and tactic_choice p =
  let l = tactic_unit p in
  match peek_kind p with
  | Some (Sym "||") ->
      ignore (bump p);
      TBin ("||", l, tactic_choice p)
  | _ -> l

and tactic_then p l =
  match peek_kind p with
  | Some (P ";") ->
      ignore (bump p);
      let next =
        match peek_kind p with
        | Some (P "[") ->
            ignore (bump p);
            let ts = tactic_choices p in
            ignore (eat_p p "]");
            TDispatch (l, ts)
        | _ -> TBin (";", l, tactic_choice p)
      in
      tactic_then p next
  | _ -> l

(* Reproduces Prolog's non-deterministic upto_in(Ts), { phrase(tactic(V), Ts) }, tk(kw(in)). *)
and parse_tactic_upto_in p =
  let start = p.pos in
  let rec find_in i =
    if i >= p.len then raise Fail
    else if p.toks.(i).kind = Kw "in" then
      let sub = clone_sub_state p start i in
      match tactic sub with
      | v when at_end sub ->
          p.pos <- i + 1;
          v
      | _ -> find_in (i + 1)
      | exception Fail -> find_in (i + 1)
    else find_in (i + 1)
  in
  find_in start

and tactic_unit p =
  match peek_kind p with
  | Some (Kw "let") -> (
      ignore (bump p);
      match peek_kind p with
      | Some (Id "rec") ->
          ignore (bump p);
          let n = parse_name p in
          let args = parse_tactic_params p in
          ignore (eat_sym p ":=");
          let v = parse_tactic_upto_in p in
          let b = tactic p in
          TLetRec (n, args, v, b)
      | _ ->
          let n = parse_name_or_hole p in
          ignore (eat_sym p ":=");
          let v = parse_tactic_upto_in p in
          let b = tactic p in
          TLet (n, v, b))
  | Some (Id "eval") ->
      ignore (bump p);
      let ws = parse_eval_words p in
      ignore (eat_kw p "in");
      TEval (ws, term p)
  | Some (Id "do") -> (
      ignore (bump p);
      let t = bump p in
      let n = match t.kind with Num s | Id s -> s | _ -> raise Fail in
      TDo (n, tactic_unit p))
  | Some (Id "by") ->
      ignore (bump p);
      TPrefix ("by", tactic p)
  | Some (Id k) when is_tactic_prefix k ->
      ignore (bump p);
      TPrefix (k, tactic_unit p)
  | Some (Id (("first" | "solve") as k)) when peek2_kind p = Some (Id k, P "[") ->
      ignore (bump p);
      ignore (bump p);
      let ts = tactic_choices p in
      ignore (eat_p p "]");
      TChoices (k, ts)
  | Some (Kw "match" | Id ("lazymatch" | "multimatch")) ->
      let k =
        match (bump p).kind with
        | Kw "match" -> "match"
        | Id k -> k
        | _ -> assert false
      in
      let subj = tactic_subject p in
      ignore (eat_kw p "with");
      if peek_kind p = Some (Sym "|") then ignore (bump p);
      let bs = tactic_branches p in
      ignore (eat_kw p "end");
      TMatch (k, subj, bs)
  | Some (P "(") ->
      ignore (bump p);
      let t = tactic p in
      ignore (eat_p p ")");
      TGroup t
  | _ -> (
      (* Try goal selector `all:` or `1,2:` before regular tactic calls. *)
      match
        try_ p (fun p ->
            let s = parse_tactic_selector p in
            ignore (eat_sym p ":");
            TSelect (s, tactic p))
      with
      | Some sel -> sel
      | None -> tactic_call p)

and tactic_call p =
  first p
    [
      (fun p ->
        ignore (eat_id p "call_spec");
        ignore (eat_kw p "with");
        let x = atom p in
        TCall ("call_spec", [ TPClause ("with", [ TPTerm x ]) ]));
      (fun p ->
        ignore (eat_id p "iEval");
        ignore (eat_p p "(");
        let t = tactic p in
        ignore (eat_p p ")");
        let ps = tactic_parts p in
        TCall ("iEval", TPTactic t :: ps));
      (fun p ->
        ignore (eat_id p "iIntros");
        let is = ipm_intro_items p in
        if is = [] then raise Fail;
        TCall ("iIntros", [ TPIpmIntros is ]));
      (fun p ->
        let n = tactic_name p in
        (match n with "exists" | "eexists" | "iExists" -> () | _ -> raise Fail);
        let e = term p in
        let rec witnesses acc =
          match peek_kind p with
          | Some (P ",") ->
              ignore (bump p);
              witnesses (term p :: acc)
          | _ -> List.rev acc
        in
        let es = witnesses [] in
        if starts_atom p then raise Fail;
        TCall (n, [ TPTerms (e :: es) ]));
      (fun p ->
        let n = tactic_name p in
        (match n with "intro" | "intros" -> () | _ -> raise Fail);
        let ps = intro_patterns p in
        if ps = [] then raise Fail;
        let rest = tactic_parts p in
        TCall (n, TPIntro ps :: rest));
      (fun p ->
        let n = tactic_name p in
        let ps = tactic_parts p in
        TCall (n, ps));
    ]

and tactic_subject p =
  match peek_kind p with
  | Some (Id "goal") ->
      ignore (bump p);
      TSubGoal
  | Some (Id "type") when peek2_kind p = Some (Id "type", Id "of") ->
      ignore (bump p);
      ignore (bump p);
      TSubType (term p)
  | _ -> TSubTerm (term p)

and tactic_choices p =
  let item =
    match try_ p tactic with
    | Some t0 -> (
        match peek_kind p with
        | Some (Sym "..") ->
            ignore (bump p);
            TRest t0
        | _ -> t0)
    | None -> TEmpty
  in
  match peek_kind p with
  | Some (Sym "|") ->
      ignore (bump p);
      item :: tactic_choices p
  | _ -> [ item ]

and tactic_branches p =
  let pats = tactic_match_pattern p in
  ignore (eat_sym p "=>");
  let rhs = tactic p in
  let br = { tbr_pats = pats; tbr_rhs = rhs } in
  match peek_kind p with
  | Some (Sym "|") ->
      ignore (bump p);
      br :: tactic_branches p
  | _ -> [ br ]

and tactic_match_pattern p =
  first p
    [
      (fun p ->
        ignore (eat_p p "[");
        let ps = tactic_match_pattern p in
        ignore (eat_p p "]");
        [ TPGroup ("[", ps, "]") ]);
      (fun p ->
        ignore (eat_id p "context");
        ignore (eat_p p "[");
        let e = term p in
        ignore (eat_p p "]");
        [ TPContext e ]);
      (fun p ->
        let n = parse_name p in
        ignore (eat_sym p ":");
        let hyp = tactic_match_type p n in
        match peek_kind p with
        | Some (P ",") ->
            ignore (bump p);
            hyp :: TPToken (P ",") :: tactic_match_pattern p
        | Some (Sym "|-") ->
            ignore (bump p);
            [ hyp; TPToken (Sym "|-"); tactic_goal_pattern p ]
        | _ -> raise Fail);
      (fun p ->
        ignore (eat_sym p "|-");
        [ TPToken (Sym "|-"); tactic_goal_pattern p ]);
      (fun p -> [ TPTerm (term p) ]);
    ]

and tactic_goal_pattern p =
  match peek2_kind p with
  | Some (Id "context", P "[") ->
      ignore (bump p);
      ignore (bump p);
      let e = term p in
      ignore (eat_p p "]");
      TPContext e
  | _ -> TPTerm (term p)

and tactic_match_type p n =
  match peek2_kind p with
  | Some (Id "context", P "[") ->
      ignore (bump p);
      ignore (bump p);
      let e = term p in
      ignore (eat_p p "]");
      TPHypCtx (n, e)
  | _ -> TPHypExpr (n, term p)

and tactic_parts p =
  let rec loop acc =
    match try_ p tactic_part with
    | Some part -> loop (part :: acc)
    | None -> List.rev acc
  in
  loop []

and tactic_part p =
  first p
    [
      (fun p ->
        ignore (eat_kw p "as");
        let ps =
          match
            try_ p (fun p ->
                ignore (eat_p p "(");
                let ps = intro_patterns p in
                ignore (eat_p p ")");
                ps)
          with
          | Some ps -> ps
          | None -> []
        in
        let pat = ipm_pat p in
        TPClause ("as", [ TPIpmAs (ps, pat) ]));
      (fun p ->
        ignore (eat_kw p "as");
        let ps = intro_patterns p in
        if ps = [] then raise Fail;
        TPClause ("as", [ TPIntro ps ]));
      (fun p ->
        ignore (eat_id p "by");
        TPClause ("by", [ TPTactic (tactic_unit p) ]));
      (fun p ->
        let k = parse_tactic_clause p in
        let ps = tactic_arguments p in
        if ps = [] then raise Fail;
        TPClause (k, ps));
      tactic_argument;
    ]

and tactic_arguments p =
  let rec loop acc =
    if peek_tactic_clause p then List.rev acc
    else
      match try_ p tactic_argument with
      | Some arg -> loop (arg :: acc)
      | None -> List.rev acc
  in
  loop []

and tactic_argument p =
  first p
    [
      (fun p ->
        ignore (eat_p p "(");
        let h = ipm_head p in
        let args =
          match peek_kind p with
          | Some (Sym "$!") ->
              ignore (bump p);
              ipm_args p
          | _ -> []
        in
        let spat =
          match peek_kind p with
          | Some (Kw "with") ->
              ignore (bump p);
              let s, _ = eat_str p in
              Some s
          | _ -> None
        in
        ignore (eat_p p ")");
        let ok =
          (match h with IpmHyp _ -> true | IpmExpr _ -> false)
          || args <> [] || spat <> None
        in
        if not ok then raise Fail;
        TPIpm (h, args, spat));
      (fun p ->
        ignore (eat_p p "(");
        let n = parse_name p in
        let op =
          match peek_kind p with
          | Some (Sym ((":=" | ":") as op)) ->
              ignore (bump p);
              op
          | _ -> raise Fail
        in
        let e = term p in
        ignore (eat_p p ")");
        TPBinding (n, op, e));
      (fun p ->
        if peek_kind p <> Some (P "(") then raise Fail;
        TPTerm (atom p));
      (fun p ->
        match peek p with
        | Some t0
          when t0.kind = Sym "?" && p.pos + 1 < p.len && p.toks.(p.pos + 1).lo = t0.hi -> (
            match p.toks.(p.pos + 1).kind with
            | Id x ->
                ignore (bump p);
                let t1 = bump p in
                TPTerm (EMeta ({ lo = t0.lo; hi = t1.hi }, x))
            | _ -> raise Fail)
        | _ -> raise Fail);
      (fun p ->
        match peek p with
        | Some t0
          when (match t0.kind with Num _ | Id _ -> true | _ -> false)
               && p.pos + 1 < p.len
               && p.toks.(p.pos + 1).kind = Sym "%"
               && p.toks.(p.pos + 1).lo = t0.hi ->
            TPTerm (atom p)
        | _ -> raise Fail);
      (fun p ->
        ignore (eat_id p "context");
        ignore (eat_p p "[");
        let e = term p in
        ignore (eat_p p "]");
        TPContext e);
      (fun p ->
        match peek_kind p with
        | Some (P open_d) -> (
            match matching_delim open_d with
            | Some close_d ->
                ignore (bump p);
                let ps = tactic_pattern p in
                ignore (eat_p p close_d);
                TPGroup (open_d, ps, close_d)
            | None -> raise Fail)
        | _ -> raise Fail);
      (fun p ->
        ignore (eat_p p "(");
        let t = tactic p in
        ignore (eat_p p ")");
        TPTactic t);
      (fun p ->
        let t = bump p in
        if not (is_tactic_token t.kind) then raise Fail;
        TPToken t.kind);
    ]

and tactic_pattern p =
  let rec loop acc =
    match try_ p tactic_part with
    | Some part -> loop (part :: acc)
    | None -> (
        match peek_kind p with
        | Some (Sym "|") ->
            ignore (bump p);
            loop (TPToken (Sym "|") :: acc)
        | _ -> List.rev acc)
  in
  loop []

let () = parse_tactic_ref := tactic

let parse_tactic_tokens ~ops (toks : token list) : tactic option =
  let p = make_state ~ops (Array.of_list toks) in
  match tactic p with
  | t when at_end p -> Some t
  | _ -> None
  | exception Fail -> None
