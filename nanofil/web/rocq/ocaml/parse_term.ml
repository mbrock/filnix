(* Recursive-descent + Pratt expression parser for Gallina, Iris,
   FrameNotation, IRNotation, and cap_* fixtures. *)

open Ast
open Parser_core

let is_big_op = function "∗" | "∧" | "∨" | "+" -> true | _ -> false
let is_iris_modality = function "pers" | "affine" | "absorb" | "subj" | "obj" -> true | _ -> false
let is_chain_op = function "<" | "<=" | "≤" -> true | _ -> false

let rec parse_names p =
  let n = parse_name_or_hole p in
  match peek_kind p with
  | Some (P ",") ->
      ignore (bump p);
      n :: parse_names p
  | _ -> (
      match try_ p parse_names with
      | Some rest -> n :: rest
      | None -> [ n ])

let parse_names0 p =
  match try_ p parse_names with Some ns -> ns | None -> []

let starts_atom p =
  match peek_kind p with
  | None -> false
  | Some k -> (
      if k = Sym "@" && p.no_at then false
      else if k = Id "is" && p.in_if then false
      else
        match k with
        | Id x -> not (is_op_word x)
        | Sym ".." -> p.in_notation_rhs
        | Num _ | Str _ | P "(" | P "[" | P "{|" | Kw "match" | Sym "@" | Sym "?" -> true
        | Sym ("⌜" | "⊤" | "∅" | "#") -> true
        | _ -> false)

let op_token = function
  | Sym op -> Some op
  | Id w when is_op_word w -> Some w
  | _ -> None

let eat_forall_kw p =
  match peek_kind p with
  | Some (Kw "forall") | Some (Sym "∀") -> (bump p).lo
  | _ -> raise Fail

let eat_exists_kw p =
  match peek_kind p with
  | Some (Kw "exists") | Some (Sym "∃") -> (bump p).lo
  | _ -> raise Fail

let eat_fun_kw p =
  match peek_kind p with
  | Some (Kw "fun") | Some (Id "λ") -> (bump p).lo
  | _ -> raise Fail

let eat_arrow_kw p =
  match peek_kind p with
  | Some (Sym "=>") | Some (Sym "⇒") -> ignore (bump p)
  | _ -> raise Fail

let parse_eval_words p =
  let rec loop acc =
    match peek_kind p with
    | Some (Kw "in") -> List.rev acc
    | Some _ ->
        let t = bump p in
        loop (tok_text t.kind :: acc)
    | None -> raise Fail
  in
  loop []

(* ── Mutually recursive term / binder / custom-DSL grammar ─────────────── *)

let rec term p = expr p ~max:200

and opt_type p =
  match peek_kind p with
  | Some (Sym ":") ->
      ignore (bump p);
      Some (term p)
  | _ -> None

and expr p ~max =
  let l0 = operand p in
  let l = as_pat p l0 in
  op_rest p ~max l

and as_pat p e =
  if p.in_pattern then
    match peek_kind p with
    | Some (Kw "as") ->
        ignore (bump p);
        let n = parse_name p in
        EAsPat ({ lo = (expr_span e).lo; hi = n.n_span.hi }, e, n)
    | _ -> e
  else e

and operand p =
  match try_ p binder_form with
  | Some e -> e
  | None -> (
      match try_ p iris_operand with
      | Some e -> e
      | None -> (
          match peek2_kind p with
          | Some (Sym "▷", Sym "^") ->
              let t0 = bump p in
              ignore (bump p);
              let n = atom p in
              let a = expr p ~max:20 in
              ELaterN ({ lo = t0.lo; hi = (expr_span a).hi }, n, a)
          | _ -> (
              match peek_kind p with
              | Some (Sym op) -> (
                  match prefix_op op with
                  | Some lv ->
                      let t0 = bump p in
                      let a = if lv < 10 then tight p else expr p ~max:lv in
                      EPre ({ lo = t0.lo; hi = (expr_span a).hi }, op, a)
                  | None -> app p)
              | _ -> app p)))

and tight p =
  match peek_kind p with
  | Some (Sym op) -> (
      match prefix_op op with
      | Some lv when lv < 10 ->
          let t0 = bump p in
          let a = tight p in
          EPre ({ lo = t0.lo; hi = (expr_span a).hi }, op, a)
      | _ -> atom p)
  | _ -> atom p

(* ── Iris operands ─────────────────────────────────────────────────────── *)

and iris_operand p =
  match peek_kind p with
  | Some (Sym "|=") -> (
      let t0 = bump p in
      ignore (eat_p p "{");
      let ms = masks p in
      ignore (eat_p p "}");
      match peek_kind p with
      | Some (Sym "▷") ->
          ignore (bump p);
          let n = step_arrow p "=>" in
          let a = expr p ~max:200 in
          EStepUpd ({ lo = t0.lo; hi = (expr_span a).hi }, ms, n, a)
      | _ ->
          ignore (eat_sym p "=>");
          let a = expr p ~max:200 in
          EFupd ({ lo = t0.lo; hi = (expr_span a).hi }, ms, a))
  | Some (Sym "<") ->
      let t0 = bump p in
      let k, _ = eat_any_id p in
      if not (is_iris_modality k) then raise Fail;
      ignore (eat_sym p ">");
      let a = expr p ~max:20 in
      EPre ({ lo = t0.lo; hi = (expr_span a).hi }, "<" ^ k ^ ">", a)
  | Some (Sym "✓") -> (
      match peek2_kind p with
      | Some (Sym "✓", P "{") ->
          let t0 = bump p in
          ignore (bump p);
          let n = term p in
          ignore (eat_p p "}");
          let a = expr p ~max:20 in
          EIndexed ({ lo = t0.lo; hi = (expr_span a).hi }, "✓", n, None, a)
      | _ -> raise Fail)
  | Some (Id "WP") ->
      let t0 = bump p in
      let e = wp_expr p in
      let at = wp_at p in
      let post, hi = wp_post p in
      EWp ({ lo = t0.lo; hi }, e, at, post)
  | Some (P "{") ->
      let t0 = eat_p p "{" in
      ignore (eat_p p "{");
      ignore (eat_p p "{");
      let pre = term p in
      ignore (eat_p p "}");
      ignore (eat_p p "}");
      ignore (eat_p p "}");
      let e = wp_expr p in
      let at = wp_at p in
      ignore (eat_p p "{");
      ignore (eat_p p "{");
      ignore (eat_p p "{");
      let bs =
        match peek_kind p with
        | Some (Id "RET") -> []
        | _ ->
            let bs = parse_binders p in
            ignore (eat_p p ",");
            bs
      in
      ignore (eat_id p "RET");
      let ret = term p in
      ignore (eat_p p ";");
      let post = term p in
      ignore (eat_p p "}");
      ignore (eat_p p "}");
      let tend = eat_p p "}" in
      ETriple ({ lo = t0.lo; hi = tend.hi }, pre, e, at, bs, ret, post)
  | _ -> raise Fail

and masks p =
  let m1 = term p in
  match peek_kind p with
  | Some (P ",") ->
      ignore (bump p);
      [ m1; term p ]
  | _ -> [ m1 ]

and wp_expr p =
  let e0 = with_no_at p true term in
  match peek_kind p with
  | Some (Sym ":") ->
      ignore (bump p);
      let ty = term p in
      ECast ({ lo = (expr_span e0).lo; hi = (expr_span ty).hi }, e0, ty)
  | _ -> e0

and wp_at p =
  match peek_kind p with
  | Some (Sym "@") -> (
      ignore (bump p);
      let x = term p in
      match peek_kind p with
      | Some (P ";") ->
          ignore (bump p);
          WpAt (Some x, term p)
      | _ -> WpAt (None, x))
  | _ -> WpNone

and wp_post p =
  ignore (eat_p p "{");
  ignore (eat_p p "{");
  let wp_binder =
    try_ p (fun p ->
        let n = parse_name_or_hole p in
        ignore (eat_p p ",");
        n)
  in
  let wp_body = term p in
  ignore (eat_p p "}");
  let tend = eat_p p "}" in
  ({ wp_binder; wp_body }, tend.hi)

and step_arrow p arrow =
  let s, _ = eat_any_sym p in
  if s = arrow then None
  else if s = arrow ^ "^" then Some (atom p)
  else raise Fail

(* ── Binder forms ──────────────────────────────────────────────────────── *)

and binder_form p =
  match peek_kind p with
  | Some (P "[") -> (
      let t0 = bump p in
      let op, _ = eat_any_sym p in
      if not (is_big_op op) then raise Fail;
      match peek_kind p with
      | Some (Id kind) ->
          ignore (bump p);
          ignore (eat_p p "]");
          let binds = big_binds p in
          ignore (eat_sym p "∈");
          let colls = big_colls p in
          ignore (eat_p p ",");
          let b = term p in
          EBigOp ({ lo = t0.lo; hi = (expr_span b).hi }, op, kind, binds, colls, b)
      | Some (P "]") ->
          ignore (bump p);
          let e = expr p ~max:20 in
          EBigAll ({ lo = t0.lo; hi = (expr_span e).hi }, op, e)
      | _ -> raise Fail)
  | Some (Id "Eval") ->
      let t0 = bump p in
      let ws = parse_eval_words p in
      ignore (eat_kw p "in");
      let e = term p in
      EEval ({ lo = t0.lo; hi = (expr_span e).hi }, ws, e)
  | Some (Kw "forall" | Sym "∀") ->
      let lo = eat_forall_kw p in
      let bs = parse_binders_typed p in
      ignore (eat_p p ",");
      let b = term p in
      EForall ({ lo; hi = (expr_span b).hi }, bs, b)
  | Some (Kw "exists" | Sym "∃") ->
      let lo = eat_exists_kw p in
      let bs = parse_binders_typed p in
      ignore (eat_p p ",");
      let b = term p in
      EExists ({ lo; hi = (expr_span b).hi }, bs, b)
  | Some (Kw "fun" | Id "λ") ->
      let lo = eat_fun_kw p in
      let bs = parse_binders_typed p in
      (match peek_kind p with
      | Some (Sym "=>" | Sym "⇒") -> eat_arrow_kw p
      | _ -> ignore (eat_p p ","));
      let b = term p in
      EFun ({ lo; hi = (expr_span b).hi }, bs, b)
  | Some (Kw "let") -> (
      let t0 = bump p in
      match peek_kind p with
      | Some (Sym "*") ->
          ignore (bump p);
          let n = parse_name_or_hole p in
          ignore (eat_sym p ":=");
          let v = term p in
          ignore (eat_kw p "in");
          let b = term p in
          ELetStar ({ lo = t0.lo; hi = (expr_span b).hi }, n, v, b)
      | Some (Sym "?") ->
          ignore (bump p);
          let pat = atom p in
          ignore (eat_sym p ":=");
          let v = term p in
          ignore (eat_kw p "in");
          let b = term p in
          ELetQ ({ lo = t0.lo; hi = (expr_span b).hi }, pat, v, b)
      | Some (Kw "fix") ->
          ignore (bump p);
          let n = parse_name p in
          let bs = parse_binders0 p in
          let ty = opt_type p in
          ignore (eat_sym p ":=");
          let v = term p in
          ignore (eat_kw p "in");
          let b = term p in
          ELetFix ({ lo = t0.lo; hi = (expr_span b).hi }, n, bs, ty, v, b)
      | Some (P "'") ->
          ignore (bump p);
          let pat = atom p in
          ignore (eat_sym p ":=");
          let v = term p in
          ignore (eat_kw p "in");
          let b = term p in
          ELetPat ({ lo = t0.lo; hi = (expr_span b).hi }, pat, v, b)
      | _ ->
          let lhs = parse_let_lhs p in
          let ty = opt_type p in
          ignore (eat_sym p ":=");
          let v = term p in
          ignore (eat_kw p "in");
          let b = term p in
          ELet ({ lo = t0.lo; hi = (expr_span b).hi }, lhs, ty, v, b))
  | Some (Kw "if") ->
      let t0 = bump p in
      let c = with_in_if p true term in
      let is_pat =
        match peek_kind p with
        | Some (Id "is") ->
            ignore (bump p);
            Some (term p)
        | _ -> None
      in
      ignore (eat_kw p "then");
      let th = term p in
      ignore (eat_kw p "else");
      let el = term p in
      let sp = { lo = t0.lo; hi = (expr_span el).hi } in
      (match is_pat with
      | Some pat -> EIfIs (sp, c, pat, th, el)
      | None -> EIf (sp, c, th, el))
  | Some (Kw "fix") ->
      let t0 = bump p in
      let n = parse_name p in
      let bs = parse_binders0 p in
      let ty = opt_type p in
      ignore (eat_sym p ":=");
      let b = term p in
      EFix ({ lo = t0.lo; hi = (expr_span b).hi }, n, bs, ty, b)
  | _ -> raise Fail

and big_binds p =
  let n = parse_name_or_hole p in
  match peek_kind p with
  | Some (Sym "↦") ->
      ignore (bump p);
      { bb_key = Some n; bb_vals = big_names p }
  | Some (P ";") ->
      ignore (bump p);
      { bb_key = None; bb_vals = n :: big_names p }
  | _ -> { bb_key = None; bb_vals = [ n ] }

and big_names p =
  let n = parse_name_or_hole p in
  match peek_kind p with
  | Some (P ";") ->
      ignore (bump p);
      n :: big_names p
  | _ -> [ n ]

and big_colls p =
  let c = term p in
  match peek_kind p with
  | Some (P ";") ->
      ignore (bump p);
      c :: big_colls p
  | _ -> [ c ]

and parse_let_lhs p =
  match peek_kind p with
  | Some (P "(") ->
      ignore (bump p);
      let ns = parse_names p in
      ignore (eat_p p ")");
      LetTuple ns
  | _ ->
      let n = parse_name_or_hole p in
      let bs = parse_binders0 p in
      LetName (n, bs)

and parse_binders_typed p =
  let bs0 = parse_binders p in
  if
    List.for_all (fun b -> b.b_kind = BBare) bs0
    && peek_kind p = Some (Sym ":")
  then (
    ignore (bump p);
    let ty = term p in
    let ns = List.concat_map (fun b -> b.b_names) bs0 in
    let lo = (List.hd bs0).b_span.lo in
    [ { b_span = { lo; hi = (expr_span ty).hi }; b_kind = BBare; b_names = ns; b_ty = Some ty } ])
  else bs0

and parse_binders p =
  let b = parse_binder p in
  b :: parse_binders0 p

and parse_binders0 p =
  let rec loop acc =
    match try_ p parse_binder with
    | Some b -> loop (b :: acc)
    | None -> List.rev acc
  in
  loop []

and parse_binder p =
  match peek_kind p with
  | Some (P "(") ->
      let t0 = bump p in
      let ns = parse_names p in
      ignore (eat_sym p ":");
      let ty = term p in
      let tend = eat_p p ")" in
      { b_span = { lo = t0.lo; hi = tend.hi }; b_kind = BParen; b_names = ns; b_ty = Some ty }
  | Some (P "{") -> (
      let t0 = bump p in
      match
        try_ p (fun p ->
            ignore (eat_id p "struct");
            let n = parse_name p in
            let tend = eat_p p "}" in
            {
              b_span = { lo = t0.lo; hi = tend.hi };
              b_kind = BStruct;
              b_names = [ n ];
              b_ty = None;
            })
      with
      | Some b -> b
      | None ->
          let ns = parse_names p in
          let ty =
            match peek_kind p with
            | Some (Sym ":") ->
                ignore (bump p);
                Some (term p)
            | _ -> None
          in
          let tend = eat_p p "}" in
          { b_span = { lo = t0.lo; hi = tend.hi }; b_kind = BBrace; b_names = ns; b_ty = ty })
  | Some (Id x) when not (is_op_word x) ->
      let t = bump p in
      let sp = { lo = t.lo; hi = t.hi } in
      { b_span = sp; b_kind = BBare; b_names = [ { n_span = sp; n_text = x } ]; b_ty = None }
  | Some (P "'") ->
      let t0 = bump p in
      let pat = atom p in
      {
        b_span = { lo = t0.lo; hi = (expr_span pat).hi };
        b_kind = BPattern pat;
        b_names = [];
        b_ty = None;
      }
  | Some (P "`") -> (
      let t0 = bump p in
      match peek_kind p with
      | Some (P (("{" | "(") as open_d)) ->
          ignore (bump p);
          let close_d = if open_d = "{" then "}" else ")" in
          let items = parse_gen_items p in
          let tend = eat_p p close_d in
          {
            b_span = { lo = t0.lo; hi = tend.hi };
            b_kind = BGen (open_d, items);
            b_names = [];
            b_ty = None;
          }
      | _ -> raise Fail)
  | _ -> raise Fail

and parse_gen_items p =
  let i = parse_gen_item p in
  match peek_kind p with
  | Some (P ",") ->
      ignore (bump p);
      i :: parse_gen_items p
  | _ -> [ i ]

and parse_gen_item p =
  match
    try_ p (fun p ->
        let n, t0 = eat_any_id p in
        ignore (eat_sym p ":");
        ignore (eat_sym p "!");
        let e = term p in
        GenBangCast ({ lo = t0.lo; hi = (expr_span e).hi }, n, e))
  with
  | Some g -> g
  | None -> (
      match peek_kind p with
      | Some (Sym "!") ->
          ignore (bump p);
          GenBang (term p)
      | _ -> GenExpr (term p))

(* ── Pratt precedence-climbing loop ────────────────────────────────────── *)

and op_rest p ~max l =
  if max >= 70 && peek2_kind p = Some (Sym "⟶", P "[") then (
    ignore (bump p);
    ignore (bump p);
    let g = term p in
    ignore (eat_p p "]");
    let r = expr p ~max:69 in
    let sp = { lo = (expr_span l).lo; hi = (expr_span r).hi } in
    let n = EMixfix (sp, [ MExpr l; MStr " ⟶["; MExpr g; MStr "] "; MExpr r ]) in
    op_rest p ~max n)
  else
    match try_iris_op p ~max l with
    | Some n -> op_rest p ~max n
    | None -> (
        match peek_kind p with
        | Some k -> (
            match op_token k with
            | Some op -> (
                match lookup_binop p op with
                | Some (lv, assoc) when lv <= max ->
                    ignore (bump p);
                    let rmax = if assoc = Right then lv else lv - 1 in
                    let r = expr p ~max:rmax in
                    let sp = { lo = (expr_span l).lo; hi = (expr_span r).hi } in
                    let n = combine sp op l r in
                    op_rest p ~max n
                | _ -> l)
            | None -> l)
        | None -> l)

and try_iris_op p ~max l =
  match peek2_kind p with
  | Some (Sym "=", P "{") when max >= 99 ->
      try_ p (fun p ->
          ignore (bump p);
          ignore (bump p);
          let ms = masks p in
          ignore (eat_p p "}");
          match peek_kind p with
          | Some (Sym "▷") ->
              ignore (bump p);
              let n = step_arrow p "=∗" in
              let r = expr p ~max:200 in
              EStepUpdw ({ lo = (expr_span l).lo; hi = (expr_span r).hi }, ms, n, l, r)
          | _ ->
              ignore (eat_sym p "=∗");
              let r = expr p ~max:200 in
              EFupdw ({ lo = (expr_span l).lo; hi = (expr_span r).hi }, ms, l, r))
  | Some (Sym (("≡" | "≼") as op), P "{") when max >= 70 ->
      try_ p (fun p ->
          ignore (bump p);
          ignore (bump p);
          let n = term p in
          ignore (eat_p p "}");
          if op = "≡" then ignore (eat_sym p "≡");
          let r = expr p ~max:69 in
          EIndexed ({ lo = (expr_span l).lo; hi = (expr_span r).hi }, op, n, Some l, r))
  | _ -> (
      match peek_kind p with
      | Some (Sym (("↦" | "↪") as op)) when max >= 20 ->
          try_ p (fun p ->
              ignore (bump p);
              let name_mod =
                match peek_kind p with
                | Some (P "[") ->
                    ignore (bump p);
                    let g = term p in
                    ignore (eat_p p "]");
                    [ PmName g ]
                | _ -> []
              in
              let dm = parse_dfrac p in
              let r = expr p ~max:19 in
              EPointsTo ({ lo = (expr_span l).lo; hi = (expr_span r).hi }, op, l, name_mod @ dm, r))
      | _ -> None)

and parse_dfrac p =
  match peek2_kind p with
  | Some (P "{", Sym "#") ->
      ignore (bump p);
      ignore (bump p);
      let q = term p in
      ignore (eat_p p "}");
      [ PmOwn q ]
  | _ -> (
      match peek_kind p with
      | Some (P "{") ->
          ignore (bump p);
          let d = term p in
          ignore (eat_p p "}");
          [ PmDfrac d ]
      | Some (Sym "□") ->
          ignore (bump p);
          [ PmPersistent ]
      | _ -> [])

and combine sp op l r =
  match l with
  | EBin (_, op1, a, b) when is_chain_op op1 && is_chain_op op ->
      EChain (sp, [ op1; op ], [ a; b; r ])
  | _ -> EBin (sp, op, l, r)

(* ── Application & atoms ───────────────────────────────────────────────── *)

and app p =
  let f = atom p in
  let rec args acc =
    if starts_atom p then
      let a = atom p in
      args (a :: acc)
    else List.rev acc
  in
  match args [] with
  | [] -> f
  | as_ ->
      let last_a = List.nth as_ (List.length as_ - 1) in
      EApp ({ lo = (expr_span f).lo; hi = (expr_span last_a).hi }, f, as_)

and atom p =
  let e00 = atom0 p in
  let e01 = parse_bits p e00 in
  let e0 = parse_projs p e01 in
  match peek2_kind p with
  | Some (Sym "%", Id k) ->
      ignore (bump p);
      let tk = bump p in
      EScope ({ lo = (expr_span e0).lo; hi = tk.hi }, e0, k)
  | _ -> e0

and parse_bits p e0 =
  let bit p =
    match peek2_kind p with
    | Some (Sym "~", Num (("0" | "1") as d)) ->
        ignore (bump p);
        let t = bump p in
        Some (d, t.hi)
    | _ -> None
  in
  match bit p with
  | None -> e0
  | Some (d0, hi0) ->
      let buf = Buffer.create 16 in
      Buffer.add_string buf d0;
      let rec more hi =
        match bit p with
        | Some (d, hi') ->
            Buffer.add_string buf d;
            more hi'
        | None -> hi
      in
      let hi = more hi0 in
      EBits ({ lo = (expr_span e0).lo; hi }, e0, Buffer.contents buf)

and parse_projs p e =
  match peek2_kind p with
  | Some (Sym ".", P "[") ->
      ignore (bump p);
      ignore (bump p);
      let k = frame_name p in
      let binding =
        match peek_kind p with
        | Some (Sym ":=") ->
            ignore (bump p);
            [ MStr " := "; MExpr (term p) ]
        | _ -> []
      in
      let tend = eat_p p "]" in
      let sp = { lo = (expr_span e).lo; hi = tend.hi } in
      let e' = EMixfix (sp, (MExpr e :: MStr ".[" :: k) @ binding @ [ MStr "]" ]) in
      parse_projs p e'
  | _ -> (
      match peek_kind p with
      | Some (Sym ((".1" | ".2" | ".*1" | ".*2") as op)) ->
          let t = bump p in
          parse_projs p (EProj ({ lo = (expr_span e).lo; hi = t.hi }, e, op))
      | _ -> e)

and atom0 p =
  match peek p with
  | None -> raise Fail
  | Some t0 -> (
      let adjacent_next k =
        p.pos + 1 < p.len && p.toks.(p.pos + 1).kind = k && p.toks.(p.pos + 1).lo = t0.hi
      in
      match t0.kind with
      | Id (("cfg" | "frame" | "run") as kind) when adjacent_next (P "{") ->
          ignore (bump p);
          ignore (bump p);
          let parts = frame_literal p kind in
          let tend = eat_p p "}" in
          EMixfix ({ lo = t0.lo; hi = tend.hi }, parts)
      | Id "ir" when adjacent_next (P "{") ->
          ignore (bump p);
          ignore (bump p);
          let i = ir_ssa_node p in
          let tend = eat_p p "}" in
          EIrInst ({ lo = t0.lo; hi = tend.hi }, i)
      | Id "ir_blk" when adjacent_next (P "{") ->
          ignore (bump p);
          ignore (bump p);
          let b = ir_block p in
          let tend = eat_p p "}" in
          EIrBlk ({ lo = t0.lo; hi = tend.hi }, b)
      | Id "ir_fn" when adjacent_next (P "{") ->
          ignore (bump p);
          ignore (bump p);
          let lk = atom p in
          let nm = atom p in
          let ps = ir_formals p in
          ignore (eat_sym p "->");
          let ret = atom p in
          let bs = ir_body p in
          let tend = eat_p p "}" in
          EIrFn ({ lo = t0.lo; hi = tend.hi }, lk, nm, ps, ret, bs)
      | Id "ir" when adjacent_next (P "[") ->
          ignore (bump p);
          ignore (bump p);
          let is = ir_seq p ir_ssa_node ";" in
          let tend = eat_p p "]" in
          EIrList ({ lo = t0.lo; hi = tend.hi }, is)
      | Id (("cap" | "cap_fn" | "cap_blk") as kind) when peek2_kind p = Some (Id kind, P "{") ->
          ignore (bump p);
          ignore (bump p);
          let ct = cap_entry p kind in
          let tend = eat_p p "}" in
          cap_tree { lo = t0.lo; hi = tend.hi } ct
      | Sym ".." when p.in_notation_rhs ->
          ignore (bump p);
          EId ({ lo = t0.lo; hi = t0.hi }, "..")
      | Id "_" ->
          ignore (bump p);
          EHole { lo = t0.lo; hi = t0.hi }
      | Sym "⌜" ->
          ignore (bump p);
          let e = term p in
          let tend = eat_sym p "⌝" in
          EPure ({ lo = t0.lo; hi = tend.hi }, e)
      | Sym (("⊤" | "∅") as c) ->
          ignore (bump p);
          EConst ({ lo = t0.lo; hi = t0.hi }, c)
      | P "(" when peek2_kind p = Some (P "(", P ")") ->
          ignore (bump p);
          let t1 = bump p in
          EUnit { lo = t0.lo; hi = t1.hi }
      | Sym "<" when peek2_kind p = Some (Sym "<", P "[") ->
          ignore (bump p);
          ignore (bump p);
          let k = term p in
          ignore (eat_sym p ":=");
          let v = term p in
          ignore (eat_p p "]");
          let tend = eat_sym p ">" in
          EInsert ({ lo = t0.lo; hi = tend.hi }, k, v)
      | Sym "#" when adjacent_next (P "[") ->
          ignore (bump p);
          ignore (bump p);
          let es = list_elems p in
          let tend = eat_p p "]" in
          EGFunctors ({ lo = t0.lo; hi = tend.hi }, es)
      | Sym "#" ->
          ignore (bump p);
          let e = atom p in
          EPre ({ lo = t0.lo; hi = (expr_span e).hi }, "#", e)
      | Sym "?" ->
          ignore (bump p);
          let x, tx = eat_any_id p in
          EMeta ({ lo = t0.lo; hi = tx.hi }, x)
      | Id "ltac"
        when p.pos + 2 < p.len
             && p.toks.(p.pos + 1).kind = Sym ":"
             && p.toks.(p.pos + 2).kind = P "(" ->
          ignore (bump p);
          ignore (bump p);
          ignore (bump p);
          let tac = !parse_tactic_ref p in
          let tend = eat_p p ")" in
          ELtac ({ lo = t0.lo; hi = tend.hi }, tac)
      | Id x when not (is_op_word x) ->
          ignore (bump p);
          EId ({ lo = t0.lo; hi = t0.hi }, x)
      | Num n ->
          ignore (bump p);
          ENum ({ lo = t0.lo; hi = t0.hi }, n)
      | Str s ->
          ignore (bump p);
          EStr ({ lo = t0.lo; hi = t0.hi }, s)
      | Sym "@" ->
          ignore (bump p);
          let x, tx = eat_any_id p in
          EExplicit ({ lo = t0.lo; hi = tx.hi }, x)
      | P "(" -> (
          ignore (bump p);
          match
            try_ p (fun p ->
                let x, _ = eat_any_id p in
                ignore (eat_sym p ":=");
                let e = term p in
                let tend = eat_p p ")" in
                ENamed ({ lo = t0.lo; hi = tend.hi }, x, e))
          with
          | Some e -> e
          | None -> (
              let e0 = term p in
              match peek_kind p with
              | Some (P ")") ->
                  let tend = bump p in
                  EParen ({ lo = t0.lo; hi = tend.hi }, e0)
              | Some (Sym ":") ->
                  ignore (bump p);
                  let ty = term p in
                  let tend = eat_p p ")" in
                  ECast ({ lo = t0.lo; hi = tend.hi }, e0, ty)
              | Some (P ",") ->
                  ignore (bump p);
                  let es = tuple_rest p in
                  let tend = eat_p p ")" in
                  ETuple ({ lo = t0.lo; hi = tend.hi }, e0 :: es)
              | Some (Sym "|") ->
                  ignore (bump p);
                  let es = or_rest p in
                  let tend = eat_p p ")" in
                  EOrPat ({ lo = t0.lo; hi = tend.hi }, e0 :: es)
              | _ -> raise Fail))
      | P "[" -> (
          ignore (bump p);
          match peek_kind p with
          | Some (P "]") ->
              let tend = bump p in
              EList ({ lo = t0.lo; hi = tend.hi }, [])
          | _ ->
              let es = list_elems p in
              let tend = eat_p p "]" in
              EList ({ lo = t0.lo; hi = tend.hi }, es))
      | P "{|" ->
          ignore (bump p);
          let fs = rec_fields p in
          let tend = eat_p p "|}" in
          ERecord ({ lo = t0.lo; hi = tend.hi }, fs)
      | P "{" -> (
          ignore (bump p);
          match
            try_ p (fun p ->
                let n = parse_name p in
                ignore (eat_sym p ":");
                let ty = term p in
                ignore (eat_sym p "|");
                let q = term p in
                let tend = eat_p p "}" in
                ESig ({ lo = t0.lo; hi = tend.hi }, n, ty, q))
          with
          | Some e -> e
          | None ->
              let e0 = term p in
              let tend = eat_p p "}" in
              EBraces ({ lo = t0.lo; hi = tend.hi }, e0))
      | Kw "match" ->
          ignore (bump p);
          let ss = scrutinees p in
          let ret =
            match peek_kind p with
            | Some (Kw "return") ->
                ignore (bump p);
                Some (expr p ~max:100)
            | _ -> None
          in
          ignore (eat_kw p "with");
          if peek_kind p = Some (Sym "|") then ignore (bump p);
          let brs = branches p in
          let tend = eat_kw p "end" in
          EMatch ({ lo = t0.lo; hi = tend.hi }, ss, ret, brs)
      | _ -> raise Fail)

(* ── FrameNotation ─────────────────────────────────────────────────────── *)

and frame_field p k =
  match peek2_kind p with
  | Some (Id x, Sym ":") when x = k ->
      ignore (bump p);
      ignore (bump p);
      true
  | _ -> false

and expect_frame_field p k = if not (frame_field p k) then raise Fail

and frame_name p =
  match peek_kind p with
  | Some (Sym "@") ->
      ignore (bump p);
      [ MStr "@"; MExpr (atom p) ]
  | _ -> [ MExpr (atom p) ]

and frame_literal p kind =
  let f = atom p in
  let frame =
    if frame_field p "env" then (
      let e = atom p in
      let ls = if frame_field p "locals" then [ MStr " locals: "; MExpr (atom p) ] else [] in
      let d = if frame_field p "doomed" then [ MStr " doomed: "; MExpr (atom p) ] else [] in
      ignore (eat_sym p "|");
      let pc = frame_pc p in
      (MExpr f :: MStr " env: " :: MExpr e :: ls) @ d @ (MStr " | " :: pc))
    else [ MExpr f ]
  in
  let tail =
    if kind = "cfg" then (
      ignore (eat_p p ";");
      let cs =
        if frame_field p "stack" then (
          let c = term p in
          ignore (eat_p p ";");
          [ MStr "; stack: "; MExpr c ])
        else []
      in
      expect_frame_field p "mem";
      let m = term p in
      ignore (eat_p p ";");
      expect_frame_field p "fuel";
      let n = term p in
      cs @ [ MStr "; mem: "; MExpr m; MStr "; fuel: "; MExpr n ])
    else []
  in
  (MStr (kind ^ "{ ") :: frame) @ tail @ [ MStr " }" ]

and frame_pc p =
  match peek_kind p with
  | Some (Id "at") ->
      ignore (bump p);
      let l = frame_name p in
      ignore (eat_p p "{");
      let is = term p in
      ignore (eat_sym p "=>");
      let j = term p in
      ignore (eat_p p "}");
      (MStr "at " :: l) @ [ MStr " { "; MExpr is; MStr " => "; MExpr j; MStr " }" ]
  | _ ->
      if frame_field p "enter" then
        let l = frame_name p in
        let from_part =
          if frame_field p "from" then MStr " from: " :: frame_name p else []
        in
        (MStr "enter: " :: l) @ from_part
      else (
        expect_frame_field p "pc";
        [ MStr "pc: "; MExpr (atom p) ])

(* ── IRNotation ────────────────────────────────────────────────────────── *)

and ir_seq : 'a. state -> (state -> 'a) -> string -> 'a list =
 fun p read sep ->
  let x = read p in
  match peek_kind p with
  | Some (P s) when s = sep ->
      ignore (bump p);
      x :: ir_seq p read sep
  | _ -> [ x ]

and ir_formals p =
  ignore (eat_p p "(");
  match peek_kind p with
  | Some (P ")") ->
      ignore (bump p);
      []
  | _ ->
      let ps = ir_seq p ir_formal "," in
      ignore (eat_p p ")");
      ps

and ir_formal p =
  let irp_ty = atom p in
  ignore (eat_sym p "%");
  let irp_name = atom p in
  { irp_ty; irp_name }

and ir_body p =
  match peek_kind p with
  | Some (Id "blocks") ->
      ignore (bump p);
      ignore (eat_p p "(");
      let xs = term p in
      ignore (eat_p p ")");
      IrBodyExpr xs
  | _ -> (
      ignore (eat_p p "{");
      match peek_kind p with
      | Some (P "}") ->
          ignore (bump p);
          IrBodyBlocks []
      | _ ->
          let bs = ir_seq p ir_block ";" in
          ignore (eat_p p "}");
          IrBodyBlocks bs)

and ir_block p =
  match peek_kind p with
  | Some (P "(") ->
      ignore (bump p);
      let x = term p in
      ignore (eat_p p ")");
      IrBlockEscape x
  | _ ->
      let t0 = eat_sym p "@" in
      let l = atom p in
      let phis = ir_phis_end p in
      let ins = ir_insts_end p in
      let j = ir_ssa_node p in
      IrBlock ({ lo = t0.lo; hi = j.irs_span.hi }, l, phis, ins, j)

and ir_phis_end p =
  match peek_kind p with
  | Some (Sym ":") ->
      ignore (bump p);
      []
  | _ ->
      ignore (eat_p p "[");
      let ps = ir_seq p ir_phi ";" in
      ignore (eat_p p "]");
      ignore (eat_sym p ":");
      ps

and ir_phi p =
  match peek_kind p with
  | Some (P "(") ->
      ignore (bump p);
      let x = term p in
      ignore (eat_p p ")");
      IrPhiEscape x
  | _ ->
      let t0 = eat_sym p "%" in
      let d = atom p in
      ignore (eat_sym p ":");
      let k = atom p in
      ignore (eat_sym p "=");
      ignore (eat_id p "phi");
      ignore (eat_p p "(");
      let incs = ir_seq p ir_incoming "," in
      let tend = eat_p p ")" in
      IrPhi ({ lo = t0.lo; hi = tend.hi }, d, k, incs)

and ir_incoming p =
  let iri_lab = atom p in
  ignore (eat_sym p "=>");
  let iri_val, _ = ir_operand p in
  { iri_lab; iri_val }

and ir_insts_end p =
  match peek_kind p with
  | Some (Sym "=>") ->
      ignore (bump p);
      IrInsts []
  | Some (Id "code") ->
      ignore (bump p);
      ignore (eat_p p "(");
      let xs = term p in
      ignore (eat_p p ")");
      ignore (eat_sym p "=>");
      IrCode xs
  | _ ->
      let is = ir_seq p ir_ssa_node ";" in
      ignore (eat_sym p "=>");
      IrInsts is

and ir_operand p =
  match peek_kind p with
  | Some (Id "val") ->
      ignore (bump p);
      ignore (eat_p p "(");
      let x = term p in
      let tend = eat_p p ")" in
      (IrVal x, tend.hi)
  | Some (Sym "%") ->
      ignore (bump p);
      let x = atom p in
      (IrTmp x, (expr_span x).hi)
  | Some (Sym "$") ->
      ignore (bump p);
      let x = atom p in
      (IrGlobal x, (expr_span x).hi)
  | Some (Sym "#") ->
      ignore (bump p);
      let x = atom p in
      (IrConst x, (expr_span x).hi)
  | _ -> raise Fail

and ir_edge p =
  match peek_kind p with
  | Some (Id "edge") ->
      ignore (bump p);
      ignore (eat_p p "(");
      let x = term p in
      let tend = eat_p p ")" in
      (IrEdgeExpr x, tend.hi)
  | Some (Id "poll") ->
      ignore (bump p);
      let l = atom p in
      (IrPoll l, (expr_span l).hi)
  | _ ->
      let l = atom p in
      (IrTo l, (expr_span l).hi)

and ir_args p =
  ignore (eat_p p "(");
  match peek_kind p with
  | Some (P ")") ->
      let tend = bump p in
      ([], tend.hi)
  | _ ->
      let args = ir_seq p ir_actual "," in
      let tend = eat_p p ")" in
      (args, tend.hi)

and ir_actual p =
  let ira_ty = atom p in
  let ira_val, _ = ir_operand p in
  { ira_ty; ira_val }

and ir_operand_ahead p =
  match peek_kind p with
  | Some (Sym "%" | Sym "$" | Sym "#" | Id "val") -> true
  | _ -> false

and ir_ssa_node p =
  match peek_kind p with
  | Some (P "(") ->
      let t0 = bump p in
      let x = term p in
      let tend = eat_p p ")" in
      { irs_span = { lo = t0.lo; hi = tend.hi }; irs_kind = IrSsaEscape x }
  | Some (Sym "%") -> (
      let t0 = bump p in
      let d = atom p in
      match peek_kind p with
      | Some (Sym ":") ->
          ignore (bump p);
          let k = atom p in
          ignore (eat_sym p "=");
          let op = atom p in
          let args, hi =
            if ir_operand_ahead p then
              let pairs = ir_seq p ir_operand "," in
              let last_hi = snd (List.nth pairs (List.length pairs - 1)) in
              (List.map fst pairs, last_hi)
            else ([], (expr_span op).hi)
          in
          { irs_span = { lo = t0.lo; hi }; irs_kind = IrLet (d, k, op, args) }
      | _ ->
          ignore (eat_sym p "=");
          let base, _ = ir_operand p in
          ignore (eat_sym p "+");
          ignore (eat_id p "p");
          let off, hi = ir_operand p in
          { irs_span = { lo = t0.lo; hi }; irs_kind = IrFlight (d, base, off) })
  | Some (Id "store") ->
      let t0 = bump p in
      let sz = atom p in
      ignore (eat_p p "[");
      let a, _ = ir_operand p in
      ignore (eat_sym p "+");
      let off = atom p in
      ignore (eat_p p "]");
      ignore (eat_sym p "<-");
      let v, hi = ir_operand p in
      { irs_span = { lo = t0.lo; hi }; irs_kind = IrStore (sz, a, off, v) }
  | Some (Id "store.ptr") ->
      let t0 = bump p in
      ignore (eat_p p "[");
      let a, _ = ir_operand p in
      ignore (eat_sym p "+");
      let off = atom p in
      ignore (eat_p p "]");
      ignore (eat_sym p "<-");
      let v, hi = ir_operand p in
      { irs_span = { lo = t0.lo; hi }; irs_kind = IrStorePtr (a, off, v) }
  | Some (Id "alloca") ->
      let t0 = bump p in
      let x = atom p in
      let sz = atom p in
      { irs_span = { lo = t0.lo; hi = (expr_span sz).hi }; irs_kind = IrAlloca (x, sz) }
  | Some (Id "goto") ->
      let t0 = bump p in
      let dst, hi = ir_edge p in
      { irs_span = { lo = t0.lo; hi }; irs_kind = IrGoto dst }
  | Some (Id "br") ->
      let t0 = bump p in
      let x, _ = ir_operand p in
      ignore (eat_sym p "?");
      let y, _ = ir_edge p in
      ignore (eat_sym p ":");
      let n, hi = ir_edge p in
      { irs_span = { lo = t0.lo; hi }; irs_kind = IrBr (x, y, n) }
  | Some (Id "ret") -> (
      let t0 = bump p in
      match peek_kind p with
      | Some (Id "void") ->
          let tv = bump p in
          { irs_span = { lo = t0.lo; hi = tv.hi }; irs_kind = IrRet IrRetVoid }
      | _ ->
          let v, hi = ir_operand p in
          { irs_span = { lo = t0.lo; hi }; irs_kind = IrRet (IrRetVal v) })
  | Some (Id "unreachable") ->
      let t0 = bump p in
      { irs_span = { lo = t0.lo; hi = t0.hi }; irs_kind = IrUnreachable }
  | Some (Id (("call" | "rawcall") as kw)) ->
      let t0 = bump p in
      let res =
        match peek_kind p with
        | Some (Sym "%") ->
            ignore (bump p);
            let d = atom p in
            ignore (eat_sym p ":");
            let k = atom p in
            ignore (eat_sym p "=");
            IrCallRes (d, k)
        | _ ->
            ignore (eat_id p "void");
            IrCallVoid
      in
      let fn, _ = ir_operand p in
      let args, hi = ir_args p in
      { irs_span = { lo = t0.lo; hi }; irs_kind = IrCall (kw, res, fn, args) }
  | _ -> raise Fail

(* ── Transport fixture cap{...} notation ──────────────────────────────── *)

and cap_entry p = function
  | "cap" -> cap_expr p
  | "cap_blk" -> cap_block p
  | "cap_fn" ->
      let l = cap_expr p in
      let n = cap_expr p in
      let ps = cap_expr p in
      ignore (eat_sym p "->");
      let r = cap_expr p in
      let bs =
        match peek_kind p with
        | Some (Id "blocks") ->
            ignore (bump p);
            ignore (eat_p p "(");
            let lst = term p in
            ignore (eat_p p ")");
            `ListExpr lst
        | _ ->
            ignore (eat_p p "{");
            let blocks = ir_seq p cap_block ";" in
            ignore (eat_p p "}");
            `Seq blocks
      in
      `Compound ("func", [ n; l; r; ps; bs ])
  | _ -> raise Fail

and cap_block p =
  ignore (eat_sym p "@");
  let l = cap_expr p in
  let ps =
    match peek_kind p with
    | Some (P "[") ->
        ignore (bump p);
        let xs = ir_seq p cap_expr ";" in
        ignore (eat_p p "]");
        xs
    | _ -> []
  in
  ignore (eat_sym p ":");
  let is =
    match peek_kind p with
    | Some (Sym "=>") -> []
    | _ -> ir_seq p cap_inst ";"
  in
  ignore (eat_sym p "=>");
  let j = cap_inst p in
  `Compound ("block", [ l; `Seq ps; `Seq is; j ])

and cap_expr p =
  match peek_kind p with
  | Some (Str s) ->
      ignore (bump p);
      `Atom s
  | Some (Sym "%") ->
      ignore (bump p);
      let d, _ = eat_str p in
      `Compound ("tmp", [ `Atom d ])
  | Some (Sym "$") ->
      ignore (bump p);
      let n, _ = eat_str p in
      `Compound ("global", [ `Atom n ])
  | Some (Sym "#") ->
      ignore (bump p);
      `Compound ("const", [ `Int (cap_number p) ])
  | Some (Id "poll") ->
      ignore (bump p);
      let l, _ = eat_str p in
      `Compound ("poll", [ `Atom l ])
  | Some (Id "param") ->
      ignore (bump p);
      let k = cap_expr p in
      ignore (eat_sym p "%");
      let d, _ = eat_str p in
      `Compound ("param", [ k; `Compound ("tmp", [ `Atom d ]) ])
  | Some (Id "phi") ->
      ignore (bump p);
      ignore (eat_sym p "%");
      let d, _ = eat_str p in
      ignore (eat_sym p ":");
      let k = cap_expr p in
      ignore (eat_sym p "=");
      ignore (eat_p p "(");
      let ps = ir_seq p cap_incoming "," in
      ignore (eat_p p ")");
      `Compound ("phi", [ `Compound ("tmp", [ `Atom d ]); k; `Seq ps ])
  | Some (Id "int") ->
      ignore (bump p);
      `Int (cap_number p)
  | Some (Id "op") ->
      ignore (bump p);
      let f, _ = eat_str p in
      ignore (eat_p p "(");
      let args = ir_seq p cap_expr "," in
      ignore (eat_p p ")");
      `Compound (f, args)
  | Some (P "[") ->
      ignore (bump p);
      let xs =
        match peek_kind p with
        | Some (P "]") -> []
        | _ -> ir_seq p cap_expr ";"
      in
      ignore (eat_p p "]");
      `Seq xs
  | Some (Id "term") ->
      ignore (bump p);
      ignore (eat_p p "(");
      let x = term p in
      ignore (eat_p p ")");
      `Gallina x
  | _ -> raise Fail

and cap_number p =
  match peek_kind p with
  | Some (Num n) ->
      let t = bump p in
      ENum ({ lo = t.lo; hi = t.hi }, n)
  | Some (P "(") ->
      let t0 = bump p in
      let tm = eat_sym p "-" in
      let n, tn = eat_num p in
      let tend = eat_p p ")" in
      EParen
        ( { lo = t0.lo; hi = tend.hi },
          EPre ({ lo = tm.lo; hi = tn.hi }, "-", ENum ({ lo = tn.lo; hi = tn.hi }, n)) )
  | _ -> raise Fail

and cap_incoming p =
  let l = cap_expr p in
  ignore (eat_sym p "=>");
  let v = cap_expr p in
  `Compound ("-", [ l; v ])

and cap_inst p =
  match peek_kind p with
  | Some (Sym "%") -> (
      ignore (bump p);
      let d, _ = eat_str p in
      let tmp = `Compound ("tmp", [ `Atom d ]) in
      match peek_kind p with
      | Some (Sym ":") ->
          ignore (bump p);
          let k = cap_expr p in
          ignore (eat_sym p "=");
          let o = cap_expr p in
          let args =
            match try_ p (fun p -> ir_seq p cap_expr ",") with
            | Some xs -> xs
            | None -> []
          in
          `Compound ("let", [ tmp; k; o; `Seq args ])
      | _ ->
          ignore (eat_sym p "=");
          let base = cap_expr p in
          ignore (eat_sym p "+");
          ignore (eat_id p "p");
          let off = cap_expr p in
          `Compound
            ( "flight",
              [
                tmp;
                `Atom "add";
                `Seq [ `Compound ("address", [ base ]); off ];
                `Compound ("lower", [ base ]);
              ] ))
  | Some (Id "goto") ->
      ignore (bump p);
      `Compound ("goto", [ cap_expr p ])
  | Some (Id "br") ->
      ignore (bump p);
      let v = cap_expr p in
      ignore (eat_sym p "?");
      let y = cap_expr p in
      ignore (eat_sym p ":");
      let n = cap_expr p in
      `Compound ("branch", [ v; y; n ])
  | Some (Id "ret") -> (
      ignore (bump p);
      match peek_kind p with
      | Some (Id "void") ->
          ignore (bump p);
          `Atom "ret"
      | _ -> `Compound ("ret", [ cap_expr p ]))
  | Some (Id "unreachable") ->
      ignore (bump p);
      `Atom "unreachable"
  | Some (Id "alloca") ->
      ignore (bump p);
      let d, _ = eat_str p in
      let n = cap_number p in
      `Compound ("local_alloc", [ `Atom d; `Int n ])
  | Some (Id "store") ->
      ignore (bump p);
      let w = cap_expr p in
      let a, off, v = cap_store p in
      `Compound ("raw_store", [ w; `Int off; v; a ])
  | Some (Id "store.ptr") ->
      ignore (bump p);
      let a, off, v = cap_store p in
      let es =
        List.map
          (fun s -> `Atom s)
          [ "aux_ensure"; "lower_barrier"; "rooted_reload"; "lower_write"; "address_write" ]
      in
      `Compound ("raw_store_pointer", [ `Int off; v; a; `Seq es ])
  | Some (Id (("call" | "rawcall") as kw)) ->
      ignore (bump p);
      let fn_name = if kw = "call" then "call" else "raw_call" in
      let res =
        match
          try_ p (fun p ->
              ignore (eat_sym p "%");
              let d, _ = eat_str p in
              ignore (eat_sym p ":");
              let k = cap_expr p in
              ignore (eat_sym p "=");
              `Compound ("result", [ `Compound ("tmp", [ `Atom d ]); k ]))
        with
        | Some r -> r
        | None ->
            ignore (eat_id p "void");
            `Atom "void"
      in
      let c = cap_expr p in
      ignore (eat_p p "(");
      let args =
        match peek_kind p with
        | Some (P ")") -> []
        | _ -> ir_seq p cap_arg ","
      in
      ignore (eat_p p ")");
      `Compound (fn_name, [ res; c; `Seq args ])
  | Some (P "(") ->
      ignore (bump p);
      let i = cap_expr p in
      ignore (eat_p p ")");
      i
  | _ -> raise Fail

and cap_store p =
  ignore (eat_p p "[");
  let a = cap_expr p in
  ignore (eat_sym p "+");
  let n = cap_number p in
  ignore (eat_p p "]");
  ignore (eat_sym p "<-");
  let v = cap_expr p in
  (a, n, v)

and cap_arg p =
  let k = cap_expr p in
  let v = cap_expr p in
  `Compound ("arg", [ k; v ])

and cap_tree sp = function
  | `Compound (f, args) ->
      EApp (sp, EId (sp, "TApp"), [ EStr (sp, f); EList (sp, List.map (cap_tree sp) args) ])
  | `Seq args ->
      EApp (sp, EId (sp, "TList"), [ EList (sp, List.map (cap_tree sp) args) ])
  | `ListExpr x -> EApp (sp, EId (sp, "TList"), [ x ])
  | `Atom s -> EApp (sp, EId (sp, "TAtom"), [ EStr (sp, s) ])
  | `Int x -> EApp (sp, EId (sp, "TInt"), [ x ])
  | `Gallina x -> x

(* ── Lists, tuples, records, match ─────────────────────────────────────── *)

and or_rest p =
  let e = term p in
  match peek_kind p with
  | Some (Sym "|") ->
      ignore (bump p);
      e :: or_rest p
  | _ -> [ e ]

and tuple_rest p =
  let e = term p in
  match peek_kind p with
  | Some (P ",") ->
      ignore (bump p);
      e :: tuple_rest p
  | _ -> [ e ]

and list_elems p =
  let e = term p in
  match peek_kind p with
  | Some (P ";") ->
      ignore (bump p);
      e :: list_elems p
  | _ -> [ e ]

and rec_fields p =
  match peek_kind p with
  | Some (Id x) -> (
      let t0 = bump p in
      let bs = parse_binders0 p in
      ignore (eat_sym p ":=");
      let e = term p in
      let sp = { lo = t0.lo; hi = (expr_span e).hi } in
      let fld = if bs = [] then RFld (sp, x, e) else RFldB (sp, x, bs, e) in
      match peek_kind p with
      | Some (P ";") ->
          ignore (bump p);
          fld :: rec_fields p
      | _ -> [ fld ])
  | _ -> []

and scrutinees p =
  let s0 = expr p ~max:100 in
  let s =
    match peek_kind p with
    | Some (Kw "as") ->
        ignore (bump p);
        ScrutAs (s0, parse_name p)
    | _ -> ScrutExpr s0
  in
  match peek_kind p with
  | Some (P ",") ->
      ignore (bump p);
      s :: scrutinees p
  | _ -> [ s ]

and branches p =
  match
    try_ p (fun p ->
        let alts = with_in_pattern p true alternatives in
        eat_arrow_kw p;
        let rhs = term p in
        { br_alts = alts; br_rhs = rhs })
  with
  | None -> []
  | Some br -> (
      match peek_kind p with
      | Some (Sym "|") ->
          ignore (bump p);
          br :: branches p
      | _ -> [ br ])

and alternatives p =
  let ps = patterns p in
  match peek_kind p with
  | Some (Sym "|") ->
      ignore (bump p);
      ps :: alternatives p
  | _ -> [ ps ]

and patterns p =
  let pat = expr p ~max:99 in
  match peek_kind p with
  | Some (P ",") ->
      ignore (bump p);
      pat :: patterns p
  | _ -> [ pat ]
