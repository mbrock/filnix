(* Checked IR (IRNotation.v) HTML renderer mirroring rocq_draw.pl lines 705-1357. *)

open Ast
open Draw_env
open Html

let nbsp = "\xc2\xa0"

let term ctx b e env = !Draw_hooks.draw_term_ref ctx b e env
let kw b s = !Draw_hooks.draw_kw_ref b s
let notes_before ctx b off = !Draw_hooks.notes_before_ref ctx b off
let aside_after ctx b off = !Draw_hooks.aside_after_ref ctx b off

let rec ir_unparen = function EParen (_, e0) -> ir_unparen e0 | e -> e

let rec ir_neg_num = function
  | EPre (_, "-", ENum (_, n)) -> Some n
  | EParen (_, e) -> ir_neg_num e
  | _ -> None

type ir_role = ROp | RMemory | RCheck | RControl

let ir_role_class = function
  | ROp -> "rq-ir-op"
  | RMemory -> "rq-ir-op-memory"
  | RCheck -> "rq-ir-op-check"
  | RControl -> "rq-ir-op-control"

let ir_class_gloss = function
  | "W" -> Some "W: 32-bit integer (word)"
  | "L" -> Some "L: 64-bit integer (long)"
  | "P" -> Some "P: pointer with Fil-C capability"
  | "A" -> Some "A: proven address cleared by a capability check"
  | "F" -> Some "F: proven function entry address"
  | "Single" -> Some "Single: 32-bit IEEE float"
  | "Double" -> Some "Double: 64-bit IEEE float"
  | "Extended" -> Some "Extended: 80-bit extended float"
  | _ -> None

let ir_type_gloss = function
  | "Wb" -> Some "Wb: 1-byte (8-bit) width"
  | "Wh" -> Some "Wh: 2-byte (16-bit) width"
  | "Ww" -> Some "Ww: 4-byte (32-bit) width"
  | "Wl" -> Some "Wl: 8-byte (64-bit) width"
  | "Wp" -> Some "Wp: 8-byte pointer with capability"
  | "Ws" -> Some "Ws: 4-byte float width"
  | "Wd" -> Some "Wd: 8-byte double width"
  | "Wx" -> Some "Wx: 10-byte extended float width"
  | "Sb" -> Some "Sb: signed 8-bit byte"
  | "Ub" -> Some "Ub: unsigned 8-bit byte"
  | "Sh" -> Some "Sh: signed 16-bit halfword"
  | "Uh" -> Some "Uh: unsigned 16-bit halfword"
  | "Sw" -> Some "Sw: signed 32-bit word"
  | "Uw" -> Some "Uw: unsigned 32-bit word"
  | "LdL" -> Some "LdL: load 64-bit integer"
  | "LdS" -> Some "LdS: load 32-bit float"
  | "LdD" -> Some "LdD: load 64-bit float"
  | "LdX" -> Some "LdX: load 80-bit extended float"
  | "CasL" -> Some "CasL: 64-bit integer compare-and-exchange"
  | "CasP" -> Some "CasP: pointer compare-and-exchange"
  | "Signed" -> Some "Signed: two's-complement signed integer"
  | "Unsigned" -> Some "Unsigned: unsigned integer"
  | _ -> None

let ir_cond_gloss = function
  | "Eq" -> Some "Eq: ="
  | "Ne" -> Some "Ne: ≠"
  | "Slt" -> Some "Slt: <, signed"
  | "Sle" -> Some "Sle: ≤, signed"
  | "Sgt" -> Some "Sgt: >, signed"
  | "Sge" -> Some "Sge: ≥, signed"
  | "Ult" -> Some "Ult: <, unsigned"
  | "Ule" -> Some "Ule: ≤, unsigned"
  | "Ugt" -> Some "Ugt: >, unsigned"
  | "Uge" -> Some "Uge: ≥, unsigned"
  | "Lt" -> Some "Lt: <"
  | "Le" -> Some "Le: ≤"
  | "Gt" -> Some "Gt: >"
  | "Ge" -> Some "Ge: ≥"
  | "Ord" -> Some "Ord: ordered (neither is NaN)"
  | "Unord" -> Some "Unord: unordered (one is NaN)"
  | "Upper" -> Some "Upper: check upper bound only"
  | "Lower" -> Some "Lower: check lower bound only"
  | _ -> None

let ir_right_gloss = function
  | "Read" -> Some ("rq-ir-cond", "Read: read access right")
  | "Write" -> Some ("rq-ir-right-write", "Write: write access right (rejected by read-only capabilities)")
  | _ -> None

let ir_op_gloss = function
  | "Add" -> Some (ROp, "Add: +")
  | "Sub" -> Some (ROp, "Sub: −")
  | "Mul" -> Some (ROp, "Mul: ×")
  | "Div" -> Some (ROp, "Div: ÷, signed")
  | "Udiv" -> Some (ROp, "Udiv: ÷, unsigned")
  | "Rem" -> Some (ROp, "Rem: remainder, signed")
  | "Urem" -> Some (ROp, "Urem: remainder, unsigned")
  | "And" -> Some (ROp, "And: bitwise and")
  | "Or" -> Some (ROp, "Or: bitwise or")
  | "Xor" -> Some (ROp, "Xor: bitwise exclusive or")
  | "Shl" -> Some (ROp, "Shl: shift left")
  | "Shr" -> Some (ROp, "Shr: logical shift right (zero-fill)")
  | "Sar" -> Some (ROp, "Sar: arithmetic shift right (sign-extending)")
  | "Neg" -> Some (ROp, "Neg: negate")
  | "Copy" -> Some (ROp, "Copy: value copy (or materialize global pointer)")
  | "Ptoi" -> Some (ROp, "Ptoi: pointer to integer (drops capability)")
  | "Itop" -> Some (ROp, "Itop: integer to pointer (null capability)")
  | "Select" -> Some (ROp, "Select: second value if first is nonzero, else third")
  | "Cmp" -> Some (ROp, "Cmp: compare two values (1 if condition holds, else 0)")
  | "Ext" -> Some (ROp, "Ext: sign- or zero-extend narrow integer")
  | "ExtF" -> Some (ROp, "ExtF: widen floating-point value")
  | "Truncd" -> Some (ROp, "Truncd: double to single")
  | "Truncx" -> Some (ROp, "Truncx: extended float to narrower format")
  | "FloatToInt" -> Some (ROp, "FloatToInt: truncate float to integer")
  | "IntToFloat" -> Some (ROp, "IntToFloat: convert integer to float")
  | "Cast" -> Some (ROp, "Cast: reinterpret bit pattern between integer and float")
  | "Sqrt" -> Some (ROp, "Sqrt: IEEE square root")
  | "VaArgs" -> Some (ROp, "VaArgs: variadic argument cursor")
  | "VaArg" -> Some (ROp, "VaArg: read next variadic argument")
  | "Setjmp" -> Some (ROp, "Setjmp: save return context")
  | "Alloc" -> Some (RMemory, "Alloc: allocate zeroed heap object with fresh Fil-C capability")
  | "RawLoad" -> Some (RMemory, "RawLoad: read memory at proven address + offset (no check of its own)")
  | "RawLoadPointer" -> Some (RMemory, "RawLoadPointer: read pointer and capability at proven address + offset")
  | "RawCas" -> Some (RMemory, "RawCas: atomic compare-and-exchange at proven address + offset")
  | "Check" -> Some (RCheck, "Check: verify pointer bounds [lo, hi), rights and alignment; yields proven address A")
  | "CheckAhead" -> Some (RCheck, "CheckAhead: verify current span [lo, ahi) and ahead span [ahi, hi)")
  | "Renew" -> Some (RCheck, "Renew: reuse a dominating check's bounds for a derived pointer")
  | "RenewHull" -> Some (RCheck, "RenewHull: reuse bounds within the hull of two dominating checks")
  | "HalfCheck" -> Some (RCheck, "HalfCheck: test one bound when the other is already proved")
  | "SpanTest" -> Some (RCheck, "SpanTest: return 1 if pointer object covers [lo, hi), else 0")
  | "RenewIf" -> Some (RCheck, "RenewIf: reuse bounds guarded by a passing SpanTest")
  | "Limit" -> Some (RCheck, "Limit: capture opaque bounds snapshot for accesses of size bytes")
  | "CheckLimit" -> Some (RCheck, "CheckLimit: verify access against a captured Limit")
  | "CheckLocal" -> Some (RCheck, "CheckLocal: prove in-bounds access to a named stack local")
  | "CheckFunction" -> Some (RCheck, "CheckFunction: verify pointer is an exact function entry")
  | _ -> None

let ir_op_pz op0 =
  let h_opt =
    match ir_unparen op0 with
    | EId (_, h) | EApp (_, EId (_, h), _) -> Some h
    | _ -> None
  in
  match h_opt with
  | Some
      ( "Check" | "CheckAhead" | "Renew" | "RenewHull" | "HalfCheck" | "SpanTest"
      | "RenewIf" | "Limit" | "CheckLimit" | "CheckLocal" | "CheckFunction"
      | "RawLoad" | "RawLoadPointer" | "RawCas" ) ->
      true
  | _ -> false

let ir_ssa_pz = function
  | IrLet (_, _, op, _) -> ir_op_pz op
  | IrStore _ | IrStorePtr _ | IrCall ("rawcall", _, _, _) | IrGoto (IrPoll _) -> true
  | IrBr (_, IrPoll _, _) | IrBr (_, _, IrPoll _) -> true
  | IrSsaEscape x -> (
      match ir_unparen x with
      | EApp (_, EId (_, ("RawStore" | "RawStorePointer" | "RawCall" | "Touch")), _) -> true
      | _ -> false)
  | _ -> false

let ir_raw_value_name raw =
  let n = String.length raw in
  let i = ref n in
  while !i > 0 && raw.[!i - 1] >= '0' && raw.[!i - 1] <= '9' do
    decr i
  done;
  if !i = 0 || !i = n then (raw, None)
  else
    let digits = String.sub raw !i (n - !i) in
    let stem0 = String.sub raw 0 !i in
    let slen = String.length stem0 in
    let stem =
      if slen > 1 && (stem0.[slen - 1] = '.' || stem0.[slen - 1] = '_') then
        String.sub stem0 0 (slen - 1)
      else stem0
    in
    (stem, Some digits)

let next_ir_prefix ctx =
  ctx.ir_seq <- ctx.ir_seq + 1;
  Printf.sprintf "ir%d--" ctx.ir_seq

let ir_block_anchor ctx lab =
  match ctx.ir_labels with
  | Some lbls when Hashtbl.mem lbls.ir_set lab ->
      Some (lbls.ir_prefix ^ uri_encode_fragment lab)
  | _ -> None

let ir_sym ctx b rocq_name label cls tip =
  if not ctx.in_button then
    match global_ref ctx rocq_name with
    | Some (href, _) ->
        el_a b "a" (Some cls) [ ("href", href); ("title", tip) ] (fun b -> esc b label)
    | None -> el_a b "span" (Some cls) [ ("title", tip) ] (fun b -> esc b label)
  else el_a b "span" (Some cls) [ ("title", tip) ] (fun b -> esc b label)

let ir_tmp ctx b role x env =
  match x with
  | EStr (_, name) ->
      let var_key = "%" ^ name in
      let stem, sub = ir_raw_value_name name in
      let cls = if role = `Def then "v ir-value def" else "v ir-value" in
      let tip = Printf.sprintf "SSA temporary %%\"%s\"" name in
      el_a b "span" (Some cls)
        [ ("data-v", var_key); ("data-tmp", name); ("title", tip) ]
        (fun b ->
          el_raw b "span" (Some "value-role") "%";
          esc b stem;
          Option.iter (fun s -> el_text b "sub" None s) sub)
  | _ ->
      let cls = if role = `Def then "ir-value def" else "ir-value" in
      el b "span" (Some cls) (fun b ->
          el_raw b "span" (Some "value-role") "%";
          term ctx b x env)

let ir_tmp_def ctx b x env = ir_tmp ctx b `Def x env
let ir_tmp_use ctx b x env = ir_tmp ctx b `Use x env

let ir_num_or_term ctx b e env =
  match e with
  | ENum (_, n) -> el_text b "span" (Some "n") n
  | _ -> (
      match ir_neg_num e with
      | Some n ->
          el b "span" (Some "n") (fun b ->
              raw b "−";
              esc b n)
      | None -> term ctx b e env)

let ir_class_badge ctx b e env =
  match e with
  | EId (_, k) -> (
      match ir_class_gloss k with
      | Some tip -> ir_sym ctx b k k "rq-ir-class" tip
      | None -> term ctx b e env)
  | _ -> term ctx b e env

let ir_type_badge ctx b e env =
  match e with
  | EId (_, t) -> (
      match ir_type_gloss t with
      | Some tip -> ir_sym ctx b t t "rq-ir-type" tip
      | None -> term ctx b e env)
  | _ -> term ctx b e env

let ir_cond_badge ctx b e env =
  match e with
  | EId (_, c) -> (
      match ir_cond_gloss c with
      | Some tip -> ir_sym ctx b c c "rq-ir-cond" tip
      | None -> term ctx b e env)
  | _ -> term ctx b e env

let ir_right_badge ctx b e env =
  match e with
  | EId (_, r) -> (
      match ir_right_gloss r with
      | Some (cls, tip) -> ir_sym ctx b r r cls tip
      | None -> term ctx b e env)
  | _ -> term ctx b e env

let ir_label_ref ctx b e env =
  match e with
  | EStr (_, lab) -> (
      let tip = Printf.sprintf "block @\"%s\"" lab in
      match (ctx.in_button, ir_block_anchor ctx lab) with
      | false, Some id ->
          el_a b "a" (Some "rq-ir-lbl")
            [ ("href", "#" ^ id); ("data-ir-label", lab); ("title", tip) ]
            (fun b ->
              el_raw b "span" (Some "rq-ir-sigil") "@";
              esc b lab)
      | _ ->
          el_a b "span" (Some "rq-ir-lbl")
            [ ("data-ir-label", lab); ("title", tip) ]
            (fun b ->
              el_raw b "span" (Some "rq-ir-sigil") "@";
              esc b lab))
  | _ ->
      el b "span" (Some "rq-ir-lbl") (fun b ->
          el_raw b "span" (Some "rq-ir-sigil") "@";
          term ctx b e env)

let ir_opnd ctx b opnd env =
  match opnd with
  | IrTmp x -> ir_tmp_use ctx b x env
  | IrGlobal (EStr (_, s)) ->
      let tip = Printf.sprintf "global symbol $\"%s\"" s in
      el_a b "span" (Some "rq-ir-global") [ ("title", tip) ] (fun b ->
          el_raw b "span" (Some "value-role") "$";
          esc b s)
  | IrGlobal x ->
      el b "span" (Some "rq-ir-global") (fun b ->
          el_raw b "span" (Some "value-role") "$";
          term ctx b x env)
  | IrConst (ENum (_, n)) ->
      let tip = Printf.sprintf "constant #%s" n in
      el_a b "span" (Some "rq-ir-const") [ ("title", tip) ] (fun b ->
          el_raw b "span" (Some "value-role") "#";
          el_text b "span" (Some "n") n)
  | IrConst x -> (
      match ir_neg_num x with
      | Some n ->
          let tip = Printf.sprintf "constant #(-%s)" n in
          el_a b "span" (Some "rq-ir-const") [ ("title", tip) ] (fun b ->
              el_raw b "span" (Some "value-role") "#";
              el b "span" (Some "n") (fun b ->
                  raw b "−";
                  esc b n))
      | None ->
          el b "span" (Some "rq-ir-const") (fun b ->
              el_raw b "span" (Some "value-role") "#";
              term ctx b x env))
  | IrVal x -> term ctx b x env

let ir_edge_draw ctx b edge env =
  match edge with
  | IrTo l -> ir_label_ref ctx b l env
  | IrPoll l ->
      ir_sym ctx b "Poll" "poll" "rq-ir-op-check"
        "Poll: garbage-collection safepoint check on this edge";
      raw b nbsp;
      ir_label_ref ctx b l env
  | IrEdgeExpr x -> term ctx b x env

type ir_param_kind =
  | PCls of expr
  | PCond of expr
  | PTy of expr
  | PRight of expr
  | PRange of expr * expr
  | PLoadTy of expr
  | PCasTy of expr
  | PNum of expr
  | PRaw of expr

let rec ir_op_params ctx b ps env =
  match ps with
  | [] -> ()
  | [ p ] -> el b "span" (Some "arg") (fun b -> ir_op_param ctx b p env)
  | p :: rest ->
      el b "span" (Some "arg") (fun b ->
          ir_op_param ctx b p env;
          el_raw b "span" (Some "sep") ",");
      raw_char b ' ';
      ir_op_params ctx b rest env

and ir_op_param ctx b p env =
  match p with
  | PCls e -> ir_class_badge ctx b e env
  | PCond e -> ir_cond_badge ctx b e env
  | PTy e -> ir_type_badge ctx b e env
  | PRight e -> ir_right_badge ctx b e env
  | PRange (lo, hi) ->
      el_a b "span" (Some "rq-ir-range") [ ("title", "byte offset range [lo, hi)") ] (fun b ->
          ir_num_or_term ctx b lo env;
          el_raw b "span" (Some "op tight") "..";
          ir_num_or_term ctx b hi env)
  | PLoadTy e -> (
      match ir_unparen e with
      | EApp (_, EId (_, "LdNarrow"), [ n ]) -> ir_type_badge ctx b n env
      | _ -> ir_type_badge ctx b e env)
  | PCasTy e -> (
      match ir_unparen e with
      | EApp (_, EId (_, "CasNarrow"), [ n ]) -> ir_type_badge ctx b n env
      | _ -> ir_type_badge ctx b e env)
  | PNum e -> ir_num_or_term ctx b e env
  | PRaw e -> term ctx b e env

let ir_op_call ctx b head role params env =
  let tip = match ir_op_gloss head with Some (_, t) -> t | None -> head in
  let cls = ir_role_class role in
  el_a b "span" (Some "c rq-ir-op-call") [ ("data-d", "args") ] (fun b ->
      ir_sym ctx b head head cls tip;
      el b "span" (Some "args") (fun b -> ir_op_params ctx b params env))

let ir_op_draw ctx b op0 env =
  match ir_unparen op0 with
  | EId (_, name) -> (
      match ir_op_gloss name with
      | Some (role, tip) -> ir_sym ctx b name name (ir_role_class role) tip
      | None -> term ctx b (ir_unparen op0) env)
  | EApp (_, EId (_, "Cmp"), [ cond; cls ]) -> ir_op_call ctx b "Cmp" ROp [ PCond cond; PCls cls ] env
  | EApp (_, EId (_, "Ext"), [ ty ]) -> ir_op_call ctx b "Ext" ROp [ PTy ty ] env
  | EApp (_, EId (_, "ExtF"), [ cls ]) -> ir_op_call ctx b "ExtF" ROp [ PCls cls ] env
  | EApp (_, EId (_, "FloatToInt"), [ cls; sg ]) ->
      ir_op_call ctx b "FloatToInt" ROp [ PCls cls; PTy sg ] env
  | EApp (_, EId (_, "IntToFloat"), [ cls; sg ]) ->
      ir_op_call ctx b "IntToFloat" ROp [ PCls cls; PTy sg ] env
  | EApp (_, EId (_, "Setjmp"), [ kind ]) -> ir_op_call ctx b "Setjmp" ROp [ PRaw kind ] env
  | EApp (_, EId (_, "Alloc"), [ align ]) -> ir_op_call ctx b "Alloc" RMemory [ PNum align ] env
  | EApp
      ( _,
        EId (_, (("Check" | "Renew" | "RenewHull" | "RenewIf" | "CheckLimit") as head)),
        [ lo; hi; r; align ] ) ->
      ir_op_call ctx b head RCheck [ PRange (lo, hi); PRight r; PNum align ] env
  | EApp (_, EId (_, "CheckAhead"), [ lo; hi; r; align; ahi ]) ->
      ir_op_call ctx b "CheckAhead" RCheck [ PRange (lo, hi); PRight r; PNum align; PNum ahi ] env
  | EApp (_, EId (_, "HalfCheck"), [ cond; lo; hi; r; align ]) ->
      ir_op_call ctx b "HalfCheck" RCheck
        [ PCond cond; PRange (lo, hi); PRight r; PNum align ]
        env
  | EApp (_, EId (_, "SpanTest"), [ lo; hi ]) ->
      ir_op_call ctx b "SpanTest" RCheck [ PRange (lo, hi) ] env
  | EApp (_, EId (_, "Limit"), [ sz ]) -> ir_op_call ctx b "Limit" RCheck [ PNum sz ] env
  | EApp (_, EId (_, "CheckLocal"), [ x; off; bytes; r; align ]) ->
      ir_op_call ctx b "CheckLocal" RCheck
        [ PRaw x; PNum off; PNum bytes; PRight r; PNum align ]
        env
  | EApp (_, EId (_, "RawLoad"), [ ld_ty; off ]) ->
      ir_op_call ctx b "RawLoad" RMemory [ PLoadTy ld_ty; PNum off ] env
  | EApp (_, EId (_, "RawLoadPointer"), [ off; es ]) ->
      ir_op_call ctx b "RawLoadPointer" RMemory [ PNum off; PRaw es ] env
  | EApp (_, EId (_, "RawCas"), [ cas_ty; off ]) ->
      ir_op_call ctx b "RawCas" RMemory [ PCasTy cas_ty; PNum off ] env
  | op -> term ctx b op env

(* Gallina escape recognition for Flight and Touch *)
let ir_name_str e0 =
  match ir_unparen e0 with
  | EApp (_, EId (_, ("TAtom" | "a")), [ (EStr _ as s) ]) -> Some s
  | _ -> None

let ir_gallina_opnd e0 =
  match ir_unparen e0 with
  | EApp (_, EId (_, "t"), [ (EStr _ as s) ]) -> IrTmp s
  | EApp (_, EId (_, "Tmp"), [ dst0 ]) -> (
      match ir_name_str dst0 with Some d -> IrTmp d | None -> IrVal e0)
  | EApp (_, EId (_, "Global"), [ g0 ]) -> (
      match ir_name_str g0 with Some g -> IrGlobal g | None -> IrVal e0)
  | EApp (_, EId (_, "Const"), [ n ]) -> IrConst n
  | _ -> IrVal e0

let ir_flight_arg e0 =
  match ir_unparen e0 with
  | EApp (_, EId (_, "FAddress"), [ v0 ]) -> Some (`Addr (ir_gallina_opnd v0))
  | EApp (_, EId (_, "FValue"), [ v0 ]) -> Some (`Val (ir_gallina_opnd v0))
  | _ -> None

let ir_flight_lower e0 =
  match ir_unparen e0 with
  | EId (_, "LowerNone") -> Some `None
  | EApp (_, EId (_, "LowerOf"), [ v0 ]) -> Some (`Of (ir_gallina_opnd v0))
  | _ -> None

let ir_opnd_same a b =
  match (a, b) with
  | IrTmp (EStr (_, s1)), IrTmp (EStr (_, s2)) -> s1 = s2
  | IrGlobal (EStr (_, s1)), IrGlobal (EStr (_, s2)) -> s1 = s2
  | _ -> false

let rec ir_flight_args_draw ctx b args env =
  let draw_one a = match a with `Addr v | `Val v -> ir_opnd ctx b v env in
  match args with
  | [] -> ()
  | [ a ] -> el b "span" (Some "arg") (fun _ -> draw_one a)
  | a :: rest ->
      el b "span" (Some "arg") (fun b ->
          draw_one a;
          el_raw b "span" (Some "sep") ",");
      raw_char b ' ';
      ir_flight_args_draw ctx b rest env

let try_ir_escape_draw ctx b x0 env =
  match ir_unparen x0 with
  | EApp (_, EId (_, "Flight"), [ dst0; op0; EList (_, fargs0); lower0 ]) -> (
      match (ir_name_str dst0, ir_flight_lower lower0) with
      | Some dst, Some lower -> (
          let parsed = List.filter_map ir_flight_arg fargs0 in
          if List.length parsed <> List.length fargs0 then false
          else
            match (ir_unparen op0, parsed, lower) with
            | EId (_, "Sub"), [ `Addr base; `Val off ], `Of donor when ir_opnd_same base donor ->
                el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
                    ir_tmp_def ctx b dst env;
                    raw b nbsp;
                    el_a b "span" (Some "op wide") [ ("title", "=") ] (fun b -> raw b "=");
                    raw_char b ' ';
                    el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
                        ir_opnd ctx b base env;
                        raw b nbsp;
                        ir_sym ctx b "Flight" "−p" "op wide rq-ir-op"
                          "Flight Sub (LowerOf base): pointer subtraction preserving base's Fil-C capability";
                        raw_char b ' ';
                        ir_opnd ctx b off env));
                true
            | _ ->
                el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
                    ir_tmp_def ctx b dst env;
                    raw b nbsp;
                    el_a b "span" (Some "op wide") [ ("title", "=") ] (fun b -> raw b "=");
                    raw_char b ' ';
                    el_a b "span" (Some "c app rq-ir-op-app") [ ("data-d", "args") ] (fun b ->
                        el_a b "span" (Some "c rq-ir-op-call") [ ("data-d", "args") ] (fun b ->
                            ir_sym ctx b "Flight" "Flight" "rq-ir-op"
                              "Flight: pointer arithmetic with explicit capability donor";
                            el b "span" (Some "args") (fun b ->
                                el b "span" (Some "arg") (fun b ->
                                    ir_op_draw ctx b op0 env;
                                    el_raw b "span" (Some "sep") ",");
                                raw_char b ' ';
                                el b "span" (Some "arg") (fun b ->
                                    match lower with
                                    | `None ->
                                        ir_sym ctx b "LowerNone" "lower none" "rq-ir-void"
                                          "LowerNone: null capability"
                                    | `Of v ->
                                        ir_sym ctx b "LowerOf" "lower" "rq-ir-op"
                                          "LowerOf: copy capability from this pointer";
                                        raw b nbsp;
                                        ir_opnd ctx b v env)));
                        el b "span" (Some "args") (fun b -> ir_flight_args_draw ctx b parsed env)));
                true)
      | _ -> false)
  | EApp (_, EId (_, "Touch"), [ q0 ]) -> (
      match ir_name_str q0 with
      | Some q ->
          ir_sym ctx b "Touch" "touch" "rq-ir-op-check"
            "Touch: consume proof temporary from a preceding vector check";
          raw b nbsp;
          ir_tmp_use ctx b q env;
          true
      | None -> false)
  | _ -> false

let rec ir_opnd_args ctx b args env =
  match args with
  | [] -> ()
  | [ a ] -> el b "span" (Some "arg") (fun b -> ir_opnd ctx b a env)
  | a :: rest ->
      el b "span" (Some "arg") (fun b ->
          ir_opnd ctx b a env;
          el_raw b "span" (Some "sep") ",");
      raw_char b ' ';
      ir_opnd_args ctx b rest env

let rec ir_call_args ctx b args env =
  match args with
  | [] -> ()
  | [ a ] ->
      el b "span" (Some "arg") (fun b ->
          ir_class_badge ctx b a.ira_ty env;
          raw b nbsp;
          ir_opnd ctx b a.ira_val env)
  | a :: rest ->
      el b "span" (Some "arg") (fun b ->
          ir_class_badge ctx b a.ira_ty env;
          raw b nbsp;
          ir_opnd ctx b a.ira_val env;
          el_raw b "span" (Some "sep") ",");
      raw_char b ' ';
      ir_call_args ctx b rest env

let ir_call_target ctx b fn args env =
  el_a b "span" (Some "c rq-ir-call-args") [ ("data-d", "args") ] (fun b ->
      ir_opnd ctx b fn env;
      if args = [] then el_empty b "span" (Some "args rq-ir-empty")
      else el b "span" (Some "args") (fun b -> ir_call_args ctx b args env))

let ir_mem_addr ctx b addr off env =
  el b "span" (Some "l rq-ir-addr") (fun b ->
      ir_opnd ctx b addr env;
      raw b nbsp;
      el_raw b "span" (Some "op") "+";
      raw b nbsp;
      ir_num_or_term ctx b off env)

let ir_local_name ctx b e env =
  match e with
  | EStr (_, s) ->
      let tip = Printf.sprintf "stack local \"%s\"" s in
      el_a b "span" (Some "rq-ir-local") [ ("title", tip) ] (fun b -> esc b s)
  | _ -> term ctx b e env

let ir_ssa_kind_draw ctx b kind env =
  match kind with
  | IrSsaEscape x -> if not (try_ir_escape_draw ctx b x env) then term ctx b x env
  | IrLet (d, k, op, args) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          el b "span" (Some "rq-ir-lhs") (fun b ->
              ir_tmp_def ctx b d env;
              raw b nbsp;
              el_a b "span" (Some "rq-ir-colon") [ ("title", ":") ] (fun b -> raw b ":");
              raw b nbsp;
              ir_class_badge ctx b k env);
          raw b nbsp;
          el_a b "span" (Some "op wide") [ ("title", "=") ] (fun b -> raw b "=");
          raw_char b ' ';
          if args = [] then ir_op_draw ctx b op env
          else
            el_a b "span" (Some "c app rq-ir-op-app") [ ("data-d", "args") ] (fun b ->
                ir_op_draw ctx b op env;
                el b "span" (Some "args") (fun b -> ir_opnd_args ctx b args env)))
  | IrFlight (d, base, off) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          ir_tmp_def ctx b d env;
          raw b nbsp;
          el_a b "span" (Some "op wide") [ ("title", "=") ] (fun b -> raw b "=");
          raw_char b ' ';
          el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
              ir_opnd ctx b base env;
              raw b nbsp;
              ir_sym ctx b "Flight" "+p" "op wide rq-ir-op"
                "Flight Add (LowerOf base): pointer arithmetic preserving base's Fil-C capability";
              raw_char b ' ';
              ir_opnd ctx b off env))
  | IrStore (sz, addr, off, src) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          el b "span" (Some "rq-ir-lhs") (fun b ->
              ir_sym ctx b "RawStore" "store" "rq-ir-op-memory"
                "RawStore: write value to memory at proven address + offset";
              raw b nbsp;
              ir_type_badge ctx b sz env;
              raw b nbsp;
              ir_mem_addr ctx b addr off env);
          raw b nbsp;
          el_a b "span" (Some "op wide rq-ir-store-arrow") [ ("title", "<-") ] (fun b ->
              raw b "←");
          raw_char b ' ';
          ir_opnd ctx b src env)
  | IrStorePtr (addr, off, src) ->
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          el b "span" (Some "rq-ir-lhs") (fun b ->
              ir_sym ctx b "RawStorePointer" "store.ptr" "rq-ir-op-memory"
                "RawStorePointer: write pointer and capability at proven address + offset";
              raw b nbsp;
              ir_mem_addr ctx b addr off env);
          raw b nbsp;
          el_a b "span" (Some "op wide rq-ir-store-arrow") [ ("title", "<-") ] (fun b ->
              raw b "←");
          raw_char b ' ';
          ir_opnd ctx b src env)
  | IrAlloca (x, sz) ->
      ir_sym ctx b "LocalAlloc" "alloca" "rq-ir-op-memory"
        "LocalAlloc: allocate zeroed stack local object";
      raw b nbsp;
      ir_local_name ctx b x env;
      raw b nbsp;
      ir_num_or_term ctx b sz env
  | IrCall (kw_s, res, fn, args) ->
      let ctor, kws, cls, tip =
        if kw_s = "rawcall" then
          ("RawCall", "rawcall", "rq-ir-op-check", "RawCall: call proven function address (class F) with no check")
        else
          ("Call", "call", "rq-ir-op-control", "Call: check callee capability and invoke function")
      in
      (match res with
      | IrCallRes (d, k) ->
          el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
              el b "span" (Some "rq-ir-lhs") (fun b ->
                  ir_sym ctx b ctor kws cls tip;
                  raw b nbsp;
                  ir_tmp_def ctx b d env;
                  raw b nbsp;
                  el_a b "span" (Some "rq-ir-colon") [ ("title", ":") ] (fun b -> raw b ":");
                  raw b nbsp;
                  ir_class_badge ctx b k env);
              raw b nbsp;
              el_a b "span" (Some "op wide") [ ("title", "=") ] (fun b -> raw b "=");
              raw_char b ' ';
              ir_call_target ctx b fn args env)
      | IrCallVoid ->
          ir_sym ctx b ctor kws cls tip;
          raw b nbsp;
          ir_sym ctx b "CVoid" "void" "rq-ir-void" "CVoid: no return value";
          raw b nbsp;
          ir_call_target ctx b fn args env)
  | IrGoto edge ->
      ir_sym ctx b "JGoto" "goto" "rq-ir-op-control" "JGoto: jump unconditionally to block";
      raw b nbsp;
      ir_edge_draw ctx b edge env
  | IrBr (cond, yes, no) ->
      ir_sym ctx b "JBranch" "br" "rq-ir-op-control"
        "JBranch: jump to first block if condition is nonzero, else second";
      raw b nbsp;
      el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
          ir_opnd ctx b cond env;
          raw b nbsp;
          el_a b "span" (Some "op wide") [ ("title", "?") ] (fun b -> raw b "?");
          raw_char b ' ';
          el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
              ir_edge_draw ctx b yes env;
              raw b nbsp;
              el_a b "span" (Some "op wide") [ ("title", ":") ] (fun b -> raw b ":");
              raw_char b ' ';
              ir_edge_draw ctx b no env))
  | IrRet IrRetVoid ->
      ir_sym ctx b "JRetVoid" "ret" "rq-ir-op-control" "JRetVoid: return from void function";
      raw b nbsp;
      el_raw b "span" (Some "rq-ir-void") "void"
  | IrRet (IrRetVal v) ->
      ir_sym ctx b "JRet" "ret" "rq-ir-op-control" "JRet: return value from function";
      raw b nbsp;
      ir_opnd ctx b v env
  | IrUnreachable ->
      ir_sym ctx b "JUnreachable" "unreachable" "rq-ir-op-control"
        "JUnreachable: traps immediately if control reaches this point"

let ir_ssa_draw ctx b s env = ir_ssa_kind_draw ctx b s.irs_kind env

let rec ir_incomings ctx b incs env =
  match incs with
  | [] -> ()
  | [ inc ] ->
      el b "span" (Some "arg") (fun b ->
          ir_label_ref ctx b inc.iri_lab env;
          raw b nbsp;
          el_a b "span" (Some "op wide") [ ("title", "=>") ] (fun b -> raw b "⇒");
          raw b nbsp;
          ir_opnd ctx b inc.iri_val env)
  | inc :: rest ->
      el b "span" (Some "arg") (fun b ->
          ir_label_ref ctx b inc.iri_lab env;
          raw b nbsp;
          el_a b "span" (Some "op wide") [ ("title", "=>") ] (fun b -> raw b "⇒");
          raw b nbsp;
          ir_opnd ctx b inc.iri_val env;
          el_raw b "span" (Some "sep") ",");
      raw_char b ' ';
      ir_incomings ctx b rest env

let ir_phi_draw ctx b d k incs env =
  el_a b "span" (Some "o") [ ("data-d", "op") ] (fun b ->
      el b "span" (Some "rq-ir-lhs") (fun b ->
          ir_tmp_def ctx b d env;
          raw b nbsp;
          el_a b "span" (Some "rq-ir-colon") [ ("title", ":") ] (fun b -> raw b ":");
          raw b nbsp;
          ir_class_badge ctx b k env);
      raw b nbsp;
      el_a b "span" (Some "op wide") [ ("title", "=") ] (fun b -> raw b "=");
      raw_char b ' ';
      el_a b "span" (Some "c rq-ir-phi-call") [ ("data-d", "args") ] (fun b ->
          ir_sym ctx b "Phi" "phi" "rq-ir-op-control"
            "Phi: selects the incoming value for the predecessor block control arrived from";
          el b "span" (Some "args") (fun b -> ir_incomings ctx b incs env)))

let ir_inst_row ctx b env s =
  let cls = if ir_ssa_pz s.irs_kind then "goal rq-ir-inst pz" else "goal rq-ir-inst" in
  notes_before ctx b s.irs_span.lo;
  el b "div" (Some cls) (fun b -> ir_ssa_draw ctx b s env);
  aside_after ctx b s.irs_span.hi

let ir_jump_row ctx b j env =
  let cls = if ir_ssa_pz j.irs_kind then "goal rq-ir-jump pz" else "goal rq-ir-jump" in
  notes_before ctx b j.irs_span.lo;
  el b "div" (Some cls) (fun b ->
      el_a b "span" (Some "op rq-ir-term-arrow") [ ("title", "=>") ] (fun b -> raw b "⇒");
      raw b nbsp;
      ir_ssa_draw ctx b j env);
  aside_after ctx b j.irs_span.hi

let ir_phi_row ctx b env = function
  | IrPhiEscape x ->
      let sp = expr_span x in
      notes_before ctx b sp.lo;
      el b "div" (Some "goal rq-ir-phi") (fun b -> term ctx b x env);
      aside_after ctx b sp.hi
  | IrPhi (sp, d, k, incs) ->
      notes_before ctx b sp.lo;
      el b "div" (Some "goal rq-ir-phi") (fun b -> ir_phi_draw ctx b d k incs env);
      aside_after ctx b sp.hi

let ir_block_insts ctx b ins env =
  match ins with
  | IrInsts is -> List.iter (ir_inst_row ctx b env) is
  | IrCode xs -> (
      match ir_unparen xs with
      | EIrList (_, is) -> List.iter (ir_inst_row ctx b env) is
      | _ ->
          let sp = expr_span xs in
          notes_before ctx b sp.lo;
          el b "div" (Some "goal rq-ir-inst") (fun b ->
              kw b "code";
              raw_char b ' ';
              term ctx b xs env);
          aside_after ctx b sp.hi)

let ir_block_label_cell ctx b l env =
  match l with
  | EStr (_, lab) ->
      let tip = Printf.sprintf "basic block @\"%s\"" lab in
      el_a b "div" (Some "rq-ir-label")
        [ ("data-ir-label", lab); ("title", tip) ]
        (fun b ->
          el_raw b "span" (Some "rq-ir-sigil") "@";
          esc b lab;
          el_raw b "span" (Some "neck") ":")
  | _ ->
      el b "div" (Some "rq-ir-label") (fun b ->
          el_raw b "span" (Some "rq-ir-sigil") "@";
          term ctx b l env;
          el_raw b "span" (Some "neck") ":")

let ir_block_row ctx b env = function
  | IrBlockEscape x ->
      let sp = expr_span x in
      notes_before ctx b sp.lo;
      el b "div" (Some "rq-ir-block rq-ir-block-escape") (fun b ->
          el b "div" (Some "goal rq-ir-escape-block") (fun b ->
              term ctx b x env;
              aside_after ctx b sp.hi))
  | IrBlock (sp, l, phis, ins, j) ->
      notes_before ctx b sp.lo;
      let attrs =
        match (l, ctx.in_button) with
        | EStr (_, lab), false -> (
            match ir_block_anchor ctx lab with Some id -> [ ("id", id) ] | None -> [])
        | _ -> []
      in
      el_a b "div" (Some "rq-ir-block") attrs (fun b ->
          ir_block_label_cell ctx b l env;
          el b "div" (Some "goals") (fun b ->
              List.iter (ir_phi_row ctx b env) phis;
              ir_block_insts ctx b ins env;
              ir_jump_row ctx b j env))

let ir_linkage ctx b lk env =
  match lk with
  | EStr (_, s) ->
      let tip = Printf.sprintf "linkage: %s" s in
      el_a b "span" (Some "rq-ir-linkage") [ ("title", tip) ] (fun b -> esc b s)
  | _ -> term ctx b lk env

let ir_fn_name ctx b nm env =
  match nm with
  | EStr (_, s) ->
      let tip = Printf.sprintf "IR function symbol \"%s\"" s in
      el_a b "span" (Some "rq-ir-fn-name") [ ("title", tip) ] (fun b -> esc b s)
  | _ -> term ctx b nm env

let rec ir_params ctx b ps env =
  match ps with
  | [] -> ()
  | [ p ] ->
      el b "span" (Some "arg") (fun b ->
          ir_class_badge ctx b p.irp_ty env;
          raw b nbsp;
          ir_tmp_def ctx b p.irp_name env)
  | p :: rest ->
      el b "span" (Some "arg") (fun b ->
          ir_class_badge ctx b p.irp_ty env;
          raw b nbsp;
          ir_tmp_def ctx b p.irp_name env;
          el_raw b "span" (Some "sep") ",");
      raw_char b ' ';
      ir_params ctx b rest env

let rec ir_class_tuple ctx b ks env =
  match ks with
  | [] -> ()
  | [ k ] -> el b "span" (Some "arg") (fun b -> ir_class_badge ctx b k env)
  | k :: rest ->
      el b "span" (Some "arg") (fun b ->
          ir_class_badge ctx b k env;
          el_raw b "span" (Some "sep") ",");
      raw_char b ' ';
      ir_class_tuple ctx b rest env

let ir_ret_type ctx b e env =
  match ir_unparen e with
  | EApp (_, EId (_, "RClass"), [ k ]) -> ir_class_badge ctx b k env
  | EId (_, "RVoid") -> ir_sym ctx b "RVoid" "void" "rq-ir-class rq-ir-void" "RVoid: no return value"
  | EApp (_, EId (_, "RTuple"), [ EList (_, ks) ]) ->
      el_a b "span" (Some "c tuple") [ ("data-d", "args") ] (fun b ->
          el b "span" (Some "args") (fun b -> ir_class_tuple ctx b ks env))
  | _ -> term ctx b e env

let ir_fn_head ctx b lk nm ps ret env =
  el_a b "span" (Some "c rq-ir-fn-sig") [ ("data-d", "args") ] (fun b ->
      ir_linkage ctx b lk env;
      raw b nbsp;
      ir_fn_name ctx b nm env;
      if ps = [] then el_empty b "span" (Some "args rq-ir-empty")
      else el b "span" (Some "args") (fun b -> ir_params ctx b ps env));
  raw b nbsp;
  el_a b "span" (Some "op wide") [ ("title", "->") ] (fun b -> raw b "→");
  raw b nbsp;
  ir_ret_type ctx b ret env

let ir_fn_block ctx b lk nm ps ret bs env =
  let prev = ctx.ir_labels in
  (match (bs, ctx.in_button) with
  | IrBodyBlocks blk_list, false ->
      let prefix = next_ir_prefix ctx in
      let ir_set = Hashtbl.create 16 in
      List.iter
        (function IrBlock (_, EStr (_, lab), _, _, _) -> Hashtbl.replace ir_set lab () | _ -> ())
        blk_list;
      ctx.ir_labels <- Some { ir_prefix = prefix; ir_set }
  | _ -> ctx.ir_labels <- None);
  Fun.protect ~finally:(fun () -> ctx.ir_labels <- prev) @@ fun () ->
  el b "div" (Some "rq-ir rq-ir-fn") (fun b ->
      el b "div" (Some "goal rq-ir-head") (fun b -> ir_fn_head ctx b lk nm ps ret env);
      match bs with
      | IrBodyBlocks [] ->
          el b "div" (Some "rq-ir-blocks rq-ir-empty-body") (fun b ->
              el_raw b "div" (Some "goal rq-ir-void") "{ }")
      | IrBodyBlocks blks ->
          el b "div" (Some "rq-ir-blocks") (fun b -> List.iter (ir_block_row ctx b env) blks)
      | IrBodyExpr xs ->
          el b "div" (Some "rq-ir-blocks") (fun b ->
              el b "div" (Some "goal rq-ir-escape-block") (fun b ->
                  kw b "blocks";
                  raw_char b ' ';
                  term ctx b xs env)))

let ir_blk_standalone ctx b blk env =
  el b "div" (Some "rq-ir rq-ir-blk") (fun b ->
      el b "div" (Some "rq-ir-blocks") (fun b -> ir_block_row ctx b env blk))

let ir_list_block ctx b is env =
  el b "div" (Some "rq-ir rq-ir-seq") (fun b -> List.iter (ir_inst_row ctx b env) is)

(* Inline fallbacks *)
let rec ir_inline_ssa_items ctx b is env =
  match is with
  | [] -> ()
  | [ i ] -> el b "span" (Some "arg") (fun b -> ir_ssa_draw ctx b i env)
  | i :: rest ->
      el b "span" (Some "arg") (fun b ->
          ir_ssa_draw ctx b i env;
          el_raw b "span" (Some "sep") ";");
      raw_char b ' ';
      ir_inline_ssa_items ctx b rest env

let ir_inline_phi ctx b p env =
  match p with
  | IrPhiEscape x -> term ctx b x env
  | IrPhi (_, d, k, incs) -> ir_phi_draw ctx b d k incs env

let rec ir_inline_phis ctx b ps env =
  match ps with
  | [] -> ()
  | [ p ] -> ir_inline_phi ctx b p env
  | p :: rest ->
      ir_inline_phi ctx b p env;
      el_raw b "span" (Some "sep") ";";
      raw_char b ' ';
      ir_inline_phis ctx b rest env

let ir_blk_inline ctx b blk env =
  match blk with
  | IrBlockEscape x -> term ctx b x env
  | IrBlock (_, l, phis, ins, j) ->
      ir_label_ref ctx b l env;
      if phis = [] then el_raw b "span" (Some "neck") ":"
      else (
        raw_char b ' ';
        el b "span" (Some "l") (fun b -> ir_inline_phis ctx b phis env);
        el_raw b "span" (Some "neck") ":");
      raw_char b ' ';
      (match ins with
      | IrInsts [] -> ()
      | IrInsts is ->
          ir_inline_ssa_items ctx b is env;
          raw_char b ' '
      | IrCode xs ->
          kw b "code";
          raw_char b ' ';
          term ctx b xs env;
          raw_char b ' ');
      el_a b "span" (Some "op rq-ir-term-arrow") [ ("title", "=>") ] (fun b -> raw b "⇒");
      raw_char b ' ';
      ir_ssa_draw ctx b j env

let rec ir_inline_blocks ctx b bs env =
  match bs with
  | [] -> ()
  | [ blk ] -> ir_blk_inline ctx b blk env
  | blk :: rest ->
      ir_blk_inline ctx b blk env;
      el_raw b "span" (Some "sep") ";";
      raw_char b ' ';
      ir_inline_blocks ctx b rest env

let ir_fn_inline ctx b lk nm ps ret bs env =
  ir_fn_head ctx b lk nm ps ret env;
  raw_char b ' ';
  match bs with
  | IrBodyBlocks blks -> el b "span" (Some "braces") (fun b -> ir_inline_blocks ctx b blks env)
  | IrBodyExpr xs ->
      kw b "blocks";
      raw_char b ' ';
      term ctx b xs env

let () =
  Draw_hooks.draw_ir_fn_block_ref := ir_fn_block;
  Draw_hooks.draw_ir_blk_standalone_ref := ir_blk_standalone;
  Draw_hooks.draw_ir_list_block_ref := ir_list_block;
  Draw_hooks.draw_ir_ssa_ref := ir_ssa_draw;
  Draw_hooks.draw_ir_inline_ssa_items_ref := ir_inline_ssa_items;
  Draw_hooks.draw_ir_blk_inline_ref := ir_blk_inline;
  Draw_hooks.draw_ir_fn_inline_ref := ir_fn_inline
