(* Vernacular sentence parser, dynamic Notation/Infix table + sibling file
   cache, Module/Section/Proof tree builder, and inline prose fragments. *)

open Ast
open Parser_core
open Parse_term
open Parse_tactic

let is_modifier = function
  | "Local" | "Global" | "Program" | "Polymorphic" | "Monomorphic" | "Private" | "#[local]" ->
      true
  | _ -> false

let is_directive = function
  | "From" | "Require" | "Import" | "Export" | "Include" | "Open" | "Close" | "Set" | "Unset"
  | "Arguments" | "Hint" | "Declare" | "Existing" | "Delimit" | "Bind" | "Implicit"
  | "Generalizable" | "Create" | "Opaque" | "Transparent" | "Typeclasses" | "Coercion" ->
      true
  | _ -> false

let is_command = function
  | "Print" | "Check" | "Compute" | "Search" | "About" | "Locate" | "Extraction" | "Extract"
  | "Recursive" | "Separate" | "Crane" | "CertiRocq" ->
      true
  | _ -> false

let is_command_word k =
  is_command k
  ||
  match k with
  | "Assumptions" | "Opaque" | "Transparent" | "All" | "Constant" | "Inlined" | "Inductive"
  | "Numeral" | "Show" | "Register" | "Library" | "Language" | "NoLoopify" ->
      true
  | _ -> false

let is_def_kw = function
  | "Definition" | "Fixpoint" | "CoFixpoint" | "Let" | "Example" | "Instance" | "Function" ->
      true
  | _ -> false

let is_thm_kw = function
  | "Theorem" | "Lemma" | "Corollary" | "Fact" | "Remark" | "Proposition" | "Property" -> true
  | _ -> false

let is_decl_kw = function
  | "Axiom" | "Axioms" | "Parameter" | "Parameters" | "Conjecture" | "Hypothesis"
  | "Hypotheses" | "Variable" | "Variables" | "Context" ->
      true
  | _ -> false

let is_proof_end = function
  | "Qed" | "Defined" | "Admitted" | "Abort" | "Save" -> true
  | _ -> false

let is_vernac_frag_kw = function
  | "Inductive" | "Record" | "Definition" | "Fixpoint" | "Theorem" | "Lemma"
  | "Axiom" | "Parameter" | "Module" | "Notation" | "Corollary" ->
      true
  | _ -> false

let is_bullet_sym s =
  let n = String.length s in
  if n = 0 then false
  else
    let c = s.[0] in
    (c = '-' || c = '+' || c = '*')
    &&
    let rec all i = if i >= n then true else s.[i] = c && all (i + 1) in
    all 1

let parse_words p =
  let rec loop acc =
    if at_end p then List.rev acc
    else
      let t = bump p in
      loop (tok_text t.kind :: acc)
  in
  loop []

let parse_remaining p =
  let rec loop acc =
    if at_end p then List.rev acc else loop (bump p :: acc)
  in
  loop []

let rec skip_attributes p =
  match peek2_kind p with
  | Some (Sym "#", P "[") ->
      ignore (bump p);
      ignore (bump p);
      let rec skip_to_rbrack () =
        let t = bump p in
        if t.kind = P "]" then () else skip_to_rbrack ()
      in
      skip_to_rbrack ();
      skip_attributes p
  | _ -> ()

let rec skip_modifiers p =
  match peek_kind p with
  | Some (Id m) when is_modifier m -> (
      match peek2_kind p with
      | Some (_, Sym _) -> ()
      | _ ->
          ignore (bump p);
          skip_modifiers p)
  | _ -> ()

let parse_def_kw p =
  match peek_kind p with
  | Some (Id kw) when is_def_kw kw ->
      ignore (bump p);
      kw
  | Some (Id "Canonical") when peek2_kind p = Some (Id "Canonical", Id "Structure") ->
      ignore (bump p);
      ignore (bump p);
      "Canonical Structure"
  | _ -> raise Fail

let parse_ctor p =
  let x, t0 = eat_any_id p in
  let bs = parse_binders0 p in
  let ty = opt_type p in
  let hi =
    match ty with
    | Some e -> (expr_span e).hi
    | None -> (
        match bs with
        | [] -> t0.hi
        | _ -> (List.nth bs (List.length bs - 1)).b_span.hi)
  in
  { c_span = { lo = t0.lo; hi }; c_name = x; c_binders = bs; c_ty = ty }

let rec parse_ctors p =
  let c = parse_ctor p in
  match peek_kind p with
  | Some (Sym "|") ->
      ignore (bump p);
      c :: parse_ctors p
  | _ -> [ c ]

let rec parse_ind_bodies p =
  let b = parse_ind_body p in
  match peek_kind p with
  | Some (Kw "with") ->
      ignore (bump p);
      b :: parse_ind_bodies p
  | _ -> [ b ]

and parse_ind_body p =
  let ib_name = parse_name p in
  let ib_binders = parse_binders0 p in
  let ib_ty = opt_type p in
  ignore (eat_sym p ":=");
  if peek_kind p = Some (Sym "|") then ignore (bump p);
  let ib_ctors = match try_ p parse_ctors with Some cs -> cs | None -> [] in
  { ib_name; ib_binders; ib_ty; ib_ctors }

let parse_field p =
  let x, t0 = eat_any_id p in
  let bs = parse_binders0 p in
  let ty =
    match peek_kind p with
    | Some (Sym (":" | ":>")) ->
        ignore (bump p);
        Some (term p)
    | _ -> None
  in
  let def =
    match peek_kind p with
    | Some (Sym ":=") ->
        ignore (bump p);
        Some (term p)
    | _ -> None
  in
  let hi =
    match (def, ty) with
    | Some d, _ -> (expr_span d).hi
    | None, Some e -> (expr_span e).hi
    | None, None -> t0.hi
  in
  { fd_span = { lo = t0.lo; hi }; fd_name = x; fd_binders = bs; fd_ty = ty; fd_def = def }

let rec parse_fields p =
  match try_ p parse_field with
  | None -> []
  | Some f -> (
      match peek_kind p with
      | Some (P ";") ->
          ignore (bump p);
          f :: parse_fields p
      | _ -> [ f ])

let rec parse_mutual_defs p =
  let n = parse_name p in
  let bs = parse_binders0 p in
  let ty = opt_type p in
  ignore (eat_sym p ":=");
  let body = term p in
  let d =
    {
      d_span = { lo = n.n_span.lo; hi = (expr_span body).hi };
      d_kw = "with";
      d_name = n;
      d_binders = bs;
      d_ty = ty;
      d_body = Some body;
    }
  in
  match peek_kind p with
  | Some (Kw "with") ->
      ignore (bump p);
      d :: parse_mutual_defs p
  | _ -> [ d ]

let parse_decl_groups p =
  match
    try_ p (fun p ->
        let ns = parse_names p in
        ignore (eat_sym p ":");
        let ty = term p in
        [ DeclTyped (ns, ty) ])
  with
  | Some gs -> gs
  | None ->
      let bs = parse_binders p in
      if List.for_all (fun b -> b.b_kind = BParen && b.b_ty <> None) bs then
        List.map (fun b -> DeclTyped (b.b_names, Option.get b.b_ty)) bs
      else [ DeclBinders bs ]

let parse_vernac sp p =
  match peek_kind p with
  | Some (Id "String") when peek2_kind p = Some (Id "String", Id "Notation") ->
      ignore (bump p);
      ignore (bump p);
      VDir (sp, "String" :: "Notation" :: parse_words p)
  | Some (Id k) when is_directive k -> VDir (sp, parse_words p)
  | Some (Id k) when is_command k ->
      let rec cmd_words acc =
        match peek_kind p with
        | Some (Id w) when is_command_word w ->
            ignore (bump p);
            cmd_words (w :: acc)
        | _ -> List.rev acc
      in
      let kws = cmd_words [] in
      VCmd (sp, kws, parse_remaining p)
  | Some (Id (("Inductive" | "CoInductive" | "Variant") as kw)) ->
      ignore (bump p);
      VInd (sp, kw, parse_ind_bodies p)
  | Some (Id (("Record" | "Structure" | "Class") as kw)) -> (
      ignore (bump p);
      let n = parse_name p in
      let bs = parse_binders0 p in
      let sort = opt_type p in
      ignore (eat_sym p ":=");
      let single =
        if kw = "Class" then
          try_ p (fun p ->
              let f = parse_field p in
              if not (at_end p) then raise Fail;
              f)
        else None
      in
      match single with
      | Some fld -> VRec (sp, kw, n, bs, sort, RecCtorSingleton, [ fld ])
      | None ->
          let ctor =
            match try_ p parse_name with Some c -> RecCtorNamed c | None -> RecCtorNone
          in
          ignore (eat_p p "{");
          let fs = parse_fields p in
          ignore (eat_p p "}");
          VRec (sp, kw, n, bs, sort, ctor, fs))
  | Some (Id kw) when is_thm_kw kw ->
      ignore (bump p);
      let n = parse_name p in
      let bs = parse_binders0 p in
      ignore (eat_sym p ":");
      VThm (sp, kw, Some n, bs, term p)
  | Some (Id "Goal") ->
      ignore (bump p);
      VThm (sp, "Goal", None, [], term p)
  | Some (Id "Ltac") ->
      ignore (bump p);
      let n = parse_name p in
      let args = parse_tactic_params p in
      ignore (eat_sym p ":=");
      VTacDef (sp, n, args, tactic p)
  | Some (Id "Tactic") when peek2_kind p = Some (Id "Tactic", Id "Notation") ->
      ignore (bump p);
      ignore (bump p);
      let parts = parse_tactic_notation_parts p in
      ignore (eat_sym p ":=");
      VTacNotation (sp, parts, tactic p)
  | Some (Id kw) when is_decl_kw kw ->
      ignore (bump p);
      VDecl (sp, kw, parse_decl_groups p)
  | Some (Id (("Notation" | "Infix" | "Abbreviation") as kw)) ->
      ignore (bump p);
      let s =
        match peek_kind p with
        | Some (Str s) ->
            ignore (bump p);
            s
        | _ ->
            let a, _ = eat_any_id p in
            let ps = parse_names0 p in
            String.concat " " (a :: List.map (fun n -> n.n_text) ps)
      in
      ignore (eat_sym p ":=");
      let e = with_notation_rhs p true atom in
      let mods = parse_words p in
      VNotation (sp, kw, s, e, mods)
  | Some (Id "Module") ->
      ignore (bump p);
      let kind =
        match peek_kind p with
        | Some (Id "Type") ->
            ignore (bump p);
            ModType
        | _ -> ModModule
      in
      let n = parse_name p in
      let bs = parse_binders0 p in
      let open_ =
        match peek_kind p with
        | Some (Sym ":=") ->
            ignore (bump p);
            ModDefined (parse_words p, None)
        | Some (Sym ":") -> (
            ignore (bump p);
            let sig_n = parse_name p in
            let args = List.map (fun x -> x.n_text) (parse_names0 p) in
            match peek_kind p with
            | Some (Sym ":=") ->
                ignore (bump p);
                ModDefined (parse_words p, Some (sig_n.n_text, args))
            | None -> ModOpenSig (sig_n.n_text, args)
            | _ -> raise Fail)
        | _ -> ModOpen
      in
      VModule (sp, kind, n, bs, open_)
  | Some (Id "Section") ->
      ignore (bump p);
      VModule (sp, ModSection, parse_name p, [], ModOpen)
  | Some (Id "End") ->
      ignore (bump p);
      VEnd (sp, parse_name p)
  | Some (Id "Proof") ->
      ignore (bump p);
      ignore (parse_words p);
      VProofStart sp
  | _ ->
      let kw = parse_def_kw p in
      let n = parse_name p in
      let bs = parse_binders0 p in
      let ty = opt_type p in
      let body =
        match peek_kind p with
        | Some (Sym ":=") ->
            ignore (bump p);
            Some (term p)
        | _ -> None
      in
      (match (body, peek_kind p) with
      | Some b, Some (Kw "with") ->
          ignore (bump p);
          let ds = parse_mutual_defs p in
          let first_def =
            {
              d_span = { lo = sp.lo; hi = (expr_span b).hi };
              d_kw = kw;
              d_name = n;
              d_binders = bs;
              d_ty = ty;
              d_body = Some b;
            }
          in
          VMutual (sp, first_def :: ds)
      | _ ->
          VDef
            {
              d_span = sp;
              d_kw = kw;
              d_name = n;
              d_binders = bs;
              d_ty = ty;
              d_body = body;
            })

let parse_sentence sp p =
  skip_attributes p;
  skip_modifiers p;
  parse_vernac sp p

(* ── Dynamic notation recording & sibling cache ────────────────────────── *)

let has_subseq sub lst =
  let rec go = function
    | [] -> false
    | x :: xs as l ->
        let rec match_p a b =
          match (a, b) with
          | [], _ -> true
          | ah :: at, bh :: bt when ah = bh -> match_p at bt
          | _ -> false
        in
        match_p sub l || go xs
  in
  go lst

let find_level mods =
  let rec go = function
    | "level" :: n :: _ -> (
        match int_of_string_opt n with Some lv -> lv | None -> 70)
    | _ :: tl -> go tl
    | [] -> 70
  in
  go mods

let find_assoc mods =
  if has_subseq [ "right"; "associativity" ] mods then Right
  else if has_subseq [ "left"; "associativity" ] mods then Left
  else NonAssoc

let unparen_once = function EParen (_, e0) -> e0 | e -> e

let record_notation (ops : op_table) (folds : fold_table) = function
  | VNotation (_, kw, s, e, mods) ->
      if has_subseq [ "in"; "custom" ] mods then ()
      else (
        let parts = String.split_on_char ' ' s in
        match parts with
        | [ x; op; y ] when x <> "" && y <> "" && std_op op = None ->
            Hashtbl.replace ops op (find_level mods, find_assoc mods);
            (match unparen_once e with
            | EApp (_, EId (_, f), [ EId (_, x1); EId (_, y1) ]) when x1 = x && y1 = y ->
                Hashtbl.replace folds f op
            | _ -> ())
        | _ when kw = "Infix" && std_op s = None -> (
            match unparen_once e with
            | EId (_, f) ->
                Hashtbl.replace ops s (find_level mods, find_assoc mods);
                Hashtbl.replace folds f s
            | _ -> ())
        | _ -> ())
  | _ -> ()

let parse_chunk_sentence ~ops ~folds (ch : Lexer.chunk) : vernac =
  let n = Array.length ch.ch_toks in
  if n = 0 then VRaw ({ lo = ch.ch_hi; hi = ch.ch_hi }, "")
  else
    let sp = { lo = ch.ch_toks.(0).lo; hi = ch.ch_hi } in
    let p = make_state ~ops ch.ch_toks in
    let s =
      match parse_sentence sp p with
      | v when at_end p -> v
      | _ -> VRaw (sp, tok_text ch.ch_toks.(0).kind)
      | exception Fail -> VRaw (sp, tok_text ch.ch_toks.(0).kind)
    in
    record_notation ops folds s;
    s

let has_substring hay needle =
  let hlen = String.length hay and nlen = String.length needle in
  if nlen = 0 then true
  else if nlen > hlen then false
  else
    let rec check i =
      if i > hlen - nlen then false
      else if String.sub hay i nlen = needle then true
      else check (i + 1)
    in
    check 0

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic) @@ fun () ->
  really_input_string ic (in_channel_length ic)

type notation_cache =
  (string, (string * (int * assoc)) list * (string * string) list) Hashtbl.t

let file_notations (cache : notation_cache) (ops : op_table) (folds : fold_table)
    (path : string) =
  let op_es, fold_es =
    match Hashtbl.find_opt cache path with
    | Some es -> es
    | None ->
        let text = read_file path in
        let es =
          if has_substring text "Notation" || has_substring text "Infix" then (
            let local_ops = Hashtbl.create 16 in
            let local_folds = Hashtbl.create 8 in
            let toks, _ = Lexer.lex text in
            List.iter
              (fun (ch : Lexer.chunk) ->
                if Array.length ch.ch_toks > 0 then
                  match ch.ch_toks.(0).kind with
                  | Id ("Notation" | "Infix") ->
                      ignore (parse_chunk_sentence ~ops:local_ops ~folds:local_folds ch)
                  | _ -> ())
              (Lexer.chunks toks);
            ( Hashtbl.fold (fun k v acc -> (k, v) :: acc) local_ops [],
              Hashtbl.fold (fun k v acc -> (k, v) :: acc) local_folds [] ))
          else ([], [])
        in
        Hashtbl.replace cache path es;
        es
  in
  List.iter
    (fun (op, spec) -> if not (Hashtbl.mem ops op) then Hashtbl.add ops op spec)
    op_es;
  List.iter
    (fun (fn, op) -> if not (Hashtbl.mem folds fn) then Hashtbl.add folds fn op)
    fold_es

let import_notations (cache : notation_cache) (ops : op_table) (folds : fold_table)
    (dir : string) (chunks : Lexer.chunk list) =
  List.iter
    (fun (ch : Lexer.chunk) ->
      let n = Array.length ch.ch_toks in
      if n > 0 then
        match ch.ch_toks.(0).kind with
        | Id ("From" | "Require" | "Import" | "Export") ->
            let rec find_imp i =
              if i >= n then ()
              else
                match ch.ch_toks.(i).kind with
                | Id ("Import" | "Export") ->
                    for j = i + 1 to n - 1 do
                      match ch.ch_toks.(j).kind with
                      | Id m ->
                          let f = Filename.concat dir (m ^ ".v") in
                          if Sys.file_exists f then file_notations cache ops folds f
                      | _ -> ()
                    done;
                    find_imp (i + 1)
                | _ -> find_imp (i + 1)
            in
            find_imp 0
        | _ -> ())
    chunks

(* ── Events & item tree builder ────────────────────────────────────────── *)

type event =
  | EvSent of vernac
  | EvProof of span
  | EvStep of span * focus list * token list
  | EvBulletOnly of focus list
  | EvQed of span * string

let strip_bullets (toks : token array) : focus list * token list =
  let n = Array.length toks in
  let rec go i acc =
    if i >= n then (List.rev acc, [])
    else if i + 2 < n then
      match (toks.(i).kind, toks.(i + 1).kind, toks.(i + 2).kind) with
      | Num num, Sym ":", P "{" -> go (i + 3) (FocusNum num :: acc)
      | _ -> go_single i acc
    else go_single i acc
  and go_single i acc =
    match toks.(i).kind with
    | P ("{" | "}" as b) -> go (i + 1) (FocusBullet b :: acc)
    | Sym s when is_bullet_sym s -> go (i + 1) (FocusBullet s :: acc)
    | _ ->
        let rest = ref [] in
        for j = n - 1 downto i do
          rest := toks.(j) :: !rest
        done;
        (List.rev acc, !rest)
  in
  go 0 []

let opens_proof = function
  | VThm _ | VProofStart _ -> true
  | VDef { d_body = None; _ } -> true
  | _ -> false

let build_events ~ops ~folds (chunks : Lexer.chunk list) : event list =
  let rec go mode acc = function
    | [] -> List.rev acc
    | (ch : Lexer.chunk) :: rest ->
        if mode = `Proof then
          let bs, rem = strip_bullets ch.ch_toks in
          match rem with
          | t0 :: _ -> (
              match t0.kind with
              | Id kw when is_proof_end kw ->
                  let sp = { lo = t0.lo; hi = ch.ch_hi } in
                  go `Vernac (EvQed (sp, kw) :: EvBulletOnly bs :: acc) rest
              | Id "Proof" ->
                  let sp = { lo = t0.lo; hi = ch.ch_hi } in
                  go `Proof (EvProof sp :: acc) rest
              | _ ->
                  let sp = { lo = t0.lo; hi = ch.ch_hi } in
                  go `Proof (EvStep (sp, bs, rem) :: acc) rest)
          | [] -> go `Proof (EvBulletOnly bs :: acc) rest
        else if Array.length ch.ch_toks = 0 then go `Vernac acc rest
        else
          let s = parse_chunk_sentence ~ops ~folds ch in
          let mode' = if opens_proof s then `Proof else `Vernac in
          go mode' (EvSent s :: acc) rest
  in
  go `Vernac [] chunks

let rec collect_proof_steps acc = function
  | EvProof _ :: rest -> collect_proof_steps acc rest
  | EvStep (sp, bs, ts) :: rest -> collect_proof_steps (PStep (sp, bs, ts) :: acc) rest
  | EvBulletOnly [] :: rest -> collect_proof_steps acc rest
  | EvBulletOnly bs :: rest -> collect_proof_steps (PBullets bs :: acc) rest
  | rest -> (List.rev acc, rest)

let rec build_tree acc = function
  | EvSent (VEnd _) :: _ as evs -> (List.rev acc, evs)
  | EvSent s :: rest -> (
      match s with
      | VModule (_, _, _, _, (ModOpen | ModOpenSig _)) ->
          let body, rest1 = build_tree [] rest in
          let end_opt, rest2 =
            match rest1 with
            | EvSent (VEnd _ as e) :: r -> (Some e, r)
            | r -> (None, r)
          in
          build_tree (IBlock (s, body, end_opt) :: acc) rest2
      | s when opens_proof s ->
          let steps, rest1 = collect_proof_steps [] rest in
          let pf_end, rest2 =
            match rest1 with
            | EvQed (sp, kw) :: r -> (Some (QedEnd (sp, kw)), r)
            | r -> (None, r)
          in
          build_tree (IProved (s, { pf_steps = steps; pf_end }) :: acc) rest2
      | _ -> build_tree (ISent s :: acc) rest)
  | EvProof sp :: rest ->
      let steps, rest1 = collect_proof_steps [] rest in
      let pf_end, rest2 =
        match rest1 with
        | EvQed (qsp, kw) :: r -> (Some (QedEnd (qsp, kw)), r)
        | r -> (None, r)
      in
      build_tree (IProved (VProofStart sp, { pf_steps = steps; pf_end }) :: acc) rest2
  | evs -> (List.rev acc, evs)

let build_top evs =
  let rec go acc evs =
    match build_tree [] evs with
    | items, [] -> List.rev_append acc items
    | items, EvSent s :: rest -> go (ISent s :: List.rev_append items acc) rest
    | items, _ :: rest -> go (List.rev_append items acc) rest
  in
  go [] evs

type parsed_file = {
  text : string;
  items : item list;
  comments : comment list;
  ops : op_table;
  folds : fold_table;
}

let parse_string ?(ops = Hashtbl.create 16) ?(folds = Hashtbl.create 8) (text : string) :
    parsed_file =
  let toks, comments = Lexer.lex text in
  let chs = Lexer.chunks toks in
  let evs = build_events ~ops ~folds chs in
  let items = build_top evs in
  { text; items; comments; ops; folds }

let parse_file ?(cache = Hashtbl.create 64) (path : string) : parsed_file =
  let text = read_file path in
  let ops = Hashtbl.create 16 in
  let folds = Hashtbl.create 8 in
  let toks, comments = Lexer.lex text in
  let chs = Lexer.chunks toks in
  import_notations cache ops folds (Filename.dirname path) chs;
  let evs = build_events ~ops ~folds chs in
  let items = build_top evs in
  { text; items; comments; ops; folds }

(* ── Inline prose fragments ────────────────────────────────────────────── *)

let rec alt_terms p =
  let c = expr p ~max:99 in
  match peek_kind p with
  | Some (Sym "|") ->
      ignore (bump p);
      c :: alt_terms p
  | _ -> [ c ]

let parse_fragment ?(ops = Hashtbl.create 8) (src : string) : fragment option =
  match Lexer.lex src with
  | exception Lexer.Lex_error _ -> None
  | toks, _ ->
      let n = Array.length toks in
      if n = 0 || Array.exists (fun t -> t.kind = Dot) toks then None
      else
        let sp = { lo = toks.(0).lo; hi = toks.(n - 1).hi } in
        let p = make_state ~ops toks in
        let check f =
          let v = f p in
          if at_end p then v else raise Fail
        in
        match
          first p
            [
              (fun p ->
                check (fun p ->
                    match peek_kind p with
                    | Some (Id k) when is_vernac_frag_kw k -> FSentence (parse_sentence sp p)
                    | _ -> raise Fail));
              (fun p ->
                check (fun p ->
                    let nm = parse_name p in
                    ignore (eat_sym p ":=");
                    let c0 = expr p ~max:99 in
                    ignore (eat_sym p "|");
                    FAlts (nm, c0 :: alt_terms p)));
              (fun p ->
                check (fun p ->
                    let nm = parse_name p in
                    ignore (eat_sym p ":=");
                    ignore (eat_p p "{");
                    let fs = parse_fields p in
                    ignore (eat_p p "}");
                    FFields (nm, fs)));
              (fun p ->
                check (fun p ->
                    let nm = parse_name p in
                    ignore (eat_sym p ":");
                    FTyped (nm, term p)));
              (fun p ->
                check (fun p ->
                    let ns = parse_names p in
                    let body =
                      match peek_kind p with
                      | Some (Sym ":=") ->
                          ignore (bump p);
                          Some (term p)
                      | _ -> None
                    in
                    ignore (eat_sym p ":");
                    FContext (ns, body, term p)));
              (fun p -> check (fun p -> FTerm (term p)));
            ]
        with
        | f -> Some f
        | exception Fail -> None
