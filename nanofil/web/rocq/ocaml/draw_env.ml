(* Shared immutable corpus index (safe across OCaml 5 domains) and per-page
   mutable rendering context, mirroring rocq_draw.pl's indexing & scope rules. *)

open Ast

type def_kind =
  | KType
  | KCtor
  | KField
  | KDef
  | KLemma
  | KAxiom
  | KParam
  | KModule
  | KOther

type global_entry = {
  g_short : string;
  g_qual : string;
  g_page : string;
  g_kind : def_kind;
  g_in_sec : bool;
  g_file : string;
}

type page_name_entry = {
  pn_offset : int;
  pn_name : string;
  pn_anchor : string;
  pn_kind : def_kind;
}

type note_kind = Own | Trailing

type note = {
  nt_lo : int;
  nt_hi : int;
  nt_text : string;
  nt_kind : note_kind;
}

type c_renderer = {
  c_fence : seq:int -> string list -> string option;
  c_inline : string -> string option;
  c_inline_auto : string -> string option;
}

type corpus = {
  (* Preserves exact insertion order to match Prolog's assertz order! *)
  by_page_qual : (string * string, global_entry) Hashtbl.t;
  by_qual : (string, global_entry list) Hashtbl.t;
  by_short : (string, global_entry list) Hashtbl.t;
  (* Prolog predicate name -> list of module names (in directory scan order) *)
  prolog_preds : (string, string list) Hashtbl.t;
  prolog_mods : (string, unit) Hashtbl.t;
  prolog_prefix : string option;
  concepts : Concepts.t;
  concepts_prefix : string;
  all_files : string list;
  c_drawer : c_renderer option;
}

type ir_labels = { ir_prefix : string; ir_set : (string, unit) Hashtbl.t }

type ctx = {
  corpus : corpus;
  page : string option;
  file : string option;
  text : string;
  newlines : int array;
  mutable notes : note list;
  mutable mod_path : string list;
  mutable in_button : bool;
  mutable in_card : bool;
  mutable in_embedding : bool;
  mutable in_ipm : bool;
  mutable ir_seq : int;
  mutable ir_labels : ir_labels option;
  mutable c_fence_seq : int;
  mutable proof_env : string list option;
  ops : Parser_core.op_table;
  folds : Parser_core.fold_table;
}

let github_blob = "https://github.com/mbrock/filnix/blob/main/"

let page_name file0 =
  let file =
    if String.starts_with ~prefix:"nanofil/" file0 then
      String.sub file0 8 (String.length file0 - 8)
    else file0
  in
  let base = try Filename.chop_extension file with Invalid_argument _ -> file in
  String.concat "-" (String.split_on_char '/' base)

let kind_to_string = function
  | KType -> "type"
  | KCtor -> "ctor"
  | KField -> "field"
  | KDef -> "def"
  | KLemma -> "lemma"
  | KAxiom -> "axiom"
  | KParam -> "param"
  | KModule -> "module"
  | KOther -> "other"

let kind_class = function
  | KCtor -> "a"
  | KType -> "ty"
  | KField | KDef | KParam -> "f"
  | KLemma | KAxiom -> "lem"
  | KModule -> "module"
  | KOther -> "g"

let is_axiom_kw = function
  | "Axiom" | "Axioms" | "Conjecture" | "Hypothesis" | "Hypotheses" -> true
  | _ -> false

let is_std_ctor = function
  | "None" | "Some" | "true" | "false" | "nil" | "cons" | "inl" | "inr" | "pair"
  | "O" | "S" | "tt" | "I" | "left" | "right" | "Eq" | "Lt" | "Gt" | "Z0"
  | "Zpos" | "Zneg" | "exist" | "existT" | "conj" | "eq_refl" ->
      true
  | _ -> false

let is_std_type = function
  | "Type" | "Prop" | "Set" | "Z" | "nat" | "bool" | "list" | "option" | "string"
  | "prod" | "sum" | "unit" | "N" | "positive" | "True" | "False" | "eq" ->
      true
  | _ -> false

let qualify mod_path name =
  match mod_path with
  | [] -> name
  | _ -> String.concat "." (mod_path @ [ name ])

let defines_of_vernac = function
  | VInd (_, _, bodies) ->
      List.concat_map
        (fun b ->
          (b.ib_name.n_text, KType)
          :: List.map (fun c -> (c.c_name, KCtor)) b.ib_ctors)
        bodies
  | VRec (_, _, n, _, _, ctor, fs) ->
      let c = match ctor with RecCtorNamed cn -> [ (cn.n_text, KCtor) ] | _ -> [] in
      ((n.n_text, KType) :: c) @ List.map (fun f -> (f.fd_name, KField)) fs
  | VDef d -> [ (d.d_name.n_text, KDef) ]
  | VMutual (_, ds) -> List.map (fun d -> (d.d_name.n_text, KDef)) ds
  | VTacDef (_, n, _, _) -> [ (n.n_text, KDef) ]
  | VThm (_, _, Some n, _, _) -> [ (n.n_text, KLemma) ]
  | VDecl (_, kw, gs) ->
      let k = if is_axiom_kw kw then KAxiom else KParam in
      List.concat_map
        (function
          | DeclTyped (ns, _) -> List.map (fun n -> (n.n_text, k)) ns
          | DeclBinders _ -> [])
        gs
  | _ -> []

let index_items ~page ~file (items : item list) : global_entry list =
  let seen = Hashtbl.create 64 in
  let acc = ref [] in
  let add short mod_path kind in_sec =
    let q = qualify mod_path short in
    let key = (short, q, page) in
    if not (Hashtbl.mem seen key) then (
      Hashtbl.add seen key ();
      acc := { g_short = short; g_qual = q; g_page = page; g_kind = kind; g_in_sec = in_sec; g_file = file } :: !acc)
  in
  let rec go mod_path in_sec = function
    | [] -> ()
    | IProved (s, _) :: rest ->
        go_sent mod_path in_sec s;
        go mod_path in_sec rest
    | IBlock (VModule (_, kind, n, _, _), body, _) :: rest ->
        let is_sec = kind = ModSection in
        add n.n_text mod_path KModule is_sec;
        let mod1, in_sec1 = if is_sec then (mod_path, true) else (mod_path @ [ n.n_text ], in_sec) in
        go mod1 in_sec1 body;
        go mod_path in_sec rest
    | IBlock (s, body, _) :: rest ->
        go_sent mod_path in_sec s;
        go mod_path in_sec body;
        go mod_path in_sec rest
    | ISent s :: rest ->
        go_sent mod_path in_sec s;
        go mod_path in_sec rest
  and go_sent mod_path in_sec s =
    let sec_decl = match s with VDecl _ -> in_sec | _ -> false in
    List.iter (fun (nm, k) -> add nm mod_path k sec_decl) (defines_of_vernac s)
  in
  go [] false items;
  List.rev !acc

let items_names (items : item list) : page_name_entry list =
  let acc = ref [] in
  let rec go mod_path = function
    | [] -> ()
    | IProved (s, _) :: rest ->
        go_sent mod_path s;
        go mod_path rest
    | IBlock (VModule (sp, kind, n, _, _), body, _) :: rest ->
        let q = qualify mod_path n.n_text in
        acc := { pn_offset = sp.lo; pn_name = n.n_text; pn_anchor = q; pn_kind = KModule } :: !acc;
        let mod1 = if kind = ModSection then mod_path else mod_path @ [ n.n_text ] in
        go mod1 body;
        go mod_path rest
    | IBlock (s, body, _) :: rest ->
        go_sent mod_path s;
        go mod_path body;
        go mod_path rest
    | ISent s :: rest ->
        go_sent mod_path s;
        go mod_path rest
  and go_sent mod_path s =
    let sp = vernac_span s in
    List.iter
      (fun (nm, k) ->
        if k <> KCtor && k <> KField then
          acc :=
            { pn_offset = sp.lo; pn_name = nm; pn_anchor = qualify mod_path nm; pn_kind = k }
            :: !acc)
      (defines_of_vernac s)
  in
  go [] items;
  List.rev !acc

type corpus_builder = {
  cb_seen : (string * string * string, unit) Hashtbl.t;
  cb_globals : global_entry list ref;
  cb_prolog_preds : (string, string list) Hashtbl.t;
  cb_prolog_mods : (string, unit) Hashtbl.t;
}

let make_corpus_builder () =
  {
    cb_seen = Hashtbl.create 4096;
    cb_globals = ref [];
    cb_prolog_preds = Hashtbl.create 512;
    cb_prolog_mods = Hashtbl.create 64;
  }

let add_global_entry cb g =
  let key = (g.g_short, g.g_qual, g.g_page) in
  if not (Hashtbl.mem cb.cb_seen key) then (
    Hashtbl.add cb.cb_seen key ();
    cb.cb_globals := g :: !(cb.cb_globals))

let add_prolog_pred cb name mod_name =
  Hashtbl.replace cb.cb_prolog_mods mod_name ();
  let cur = match Hashtbl.find_opt cb.cb_prolog_preds name with Some l -> l | None -> [] in
  if not (List.mem mod_name cur) then Hashtbl.replace cb.cb_prolog_preds name (cur @ [ mod_name ])

let finalize_corpus cb ~prolog_prefix ~concepts ~concepts_prefix ~all_files ~c_drawer : corpus =
  let gs = List.rev !(cb.cb_globals) in
  let by_page_qual = Hashtbl.create (max 16 (List.length gs)) in
  let by_qual_rev = Hashtbl.create (max 16 (List.length gs)) in
  let by_short_rev = Hashtbl.create (max 16 (List.length gs)) in
  List.iter
    (fun g ->
      if not (Hashtbl.mem by_page_qual (g.g_page, g.g_qual)) then
        Hashtbl.add by_page_qual (g.g_page, g.g_qual) g;
      let ql = match Hashtbl.find_opt by_qual_rev g.g_qual with Some l -> l | None -> [] in
      Hashtbl.replace by_qual_rev g.g_qual (g :: ql);
      let sl = match Hashtbl.find_opt by_short_rev g.g_short with Some l -> l | None -> [] in
      Hashtbl.replace by_short_rev g.g_short (g :: sl))
    gs;
  let by_qual = Hashtbl.create (Hashtbl.length by_qual_rev) in
  Hashtbl.iter (fun k v -> Hashtbl.add by_qual k (List.rev v)) by_qual_rev;
  let by_short = Hashtbl.create (Hashtbl.length by_short_rev) in
  Hashtbl.iter (fun k v -> Hashtbl.add by_short k (List.rev v)) by_short_rev;
  {
    by_page_qual;
    by_qual;
    by_short;
    prolog_preds = cb.cb_prolog_preds;
    prolog_mods = cb.cb_prolog_mods;
    prolog_prefix;
    concepts;
    concepts_prefix;
    all_files;
    c_drawer;
  }

let page_tree p =
  if String.starts_with ~prefix:"rocq-backend-" p then `Backend
  else if String.starts_with ~prefix:"rocq-glibc-" p then `Glibc
  else if String.starts_with ~prefix:"rocq-spikes-" p then `Spikes
  else `Theories

let page_in_scope page p =
  p = page
  || String.starts_with ~prefix:"rocq-theories-" p
  || page_tree page = page_tree p

let last_part x =
  match String.rindex_opt x '.' with
  | Some i -> String.sub x (i + 1) (String.length x - i - 1)
  | None -> x

(* Exact match to rocq_draw.pl's global_ref/3! *)
let global_ref (ctx : ctx) (x : string) : (string * def_kind) option =
  match ctx.page with
  | None -> None
  | Some page ->
      let c = ctx.corpus in
      let hit =
        let q0 = qualify ctx.mod_path x in
        match Hashtbl.find_opt c.by_page_qual (page, q0) with
        | Some g -> Some (g.g_qual, g.g_page, g.g_kind)
        | None -> (
            match Hashtbl.find_opt c.by_page_qual (page, x) with
            | Some g -> Some (g.g_qual, g.g_page, g.g_kind)
            | None -> (
                let from_qual =
                  match Hashtbl.find_opt c.by_qual x with
                  | None -> None
                  | Some gs ->
                      List.find_map
                        (fun g ->
                          if (not g.g_in_sec) && page_in_scope page g.g_page then
                            Some (g.g_qual, g.g_page, g.g_kind)
                          else None)
                        gs
                in
                match from_qual with
                | Some _ as h -> h
                | None -> (
                    let from_r =
                      if String.starts_with ~prefix:"R." x then
                        let s0 = String.sub x 2 (String.length x - 2) in
                        let q = "Runtime." ^ s0 in
                        match Hashtbl.find_opt c.by_short s0 with
                        | None -> None
                        | Some gs ->
                            List.find_map
                              (fun g ->
                                if g.g_qual = q && page_in_scope page g.g_page then
                                  Some (q, g.g_page, g.g_kind)
                                else None)
                              gs
                      else None
                    in
                    match from_r with
                    | Some _ as h -> h
                    | None -> (
                        let from_file_dot =
                          match String.split_on_char '.' x with
                          | [ f; s0 ] -> (
                              let suf = "-" ^ f in
                              match Hashtbl.find_opt c.by_short s0 with
                              | None -> None
                              | Some gs ->
                                  List.find_map
                                    (fun g ->
                                      if
                                        (not g.g_in_sec)
                                        && String.ends_with ~suffix:suf g.g_page
                                      then Some (g.g_qual, g.g_page, g.g_kind)
                                      else None)
                                    gs)
                          | _ -> None
                        in
                        match from_file_dot with
                        | Some _ as h -> h
                        | None -> (
                            let s = last_part x in
                            match Hashtbl.find_opt c.by_short s with
                            | None -> None
                            | Some gs -> (
                                let hits =
                                  List.filter
                                    (fun g ->
                                      g.g_page = page
                                      || ((not g.g_in_sec) && page_in_scope page g.g_page))
                                    gs
                                in
                                match hits with
                                | [] -> None
                                | _ -> (
                                    match List.find_opt (fun g -> g.g_page = page) hits with
                                    | Some g -> Some (g.g_qual, g.g_page, g.g_kind)
                                    | None -> (
                                        let tr = page_tree page in
                                        let tree_hit =
                                          if tr <> `Theories then
                                            let th =
                                              List.filter (fun g -> page_tree g.g_page = tr) hits
                                            in
                                            match th with
                                            | g :: rest
                                              when List.for_all
                                                     (fun g1 -> g1.g_page = g.g_page)
                                                     rest ->
                                                Some (g.g_qual, g.g_page, g.g_kind)
                                            | _ -> None
                                          else None
                                        in
                                        match tree_hit with
                                        | Some _ as h -> h
                                        | None -> (
                                            match hits with
                                            | g :: rest
                                              when List.for_all
                                                     (fun g1 -> g1.g_page = g.g_page)
                                                     rest ->
                                                Some (g.g_qual, g.g_page, g.g_kind)
                                            | _ -> None)))))))))
      in
      Option.map
        (fun (q, p, k) ->
          let frag = Html.uri_encode_fragment q in
          let href = if p = page then "#" ^ frag else p ^ ".html#" ^ frag in
          (href, k))
        hit

let name_kind ctx x =
  match ctx.page with
  | Some _ -> (
      match global_ref ctx x with
      | Some (_, k) -> k
      | None ->
          if is_std_ctor x then KCtor
          else if is_std_type x then KType
          else KOther)
  | None ->
      if is_std_ctor x then KCtor
      else if is_std_type x then KType
      else if
        String.length x > 0
        && x.[0] >= 'A'
        && x.[0] <= 'Z'
        && not (String.contains x '.')
      then KCtor
      else KOther

let is_ctor ctx x = name_kind ctx x = KCtor

let compute_newlines text =
  let n = String.length text in
  let count = ref 0 in
  for i = 0 to n - 1 do
    if text.[i] = '\n' then incr count
  done;
  let arr = Array.make !count 0 in
  let idx = ref 0 in
  for i = 0 to n - 1 do
    if text.[i] = '\n' then (
      arr.(!idx) <- i;
      incr idx)
  done;
  arr

let line_of ctx off =
  let arr = ctx.newlines in
  let rec bsearch lo hi =
    if lo > hi then lo
    else
      let mid = (lo + hi) lsr 1 in
      if arr.(mid) < off then bsearch (mid + 1) hi else bsearch lo (mid - 1)
  in
  bsearch 0 (Array.length arr - 1) + 1

let note_kind text (cm : comment) : note =
  let rec indent_only i =
    if i <= 0 then true
    else
      match text.[i - 1] with
      | '\n' -> true
      | ' ' | '\t' -> indent_only (i - 1)
      | _ -> false
  in
  {
    nt_lo = cm.cm_lo;
    nt_hi = cm.cm_hi;
    nt_text = cm.cm_text;
    nt_kind = (if indent_only cm.cm_lo then Own else Trailing);
  }

let make_ctx ~corpus ~page ~file ~text ~notes ~ops ~folds =
  {
    corpus;
    page;
    file;
    text;
    newlines = compute_newlines text;
    notes;
    mod_path = [];
    in_button = false;
    in_card = false;
    in_embedding = false;
    in_ipm = false;
    ir_seq = 0;
    ir_labels = None;
    c_fence_seq = 0;
    proof_env = None;
    ops;
    folds;
  }

let anchor ctx name = qualify ctx.mod_path name

let src_text ctx (sp : span) = String.sub ctx.text sp.lo (sp.hi - sp.lo)
