(* Page shell, sidebar TOC/siblings, index.html, and parallel rendering driver
   mirroring nanofil/web/rocq/dterm_rocq.pl. *)

open Ast
open Draw_env
open Html

let nbsp = "\xc2\xa0"

(* Ensure hook modules are initialized even if only invoked via Draw_hooks. *)
let () =
  ignore (Draw_term.op_glyph "->");
  ignore (Draw_ir.ir_role_class Draw_ir.ROp);
  ignore (Draw_tactic.tactic_structural TEmpty);
  ignore (Draw_prose.heading_id "")

type page_meta = {
  pm_file : string;
  pm_summary : string;
  pm_lines : int;
  pm_lemmas : int;
  pm_axioms : int;
}

let is_shown_as_text = function
  | "Extraction" | "Extract" | "Check" | "Compute" | "Print" | "Eval" | "Search" -> true
  | _ -> false

let rec collect_warn_raws acc = function
  | [] -> List.rev acc
  | ISent (VRaw (sp, kw)) :: rest when not (is_shown_as_text kw) ->
      collect_warn_raws ((sp, kw) :: acc) rest
  | IBlock (_, body, _) :: rest ->
      let acc = List.rev_append (collect_warn_raws [] body) acc in
      collect_warn_raws acc rest
  | _ :: rest -> collect_warn_raws acc rest

(* Index Prolog predicates defined in DIR/*.pl (lines starting with lowercase ident + '(' or ':'). *)
let index_prolog_dir cb dir =
  let files = Sys.readdir dir |> Array.to_list |> List.sort String.compare in
  List.iter
    (fun e ->
      if Filename.check_suffix e ".pl" then
        let m = Filename.chop_suffix e ".pl" in
        let text = Parse_vernac.read_file (Filename.concat dir e) in
        List.iter
          (fun line ->
            let n = String.length line in
            if n >= 2 && line.[0] >= 'a' && line.[0] <= 'z' then (
              let j = ref 1 in
              while !j < n && Draw_prose.is_csym line.[!j] do
                incr j
              done;
              if !j < n && (line.[!j] = '(' || line.[!j] = ':') then
                add_prolog_pred cb (String.sub line 0 !j) m))
          (String.split_on_char '\n' text))
    files

let first_offset = function
  | IProved (s, _) | IBlock (s, _, _) | ISent s -> (vernac_span s).lo

let page_head items text notes =
  let from = match items with i :: _ -> first_offset i | [] -> String.length text in
  List.partition (fun nt -> nt.nt_lo < from) notes

let header_title text lines0 =
  match (Draw_prose.comment_heading text, lines0) with
  | Some (_, title), _ :: rest -> (Some title, rest)
  | None, first :: rest when String.starts_with ~prefix:"# " first ->
      (Some (Markdown.trim_spaces (String.sub first 2 (String.length first - 2))), rest)
  | _ -> (None, lines0)

let summarize_text file text head =
  let nl = ref 1 in
  String.iter (fun c -> if c = '\n' then incr nl) text;
  let sum =
    match Blurbs.find_opt file with
    | Some s -> s
    | None -> (
        match head with
        | nt :: _ -> (
            let lines0 = Draw_prose.comment_prose_lines nt.nt_text in
            let _, lines = header_title nt.nt_text lines0 in
            match Markdown.blocks lines with
            | Markdown.P p :: _ ->
                let n = String.length p in
                let rec find_dot i =
                  if i + 1 >= n then None
                  else if p.[i] = '.' && p.[i + 1] = ' ' && i > 20 then Some i
                  else find_dot (i + 1)
                in
                (match find_dot 0 with Some b -> String.sub p 0 (b + 1) | None -> p)
            | _ -> "")
        | [] -> "")
  in
  (sum, !nl)

let page_meta_of file text items notes =
  let head, _ = page_head items text notes in
  let pm_summary, pm_lines = summarize_text file text head in
  let ns = items_names items in
  let pm_lemmas =
    List.fold_left (fun a x -> if x.pn_kind = KLemma then a + 1 else a) 0 ns
  in
  let pm_axioms =
    List.fold_left (fun a x -> if x.pn_kind = KAxiom then a + 1 else a) 0 ns
  in
  { pm_file = file; pm_summary; pm_lines; pm_lemmas; pm_axioms }

(* ── Sidebar contents groups ───────────────────────────────────────────── *)

type nav_group = { ng_title : string option; ng_names : page_name_entry list }

type toc_item = TocSec of string | TocName of page_name_entry

let contents items body_notes =
  let ns = items_names items in
  let secs =
    List.filter_map
      (fun nt ->
        match Draw_prose.comment_heading nt.nt_text with
        | Some (lvl, title) when lvl <= 3 -> Some (nt.nt_lo, TocSec title)
        | _ -> None)
      body_notes
  in
  let name_pairs = List.map (fun n -> (n.pn_offset, TocName n)) ns in
  (* keysort in Prolog is stable on keys! *)
  let combined = List.stable_sort (fun (a, _) (b, _) -> compare a b) (secs @ name_pairs) in
  let xs = List.map snd combined in
  let rec group cur_title = function
    | [] -> []
    | TocSec t :: rest -> group (Some t) rest
    | rest ->
        let rec take acc = function
          | TocName n :: r -> take (n :: acc) r
          | r -> (List.rev acc, r)
        in
        let group_ns, rem = take [] rest in
        { ng_title = cur_title; ng_names = group_ns } :: group cur_title rem
  in
  group None xs

(* ── Page HTML shell, crumbs, sidebar ──────────────────────────────────── *)

let shell b ~title ~crumbs ~main =
  raw b "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n";
  raw b "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n";
  raw b "<title>";
  esc b title;
  raw b " · Rocq · nanofil · Filnix wiki</title>\n";
  raw b "<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n";
  raw b "<link rel=\"preconnect\" href=\"https://fonts.gstatic.com\" crossorigin>\n";
  raw b
    "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=DM+Mono:ital,wght@0,300;0,400;0,500;1,400&amp;family=Public+Sans:ital,wght@0,100..900;1,100..900&amp;display=swap\">\n";
  raw b "<link rel=\"stylesheet\" href=\"../../style.css\">\n";
  raw b "<link rel=\"stylesheet\" href=\"../dterm.css\">\n";
  raw b "<link rel=\"stylesheet\" href=\"dterm-rocq.css\">\n";
  raw b "</head>\n<body>\n";
  site_header b ~root:"../../" ~door:"nanofil" ~crumbs ~right:(fun b ->
      el_a b "a" None [ ("href", "../formal.html") ] (fun b -> raw b "the formal campaign"));
  el b "main" (Some "page-frame dterm-page") main;
  raw b "\n<script src=\"../dterm.js\"></script>\n<script src=\"dterm-rocq.js\"></script>\n</body>\n</html>\n"

let draw_crumbs b title =
  el_a b "a" (Some "crumb") [ ("href", "../../index.html") ] (fun b -> raw b "Wiki");
  el_raw b "span" (Some "crumb-sep") "›";
  el_a b "a" (Some "crumb") [ ("href", "../index.html") ] (fun b -> raw b "nanofil");
  el_raw b "span" (Some "crumb-sep") "›";
  el_a b "a" (Some "crumb") [ ("href", "index.html") ] (fun b -> raw b "Rocq");
  el_raw b "span" (Some "crumb-sep") "›";
  el_text b "span" (Some "crumb current") title

let draw_sidebar ctx b current groups =
  let dir = Filename.dirname current in
  let siblings = List.filter (fun f -> Filename.dirname f = dir) ctx.corpus.all_files in
  el_a b "nav" (Some "toc dterm-nav nix-nav rq-nav") [ ("aria-label", "Contents") ] (fun b ->
      if groups <> [] then
        el_a b "details" (Some "nav-block contents") [ ("open", "open") ] (fun b ->
            el_raw b "summary" (Some "toc-title") "Contents";
            List.iter
              (fun g ->
                let title = Option.value ~default:"top" g.ng_title in
                el_a b "details" (Some "nav-group") [ ("open", "open") ] (fun b ->
                    el b "summary" None (fun b ->
                        el_text b "span" (Some "nav-group-title") title);
                    el b "ul" (Some "nav-names long") (fun b ->
                        List.iter
                          (fun n ->
                            let href = "#" ^ uri_encode_fragment n.pn_anchor in
                            el b "li" (Some (kind_to_string n.pn_kind)) (fun b ->
                                el_a b "a" None [ ("href", href) ] (fun b -> esc b n.pn_name)))
                          g.ng_names)))
              groups);
      el_a b "details" (Some "nav-block files") [ ("open", "open") ] (fun b ->
          el_raw b "summary" (Some "toc-title") "Files";
          el b "ul" (Some "nav-top") (fun b ->
              el b "li" None (fun b ->
                  el_a b "a" None [ ("href", "index.html") ] (fun b -> raw b "Index"));
              List.iter
                (fun f ->
                  let h = page_name f ^ ".html" in
                  let cls = if f = current then Some "current" else None in
                  let base = Filename.basename f in
                  el b "li" cls (fun b ->
                      el_a b "a" None [ ("href", h) ] (fun b -> esc b base)))
                siblings)))

let draw_lede ctx b nt =
  let lines0 = Draw_prose.comment_prose_lines nt.nt_text in
  let title_opt, lines = header_title nt.nt_text lines0 in
  Option.iter (fun t -> el_text b "p" (Some "rq-subtitle") t) title_opt;
  Draw_prose.rocq_prose ctx b lines

let render_source_page ~corpus ~file (pf : Parse_vernac.parsed_file) : string =
  let page = page_name file in
  let notes = List.map (note_kind pf.text) pf.comments in
  let head, body_notes = page_head pf.items pf.text notes in
  let groups = contents pf.items body_notes in
  let ctx =
    make_ctx ~corpus ~page:(Some page) ~file:(Some file) ~text:pf.text ~notes:body_notes
      ~ops:pf.ops ~folds:pf.folds
  in
  let display_file =
    if String.starts_with ~prefix:"nanofil/" file then
      String.sub file 8 (String.length file - 8)
    else file
  in
  let b = Html.create (max 4096 (String.length pf.text * 6)) in
  shell b ~title:display_file
    ~crumbs:(fun b -> draw_crumbs b display_file)
    ~main:(fun b ->
      draw_sidebar ctx b file groups;
      el b "article" (Some "dterm dterm-rocq") (fun b ->
          el_text b "h1" (Some "source-title") display_file;
          el b "div" (Some "prose lede") (fun b -> List.iter (draw_lede ctx b) head);
          Draw_prose.rocq_layout b;
          el b "div" (Some "rq-root") (fun b -> Draw_term.rocq_items ctx b pf.items)));
  Html.contents b

(* ── Index page ────────────────────────────────────────────────────────── *)

type role_group = {
  rg_title : string;
  rg_note : Html.t -> unit;
  rg_dirs : string list;
}

let role_groups : role_group list =
  [
    {
      rg_title = "Live campaign: GNU Hello over userland glibc";
      rg_note =
        (fun b ->
          raw b "Active proof campaign (";
          el_raw b "code" None "nanofil-glibc";
          raw b ", ";
          el_a b "a" None [ ("href", "../docs/glibc-ir.html") ] (fun b -> raw b "glibc-ir.md");
          raw b ") proving userland glibc compiled to nanofil IR over audited libpizlo ";
          el_raw b "code" None "zsys_*";
          raw b " syscall contracts (";
          el_a b "a" None [ ("href", "../docs/zsys.html") ] (fun b -> raw b "zsys.md");
          raw b ").");
      rg_dirs =
        [
          "nanofil/rocq/glibc/zsys";
          "nanofil/rocq/glibc/string";
          "nanofil/rocq/glibc/stdlib";
          "nanofil/rocq/glibc/libio";
          "nanofil/rocq/glibc/hello";
          "nanofil/rocq/glibc";
        ];
    };
    {
      rg_title = "Core framework: IR model, validator soundness, external calls, and Iris program logic";
      rg_note =
        (fun b ->
          raw b "Shared foundation (";
          el_raw b "code" None "nanofil-rocq";
          raw b ", ";
          el_a b "a" None [ ("href", "../formal.html") ] (fun b -> raw b "formal.md");
          raw b ", ";
          el_a b "a" None [ ("href", "../logic.html") ] (fun b -> raw b "logic.md");
          raw b "): the checked-IR semantics and validator, the ";
          el_raw b "code" None "valid_no_unchecked";
          raw b " soundness theorem, the external-call boundary, and the Iris separation logic used by all program proofs.");
      rg_dirs =
        [
          "nanofil/rocq/theories/core";
          "nanofil/rocq/theories/soundness";
          "nanofil/rocq/theories/external";
          "nanofil/rocq/theories/logic";
        ];
    };
    {
      rg_title = "Program-logic worked example and constant-time spikes";
      rg_note =
        (fun b ->
          raw b "Worked examples (";
          el_raw b "code" None "listsum.c";
          raw b ") proved through the production ";
          el_raw b "code" None "Logic.v";
          raw b " framework (";
          el_raw b "code" None "nanofil-logic-spikes";
          raw b ", ";
          el_a b "a" None [ ("href", "../logic.html") ] (fun b -> raw b "logic.md");
          raw b ") and constant-time poison taint semantics.");
      rg_dirs = [ "nanofil/rocq/spikes" ];
    };
    {
      rg_title = "Gallina compiler backend and λANF lowering";
      rg_note =
        (fun b ->
          raw b "Separate compiler workstreams: the Gallina IR-to-x86-64 compiler backend and NFB bytecode round-trip proofs (";
          el_a b "a" None [ ("href", "../docs/gallina-backend.html") ] (fun b ->
              raw b "gallina-backend.md");
          raw b ", ";
          el_a b "a" None [ ("href", "../docs/nfb.html") ] (fun b -> raw b "nfb.md");
          raw b "), its C++ (Crane) and C (CertiRocq) extractions, and the CertiRocq λANF-to-IR lowering pass (";
          el_a b "a" None [ ("href", "../lambda-anf.html") ] (fun b -> raw b "lambda-anf.md");
          raw b ").");
      rg_dirs =
        [
          "nanofil/rocq/backend";
          "nanofil/rocq/backend/crane";
          "nanofil/rocq/backend/certirocq";
          "nanofil/anf/lower";
          "nanofil/anf/lower/tests";
          "nanofil/anf/backend";
        ];
    };
  ]

let draw_count b n w =
  if n = 0 then ()
  else if n = 1 then (
    raw b " · 1";
    raw b nbsp;
    esc b w)
  else (
    raw b " · ";
    esc_int b n;
    raw b nbsp;
    esc b w;
    raw_char b 's')

let draw_file_dir corpus b pages dir =
  let r =
    if String.starts_with ~prefix:"nanofil/" dir then
      String.sub dir 8 (String.length dir - 8)
    else dir
  in
  let src = "https://github.com/mbrock/filnix/tree/main/" ^ dir in
  el b "h3" (Some "rq-dir") (fun b ->
      el_a b "a" None [ ("href", src) ] (fun b ->
          esc b r;
          raw_char b '/'));
  el b "dl" (Some "rq-files") (fun b ->
      List.iter
        (fun pm ->
          if Filename.dirname pm.pm_file = dir then (
            let p = page_name pm.pm_file in
            let h = p ^ ".html" in
            let base = Filename.basename pm.pm_file in
            let row_ctx =
              make_ctx ~corpus ~page:(Some p) ~file:(Some pm.pm_file) ~text:"" ~notes:[]
                ~ops:(Hashtbl.create 1) ~folds:(Hashtbl.create 1)
            in
            el b "dt" None (fun b ->
                el_a b "a" None [ ("href", h) ] (fun b -> esc b base);
                el b "span" (Some "rq-file-meta") (fun b ->
                    esc_int b pm.pm_lines;
                    raw b nbsp;
                    raw b "lines";
                    draw_count b pm.pm_lemmas "lemma";
                    draw_count b pm.pm_axioms "axiom"));
            el b "dd" None (fun b -> Draw_prose.rocq_prose_inline row_ctx b pm.pm_summary)))
        pages)

let render_index_page ~corpus (pages : page_meta list) : string =
  let b = Html.create 65536 in
  let ds =
    pages |> List.map (fun pm -> Filename.dirname pm.pm_file) |> List.sort_uniq String.compare
  in
  let known =
    role_groups |> List.concat_map (fun g -> g.rg_dirs) |> List.sort_uniq String.compare
  in
  let extra = List.filter (fun d -> not (List.mem d known)) ds in
  shell b ~title:"Rocq"
    ~crumbs:(fun b ->
      el_a b "a" (Some "crumb") [ ("href", "../../index.html") ] (fun b -> raw b "Wiki");
      el_raw b "span" (Some "crumb-sep") "›";
      el_a b "a" (Some "crumb") [ ("href", "../index.html") ] (fun b -> raw b "nanofil");
      el_raw b "span" (Some "crumb-sep") "›";
      el_raw b "span" (Some "crumb current") "Rocq")
    ~main:(fun b ->
      el b "article" (Some "dterm dterm-rocq rq-index") (fun b ->
          el_raw b "h1" (Some "source-title") "nanofil's Rocq model and proofs";
          el b "div" (Some "prose lede") (fun b ->
              el b "p" None (fun b ->
                  raw b "This directory contains the Rocq formalization and proofs for ";
                  el_a b "a" None [ ("href", "../index.html") ] (fun b -> raw b "nanofil");
                  raw b " (";
                  el_a b "a" None [ ("href", "../formal.html") ] (fun b ->
                      raw b "the formal campaign");
                  raw b "). It defines an executable small-step semantics and validator for nanofil's checked capability IR (";
                  el_raw b "code" None "rocq/theories/core/";
                  raw b "), proves that a module the validator accepts never makes an unchecked memory access under the Fil-C runtime axioms (";
                  el_a b "a" None [ ("href", "rocq-theories-soundness-Soundness.html") ] (fun b ->
                      raw b "Soundness.v");
                  raw b "), and builds an Iris separation logic for proving that compiled C programs never panic (";
                  el_raw b "code" None "rocq/theories/logic/";
                  raw b "). It also includes a Gallina x86-64 compiler backend and NFB bytecode round-trip proofs (";
                  el_raw b "code" None "rocq/backend/";
                  raw b ") and a λANF-to-IR lowering pass (";
                  el_raw b "code" None "anf/lower/";
                  raw b ").");
              el b "p" None (fun b ->
                  raw b "The active whole-program campaign (";
                  el_raw b "code" None "rocq/glibc/";
                  raw b ", ";
                  el_a b "a" None [ ("href", "../docs/glibc-ir.html") ] (fun b ->
                      raw b "glibc-ir.md");
                  raw b ") links C programs against userland glibc compiled to nanofil IR and pushes trusted contracts down to libpizlo's ";
                  el_raw b "code" None "zsys_*";
                  raw b " syscall and runtime boundary (";
                  el_a b "a" None [ ("href", "../docs/zsys.html") ] (fun b -> raw b "zsys.md");
                  raw b "). The proof of ";
                  el_raw b "code" None "listsum.c";
                  raw b " is a worked example of the program logic (";
                  el_raw b "code" None "rocq/spikes/";
                  raw b "). Files that a generator writes, such as the IR fixtures, say ";
                  el_raw b "code" None "Do not edit";
                  raw b " in their headers and are omitted from this index.");
              el_raw b "h2" (Some "prose-h") "Start here";
              el b "ul" None (fun b ->
                  el b "li" None (fun b ->
                      el_raw b "strong" None "Live GNU Hello over userland glibc (";
                      el_raw b "code" None "rocq/glibc/";
                      el_raw b "strong" None "): ";
                      raw b "Start with ";
                      el_a b "a" None [ ("href", "rocq-glibc-zsys-OsWorld.html") ] (fun b ->
                          raw b "OsWorld.v");
                      raw b " and ";
                      el_a b "a" None [ ("href", "rocq-glibc-zsys-OsRegistry.html") ] (fun b ->
                          raw b "OsRegistry.v");
                      raw b " for the audited ";
                      el_raw b "code" None "zsys_*";
                      raw b " syscall boundary and ";
                      el_raw b "code" None "errno";
                      raw b " lending, ";
                      el_a b "a" None [ ("href", "rocq-glibc-string-WordString.html") ] (fun b ->
                          raw b "WordString.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-glibc-string-StrlenWord.html") ] (fun b ->
                          raw b "StrlenWord.v");
                      raw b ", and ";
                      el_a b "a" None [ ("href", "rocq-glibc-string-StrcmpLogic.html") ] (fun b ->
                          raw b "StrcmpLogic.v");
                      raw b " for fractional word-aligned string ownership, ";
                      el_raw b "code" None "strlen";
                      raw b ", and ";
                      el_raw b "code" None "strcmp";
                      raw b ", and ";
                      el_a b "a" None [ ("href", "rocq-glibc-stdlib-AllocLogic.html") ] (fun b ->
                          raw b "AllocLogic.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-glibc-stdlib-AtexitLogic.html") ] (fun b ->
                          raw b "AtexitLogic.v");
                      raw b ", and ";
                      el_a b "a" None [ ("href", "rocq-glibc-stdlib-LeavesLogic.html") ] (fun b ->
                          raw b "LeavesLogic.v");
                      raw b " for ";
                      el_raw b "code" None "malloc";
                      raw b ", ";
                      el_raw b "code" None "free";
                      raw b ", ";
                      el_raw b "code" None "atexit";
                      raw b ", and TLS/locale leaf triples. ";
                      el_a b "a" None [ ("href", "rocq-glibc-hello-HelloStartNeverPanics.html") ]
                        (fun b -> raw b "HelloStartNeverPanics.v");
                      raw b " and ";
                      el_a b "a" None [ ("href", "rocq-glibc-hello-HelloInterpNeverPanics.html") ]
                        (fun b -> raw b "HelloInterpNeverPanics.v");
                      raw b " assemble the end-to-end whole-program theorem for GNU Hello over compiled glibc IR.");
                  el b "li" None (fun b ->
                      el_raw b "strong" None "Core IR model and validator soundness (";
                      el_raw b "code" None "rocq/theories/core/";
                      el_raw b "strong" None ", ";
                      el_raw b "code" None "rocq/theories/soundness/";
                      el_raw b "strong" None "): ";
                      raw b "Read ";
                      el_a b "a" None [ ("href", "rocq-theories-core-Syntax.html") ] (fun b ->
                          raw b "Syntax.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-theories-core-Semantics.html") ] (fun b ->
                          raw b "Semantics.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-theories-core-Runtime.html") ] (fun b ->
                          raw b "Runtime.v");
                      raw b ", and ";
                      el_a b "a" None [ ("href", "rocq-theories-core-Validate.html") ] (fun b ->
                          raw b "Validate.v");
                      raw b " for the checked IR and validator, then ";
                      el_a b "a" None [ ("href", "rocq-theories-soundness-Machine.html") ] (fun b ->
                          raw b "Machine.v");
                      raw b " and ";
                      el_a b "a" None [ ("href", "rocq-theories-soundness-Soundness.html") ] (fun b ->
                          raw b "Soundness.v");
                      raw b " (";
                      el_raw b "code" None "valid_no_unchecked";
                      raw b ") for the proof that validated IR never steps to ";
                      el_raw b "code" None "unchecked";
                      raw b ".");
                  el b "li" None (fun b ->
                      el_raw b "strong" None "Iris program logic (";
                      el_raw b "code" None "rocq/theories/logic/";
                      el_raw b "strong" None ", ";
                      el_raw b "code" None "rocq/theories/external/";
                      el_raw b "strong" None "): ";
                      raw b "Read ";
                      el_a b "a" None [ ("href", "rocq-theories-logic-Panics.html") ] (fun b ->
                          raw b "Panics.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-theories-logic-Pieces.html") ] (fun b ->
                          raw b "Pieces.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-theories-logic-Heap.html") ] (fun b ->
                          raw b "Heap.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-theories-logic-Language.html") ] (fun b ->
                          raw b "Language.v");
                      raw b ", and ";
                      el_a b "a" None [ ("href", "rocq-theories-logic-Logic.html") ] (fun b ->
                          raw b "Logic.v");
                      raw b " (";
                      el_a b "a" None [ ("href", "../logic.html") ] (fun b ->
                          raw b "the program logic");
                      raw b "), with ";
                      el_a b "a" None [ ("href", "rocq-theories-external-ExternalCalls.html") ]
                        (fun b -> raw b "ExternalCalls.v");
                      raw b " and ";
                      el_a b "a" None [ ("href", "rocq-theories-logic-ContractFrame.html") ] (fun b ->
                          raw b "ContractFrame.v");
                      raw b " for external-call contracts and framing.");
                  el b "li" None (fun b ->
                      el_raw b "strong" None "Compiler backend: ";
                      raw b "The Gallina compiler backend and NFB bytecode proofs are in ";
                      el_raw b "code" None "rocq/backend/";
                      raw b " (";
                      el_a b "a" None [ ("href", "rocq-backend-Compile.html") ] (fun b ->
                          raw b "Compile.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-backend-Regs.html") ] (fun b ->
                          raw b "Regs.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-backend-RegsProof.html") ] (fun b ->
                          raw b "RegsProof.v");
                      raw b ", ";
                      el_a b "a" None [ ("href", "rocq-backend-NfbProof.html") ] (fun b ->
                          raw b "NfbProof.v");
                      raw b ").")));
          List.iter
            (fun g ->
              let present = List.filter (fun d -> List.mem d ds) g.rg_dirs in
              if present <> [] then (
                el_text b "h2" (Some "rq-sec") g.rg_title;
                el b "p" (Some "rq-group-note") g.rg_note;
                List.iter (draw_file_dir corpus b pages) present))
            role_groups;
          List.iter (draw_file_dir corpus b pages) extra));
  Html.contents b

let write_file path content =
  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc content)

(* Full parallel two-pass site renderer using OCaml 5 domains.
   Pass 1 parses all files in parallel (keeping parsed ASTs in memory —
   all 1,024 files take only ~150 MiB total!) and merges the global index in
   exact deterministic input order.
   Pass 2 renders all HTML pages in parallel across domains with zero locks! *)
let render_site ~out ~root ~prolog_dir ~concepts_dir ~no_index ~jobs ~c_batch ~swipl
    (files : string list) =
  let t0 = Unix.gettimeofday () in
  let file_arr = Array.of_list files in
  let n_files = Array.length file_arr in
  let jobs = max 1 (min jobs (max 1 n_files)) in

  let concepts =
    match concepts_dir with Some d -> Concepts.load_dir d | None -> Concepts.empty ()
  in
  let cb = make_corpus_builder () in
  Option.iter (index_prolog_dir cb) prolog_dir;

  (* Pass 1: parse all files in parallel across OCaml 5 domains *)
  let parsed = Array.make n_files None in
  let failed = Atomic.make false in
  let parse_slice lo hi =
    let cache = Hashtbl.create 64 in
    for i = lo to hi - 1 do
      let f = file_arr.(i) in
      let full = Filename.concat root f in
      match Parse_vernac.parse_file ~cache full with
      | exception Lexer.Lex_error off ->
          Printf.eprintf "dterm-rocq: cannot read %s (lex error at byte %d)\n%!" f off;
          Atomic.set failed true
      | pf ->
          let warns = collect_warn_raws [] pf.items in
          List.iter
            (fun ((sp : span), kw) ->
              Printf.eprintf "%s:%d: dterm-rocq draws this %s as text\n%!" f
                (Reprint.line_of_offset pf.text sp.lo) kw)
            warns;
          parsed.(i) <- Some pf
    done
  in
  if jobs <= 1 then parse_slice 0 n_files
  else (
    let ds =
      List.init jobs (fun j ->
          let lo = j * n_files / jobs in
          let hi = (j + 1) * n_files / jobs in
          Domain.spawn (fun () -> parse_slice lo hi))
    in
    List.iter Domain.join ds);
  if Atomic.get failed then exit 1;
  let t_parse = Unix.gettimeofday () in

  (* Optional Pass 1.5: render deduplicated C snippets once through c_batch.pl *)
  let c_drawer, c_stats =
    match (c_batch, prolog_dir) with
    | Some script, Some pdir ->
        let drawer, nf, ni, na =
          C_batch.run ~swipl ~script ~prolog_dir:pdir ~play_root:"../play/" ~concepts parsed
        in
        (Some drawer, Some (nf, ni, na))
    | _ -> (None, None)
  in
  let t_cbatch = Unix.gettimeofday () in

  (* Build global index and page metadata in exact deterministic file order *)
  let metas = Array.make n_files None in
  for i = 0 to n_files - 1 do
    let f = file_arr.(i) in
    let pf = Option.get parsed.(i) in
    let p = page_name f in
    let gs = index_items ~page:p ~file:f pf.items in
    List.iter (add_global_entry cb) gs;
    let notes = List.map (note_kind pf.text) pf.comments in
    metas.(i) <- Some (page_meta_of f pf.text pf.items notes)
  done;
  let corpus =
    finalize_corpus cb
      ~prolog_prefix:(Option.map (fun _ -> "../") prolog_dir)
      ~concepts
      ~concepts_prefix:"../"
      ~all_files:files
      ~c_drawer
  in
  let t_index = Unix.gettimeofday () in

  (* Pass 2: render all HTML pages in parallel across OCaml 5 domains *)
  let render_slice lo hi =
    for i = lo to hi - 1 do
      let f = file_arr.(i) in
      let pf = Option.get parsed.(i) in
      let html = render_source_page ~corpus ~file:f pf in
      let out_path = Filename.concat out (page_name f ^ ".html") in
      write_file out_path html
    done
  in
  if jobs <= 1 then render_slice 0 n_files
  else (
    let ds =
      List.init jobs (fun j ->
          let lo = j * n_files / jobs in
          let hi = (j + 1) * n_files / jobs in
          Domain.spawn (fun () -> render_slice lo hi))
    in
    List.iter Domain.join ds);

  if not no_index then (
    let meta_list = Array.to_list metas |> List.map Option.get in
    let idx_html = render_index_page ~corpus meta_list in
    write_file (Filename.concat out "index.html") idx_html);

  let t_end = Unix.gettimeofday () in
  let c_note =
    match c_stats with
    | Some (nf, ni, na) ->
        Printf.sprintf " c_batch=%.1fms(%dF/%dI/%dA)"
          ((t_cbatch -. t_parse) *. 1000.0) nf ni na
    | None -> ""
  in
  Printf.eprintf
    "dterm-rocq (%d domain%s): %d pages | parse=%.1fms%s index=%.1fms render=%.1fms total=%.1fms (%.3f ms/page)\n%!"
    jobs
    (if jobs = 1 then "" else "s")
    n_files
    ((t_parse -. t0) *. 1000.0)
    c_note
    ((t_index -. t_cbatch) *. 1000.0)
    ((t_end -. t_index) *. 1000.0)
    ((t_end -. t0) *. 1000.0)
    (if n_files = 0 then 0.0 else ((t_end -. t0) *. 1000.0) /. float_of_int n_files)
