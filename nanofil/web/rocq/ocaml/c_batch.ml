(* Batched C-in-Rocq-comments sidecar client.
   Collects all unique ```c fences, `c:...` inline spans, and unmarked C-keyword
   inline candidates across all parsed .v files and loaded concepts, renders them
   in a single swipl invocation of nanofil/web/c/c_batch.pl, and returns an
   immutable lock-free Draw_env.c_renderer safe to share across OCaml 5 domains. *)

open Ast
open Draw_env

(* ── Standard RFC 4648 Base64 (zero dependencies) ──────────────────────── *)

let b64_enc_tbl = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

let base64_encode s =
  let n = String.length s in
  let out = Bytes.create (((n + 2) / 3) * 4) in
  let i = ref 0 in
  let o = ref 0 in
  while !i + 2 < n do
    let a = Char.code s.[!i] in
    let b = Char.code s.[!i + 1] in
    let c = Char.code s.[!i + 2] in
    Bytes.set out !o b64_enc_tbl.[a lsr 2];
    Bytes.set out (!o + 1) b64_enc_tbl.[((a land 3) lsl 4) lor (b lsr 4)];
    Bytes.set out (!o + 2) b64_enc_tbl.[((b land 15) lsl 2) lor (c lsr 6)];
    Bytes.set out (!o + 3) b64_enc_tbl.[c land 63];
    i := !i + 3;
    o := !o + 4
  done;
  (match n - !i with
  | 1 ->
      let a = Char.code s.[!i] in
      Bytes.set out !o b64_enc_tbl.[a lsr 2];
      Bytes.set out (!o + 1) b64_enc_tbl.[(a land 3) lsl 4];
      Bytes.set out (!o + 2) '=';
      Bytes.set out (!o + 3) '='
  | 2 ->
      let a = Char.code s.[!i] in
      let b = Char.code s.[!i + 1] in
      Bytes.set out !o b64_enc_tbl.[a lsr 2];
      Bytes.set out (!o + 1) b64_enc_tbl.[((a land 3) lsl 4) lor (b lsr 4)];
      Bytes.set out (!o + 2) b64_enc_tbl.[(b land 15) lsl 2];
      Bytes.set out (!o + 3) '='
  | _ -> ());
  Bytes.unsafe_to_string out

let b64_dec_val c =
  if c >= 'A' && c <= 'Z' then Char.code c - Char.code 'A'
  else if c >= 'a' && c <= 'z' then Char.code c - Char.code 'a' + 26
  else if c >= '0' && c <= '9' then Char.code c - Char.code '0' + 52
  else if c = '+' then 62
  else if c = '/' then 63
  else -1

let base64_decode s =
  let n = String.length s in
  let b = Buffer.create ((n * 3) / 4 + 4) in
  let acc = ref 0 in
  let bits = ref 0 in
  let i = ref 0 in
  let stop = ref false in
  while !i < n && not !stop do
    let c = s.[!i] in
    incr i;
    if c = '=' then stop := true
    else
      let v = b64_dec_val c in
      if v >= 0 then (
        acc := (!acc lsl 6) lor v;
        bits := !bits + 6;
        if !bits >= 8 then (
          bits := !bits - 8;
          Buffer.add_char b (Char.chr ((!acc lsr !bits) land 0xff))))
  done;
  Buffer.contents b

(* ── Sound superset of C keywords eligible for c_inline_auto ───────────── *)

(* Every keyword/2 (plus non-boolean c23_keyword/2) in nanofil/src/c_lex.pl,
   excluding true, false, bool, nullptr which c_draw.pl:1093 rejects. *)
let c_auto_keywords : (string, unit) Hashtbl.t =
  let tbl = Hashtbl.create 97 in
  List.iter
    (fun k -> Hashtbl.replace tbl k ())
    [
      "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do";
      "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if";
      "inline"; "int"; "long"; "register"; "restrict"; "return"; "short";
      "signed"; "sizeof"; "static"; "struct"; "switch"; "typedef"; "union";
      "unsigned"; "void"; "volatile"; "while";
      "_Alignas"; "_Alignof"; "_Atomic"; "_Bool"; "_Complex"; "_Generic";
      "_Imaginary"; "__real__"; "__real"; "__imag__"; "__imag"; "_Noreturn";
      "_Static_assert"; "_Thread_local"; "__restrict"; "__restrict__";
      "__inline"; "__inline__"; "__const"; "__const__"; "__volatile";
      "__volatile__"; "__signed"; "__signed__"; "asm"; "__asm"; "__asm__";
      "__attribute"; "__attribute__"; "__extension__"; "__auto_type";
      "__typeof"; "__typeof__"; "typeof"; "__alignof"; "__alignof__";
      "__int128"; "_Float16"; "__bf16"; "__thread";
      "static_assert"; "alignas"; "alignof"; "thread_local";
    ];
  tbl

let is_ident_start c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'

let is_ident_cont c =
  is_ident_start c || (c >= '0' && c <= '9')

(* Returns true whenever c_inline_auto could possibly accept s: s must have at
   least 2 tokens (so not a single bare identifier) and contain a C keyword word. *)
let has_c_auto_keyword s =
  let n = String.length s in
  if n < 3 then false
  else
    let found_kw = ref false in
    let tokens = ref 0 in
    let i = ref 0 in
    while !i < n && not (!found_kw && !tokens >= 2) do
      let c = s.[!i] in
      if c = ' ' || c = '\t' || c = '\n' || c = '\r' then incr i
      else if is_ident_start c then (
        let j = ref (!i + 1) in
        while !j < n && is_ident_cont s.[!j] do
          incr j
        done;
        incr tokens;
        if not !found_kw then (
          let w = String.sub s !i (!j - !i) in
          if Hashtbl.mem c_auto_keywords w then found_kw := true);
        i := !j)
      else (
        incr tokens;
        incr i)
    done;
    !found_kw && !tokens >= 2

(* ── Candidate collector mirroring Draw_prose's Markdown + inline walk ─── *)

let collect_candidates ~concepts (parsed : Parse_vernac.parsed_file option array) =
  let fences = Hashtbl.create 64 in
  let inlines = Hashtbl.create 512 in
  let autos = Hashtbl.create 512 in
  let fence_list = ref [] in
  let inline_list = ref [] in
  let auto_list = ref [] in
  let add_fence s =
    if not (Hashtbl.mem fences s) then (
      Hashtbl.add fences s ();
      fence_list := s :: !fence_list)
  in
  let add_code s =
    match Draw_prose.strip_c_prefix s with
    | Some _ ->
        if not (Hashtbl.mem inlines s) then (
          Hashtbl.add inlines s ();
          inline_list := s :: !inline_list)
    | None ->
        if has_c_auto_keyword s && not (Hashtbl.mem autos s) then (
          Hashtbl.add autos s ();
          auto_list := s :: !auto_list)
  in
  let rec scan_inline text =
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
            | Some (_, _, next_i) -> go next_i
            | None -> go_bracket i)
        | '[' -> go_bracket i
        | '`' -> (
            match String.index_from_opt text (i + 1) '`' with
            | Some k ->
                add_code (String.sub text (i + 1) (k - i - 1));
                go (k + 1)
            | None -> go (i + 1))
        | _ -> go (i + 1)
    and go_bracket i =
      let md_link =
        match String.index_from_opt text (i + 1) ']' with
        | Some rb when rb + 1 < n && text.[rb + 1] = '(' -> (
            match String.index_from_opt text (rb + 2) ')' with
            | Some rp ->
                let u = String.sub text (rb + 2) (rp - rb - 2) in
                if not (String.contains u ' ') then
                  Some (String.sub text (i + 1) (rb - i - 1), rp + 1)
                else None
            | None -> None)
        | _ -> None
      in
      match md_link with
      | Some (ts, next_i) ->
          scan_inline ts;
          go next_i
      | None -> (
          match scan_bracketed (i + 1) 1 with
          | Some rb ->
              add_code (String.sub text (i + 1) (rb - i - 1));
              go (rb + 1)
          | None -> go (i + 1))
    in
    go 0
  and scan_blocks bs =
    List.iter
      (function
        | Markdown.P t | Markdown.H (_, t) -> scan_inline t
        | Markdown.Ul items -> List.iter scan_inline items
        | Markdown.Table (head, rows) ->
            List.iter scan_inline head;
            List.iter (List.iter scan_inline) rows
        | Markdown.Fence ("c", flines) -> add_fence (String.concat "\n" flines)
        | Markdown.Fence (("rocq" | "coq" | ""), flines) -> (
            let text = String.concat "\n" flines in
            match Parse_vernac.parse_string text with
            | exception Lexer.Lex_error _ -> ()
            | pf ->
                if not (List.exists (function ISent (VRaw _) -> true | _ -> false) pf.items) then
                  List.iter (fun cm -> scan_comment cm.cm_text) pf.comments)
        | Markdown.Pre _ | Markdown.Embed _ | Markdown.Fence _ -> ())
      bs
  and scan_lines lines = scan_blocks (Markdown.blocks (Markdown.dedent lines))
  and scan_comment cm_text =
    let lines = Draw_prose.comment_prose_lines cm_text in
    (match Draw_prose.comment_heading cm_text with
    | Some (_, title) ->
        scan_inline title;
        (match lines with _ :: rest -> scan_lines rest | [] -> ())
    | None -> (
        match lines with
        | first :: rest when String.starts_with ~prefix:"# " first ->
            scan_inline (Markdown.trim_spaces (String.sub first 2 (String.length first - 2)));
            scan_lines rest
        | _ -> scan_lines lines));
    (* Trailing comments are also joined with spaces for aside_after. *)
    if List.length lines > 1 then scan_inline (String.concat " " lines)
  in
  Array.iter
    (function
      | Some (pf : Parse_vernac.parsed_file) ->
          List.iter (fun cm -> scan_comment cm.cm_text) pf.comments
      | None -> ())
    parsed;
  Concepts.iter
    (fun (e : Concepts.entry) ->
      scan_lines e.body;
      let sum = Concepts.plain (Concepts.summary concepts e.id) in
      scan_inline sum)
    concepts;
  (List.rev !fence_list, List.rev !inline_list, List.rev !auto_list)

(* ── Anchor prefix rewriter for 2nd+ ```c fence on a single page ───────── *)

let replace_all ~needle ~with_ s =
  let n = String.length s in
  let m = String.length needle in
  if m = 0 || n < m then s
  else
    let b = Buffer.create n in
    let rec go i =
      if i > n - m then Buffer.add_substring b s i (n - i)
      else
        let rec match_at k =
          if k = m then true
          else if s.[i + k] = needle.[k] then match_at (k + 1)
          else false
        in
        if match_at 0 then (
          Buffer.add_string b with_;
          go (i + m))
        else (
          Buffer.add_char b s.[i];
          go (i + 1))
    in
    go 0;
    Buffer.contents b

let rewrite_fence_prefix ~seq html =
  if seq <= 1 then html
  else
    let id_new = Printf.sprintf "id=\"c%d-" seq in
    let href_new = Printf.sprintf "href=\"#c%d-" seq in
    html
    |> replace_all ~needle:"id=\"c1-" ~with_:id_new
    |> replace_all ~needle:"href=\"#c1-" ~with_:href_new

(* ── Run swipl c_batch.pl once for the whole corpus ────────────────────── *)

let run ~swipl ~script ~prolog_dir ~play_root ~concepts parsed : c_renderer * int * int * int =
  let fences, inlines, autos = collect_candidates ~concepts parsed in
  let nf = List.length fences and ni = List.length inlines and na = List.length autos in
  let fence_tbl = Hashtbl.create (max 16 (nf * 2)) in
  let inline_tbl = Hashtbl.create (max 16 (ni * 2)) in
  let auto_tbl = Hashtbl.create (max 16 (na * 2)) in
  if nf + ni + na > 0 then (
    let in_path = Filename.temp_file "dterm_c_in_" ".txt" in
    let out_path = Filename.temp_file "dterm_c_out_" ".txt" in
    let cleanup () =
      (try Sys.remove in_path with _ -> ());
      (try Sys.remove out_path with _ -> ())
    in
    Fun.protect ~finally:cleanup @@ fun () ->
    let oc = open_out_bin in_path in
    Fun.protect
      ~finally:(fun () -> close_out oc)
      (fun () ->
        List.iter
          (fun s ->
            output_string oc "F ";
            output_string oc (base64_encode s);
            output_char oc '\n')
          fences;
        List.iter
          (fun s ->
            output_string oc "I ";
            output_string oc (base64_encode s);
            output_char oc '\n')
          inlines;
        List.iter
          (fun s ->
            output_string oc "A ";
            output_string oc (base64_encode s);
            output_char oc '\n')
          autos);
    let argv = [| swipl; "-q"; script; prolog_dir; play_root; in_path; out_path |] in
    let pid = Unix.create_process swipl argv Unix.stdin Unix.stdout Unix.stderr in
    let _, status = Unix.waitpid [] pid in
    (match status with
    | Unix.WEXITED 0 -> ()
    | Unix.WEXITED c ->
        failwith (Printf.sprintf "c_batch (%s) exited with code %d" script c)
    | Unix.WSIGNALED s ->
        failwith (Printf.sprintf "c_batch (%s) killed by signal %d" script s)
    | Unix.WSTOPPED s ->
        failwith (Printf.sprintf "c_batch (%s) stopped by signal %d" script s));
    let ic = open_in_bin out_path in
    Fun.protect
      ~finally:(fun () -> close_in ic)
      (fun () ->
        let read_entry tbl key =
          let line = input_line ic in
          let line =
            if String.length line > 0 && line.[String.length line - 1] = '\r' then
              String.sub line 0 (String.length line - 1)
            else line
          in
          if String.starts_with ~prefix:"OK " line then
            let html = base64_decode (String.sub line 3 (String.length line - 3)) in
            Hashtbl.replace tbl key html
        in
        List.iter (read_entry fence_tbl) fences;
        List.iter (read_entry inline_tbl) inlines;
        List.iter (read_entry auto_tbl) autos));
  let drawer =
    {
      c_fence =
        (fun ~seq lines ->
          let key = String.concat "\n" lines in
          Option.map (rewrite_fence_prefix ~seq) (Hashtbl.find_opt fence_tbl key));
      c_inline = (fun code -> Hashtbl.find_opt inline_tbl code);
      c_inline_auto = (fun code -> Hashtbl.find_opt auto_tbl code);
    }
  in
  (drawer, nf, ni, na)
