(* Concept node loader & resolver mirroring nanofil/web/concepts.pl. *)

type kind = FilC | Nanofil | Iris

type entry = {
  id : string;
  names : string list;
  body : string list;
  kind : (kind * string) option;
}

type t = {
  by_id : (string, entry) Hashtbl.t;
  by_key : (string, string) Hashtbl.t;
  guide_docs : (string, unit) Hashtbl.t;
}

let empty () =
  {
    by_id = Hashtbl.create 64;
    by_key = Hashtbl.create 256;
    guide_docs = Hashtbl.create 16;
  }

let is_loaded t = Hashtbl.length t.by_id > 0

let iter f t = Hashtbl.iter (fun _ e -> f e) t.by_id

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic) @@ fun () ->
  really_input_string ic (in_channel_length ic)

let normalize_key s =
  let low = String.lowercase_ascii s in
  let b = Buffer.create (String.length low) in
  let prev_sp = ref true in
  String.iter
    (fun c ->
      let c = if c = '-' || c = '_' then ' ' else c in
      if c = ' ' then (
        if not !prev_sp then (
          Buffer.add_char b ' ';
          prev_sp := true))
      else (
        Buffer.add_char b c;
        prev_sp := false))
    low;
  let r = Buffer.contents b in
  let n = String.length r in
  if n > 0 && r.[n - 1] = ' ' then String.sub r 0 (n - 1) else r

let parse_kind_line l =
  let prefixes =
    [ ("**Fil-C**", FilC); ("**nanofil**", Nanofil); ("**Iris**", Iris) ]
  in
  let rec try_p = function
    | [] -> None
    | (mark, k) :: rest ->
        if String.starts_with ~prefix:mark l then
          let r0 = String.sub l (String.length mark) (String.length l - String.length mark) in
          let r1 = Markdown.trim_spaces r0 in
          if r1 = "" then Some (k, "")
          else if String.starts_with ~prefix:"·" r1 then
            let r2 = String.sub r1 (String.length "·") (String.length r1 - String.length "·") in
            Some (k, Markdown.trim_spaces r2)
          else None
        else try_p rest
  in
  try_p prefixes

let load_concept t id path =
  let text = read_file path in
  let lines0 = String.split_on_char '\n' text in
  match lines0 with
  | first :: rest when String.starts_with ~prefix:"# " first ->
      let title = String.sub first 2 (String.length first - 2) in
      let names =
        String.split_on_char '/' title
        |> List.map Markdown.trim_spaces
        |> List.filter (fun s -> s <> "")
      in
      let lines2 = Markdown.trim_blank_ends rest in
      let kind, body =
        match lines2 with
        | kline :: rest3 -> (
            match parse_kind_line kline with
            | Some kr -> (Some kr, Markdown.drop_leading_blank rest3)
            | None -> (None, lines2))
        | [] -> (None, [])
      in
      Hashtbl.replace t.by_id id { id; names; body; kind };
      List.iter
        (fun nm ->
          let k = normalize_key nm in
          match Hashtbl.find_opt t.by_key k with
          | Some existing when existing <> id ->
              failwith
                (Printf.sprintf "%s: the name %s is also concept %s's" path nm existing)
          | _ -> Hashtbl.replace t.by_key k id)
        (id :: names)
  | _ -> failwith (Printf.sprintf "%s: a concept starts with a # Title line" path)

let load_dir dir =
  let t = empty () in
  let files = Sys.readdir dir |> Array.to_list |> List.sort String.compare in
  List.iter
    (fun e ->
      if Filename.check_suffix e ".md" then
        let id = Filename.chop_suffix e ".md" in
        if id <> "README" then load_concept t id (Filename.concat dir e))
    files;
  t

let resolve t name =
  let k = normalize_key name in
  match Hashtbl.find_opt t.by_key k with
  | Some _ as hit -> hit
  | None -> (
      let len = String.length k in
      let try_drop suf =
        let slen = String.length suf in
        if len > slen && String.ends_with ~suffix:suf k then
          Hashtbl.find_opt t.by_key (String.sub k 0 (len - slen))
        else None
      in
      match try_drop "es" with Some _ as hit -> hit | None -> try_drop "s")

let get t id = Hashtbl.find t.by_id id
let title t id = List.hd (get t id).names
let page id = "concept-" ^ id ^ ".html"

let summary t id =
  let e = get t id in
  let rec take_para acc = function
    | l :: ls when not (Markdown.is_blank l) -> take_para (Markdown.trim_spaces l :: acc) ls
    | _ -> List.rev acc
  in
  String.concat " " (take_para [] e.body)

(* Parse [[name]] or [[name|shown]] starting right AFTER "[[".
   Returns (name, shown, next_byte_index) if valid. *)
let parse_link_after_open s i =
  let n = String.length s in
  let rec scan j =
    if j + 1 >= n then None
    else if s.[j] = ']' && s.[j + 1] = ']' then
      let inner = String.sub s i (j - i) in
      if
        inner = ""
        || String.contains inner '\n'
        || String.contains inner '['
        || String.contains inner ']'
        || String.contains inner ':'
        || String.contains inner '('
      then None
      else
        let name, shown =
          match String.index_opt inner '|' with
          | Some bar ->
              (String.sub inner 0 bar, String.sub inner (bar + 1) (String.length inner - bar - 1))
          | None -> (inner, inner)
        in
        Some (name, shown, j + 2)
    else if s.[j] = '\n' || s.[j] = '[' || s.[j] = ']' then None
    else scan (j + 1)
  in
  scan i

(* concept_plain: strip links for card summaries. *)
let plain text =
  let n = String.length text in
  let b = Buffer.create n in
  let rec go i =
    if i >= n then Buffer.contents b
    else
      match text.[i] with
      | '`' -> (
          match String.index_from_opt text (i + 1) '`' with
          | Some k ->
              Buffer.add_substring b text i (k - i + 1);
              go (k + 1)
          | None ->
              Buffer.add_char b '`';
              go (i + 1))
      | '[' when i + 1 < n && text.[i + 1] = '[' -> (
          match parse_link_after_open text (i + 2) with
          | Some (_, shown, next_i) ->
              Buffer.add_string b shown;
              go next_i
          | None ->
              Buffer.add_char b '[';
              go (i + 1))
      | '[' -> (
          let try_md_link () =
            match String.index_from_opt text (i + 1) ']' with
            | Some rb when rb + 1 < n && text.[rb + 1] = '(' -> (
                match String.index_from_opt text (rb + 2) ')' with
                | Some rp ->
                    let url = String.sub text (rb + 2) (rp - rb - 2) in
                    if not (String.contains url ' ') then (
                      Buffer.add_substring b text (i + 1) (rb - i - 1);
                      Some (rp + 1))
                    else None
                | None -> None)
            | _ -> None
          in
          match try_md_link () with
          | Some next_i -> go next_i
          | None -> (
              match String.index_from_opt text (i + 1) ']' with
              | Some rb ->
                  let inner = String.sub text (i + 1) (rb - i - 1) in
                  if (not (String.contains inner '[')) && not (String.contains inner '\n') then (
                    Buffer.add_char b '`';
                    Buffer.add_string b inner;
                    Buffer.add_char b '`';
                    go (rb + 1))
                  else (
                    Buffer.add_char b '[';
                    go (i + 1))
              | None ->
                  Buffer.add_char b '[';
                  go (i + 1)))
      | c ->
          Buffer.add_char b c;
          go (i + 1)
  in
  go 0

let concept_rel path =
  let parts0 = String.split_on_char '/' path in
  let rev =
    List.fold_left
      (fun acc seg ->
        if seg = ".." then match acc with _ :: tl -> tl | [] -> []
        else seg :: acc)
      [ "concepts"; "docs"; "nanofil" ]
      parts0
  in
  List.rev rev

let concept_url t ~prefix url =
  if String.starts_with ~prefix:"#" url then url
  else
    match String.index_opt url ':' with
    | Some b when b > 0 -> url
    | _ ->
        let path, frag =
          match String.index_opt url '#' with
          | Some b -> (String.sub url 0 b, String.sub url b (String.length url - b))
          | None -> (url, "")
        in
        let href0 =
          if Filename.check_suffix path ".md" && not (String.contains path '/') then
            let id = Filename.chop_suffix path ".md" in
            prefix ^ page id
          else if
            String.starts_with ~prefix:"../" path && Filename.check_suffix path ".md"
          then
            let f = String.sub path 3 (String.length path - 3) in
            if not (String.contains f '/') then
              let d = Filename.chop_suffix f ".md" in
              if Hashtbl.mem t.guide_docs d then prefix ^ d ^ ".html"
              else prefix ^ "docs/" ^ d ^ ".html"
            else
              let rel = String.concat "/" (concept_rel path) in
              "https://github.com/mbrock/filnix/blob/main/" ^ rel
          else if
            String.starts_with ~prefix:"../../rocq/" path && Filename.check_suffix path ".v"
          then
            let f = String.sub path 11 (String.length path - 11) in
            let base = Filename.chop_suffix f ".v" in
            let pg = String.concat "-" ("rocq" :: String.split_on_char '/' base) in
            prefix ^ "rocq/" ^ pg ^ ".html"
          else if
            String.starts_with ~prefix:"../../src/" path && Filename.check_suffix path ".pl"
          then
            let f = String.sub path 10 (String.length path - 10) in
            let m = Filename.chop_suffix f ".pl" in
            prefix ^ m ^ ".html"
          else if Filename.check_suffix path ".nix" then
            match concept_rel path with
            | "experiments" :: _ ->
                let rel = String.concat "/" (concept_rel path) in
                "https://github.com/mbrock/filnix/blob/main/" ^ rel
            | parts ->
                let b0 = String.concat "-" parts in
                let b = Filename.chop_suffix b0 ".nix" in
                prefix ^ "../nix/" ^ b ^ ".html"
          else
            let rel = String.concat "/" (concept_rel path) in
            "https://github.com/mbrock/filnix/blob/main/" ^ rel
        in
        href0 ^ frag
