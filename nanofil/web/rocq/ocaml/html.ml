(* Fast direct-to-Buffer.t HTML emitter mirroring nanofil/web/dterm_html.pl. *)

type t = Buffer.t

let create n : t = Buffer.create n
let contents (b : t) = Buffer.contents b
let raw (b : t) s = Buffer.add_string b s
let raw_char (b : t) c = Buffer.add_char b c
let raw_sub (b : t) s lo len = Buffer.add_substring b s lo len

let esc_char (b : t) = function
  | '<' -> Buffer.add_string b "&lt;"
  | '>' -> Buffer.add_string b "&gt;"
  | '&' -> Buffer.add_string b "&amp;"
  | '"' -> Buffer.add_string b "&quot;"
  | c -> Buffer.add_char b c

let esc (b : t) s =
  let n = String.length s in
  let rec loop start i =
    if i >= n then (if start < n then Buffer.add_substring b s start (n - start))
    else
      match s.[i] with
      | '<' | '>' | '&' | '"' as c ->
          if start < i then Buffer.add_substring b s start (i - start);
          esc_char b c;
          loop (i + 1) (i + 1)
      | _ -> loop start (i + 1)
  in
  loop 0 0

let esc_int (b : t) i = Buffer.add_string b (string_of_int i)

let el_a (b : t) tag cls attrs body =
  Buffer.add_char b '<';
  Buffer.add_string b tag;
  (match cls with
  | None -> ()
  | Some c ->
      Buffer.add_string b " class=\"";
      Buffer.add_string b c;
      Buffer.add_char b '"');
  List.iter
    (fun (k, v) ->
      Buffer.add_char b ' ';
      Buffer.add_string b k;
      Buffer.add_string b "=\"";
      esc b v;
      Buffer.add_char b '"')
    attrs;
  Buffer.add_char b '>';
  body b;
  Buffer.add_string b "</";
  Buffer.add_string b tag;
  Buffer.add_char b '>'

let el (b : t) tag cls body = el_a b tag cls [] body

let el_text (b : t) tag cls s = el b tag cls (fun b -> esc b s)
let el_raw (b : t) tag cls s = el b tag cls (fun b -> raw b s)
let el_empty (b : t) tag cls = el b tag cls (fun _ -> ())

let seq b xs f = List.iter (fun x -> f b x) xs

(* Exact match to SWI-Prolog's uri_encoded(fragment, Text, Encoded). *)
let is_frag_safe = function
  | '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | '-' | '.' | '/'
  | '0' .. '9' | ':' | ';' | '=' | '?' | '@' | 'A' .. 'Z' | '_' | 'a' .. 'z' | '~' ->
      true
  | _ -> false

let hex_digits = "0123456789ABCDEF"

let uri_encode_fragment s =
  let n = String.length s in
  let needs = ref false in
  for i = 0 to n - 1 do
    if not (is_frag_safe s.[i]) then needs := true
  done;
  if not !needs then s
  else
    let b = Buffer.create (n + 8) in
    for i = 0 to n - 1 do
      let c = s.[i] in
      if is_frag_safe c then Buffer.add_char b c
      else
        let v = Char.code c in
        Buffer.add_char b '%';
        Buffer.add_char b hex_digits.[v lsr 4];
        Buffer.add_char b hex_digits.[v land 0xF]
    done;
    Buffer.contents b

let site_doors =
  [
    ("docs", "Docs", "docs/");
    ("explainers", "Explainers", "index.html#explainers");
    ("nix", "Nix", "nix/");
    ("nanofil", "nanofil", "nanofil/");
    ("campaigns", "Campaigns", "https://nix.swa.sh/");
    ("source", "Source", "https://github.com/mbrock/filnix");
  ]

let contains_sub hay needle =
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

let site_header (b : t) ~root ~door ~crumbs ~right =
  let home = root ^ "index.html" in
  raw b "<header class=\"library\"><div class=\"page-frame library-frame\">\n";
  raw b "  <div class=\"library-heading\"><p class=\"eyebrow\">Fil-C on Nix</p><h1>";
  el_a b "a" None [ ("href", home) ] (fun b -> raw b "Filnix wiki");
  raw b "</h1></div>\n  <nav class=\"doors\">\n";
  List.iter
    (fun (id, label, path) ->
      let href = if contains_sub path "://" then path else root ^ path in
      let cls = if id = door then "door selected" else "door" in
      raw b "    ";
      el_a b "a" (Some cls) [ ("href", href) ] (fun b -> raw b label);
      raw_char b '\n')
    site_doors;
  raw b "  </nav>\n</div></header>\n";
  raw b "<div class=\"status\"><div class=\"page-frame status-frame\">\n";
  el_a b "nav" (Some "crumbs") [ ("aria-label", "Breadcrumb") ] crumbs;
  el b "span" (Some "status-right") right;
  raw b "\n</div></div>\n"
