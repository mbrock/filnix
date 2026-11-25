(* Zero-dependency UTF-8 lexer, nested comment scanner, and sentence chunker.
   Uses OCaml 5's built-in String.get_utf_8_uchar over immutable strings. *)

open Ast

exception Lex_error of int

let is_white_byte = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false
let is_digit_byte c = c >= '0' && c <= '9'

let is_latin_sym u =
  u = 0x00AC (* ¬ *)
  || u = 0x00D7 (* × *)
  || u = 0x00F7 (* ÷ *)
  || u = 0x00B1 (* ± *)

let is_single_sym u =
  match u with
  | 0x231C (* ⌜ *) | 0x231D (* ⌝ *) | 0x25B7 (* ▷ *) | 0x25A1 (* □ *)
  | 0x25C7 (* ◇ *) | 0x25A0 (* ■ *) | 0x22A4 (* ⊤ *) | 0x2205 (* ∅ *)
  | 0x2191 (* ↑ *) | 0x25CF (* ● *) | 0x25EF (* ◯ *) | 0x00A3 (* £ *) ->
      true
  | _ -> false

let is_letter u =
  (u >= 0x61 && u <= 0x7A) (* a-z *)
  || (u >= 0x41 && u <= 0x5A) (* A-Z *)
  || (u >= 0x80 && u <= 0x1FFF && not (is_latin_sym u))
  || u = 0x2113 (* ℓ *)

let is_id_start u = is_letter u || u = 0x5F (* _ *)

let is_id_char u =
  is_id_start u
  || (u >= 0x30 && u <= 0x39)
  || u = 0x27 (* ' *)
  || (u >= 0x2080 && u <= 0x2089) (* ₀..₉ *)

let is_ascii_sym = function
  | '!' | '#' | '$' | '%' | '&' | '*' | '+' | '-' | '/' | ':' | '<' | '='
  | '>' | '?' | '@' | '\\' | '^' | '|' | '~' ->
      true
  | _ -> false

let is_sym_char u =
  (u < 128 && is_ascii_sym (Char.unsafe_chr u))
  || is_latin_sym u
  || (u >= 0x2000 && not (is_letter u))

let is_keyword = function
  | "forall" | "fun" | "exists" | "let" | "in" | "match" | "with" | "end"
  | "if" | "then" | "else" | "as" | "return" | "fix" | "cofix" ->
      true
  | _ -> false

let is_punct_byte = function
  | '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' | '`' -> true
  | _ -> false

let decode_uchar (s : string) (i : int) : int * int =
  let d = String.get_utf_8_uchar s i in
  let len = Uchar.utf_decode_length d in
  let u = Uchar.to_int (Uchar.utf_decode_uchar d) in
  (u, len)

(* Scan a Rocq string body starting right after the opening '"', returning the
   index right after the closing '"'. Escaped "" stays intact. *)
let scan_string_end (s : string) (n : int) (start : int) : int =
  let rec loop i =
    if i >= n then raise (Lex_error start)
    else if s.[i] = '"' then
      if i + 1 < n && s.[i + 1] = '"' then loop (i + 2) else i + 1
    else loop (i + 1)
  in
  loop start

(* Scan nested (* ... *) comment starting right after "(*", skipping embedded
   strings just as Rocq does. Returns index right after closing "*)". *)
let scan_comment_end (s : string) (n : int) (start : int) : int =
  let rec loop i depth =
    if i >= n then raise (Lex_error start)
    else
      match s.[i] with
      | '"' -> loop (scan_string_end s n (i + 1)) depth
      | '(' when i + 1 < n && s.[i + 1] = '*' -> loop (i + 2) (depth + 1)
      | '*' when i + 1 < n && s.[i + 1] = ')' ->
          if depth = 1 then i + 2 else loop (i + 2) (depth - 1)
      | _ -> loop (i + 1) depth
  in
  loop start 1

(* Scan a qualified identifier starting at [start] (known to satisfy is_id_start). *)
let scan_ident (s : string) (n : int) (start : int) : int =
  let rec seg i =
    if i >= n then i
    else
      let u, step = decode_uchar s i in
      if is_id_char u then seg (i + step)
      else if s.[i] = '.' && i + 1 < n then
        let u2, step2 = decode_uchar s (i + 1) in
        if is_id_start u2 then seg (i + 1 + step2) else i
      else i
  in
  seg start

(* Scan a run of symbol characters, stopping before "|}" and (after the first
   character) before "?x" where x starts an identifier. *)
let scan_sym_run (s : string) (n : int) (start : int) : int =
  let rec more i =
    if i >= n then i
    else if s.[i] = '|' && i + 1 < n && s.[i + 1] = '}' then i
    else if s.[i] = '?' && i + 1 < n then
      let u2, _ = decode_uchar s (i + 1) in
      if is_id_start u2 then i
      else
        let u, step = decode_uchar s i in
        if is_sym_char u && not (is_single_sym u) then more (i + step) else i
    else
      let u, step = decode_uchar s i in
      if is_sym_char u && not (is_single_sym u) then more (i + step) else i
  in
  if start >= n then start
  else if s.[start] = '|' && start + 1 < n && s.[start + 1] = '}' then start
  else
    let u, step = decode_uchar s start in
    if is_sym_char u && not (is_single_sym u) then more (start + step)
    else start

let lex (s : string) : token array * comment list =
  let n = String.length s in
  let toks = ref [] in
  let cms = ref [] in
  let rec skip i =
    if i >= n then i
    else if is_white_byte s.[i] then skip (i + 1)
    else if s.[i] = '(' && i + 1 < n && s.[i + 1] = '*' then (
      let hi = scan_comment_end s n (i + 2) in
      cms := { cm_lo = i; cm_hi = hi; cm_text = String.sub s i (hi - i) } :: !cms;
      skip hi)
    else i
  in
  let emit kind lo hi = toks := { kind; lo; hi } :: !toks in
  let rec loop i =
    let i = skip i in
    if i >= n then ()
    else
      let c = s.[i] in
      if c = '"' then (
        let hi = scan_string_end s n (i + 1) in
        emit (Str (String.sub s (i + 1) (hi - i - 2))) i hi;
        loop hi)
      else if c = '.' && i + 1 < n && s.[i + 1] = '.' then (
        emit (Sym "..") i (i + 2);
        loop (i + 2))
      else if c = '.' && (i + 1 = n || is_white_byte s.[i + 1]) then (
        emit Dot i (i + 1);
        loop (i + 1))
      else if c = '.' && i + 1 < n && s.[i + 1] = '(' then (
        emit (Sym ".(") i (i + 2);
        loop (i + 2))
      else if
        c = '.' && i + 2 < n && s.[i + 1] = '*'
        && (s.[i + 2] = '1' || s.[i + 2] = '2')
      then (
        emit (Sym (String.sub s i 3)) i (i + 3);
        loop (i + 3))
      else if
        c = '.' && i + 1 < n
        && (s.[i + 1] = '1' || s.[i + 1] = '2')
        && not (i + 2 < n && is_digit_byte s.[i + 2])
      then (
        emit (Sym (String.sub s i 2)) i (i + 2);
        loop (i + 2))
      else if
        c = '-' && i + 2 < n
        && (s.[i + 1] = 'd' || s.[i + 1] = 'n')
        && s.[i + 2] = '>'
      then (
        emit (Sym (String.sub s i 3)) i (i + 3);
        loop (i + 3))
      else if c = '{' && i + 1 < n && s.[i + 1] = '|' then (
        emit (P "{|") i (i + 2);
        loop (i + 2))
      else if c = '|' && i + 1 < n && s.[i + 1] = '}' then (
        emit (P "|}") i (i + 2);
        loop (i + 2))
      else if is_punct_byte c then (
        emit (P (String.make 1 c)) i (i + 1);
        loop (i + 1))
      else if c = '\'' then (
        emit (P "'") i (i + 1);
        loop (i + 1))
      else if is_digit_byte c then (
        let rec scan_num j =
          if j < n && (is_digit_byte s.[j] || s.[j] = '_') then scan_num (j + 1)
          else j
        in
        let hi = scan_num (i + 1) in
        emit (Num (String.sub s i (hi - i))) i hi;
        loop hi)
      else
        let u, step = decode_uchar s i in
        if u = 0x2039 (* ‹ *) then (
          (* Guillemet-quoted C-expression temporary: ‹buf+8› *)
          let rec scan_q j =
            if j >= n then raise (Lex_error i)
            else
              let uq, sq = decode_uchar s j in
              if uq = 0x203A (* › *) then
                if j = i + step then raise (Lex_error i) else j + sq
              else if
                uq = 0x2039 || uq = 0x22 || (uq < 128 && is_white_byte (Char.unsafe_chr uq))
              then raise (Lex_error i)
              else scan_q (j + sq)
          in
          let hi = scan_q (i + step) in
          emit (Id (String.sub s i (hi - i))) i hi;
          loop hi)
        else if is_single_sym u then (
          emit (Sym (String.sub s i step)) i (i + step);
          loop (i + step))
        else if is_id_start u then (
          let hi = scan_ident s n i in
          let text = String.sub s i (hi - i) in
          emit (if is_keyword text then Kw text else Id text) i hi;
          loop hi)
        else
          let hi = scan_sym_run s n i in
          if hi > i then (
            emit (Sym (String.sub s i (hi - i))) i hi;
            loop hi)
          else if c = '.' then (
            emit (Sym ".") i (i + 1);
            loop (i + 1))
          else raise (Lex_error i)
  in
  loop 0;
  (Array.of_list (List.rev !toks), List.rev !cms)

(* Split flat token array into sentence chunks between Dot tokens.
   Each chunk is (slice_start, slice_len, end_byte_offset_incl_dot). *)
type chunk = { ch_toks : token array; ch_hi : int }

let chunks (toks : token array) : chunk list =
  let n = Array.length toks in
  let acc = ref [] in
  let rec go start i =
    if start >= n then ()
    else if i >= n then (
      let len = n - start in
      if len > 0 then
        acc := { ch_toks = Array.sub toks start len; ch_hi = toks.(n - 1).hi } :: !acc)
    else if toks.(i).kind = Dot then (
      let len = i - start in
      acc := { ch_toks = Array.sub toks start len; ch_hi = toks.(i).hi } :: !acc;
      go (i + 1) (i + 1))
    else go start (i + 1)
  in
  go 0 0;
  List.rev !acc
