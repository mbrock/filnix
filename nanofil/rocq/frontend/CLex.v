(** The C lexer turns preprocessed C source text into located tokens, handling
    line markers, comments, numeric constants, narrow and wide string or
    character literals, punctuators, GNU keywords, and `#pragma weak` /
    `#pragma pack`. This module is a pure, tail-recursive Gallina translation
    of nanofil/src/c_lex.pl.

    Every loop over input characters and token streams is tail-recursive with
    an explicit accumulator, so extracted code scans multi-megabyte
    preprocessed translation units in constant stack space. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Frontend Require Import CAst CAttrs.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Characters and strings

    Extracting [code], [byte], and [string_of_rev] to native OCaml character
    and byte-buffer operations avoids unpacking characters bit by bit, matching
    IrText.v and Prims.v. *)

Definition code (c : ascii) : nat := nat_of_ascii c.
Definition byte (n : nat) : ascii := ascii_of_nat n.
Definition string_of_rev (cs : list ascii) : string :=
  string_of_list_ascii (rev_append cs []).

Definition in_range (lo hi c : ascii) : bool :=
  let k := code c in (code lo <=? k)%nat && (k <=? code hi)%nat.

Definition is_blank (c : ascii) : bool :=
  Ascii.eqb c " "%char || Ascii.eqb c "009"%char || Ascii.eqb c "013"%char ||
  Ascii.eqb c "012"%char || Ascii.eqb c "011"%char.

Definition is_nl (c : ascii) : bool := Ascii.eqb c "010"%char.

Definition is_digit (c : ascii) : bool := in_range "0"%char "9"%char c.

Definition is_oct_digit (c : ascii) : bool := in_range "0"%char "7"%char c.

Definition is_bin_digit (c : ascii) : bool :=
  Ascii.eqb c "0"%char || Ascii.eqb c "1"%char.

Definition is_letter (c : ascii) : bool :=
  in_range "a"%char "z"%char c || in_range "A"%char "Z"%char c.

Definition is_ident_start (c : ascii) : bool :=
  is_letter c || Ascii.eqb c "_"%char || Ascii.eqb c "$"%char.

Definition is_ident_char (c : ascii) : bool :=
  is_ident_start c || is_digit c.

Definition dec_digit_val (c : ascii) : Z :=
  Z.of_nat (code c - code "0"%char).

Definition hex_weight (c : ascii) : option Z :=
  if in_range "0"%char "9"%char c then Some (Z.of_nat (code c - code "0"%char))
  else if in_range "a"%char "f"%char c then Some (Z.of_nat (code c - code "a"%char) + 10)
  else if in_range "A"%char "F"%char c then Some (Z.of_nat (code c - code "A"%char) + 10)
  else None.

Definition loc_next_line (l : c_loc) : c_loc :=
  match l with
  | Loc f n => Loc f (n + 1)
  | LocEof => LocEof
  end.

Definition loc_err {A : Type} (l : c_loc) (msg : string) : c_result A :=
  CErr (loc_to_string l ++ ": " ++ msg)%string.

(** ## Keywords and punctuators

    GNU alternate spellings such as `__restrict__` and `__asm__` fold onto
    their canonical keyword names during lexing, matching c_lex.pl. *)

Fixpoint assoc_str {A : Type} (s : string) (xs : list (string * A)) : option A :=
  match xs with
  | [] => None
  | (k, v) :: rest => if String.eqb s k then Some v else assoc_str s rest
  end.

Definition keyword_table : list (string * string) :=
  [ ("auto", "auto"); ("break", "break"); ("case", "case"); ("char", "char");
    ("const", "const"); ("__const", "const"); ("__const__", "const");
    ("continue", "continue"); ("default", "default"); ("do", "do");
    ("double", "double"); ("else", "else"); ("enum", "enum");
    ("extern", "extern"); ("float", "float"); ("for", "for");
    ("goto", "goto"); ("if", "if"); ("inline", "inline");
    ("__inline", "inline"); ("__inline__", "inline"); ("int", "int");
    ("long", "long"); ("register", "register"); ("restrict", "restrict");
    ("__restrict", "restrict"); ("__restrict__", "restrict");
    ("return", "return"); ("short", "short"); ("signed", "signed");
    ("__signed", "signed"); ("__signed__", "signed"); ("sizeof", "sizeof");
    ("static", "static"); ("struct", "struct"); ("switch", "switch");
    ("typedef", "typedef"); ("union", "union"); ("unsigned", "unsigned");
    ("void", "void"); ("volatile", "volatile"); ("__volatile", "volatile");
    ("__volatile__", "volatile"); ("while", "while");
    ("_Alignas", "alignas"); ("_Alignof", "alignof");
    ("__alignof", "alignof"); ("__alignof__", "alignof");
    ("_Atomic", "atomic"); ("_Bool", "bool"); ("_Complex", "complex");
    ("_Generic", "generic"); ("_Imaginary", "imaginary");
    ("__real__", "real"); ("__real", "real");
    ("__imag__", "imag"); ("__imag", "imag");
    ("_Noreturn", "noreturn"); ("_Static_assert", "static_assert");
    ("_Thread_local", "thread_local"); ("__thread", "thread_local");
    ("asm", "asm"); ("__asm", "asm"); ("__asm__", "asm");
    ("__attribute", "attribute"); ("__attribute__", "attribute");
    ("__extension__", "extension"); ("__auto_type", "auto_type");
    ("typeof", "typeof"); ("__typeof", "typeof"); ("__typeof__", "typeof");
    ("__int128", "int128"); ("_Float16", "float16"); ("__bf16", "bf16") ]%string.

Definition lookup_keyword (s : string) : option string :=
  assoc_str s keyword_table.

Definition c23_keyword_names : list string :=
  [ "bool"; "true"; "false"; "nullptr"; "static_assert";
    "alignas"; "alignof"; "thread_local" ]%string.

Definition lookup_c23_keyword (s : string) : option string :=
  if str_in s c23_keyword_names then Some s else None.

(** Promote C23 keyword identifiers in an already-lexed token stream. *)
Definition c23_tokens (ts : list token) : list token :=
  let fix go (xs acc : list token) : list token :=
    match xs with
    | [] => rev_append acc []
    | mkTok (TId s) loc :: rest =>
        let tk :=
          match lookup_c23_keyword s with
          | Some k => mkTok (TKw k) loc
          | None => mkTok (TId s) loc
          end in
        go rest (tk :: acc)
    | t :: rest => go rest (t :: acc)
    end in
  go ts [].

(** Match a two-character C punctuator. *)
Definition match_punct2 (a b : ascii) : option string :=
  if Ascii.eqb b "="%char then
    if Ascii.eqb a "<"%char then Some "<="%string
    else if Ascii.eqb a ">"%char then Some ">="%string
    else if Ascii.eqb a "="%char then Some "=="%string
    else if Ascii.eqb a "!"%char then Some "!="%string
    else if Ascii.eqb a "*"%char then Some "*="%string
    else if Ascii.eqb a "/"%char then Some "/="%string
    else if Ascii.eqb a "%"%char then Some "%="%string
    else if Ascii.eqb a "+"%char then Some "+="%string
    else if Ascii.eqb a "-"%char then Some "-="%string
    else if Ascii.eqb a "&"%char then Some "&="%string
    else if Ascii.eqb a "^"%char then Some "^="%string
    else if Ascii.eqb a "|"%char then Some "|="%string
    else None
  else if Ascii.eqb a "-"%char && Ascii.eqb b ">"%char then Some "->"%string
  else if Ascii.eqb a "+"%char && Ascii.eqb b "+"%char then Some "++"%string
  else if Ascii.eqb a "-"%char && Ascii.eqb b "-"%char then Some "--"%string
  else if Ascii.eqb a "<"%char && Ascii.eqb b "<"%char then Some "<<"%string
  else if Ascii.eqb a ">"%char && Ascii.eqb b ">"%char then Some ">>"%string
  else if Ascii.eqb a "&"%char && Ascii.eqb b "&"%char then Some "&&"%string
  else if Ascii.eqb a "|"%char && Ascii.eqb b "|"%char then Some "||"%string
  else if Ascii.eqb a "#"%char && Ascii.eqb b "#"%char then Some "##"%string
  else None.

(** Match a single-character C punctuator, returning a pre-allocated string
    literal. *)
Definition single_punct_str (a : ascii) : option string :=
  if Ascii.eqb a ";"%char then Some ";"%string
  else if Ascii.eqb a "("%char then Some "("%string
  else if Ascii.eqb a ")"%char then Some ")"%string
  else if Ascii.eqb a ","%char then Some ","%string
  else if Ascii.eqb a "{"%char then Some "{"%string
  else if Ascii.eqb a "}"%char then Some "}"%string
  else if Ascii.eqb a "*"%char then Some "*"%string
  else if Ascii.eqb a "="%char then Some "="%string
  else if Ascii.eqb a "["%char then Some "["%string
  else if Ascii.eqb a "]"%char then Some "]"%string
  else if Ascii.eqb a "."%char then Some "."%string
  else if Ascii.eqb a "&"%char then Some "&"%string
  else if Ascii.eqb a "+"%char then Some "+"%string
  else if Ascii.eqb a "-"%char then Some "-"%string
  else if Ascii.eqb a ":"%char then Some ":"%string
  else if Ascii.eqb a "<"%char then Some "<"%string
  else if Ascii.eqb a ">"%char then Some ">"%string
  else if Ascii.eqb a "!"%char then Some "!"%string
  else if Ascii.eqb a "/"%char then Some "/"%string
  else if Ascii.eqb a "?"%char then Some "?"%string
  else if Ascii.eqb a "|"%char then Some "|"%string
  else if Ascii.eqb a "~"%char then Some "~"%string
  else if Ascii.eqb a "%"%char then Some "%"%string
  else if Ascii.eqb a "^"%char then Some "^"%string
  else if Ascii.eqb a "#"%char then Some "#"%string
  else None.

(** Match the longest C punctuator at the head of the character list. *)
Definition match_punct (cs : list ascii) : option (string * list ascii) :=
  match cs with
  | a :: b :: c :: rest =>
      if Ascii.eqb a "."%char && Ascii.eqb b "."%char && Ascii.eqb c "."%char then
        Some ("..."%string, rest)
      else if Ascii.eqb a "<"%char && Ascii.eqb b "<"%char && Ascii.eqb c "="%char then
        Some ("<<="%string, rest)
      else if Ascii.eqb a ">"%char && Ascii.eqb b ">"%char && Ascii.eqb c "="%char then
        Some (">>="%string, rest)
      else
        match match_punct2 a b with
        | Some s => Some (s, c :: rest)
        | None =>
            match single_punct_str a with
            | Some s => Some (s, b :: c :: rest)
            | None => None
            end
        end
  | a :: b :: rest =>
      match match_punct2 a b with
      | Some s => Some (s, rest)
      | None =>
          match single_punct_str a with
          | Some s => Some (s, b :: rest)
          | None => None
          end
      end
  | a :: rest =>
      match single_punct_str a with
      | Some s => Some (s, rest)
      | None => None
      end
  | [] => None
  end.

(** ## Numeric literals

    Preprocessing numbers consume identifier characters, dots, and exponent
    signs before classification into integer, floating, or GNU imaginary
    floating constants. *)

Fixpoint scan_pp_number (cs acc : list ascii) : list ascii * list ascii :=
  match cs with
  | [] => (rev_append acc [], [])
  | e :: cs1 =>
      match cs1 with
      | s :: rest =>
          if (Ascii.eqb e "e"%char || Ascii.eqb e "E"%char ||
              Ascii.eqb e "p"%char || Ascii.eqb e "P"%char) &&
             (Ascii.eqb s "+"%char || Ascii.eqb s "-"%char)
          then scan_pp_number rest (s :: e :: acc)
          else if is_ident_char e || Ascii.eqb e "."%char
          then scan_pp_number cs1 (e :: acc)
          else (rev_append acc [], cs)
      | [] =>
          if is_ident_char e || Ascii.eqb e "."%char
          then (rev_append (e :: acc) [], [])
          else (rev_append acc [], cs)
      end
  end.

Fixpoint take_hex_digits (cs : list ascii) (v : Z) (cnt : nat)
  : Z * nat * list ascii :=
  match cs with
  | c :: rest =>
      match hex_weight c with
      | Some w => take_hex_digits rest (v * 16 + w) (S cnt)
      | None => (v, cnt, cs)
      end
  | [] => (v, cnt, [])
  end.

Fixpoint take_bin_digits (cs : list ascii) (v : Z) (cnt : nat)
  : Z * nat * list ascii :=
  match cs with
  | c :: rest =>
      if is_bin_digit c then
        take_bin_digits rest (v * 2 + dec_digit_val c) (S cnt)
      else (v, cnt, cs)
  | [] => (v, cnt, [])
  end.

Fixpoint take_oct_digits (cs : list ascii) (v : Z) : Z * list ascii :=
  match cs with
  | c :: rest =>
      if is_oct_digit c then
        take_oct_digits rest (v * 8 + dec_digit_val c)
      else (v, cs)
  | [] => (v, [])
  end.

Fixpoint take_dec_digits (cs : list ascii) (v : Z) (cnt : nat)
  : Z * nat * list ascii :=
  match cs with
  | c :: rest =>
      if is_digit c then
        take_dec_digits rest (v * 10 + dec_digit_val c) (S cnt)
      else (v, cnt, cs)
  | [] => (v, cnt, [])
  end.

Definition lower_ul (c : ascii) : ascii :=
  if Ascii.eqb c "U"%char then "u"%char
  else if Ascii.eqb c "L"%char then "l"%char
  else if Ascii.eqb c "X"%char then "x"%char
  else c.

Definition parse_int_suffix (cs : list ascii) : option int_suffix :=
  match map lower_ul cs with
  | [] => Some SufNone
  | [a] =>
      if Ascii.eqb a "u"%char then Some SufU
      else if Ascii.eqb a "l"%char then Some SufL
      else None
  | [a; b] =>
      if Ascii.eqb a "l"%char && Ascii.eqb b "l"%char then Some SufLL
      else if (Ascii.eqb a "u"%char && Ascii.eqb b "l"%char) ||
              (Ascii.eqb a "l"%char && Ascii.eqb b "u"%char) then Some SufUL
      else None
  | [a; b; c] =>
      if (Ascii.eqb a "u"%char && Ascii.eqb b "l"%char && Ascii.eqb c "l"%char) ||
         (Ascii.eqb a "l"%char && Ascii.eqb b "l"%char && Ascii.eqb c "u"%char)
      then Some SufULL
      else None
  | _ => None
  end.

Definition parse_int_literal (cs : list ascii) : option (Z * int_suffix * int_radix) :=
  let parse_dec (_ : unit) :=
    let '(v, cnt, suf) := take_dec_digits cs 0 O in
    if Nat.eqb cnt 0 then None
    else
      match parse_int_suffix suf with
      | Some s => Some (v, s, RadDec)
      | None => None
      end in
  match cs with
  | c0 :: rest =>
      if Ascii.eqb c0 "0"%char then
        match rest with
        | c1 :: rest2 =>
            if Ascii.eqb c1 "x"%char || Ascii.eqb c1 "X"%char then
              let '(v, cnt, suf) := take_hex_digits rest2 0 O in
              if Nat.eqb cnt 0 then None
              else
                match parse_int_suffix suf with
                | Some s => Some (v, s, RadOther)
                | None => None
                end
            else if Ascii.eqb c1 "b"%char || Ascii.eqb c1 "B"%char then
              let '(v, cnt, suf) := take_bin_digits rest2 0 O in
              if Nat.eqb cnt 0 then None
              else
                match parse_int_suffix suf with
                | Some s => Some (v, s, RadOther)
                | None => None
                end
            else
              let '(v, suf) := take_oct_digits rest 0 in
              match parse_int_suffix suf with
              | Some s => Some (v, s, RadOther)
              | None => None
              end
        | [] => Some (0, SufNone, RadOther)
        end
      else parse_dec tt
  | [] => None
  end.

Definition is_float_char (c : ascii) : bool :=
  is_digit c || in_range "a"%char "f"%char c || in_range "A"%char "F"%char c ||
  Ascii.eqb c "."%char || Ascii.eqb c "+"%char || Ascii.eqb c "-"%char ||
  Ascii.eqb c "l"%char || Ascii.eqb c "L"%char ||
  Ascii.eqb c "p"%char || Ascii.eqb c "P"%char ||
  Ascii.eqb c "x"%char || Ascii.eqb c "X"%char.

Definition is_imag_char (c : ascii) : bool :=
  Ascii.eqb c "i"%char || Ascii.eqb c "I"%char ||
  Ascii.eqb c "j"%char || Ascii.eqb c "J"%char.

Definition is_fl_char (c : ascii) : bool :=
  Ascii.eqb c "f"%char || Ascii.eqb c "F"%char ||
  Ascii.eqb c "l"%char || Ascii.eqb c "L"%char.

Definition strip_imaginary (cs : list ascii) : option (list ascii) :=
  match rev_append cs [] with
  | i :: rbody =>
      if is_imag_char i then Some (rev_append rbody [])
      else if is_fl_char i then
        match rbody with
        | i2 :: rbody2 =>
            if is_imag_char i2 then Some (rev_append (i :: rbody2) [])
            else None
        | [] => None
        end
      else None
  | [] => None
  end.

Definition string_of_chars (cs : list ascii) : string :=
  string_of_rev (rev_append cs []).

Definition classify_number (cs : list ascii) (l : c_loc) : c_result tok_kind :=
  match parse_int_literal cs with
  | Some (v, suf, rad) => COk (TInt v suf rad)
  | None =>
      match strip_imaginary cs with
      | Some cs1 =>
          match parse_int_literal cs1 with
          | None =>
              if forallb is_float_char cs1 then COk (TImag (string_of_chars cs1))
              else if forallb is_float_char cs then COk (TFloat (string_of_chars cs))
              else loc_err l ("bad number " ++ string_of_chars cs)%string
          | Some _ =>
              if forallb is_float_char cs then COk (TFloat (string_of_chars cs))
              else loc_err l ("bad number " ++ string_of_chars cs)%string
          end
      | None =>
          if forallb is_float_char cs then COk (TFloat (string_of_chars cs))
          else loc_err l ("bad number " ++ string_of_chars cs)%string
      end
  end.

(** ## UTF-8 encoding and decoding for character and string literals

    Narrow literals preserve raw bytes and encode `\u`/`\U` universal character
    names as UTF-8. Wide literals decode source UTF-8 sequences into code
    points while keeping invalid bytes verbatim. *)

Definition utf8_bytes (k : Z) : list Z :=
  if k <? 128 then [k]
  else if k <? 2048 then
    [Z.lor 192 (Z.shiftr k 6); Z.lor 128 (Z.land k 63)]
  else if k <? 65536 then
    [Z.lor 224 (Z.shiftr k 12);
     Z.lor 128 (Z.land (Z.shiftr k 6) 63);
     Z.lor 128 (Z.land k 63)]
  else
    [Z.lor 240 (Z.shiftr k 18);
     Z.lor 128 (Z.land (Z.shiftr k 12) 63);
     Z.lor 128 (Z.land (Z.shiftr k 6) 63);
     Z.lor 128 (Z.land k 63)].

Fixpoint utf8_cont (n : nat) (k : Z) (cs : list ascii) : option (Z * list ascii) :=
  match n with
  | O => Some (k, cs)
  | S n' =>
      match cs with
      | c :: rest =>
          let b := Z.of_nat (code c) in
          if Z.eqb (Z.land b 192) 128 then
            utf8_cont n' (Z.lor (Z.shiftl k 6) (Z.land b 63)) rest
          else None
      | [] => None
      end
  end.

Definition decode_utf8_char (cs : list ascii) : option (Z * list ascii) :=
  match cs with
  | c0 :: rest =>
      let b0 := Z.of_nat (code c0) in
      if (194 <=? b0) && (b0 <=? 244) then
        let '(n, k0) :=
          if b0 <? 224 then (1%nat, Z.land b0 31)
          else if b0 <? 240 then (2%nat, Z.land b0 15)
          else (3%nat, Z.land b0 7) in
        match utf8_cont n k0 rest with
        | Some (k, rem) =>
            if Nat.eqb (List.length (utf8_bytes k)) (S n) then Some (k, rem)
            else None
        | None => None
        end
      else None
  | [] => None
  end.

Definition simple_escape (c : ascii) : option Z :=
  if Ascii.eqb c "n"%char then Some 10
  else if Ascii.eqb c "t"%char then Some 9
  else if Ascii.eqb c "r"%char then Some 13
  else if Ascii.eqb c "a"%char then Some 7
  else if Ascii.eqb c "b"%char then Some 8
  else if Ascii.eqb c "f"%char then Some 12
  else if Ascii.eqb c "v"%char then Some 11
  else if Ascii.eqb c "\"%char then Some 92
  else if Ascii.eqb c "'"%char then Some 39
  else if Ascii.eqb c """"%char then Some 34
  else if Ascii.eqb c "?"%char then Some 63
  else if Ascii.eqb c "e"%char || Ascii.eqb c "E"%char then Some 27
  else None.

Fixpoint take_hex_exact (n : nat) (cs : list ascii) (v : Z)
  : option (Z * list ascii) :=
  match n with
  | O => Some (v, cs)
  | S n' =>
      match cs with
      | c :: rest =>
          match hex_weight c with
          | Some w => take_hex_exact n' rest (v * 16 + w)
          | None => None
          end
      | [] => None
      end
  end.

Fixpoint take_oct_upto (n : nat) (cs : list ascii) (v : Z) : Z * list ascii :=
  match n with
  | O => (v, cs)
  | S n' =>
      match cs with
      | c :: rest =>
          if is_oct_digit c then
            take_oct_upto n' rest (v * 8 + dec_digit_val c)
          else (v, cs)
      | [] => (v, [])
      end
  end.

Definition try_ucn (cs : list ascii) : option (Z * list ascii) :=
  match cs with
  | c :: rest =>
      if Ascii.eqb c "u"%char then take_hex_exact 4 rest 0
      else if Ascii.eqb c "U"%char then take_hex_exact 8 rest 0
      else None
  | [] => None
  end.

Definition scan_narrow_escape (cs : list ascii) (l : c_loc)
  : c_result (Z * list ascii) :=
  match cs with
  | [] => loc_err l "unterminated literal"%string
  | c :: rest =>
      match simple_escape c with
      | Some b => COk (b, rest)
      | None =>
          if Ascii.eqb c "x"%char then
            let '(v, cnt, rem) := take_hex_digits rest 0 O in
            if Nat.eqb cnt 0 then loc_err l "bad hex escape"%string
            else COk (Z.land v 255, rem)
          else if is_oct_digit c then
            let '(v, rem) := take_oct_upto 2 rest (dec_digit_val c) in
            COk (Z.land v 255, rem)
          else if is_nl c then
            loc_err l "unterminated literal"%string
          else
            COk (Z.of_nat (code c), rest)
      end
  end.

Fixpoint scan_narrow_lit (fuel : nat) (quote : ascii) (l : c_loc)
  (cs : list ascii) (acc : list Z) : c_result (list Z * list ascii) :=
  match fuel with
  | O => loc_err l "unterminated literal"%string
  | S f =>
      match cs with
      | [] => loc_err l "unterminated literal"%string
      | c :: rest =>
          if Ascii.eqb c quote then COk (rev_append acc [], rest)
          else if is_nl c then loc_err l "unterminated literal"%string
          else if Ascii.eqb c "\"%char then
            match try_ucn rest with
            | Some (k, rem) =>
                scan_narrow_lit f quote l rem (rev_append (utf8_bytes k) acc)
            | None =>
                match scan_narrow_escape rest l with
                | COk (b, rem) => scan_narrow_lit f quote l rem (b :: acc)
                | CErr m => CErr m
                end
            end
          else
            scan_narrow_lit f quote l rest (Z.of_nat (code c) :: acc)
      end
  end.

Definition scan_wide_escape (cs : list ascii) (l : c_loc)
  : c_result (Z * list ascii) :=
  match cs with
  | [] => loc_err l "unterminated literal"%string
  | c :: rest =>
      match simple_escape c with
      | Some b => COk (b, rest)
      | None =>
          if Ascii.eqb c "x"%char then
            let '(v, cnt, rem) := take_hex_digits rest 0 O in
            if Nat.eqb cnt 0 then loc_err l "bad hex escape"%string
            else COk (v, rem)
          else if Ascii.eqb c "u"%char then
            match take_hex_exact 4 rest 0 with
            | Some (v, rem) => COk (v, rem)
            | None => loc_err l "bad universal character name"%string
            end
          else if Ascii.eqb c "U"%char then
            match take_hex_exact 8 rest 0 with
            | Some (v, rem) => COk (v, rem)
            | None => loc_err l "bad universal character name"%string
            end
          else if is_oct_digit c then
            let '(v, rem) := take_oct_upto 2 rest (dec_digit_val c) in
            COk (v, rem)
          else
            match decode_utf8_char cs with
            | Some (v, rem) =>
                if Z.eqb v 10 then loc_err l "unterminated literal"%string
                else COk (v, rem)
            | None =>
                if is_nl c then loc_err l "unterminated literal"%string
                else COk (Z.of_nat (code c), rest)
            end
      end
  end.

Fixpoint scan_wide_lit (fuel : nat) (quote : ascii) (l : c_loc)
  (cs : list ascii) (acc : list Z) : c_result (list Z * list ascii) :=
  match fuel with
  | O => loc_err l "unterminated literal"%string
  | S f =>
      match cs with
      | [] => loc_err l "unterminated literal"%string
      | c :: rest =>
          if Ascii.eqb c quote then COk (rev_append acc [], rest)
          else if is_nl c then loc_err l "unterminated literal"%string
          else if Ascii.eqb c "\"%char then
            match scan_wide_escape rest l with
            | COk (v, rem) => scan_wide_lit f quote l rem (v :: acc)
            | CErr m => CErr m
            end
          else
            match decode_utf8_char cs with
            | Some (k, rem) => scan_wide_lit f quote l rem (k :: acc)
            | None => scan_wide_lit f quote l rest (Z.of_nat (code c) :: acc)
            end
      end
  end.

Definition wide_prefix (c : ascii) : option wide_type :=
  if Ascii.eqb c "L"%char then Some WInt
  else if Ascii.eqb c "u"%char then Some WUShort
  else if Ascii.eqb c "U"%char then Some WUInt
  else None.

Definition wide_max (wt : wide_type) : Z :=
  match wt with
  | WInt => 2147483647
  | WUShort => 65535
  | WUInt => 4294967295
  end.

Definition wide_type_name (wt : wide_type) : string :=
  match wt with
  | WInt => "int"%string
  | WUShort => "ushort"%string
  | WUInt => "uint"%string
  end.

Definition check_wide_fits (wt : wide_type) (vs : list Z) (l : c_loc)
  : c_result unit :=
  let mx := wide_max wt in
  let fix go (xs : list Z) : c_result unit :=
    match xs with
    | [] => COk tt
    | v :: rest =>
        if v >? mx then
          loc_err l ("wide literal element " ++ z_to_string v ++
                     " does not fit " ++ wide_type_name wt)%string
        else go rest
    end in
  go vs.

Definition char_fit_type (wt : wide_type) : wide_type :=
  match wt with
  | WInt => WInt
  | WUShort => WUShort
  | WUInt => WInt
  end.

Definition wide_char_value (vs : list Z) (wt : wide_type) (l : c_loc)
  : c_result Z :=
  match vs with
  | [v] =>
      match check_wide_fits (char_fit_type wt) [v] l with
      | COk tt => COk v
      | CErr m => CErr m
      end
  | _ => loc_err l "multi-character constant"%string
  end.

Definition narrow_char_value (bs : list Z) (l : c_loc) : c_result Z :=
  match bs with
  | [b] => COk (if b >=? 128 then b - 256 else b)
  | _ => loc_err l "multi-character constant"%string
  end.

(** ## Comments, line markers, and `#pragma` lines

    Line markers (`# N "file"` and `#line N "file"`) update the active
    location; `#pragma weak` and `#pragma pack` become tokens; other
    directives are skipped to the end of their line. *)

Fixpoint skip_spaces (cs : list ascii) : list ascii :=
  match cs with
  | c :: rest => if is_blank c then skip_spaces rest else cs
  | [] => []
  end.

Fixpoint skip_line_rest (cs : list ascii) : list ascii :=
  match cs with
  | [] => []
  | c :: rest => if is_nl c then cs else skip_line_rest rest
  end.

Fixpoint take_line_rest (cs acc : list ascii) : list ascii * list ascii :=
  match cs with
  | [] => (rev_append acc [], [])
  | c :: rest =>
      if is_nl c then (rev_append acc [], cs)
      else take_line_rest rest (c :: acc)
  end.

Fixpoint skip_block_comment (cs : list ascii) (l : c_loc)
  : c_result (c_loc * list ascii) :=
  match cs with
  | [] => loc_err l "unterminated comment"%string
  | c :: rest =>
      if Ascii.eqb c "*"%char then
        match rest with
        | d :: r2 =>
            if Ascii.eqb d "/"%char then COk (l, r2)
            else skip_block_comment rest l
        | [] => loc_err l "unterminated comment"%string
        end
      else
        let l1 := if is_nl c then loc_next_line l else l in
        skip_block_comment rest l1
  end.

Fixpoint take_ident_rest (cs acc : list ascii) : string * list ascii :=
  match cs with
  | c :: rest =>
      if is_ident_char c then take_ident_rest rest (c :: acc)
      else (string_of_rev acc, cs)
  | [] => (string_of_rev acc, [])
  end.

Definition match_word (w : list ascii) (cs : list ascii) : option (list ascii) :=
  let fix go (xs ys : list ascii) : option (list ascii) :=
    match xs, ys with
    | [], _ => Some ys
    | x :: xs', y :: ys' =>
        if Ascii.eqb x y then go xs' ys' else None
    | _, [] => None
    end in
  go w cs.

Fixpoint take_marker_file (cs acc : list ascii) : option (string * list ascii) :=
  match cs with
  | [] => None
  | c :: rest =>
      if Ascii.eqb c """"%char then Some (string_of_rev acc, rest)
      else take_marker_file rest (c :: acc)
  end.

Definition scan_directive (cs : list ascii) (l : c_loc) : c_loc * list ascii :=
  let cs1 := skip_spaces cs in
  let cs2 :=
    match match_word ["l"; "i"; "n"; "e"]%char cs1 with
    | Some r => skip_spaces r
    | None => cs1
    end in
  let '(n, cnt, cs3) := take_dec_digits cs2 0 O in
  if Nat.eqb cnt 0 then
    (l, skip_line_rest cs2)
  else
    let cs4 := skip_spaces cs3 in
    let n0 := n - 1 in
    let '(file, cs5) :=
      match cs4 with
      | q :: r =>
          if Ascii.eqb q """"%char then
            match take_marker_file r [] with
            | Some (f, rem) => (f, rem)
            | None => (match l with Loc f _ => f | LocEof => ""%string end, cs4)
            end
          else (match l with Loc f _ => f | LocEof => ""%string end, cs4)
      | [] => (match l with Loc f _ => f | LocEof => ""%string end, cs4)
      end in
    (Loc file n0, skip_line_rest cs5).

Definition try_pragma_weak (cs : list ascii)
  : option (string * option string * list ascii) :=
  let cs1 := skip_spaces cs in
  match match_word ["p"; "r"; "a"; "g"; "m"; "a"]%char cs1 with
  | Some (c :: r1) =>
      if is_blank c then
        let r2 := skip_spaces r1 in
        match match_word ["w"; "e"; "a"; "k"]%char r2 with
        | Some (d :: r3) =>
            if is_blank d then
              let r4 := skip_spaces r3 in
              match r4 with
              | ic :: r5 =>
                  if is_ident_start ic then
                    let '(name, r6) := take_ident_rest r5 [ic] in
                    let r7 := skip_spaces r6 in
                    let '(tgt, r8) :=
                      match r7 with
                      | eqc :: r7' =>
                          if Ascii.eqb eqc "="%char then
                            let r7'' := skip_spaces r7' in
                            match r7'' with
                            | tc :: r7''' =>
                                if is_ident_start tc then
                                  let '(tname, rem) := take_ident_rest r7''' [tc] in
                                  (Some (Some tname), skip_spaces rem)
                                else (None, r7'')
                            | [] => (None, [])
                            end
                          else (Some None, r7)
                      | [] => (Some None, r7)
                      end in
                    match tgt with
                    | Some target =>
                        match r8 with
                        | [] => Some (name, target, [])
                        | nl :: _ =>
                            if is_nl nl then Some (name, target, r8)
                            else None
                        end
                    | None => None
                    end
                  else None
              | [] => None
              end
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

Definition try_pragma_pack_prefix (cs : list ascii) : option (list ascii) :=
  let cs1 := skip_spaces cs in
  match match_word ["p"; "r"; "a"; "g"; "m"; "a"]%char cs1 with
  | Some (c :: r1) =>
      if is_blank c then
        let r2 := skip_spaces r1 in
        match_word ["p"; "a"; "c"; "k"]%char r2
      else None
  | _ => None
  end.

Inductive pack_arg_val : Type :=
| PAAtom (s : string)
| PAInt (n : Z).

Definition pack_arg_of_tok (t : token) : option pack_arg_val :=
  match tok_val t with
  | TId s => Some (PAAtom s)
  | TPunct s => Some (PAAtom s)
  | TInt n _ _ => Some (PAInt n)
  | _ => None
  end.

Definition is_pack_value (n : Z) : bool :=
  Z.eqb n 1 || Z.eqb n 2 || Z.eqb n 4 || Z.eqb n 8 || Z.eqb n 16.

Definition is_pack_label (s : string) : bool :=
  match String.get 0 s with
  | Some c => is_ident_start c
  | None => false
  end.

Definition parse_pack_inner (args : list pack_arg_val) : option pack_op :=
  match args with
  | [] => Some (PackSet None)
  | [PAAtom a] =>
      if String.eqb a "push"%string then Some (PackPush None None)
      else if String.eqb a "pop"%string then Some (PackPop None)
      else if String.eqb a "show"%string then Some PackShow
      else None
  | [PAInt n] =>
      if is_pack_value n then Some (PackSet (Some n)) else None
  | [PAAtom a; PAAtom c; PAInt n] =>
      if String.eqb a "push"%string && String.eqb c ","%string && is_pack_value n
      then Some (PackPush None (Some n))
      else None
  | [PAAtom a; PAAtom c; PAAtom l] =>
      if String.eqb c ","%string && is_pack_label l then
        if String.eqb a "push"%string then Some (PackPush (Some l) None)
        else if String.eqb a "pop"%string then Some (PackPop (Some l))
        else None
      else None
  | [PAAtom a; PAAtom c1; PAAtom l; PAAtom c2; PAInt n] =>
      if String.eqb a "push"%string && String.eqb c1 ","%string &&
         String.eqb c2 ","%string && is_pack_label l && is_pack_value n
      then Some (PackPush (Some l) (Some n))
      else None
  | _ => None
  end.

Fixpoint map_opt {A B : Type} (f : A -> option B) (xs : list A)
  : option (list B) :=
  match xs with
  | [] => Some []
  | x :: rest =>
      match f x, map_opt f rest with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Definition strip_parens_pack (args : list pack_arg_val)
  : option (list pack_arg_val) :=
  match args with
  | PAAtom lp :: rest =>
      if String.eqb lp "("%string then
        match rev_append rest [] with
        | PAAtom rp :: rinner =>
            if String.eqb rp ")"%string then Some (rev_append rinner [])
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

(** ## Main tail-recursive scanner

    Scanning one token never recurses unboundedly; [lex_raw] consumes the
    entire character stream into a reversed accumulator and reverses it once
    at the end of input. *)

Definition scan_one_token (fuel : nat) (cs : list ascii) (l : c_loc)
  : c_result (tok_kind * list ascii) :=
  let scan_default (c : ascii) (rest : list ascii) : c_result (tok_kind * list ascii) :=
    if is_ident_start c then
      let '(s, rem) := take_ident_rest rest [c] in
      let tk := match lookup_keyword s with Some k => TKw k | None => TId s end in
      COk (tk, rem)
    else if is_digit c then
      let '(num_cs, rem) := scan_pp_number rest [c] in
      match classify_number num_cs l with
      | COk tk => COk (tk, rem)
      | CErr m => CErr m
      end
    else
      match match_punct cs with
      | Some (ps, rem) => COk (TPunct ps, rem)
      | None => loc_err l "unexpected character"%string
      end in
  let scan_wide_with (wt : wide_type) (c : ascii) (rest : list ascii)
    : c_result (tok_kind * list ascii) :=
    match rest with
    | q :: r2 =>
        if Ascii.eqb q "'"%char then
          match scan_wide_lit fuel "'"%char l r2 [] with
          | COk (vs, rem) =>
              match wide_char_value vs wt l with
              | COk v => COk (TChr v, rem)
              | CErr m => CErr m
              end
          | CErr m => CErr m
          end
        else if Ascii.eqb q """"%char then
          match scan_wide_lit fuel """"%char l r2 [] with
          | COk (vs, rem) =>
              match check_wide_fits wt vs l with
              | COk tt => COk (TWStr wt vs, rem)
              | CErr m => CErr m
              end
          | CErr m => CErr m
          end
        else scan_default c rest
    | [] => scan_default c rest
    end in
  match cs with
  | [] => loc_err l "unexpected end of input"%string
  | c :: rest =>
      if Ascii.eqb c "'"%char then
        match rest with
        | q :: _ =>
            if Ascii.eqb q "'"%char then loc_err l "empty character constant"%string
            else
              match scan_narrow_lit fuel "'"%char l rest [] with
              | COk (bs, rem) =>
                  match narrow_char_value bs l with
                  | COk v => COk (TChr v, rem)
                  | CErr m => CErr m
                  end
              | CErr m => CErr m
              end
        | [] => loc_err l "unterminated literal"%string
        end
      else if Ascii.eqb c """"%char then
        match scan_narrow_lit fuel """"%char l rest [] with
        | COk (bs, rem) => COk (TStr bs, rem)
        | CErr m => CErr m
        end
      else if Ascii.eqb c "u"%char then
        match rest with
        | d :: q :: r2 =>
            if Ascii.eqb d "8"%char && Ascii.eqb q """"%char then
              match scan_narrow_lit fuel """"%char l r2 [] with
              | COk (bs, rem) => COk (TStr bs, rem)
              | CErr m => CErr m
              end
            else scan_wide_with WUShort c rest
        | _ => scan_wide_with WUShort c rest
        end
      else if Ascii.eqb c "L"%char then
        scan_wide_with WInt c rest
      else if Ascii.eqb c "U"%char then
        scan_wide_with WUInt c rest
      else if Ascii.eqb c "."%char then
        match rest with
        | d :: r2 =>
            if is_digit d then
              let '(num_cs, rem) := scan_pp_number r2 [d; c] in
              match classify_number num_cs l with
              | COk tk => COk (tk, rem)
              | CErr m => CErr m
              end
            else scan_default c rest
        | [] => scan_default c rest
        end
      else scan_default c rest
  end.

Fixpoint lex_loop (fuel : nat) (cs : list ascii) (l : c_loc) (bol : bool)
  (acc : list token) : c_result (list token) :=
  match fuel with
  | O => loc_err l "lexer fuel exhausted"%string
  | S f =>
      match cs with
      | [] => COk (rev_append acc [])
      | c :: rest =>
          if is_nl c then
            lex_loop f rest (loc_next_line l) true acc
          else if bol && Ascii.eqb c "#"%char then
            match try_pragma_weak rest with
            | Some (name, target, rem) =>
                lex_loop f rem l false (mkTok (TPragmaWeak name target) l :: acc)
            | None =>
                match try_pragma_pack_prefix rest with
                | Some after_pack =>
                    let '(line_cs, rem) := take_line_rest after_pack [] in
                    match lex_loop f line_cs l false [] with
                    | COk arg_toks =>
                        match map_opt pack_arg_of_tok arg_toks with
                        | Some args =>
                            match strip_parens_pack args with
                            | Some inner =>
                                match parse_pack_inner inner with
                                | Some op =>
                                    lex_loop f rem l false (mkTok (TPragmaPack op) l :: acc)
                                | None =>
                                    loc_err l "this #pragma pack is not supported"%string
                                end
                            | None =>
                                loc_err l "this #pragma pack is not supported"%string
                            end
                        | None =>
                            loc_err l "this #pragma pack is not supported"%string
                        end
                    | CErr _ =>
                        loc_err l "this #pragma pack is not supported"%string
                    end
                | None =>
                    let '(l1, rem) := scan_directive rest l in
                    lex_loop f rem l1 true acc
                end
            end
          else if is_blank c then
            lex_loop f rest l bol acc
          else if Ascii.eqb c "/"%char then
            match rest with
            | d :: r2 =>
                if Ascii.eqb d "*"%char then
                  match skip_block_comment r2 l with
                  | COk (l1, rem) => lex_loop f rem l1 bol acc
                  | CErr m => CErr m
                  end
                else if Ascii.eqb d "/"%char then
                  lex_loop f (skip_line_rest r2) l false acc
                else
                  match scan_one_token (S f) cs l with
                  | COk (tk, rem) => lex_loop f rem l false (mkTok tk l :: acc)
                  | CErr m => CErr m
                  end
            | [] =>
                match scan_one_token (S f) cs l with
                | COk (tk, rem) => lex_loop f rem l false (mkTok tk l :: acc)
                | CErr m => CErr m
                end
            end
          else
            match scan_one_token (S f) cs l with
            | COk (tk, rem) => lex_loop f rem l false (mkTok tk l :: acc)
            | CErr m => CErr m
            end
      end
  end.

(** ## Post-lex `#pragma pack` and `#pragma weak` pass

    Mirroring c_lex.pl's [pack_tokens/2], `#pragma pack` injects
    `__attribute__((__nanofil_pack__(N)))` after `struct`/`union` keywords and
    block-scoped `#pragma weak` directives hoist to file scope at the end of
    the stream. When neither pragma appears, the token list is returned
    unchanged without copying. *)

Definition has_pragma_pack (ts : list token) : bool :=
  existsb (fun t => match tok_val t with TPragmaPack _ => true | _ => false end) ts.

Definition has_pragma_weak (ts : list token) : bool :=
  existsb (fun t => match tok_val t with TPragmaWeak _ _ => true | _ => false end) ts.

Definition pack_stack_step (op : pack_op)
  (cur : option Z) (saved : list (option string * option Z))
  : option Z * list (option string * option Z) :=
  match op with
  | PackSet n => (n, saved)
  | PackPush lbl None => (cur, (lbl, cur) :: saved)
  | PackPush lbl (Some n) => (Some n, (lbl, cur) :: saved)
  | PackPop None =>
      match saved with
      | (_, v) :: s' => (v, s')
      | [] => (None, [])
      end
  | PackPop (Some lbl) =>
      let fix find_lbl (xs : list (option string * option Z))
        : option (option Z * list (option string * option Z)) :=
        match xs with
        | [] => None
        | (Some l', v) :: rest =>
            if String.eqb l' lbl then Some (v, rest) else find_lbl rest
        | _ :: rest => find_lbl rest
        end in
      match find_lbl saved with
      | Some res => res
      | None => (cur, saved)
      end
  | PackShow => (cur, saved)
  end.

Definition nanofil_pack_attr_rev (n : Z) (l : c_loc) : list token :=
  [ mkTok (TPunct ")"%string) l;
    mkTok (TPunct ")"%string) l;
    mkTok (TPunct ")"%string) l;
    mkTok (TInt n SufNone RadDec) l;
    mkTok (TPunct "("%string) l;
    mkTok (TId "__nanofil_pack__"%string) l;
    mkTok (TPunct "("%string) l;
    mkTok (TPunct "("%string) l;
    mkTok (TKw "attribute"%string) l ].

Fixpoint apply_pack_walk (ts : list token)
  (cur : option Z) (saved : list (option string * option Z))
  (acc : list token) : list token :=
  match ts with
  | [] => rev_append acc []
  | mkTok (TPragmaPack op) _ :: rest =>
      let '(cur1, saved1) := pack_stack_step op cur saved in
      apply_pack_walk rest cur1 saved1 acc
  | (mkTok (TKw k) l as t) :: rest =>
      match cur with
      | Some n =>
          if String.eqb k "struct"%string || String.eqb k "union"%string then
            apply_pack_walk rest cur saved (app (nanofil_pack_attr_rev n l) (t :: acc))
          else
            apply_pack_walk rest cur saved (t :: acc)
      | None =>
          apply_pack_walk rest cur saved (t :: acc)
      end
  | t :: rest =>
      apply_pack_walk rest cur saved (t :: acc)
  end.

Fixpoint hoist_weak_walk (ts : list token) (depth : Z)
  (acc hoisted : list token) : list token :=
  match ts with
  | [] => rev_append acc (rev_append hoisted [])
  | (mkTok (TPragmaWeak _ _) _ as t) :: rest =>
      if depth >? 0 then hoist_weak_walk rest depth acc (t :: hoisted)
      else hoist_weak_walk rest depth (t :: acc) hoisted
  | (mkTok (TPunct p) _ as t) :: rest =>
      let d1 :=
        if String.eqb p "{"%string then depth + 1
        else if String.eqb p "}"%string then depth - 1
        else depth in
      hoist_weak_walk rest d1 (t :: acc) hoisted
  | t :: rest =>
      hoist_weak_walk rest depth (t :: acc) hoisted
  end.

Definition pack_tokens (ts0 : list token) : list token :=
  let ts1 :=
    if has_pragma_pack ts0 then apply_pack_walk ts0 None [] [] else ts0 in
  if has_pragma_weak ts1 then hoist_weak_walk ts1 0 [] [] else ts1.

(** Lex preprocessed C source characters starting at line 1 of [file]. *)
Definition lex_chars (file : string) (cs : list ascii) : c_result (list token) :=
  let fuel := S (4 * List.length cs + Z.to_nat 32) in
  match lex_loop fuel cs (Loc file 1) true [] with
  | COk ts => COk (pack_tokens ts)
  | CErr m => CErr m
  end.
