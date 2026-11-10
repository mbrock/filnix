(** A reader of IR text (src/ir_text.pl): a module written as Prolog
    clauses, one `func/5`, `data/4`, `alias/3` or `context/2` term per
    item, which the Prolog compiler reads with `read_term/3`. This
    reader gives the same term as `read_ir_file/3` or gives nothing:
    it never reads a text differently from SWI-Prolog.

    It reads what the printer of ir_text.pl writes and a little more:
    `%` and block comments, names, quoted atoms and double-quoted
    strings with their escapes, symbol atoms, decimal integers,
    compounds, proper lists, and one operator, an infix `-` between
    two terms (a phi's edges are written `start-const(0)`). It gives
    nothing for the rest of Prolog's syntax: variables, every other
    use of an operator, parentheses around a term, a bar in a list,
    floats, the other number forms, back-quoted strings, and any byte
    outside ASCII that is not inside quotes.

    A term becomes a [term] as the backend's driver reads the terms
    Prolog prints: `[]` is [TList []], the quoted atom `'[]'` is
    [TAtom "[]"], an atom's name is its UTF-8 bytes, and a
    double-quoted string is the list of its characters, each an atom
    of one character.

    The text is the list of the file's bytes. Every loop over the
    text, the clauses, the arguments of a compound and the elements
    of a list is a tail call, so the extracted reader needs no more
    stack for 200,000 items than for one; the terms being read are
    kept in a list of frames, not in the calls. *)

From Stdlib Require Import String ZArith List Bool Ascii Arith.
From Nanofil Require Import Term.
Import ListNotations.

(** * Characters

    The three definitions below are the ones to give an OCaml
    definition of when extracting: taking a character apart into its
    eight bits is slow there. *)

(** The code of the character [c], 0 to 255. *)
Definition code (c : ascii) : nat := nat_of_ascii c.

(** The character whose code is [n], for an n below 256. *)
Definition byte (n : nat) : ascii := ascii_of_nat n.

(** The string of the characters [cs], which are given last first, as
    a loop collects them. *)
Definition string_of_rev (cs : list ascii) : string := string_of_list_ascii (rev_append cs []).

(** The codes of the characters the reader names. *)
Definition c_tab : nat := 9.
Definition c_nl : nat := 10.
Definition c_cr : nat := 13.
Definition c_space : nat := 32.
Definition c_bang : nat := 33.
Definition c_dquote : nat := 34.
Definition c_percent : nat := 37.
Definition c_squote : nat := 39.
Definition c_lparen : nat := 40.
Definition c_rparen : nat := 41.
Definition c_star : nat := 42.
Definition c_comma : nat := 44.
Definition c_minus : nat := 45.
Definition c_dot : nat := 46.
Definition c_slash : nat := 47.
Definition c_0 : nat := 48.
Definition c_9 : nat := 57.
Definition c_semicolon : nat := 59.
Definition c_upper_a : nat := 65.
Definition c_upper_z : nat := 90.
Definition c_lbracket : nat := 91.
Definition c_backslash : nat := 92.
Definition c_rbracket : nat := 93.
Definition c_underscore : nat := 95.
Definition c_a : nat := 97.
Definition c_x : nat := 120.
Definition c_z : nat := 122.
Definition c_lbrace : nat := 123.
Definition c_rbrace : nat := 125.
Definition c_tilde : nat := 126.
Definition c_7 : nat := 55.
Definition c_upper_f : nat := 70.
Definition c_f : nat := 102.

(** Numbers the reader counts with: the two bases of a numeric
    escape, one more than the most digits of one, what a letter's
    code is above its value as a digit, and the first bytes and the
    continuation bytes of UTF-8. Each is a definition of its own
    because the extracted code builds a number again each time it
    meets one written inside a function. *)
Definition eight : nat := 8.
Definition sixteen : nat := 16.
Definition nine : nat := 9.
Definition upper_digit : nat := 55.
Definition lower_digit : nat := 87.
Definition b128 : nat := 128.
Definition b143 : nat := 143.
Definition b144 : nat := 144.
Definition b159 : nat := 159.
Definition b160 : nat := 160.
Definition b191 : nat := 191.
Definition b194 : nat := 194.
Definition b223 : nat := 223.
Definition b224 : nat := 224.
Definition b225 : nat := 225.
Definition b237 : nat := 237.
Definition b239 : nat := 239.
Definition b240 : nat := 240.
Definition b241 : nat := 241.
Definition b243 : nat := 243.
Definition b244 : nat := 244.

(** Whether [n] is from [lo] to [hi], both included. *)
Definition between (lo hi n : nat) : bool := (lo <=? n) && (n <=? hi).

(** Whether the code [n] is layout: a space, a newline, a tab or a
    carriage return. *)
Definition is_layout (n : nat) : bool :=
  (n =? c_space) || (n =? c_nl) || (n =? c_tab) || (n =? c_cr).

(** Whether the code [n] is a lowercase letter, which starts a name. *)
Definition is_lower (n : nat) : bool := between c_a c_z n.

(** Whether the code [n] is a decimal digit. *)
Definition is_digit (n : nat) : bool := between c_0 c_9 n.

(** Whether the code [n] may follow the first letter of a name: a
    letter, a digit or an underscore. *)
Definition is_alnum (n : nat) : bool :=
  is_lower n || between c_upper_a c_upper_z n || is_digit n || (n =? c_underscore).

(** The codes of Prolog's symbol characters, `#$&*+-/:<=>?@\^~`, but
    for the full stop, which the reader takes only as a clause's
    end. *)
Definition symbol_codes : list nat :=
  [35; 36; 38; 42; 43; 45; 47; 58; 60; 61; 62; 63; 64; 92; 94; 126].

(** Whether the code [n] is a symbol character other than the full
    stop. A run of them is one atom, as `+` or `=<`. *)
Definition is_symbol (n : nat) : bool := existsb (Nat.eqb n) symbol_codes.

(** Whether the code [n] may stand as itself in a comment or between
    quotes: a printing ASCII character. *)
Definition is_printing (n : nat) : bool := between c_space c_tilde n.

(** Whether the text [cs] starts with the character of code [n]. *)
Definition starts (n : nat) (cs : list ascii) : bool :=
  match cs with
  | [] => false
  | c :: _ => code c =? n
  end.

(** * Layout and comments *)

(** Where the reader is while it skips layout: between tokens, in a
    `%` comment, in a block comment, or in a block comment just after
    a `*`. *)
Inductive skip_state : Type :=
| InLayout
| InLine
| InBlock
| InStar.

(** The text [cs] from its first character that is neither layout nor
    in a comment, the reader being in the state [s]. Nothing for a
    block comment that does not end, for a block comment with a `/*`
    inside it (SWI-Prolog nests them), and for a character in a
    comment that is not ASCII printing or layout. A `/` that no `*`
    follows is not a comment and is left in the text. *)
Fixpoint skip (s : skip_state) (cs : list ascii) : option (list ascii) :=
  match cs with
  | [] =>
      match s with
      | InLayout | InLine => Some []
      | InBlock | InStar => None
      end
  | c :: cs' =>
      let n := code c in
      match s with
      | InLayout =>
          if is_layout n then skip InLayout cs'
          else if n =? c_percent then skip InLine cs'
          else if n =? c_slash then
            match cs' with
            | d :: cs'' => if code d =? c_star then skip InBlock cs'' else Some cs
            | [] => Some cs
            end
          else Some cs
      | InLine =>
          if n =? c_nl then skip InLayout cs'
          else if is_printing n || is_layout n then skip InLine cs'
          else None
      | InBlock =>
          if n =? c_star then skip InStar cs'
          else if (n =? c_slash) && starts c_star cs' then None
          else if is_printing n || is_layout n then skip InBlock cs'
          else None
      | InStar =>
          if n =? c_slash then skip InLayout cs'
          else if n =? c_star then skip InStar cs'
          else if is_printing n || is_layout n then skip InBlock cs'
          else None
      end
  end.

(** * Names and integers *)

(** The name whose characters after those in [acc] (last first) are
    the letters, digits and underscores at the front of [cs], and the
    text after it. *)
Fixpoint ident (cs : list ascii) (acc : list ascii) : string * list ascii :=
  match cs with
  | [] => (string_of_rev acc, [])
  | c :: cs' =>
      if is_alnum (code c) then ident cs' (c :: acc) else (string_of_rev acc, cs)
  end.

(** The symbol atom whose characters after those in [acc] are the
    symbol characters at the front of [cs], and the text after it.
    Nothing when the run has a `/` then a `*`, which SWI does not
    read as one atom. The run stops before a full stop, and the step
    after the atom refuses one there: inside brackets always, and
    outside them because a lone symbol atom is no item. So `=..`
    is refused, though SWI reads it. *)
Fixpoint symbols (cs : list ascii) (acc : list ascii) : option (string * list ascii) :=
  match cs with
  | [] => Some (string_of_rev acc, [])
  | c :: cs' =>
      let n := code c in
      if is_symbol n then
        if (n =? c_slash) && starts c_star cs' then None else symbols cs' (c :: acc)
      else Some (string_of_rev acc, cs)
  end.

(** Ten, the base of an integer's digits. A definition of its own, so
    the extracted reader builds the number once. *)
Definition ten : Z := 10.

(** The integer whose digits are those of [z] and then the decimal
    digits at the front of [cs], and the text after them. *)
Fixpoint digits (cs : list ascii) (z : Z) : Z * list ascii :=
  match cs with
  | [] => (z, [])
  | c :: cs' =>
      let n := code c in
      if is_digit n then digits cs' (z * ten + Z.of_nat (n - c_0))%Z else (z, cs)
  end.

(** * Quoted text *)

(** The escapes of one character after a backslash, each with the
    code it stands for: `\a`, `\b`, `\f`, `\n`, `\r`, `\t`, `\v`, and
    a backslash or a quote of any kind standing for itself. *)
Definition escapes : list (nat * Z) :=
  [(97, 7%Z); (98, 8%Z); (102, 12%Z); (110, 10%Z); (114, 13%Z); (116, 9%Z); (118, 11%Z);
   (92, 92%Z); (39, 39%Z); (34, 34%Z); (96, 96%Z)].

(** The code the escape character of code [n] stands for in the
    table [l], if it is there. *)
Fixpoint escape_code (n : nat) (l : list (nat * Z)) : option Z :=
  match l with
  | [] => None
  | (k, z) :: l' => if n =? k then Some z else escape_code n l'
  end.

(** The value of the character of code [n] as a digit in the base
    [base], 8 or 16, if it is one. A hexadecimal digit's letter may
    be of either case. *)
Definition digit_value (base n : nat) : option nat :=
  let d :=
    if is_digit n then n - c_0
    else if between c_a c_f n then n - lower_digit
    else if between c_upper_a c_upper_f n then n - upper_digit
    else base in
  if d <? base then Some d else None.

(** The number whose digits in the base [base] are those of [z] and
    then the digits at the front of [cs], which a backslash must end,
    and the text after that backslash. [fuel] is one more than the
    most digits read: nothing for a longer number. *)
Fixpoint numeric (fuel base : nat) (cs : list ascii) (z : Z) : option (Z * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match cs with
      | [] => None
      | c :: cs' =>
          let n := code c in
          if n =? c_backslash then Some (z, cs')
          else
            match digit_value base n with
            | Some d => numeric fuel' base cs' (z * Z.of_nat base + Z.of_nat d)%Z
            | None => None
            end
      end
  end.

(** The numbers of UTF-8: where each longer form starts, and what its
    bytes add to their six bits. Definitions of their own, as [ten]. *)
Definition z64 : Z := 64.
Definition z128 : Z := 128.
Definition z192 : Z := 192.
Definition z224 : Z := 224.
Definition z240 : Z := 240.
Definition z2048 : Z := 2048.
Definition z4096 : Z := 4096.
Definition z65536 : Z := 65536.
Definition z262144 : Z := 262144.

(** The last character code, 0x10FFFF, and the first and the last
    surrogate, 0xD800 and 0xDFFF, which are no characters. *)
Definition last_code : Z := 1114111.
Definition first_surrogate : Z := 55296.
Definition last_surrogate : Z := 57343.

(** Whether [z] is a character code an escape may give: not above
    0x10FFFF, and not a surrogate (0xD800 to 0xDFFF). Zero is one:
    `\0\` is the NUL character. *)
Definition is_char_code (z : Z) : bool :=
  ((0 <=? z) && (z <=? last_code) && negb ((first_surrogate <=? z) && (z <=? last_surrogate)))%Z.

(** The character whose code is [z], for a z from 0 to 255. *)
Definition zbyte (z : Z) : ascii := byte (Z.to_nat z).

(** The UTF-8 bytes of the character code [z], last first, in front
    of [acc]. *)
Definition utf8 (z : Z) (acc : list ascii) : list ascii :=
  (if z <? z128 then zbyte z :: acc
   else if z <? z2048 then zbyte (z128 + z mod z64) :: zbyte (z192 + z / z64) :: acc
   else if z <? z65536 then
     zbyte (z128 + z mod z64) :: zbyte (z128 + (z / z64) mod z64)
       :: zbyte (z224 + z / z4096) :: acc
   else
     zbyte (z128 + z mod z64) :: zbyte (z128 + (z / z64) mod z64)
       :: zbyte (z128 + (z / z4096) mod z64) :: zbyte (z240 + z / z262144) :: acc)%Z.

(** The code that the escape at the front of [cs] stands for, [cs]
    being the text after a backslash, and the text after the escape.
    The escapes are those of [escapes], `\x` with one to eight
    hexadecimal digits and a closing backslash, and one to eight
    octal digits with a closing backslash. Nothing for any other
    escape, and for a number that is not a character's code. *)
Definition escape (cs : list ascii) : option (Z * list ascii) :=
  match cs with
  | [] => None
  | c :: cs' =>
      let n := code c in
      match escape_code n escapes with
      | Some z => Some (z, cs')
      | None =>
          match (if n =? c_x then
                   if starts c_backslash cs' then None else numeric nine sixteen cs' 0%Z
                 else if between c_0 c_7 n then numeric nine eight cs 0%Z
                 else None) with
          | Some (z, cs'') => if is_char_code z then Some (z, cs'') else None
          | None => None
          end
      end
  end.

(** The text [cs] after [k] bytes that continue a UTF-8 character,
    with those bytes in front of [acc], last first. The first of them
    must have a code from [lo] to [hi], the others one from 128 to
    191. Nothing when a byte is not such a one. *)
Fixpoint continuation (k lo hi : nat) (cs : list ascii) (acc : list ascii)
    : option (list ascii * list ascii) :=
  match k with
  | O => Some (acc, cs)
  | S k' =>
      match cs with
      | [] => None
      | c :: cs' =>
          if between lo hi (code c) then continuation k' b128 b191 cs' (c :: acc) else None
      end
  end.

(** The same for a UTF-8 character whose first byte, of code [n], is
    already in [acc]: the bytes that must follow it are read. Nothing
    for a first byte that starts no character, and for the forms
    UTF-8 forbids: a longer form than a code needs, a surrogate, and
    a code above 0x10FFFF. SWI reads such bytes as other characters
    than the ones the bytes spell. *)
Definition utf8_rest (n : nat) (cs : list ascii) (acc : list ascii)
    : option (list ascii * list ascii) :=
  if between b194 b223 n then continuation 1 b128 b191 cs acc
  else if n =? b224 then continuation 2 b160 b191 cs acc
  else if n =? b237 then continuation 2 b128 b159 cs acc
  else if between b225 b239 n then continuation 2 b128 b191 cs acc
  else if n =? b240 then continuation 3 b144 b191 cs acc
  else if between b241 b243 n then continuation 3 b128 b191 cs acc
  else if n =? b244 then continuation 3 b128 b143 cs acc
  else None.

(** The bytes of a quoted atom or a string, last first and in front
    of [acc], and the text after its closing quote. [cs] is the text
    after the opening quote, whose code is [q]. A doubled quote is
    one quote, a backslash starts an escape ([escape]), and a
    character outside ASCII must be well-formed UTF-8. Nothing for
    text with no closing quote and for a control character, a
    newline included, written as itself. [fuel] is at least the
    length of [cs]. *)
Fixpoint quoted (fuel q : nat) (cs : list ascii) (acc : list ascii)
    : option (list ascii * list ascii) :=
  match fuel with
  | O => None
  | S fuel' =>
      match cs with
      | [] => None
      | c :: cs' =>
          let n := code c in
          if n =? q then
            if starts q cs' then quoted fuel' q (tl cs') (c :: acc) else Some (acc, cs')
          else if n =? c_backslash then
            match escape cs' with
            | Some (z, cs'') => quoted fuel' q cs'' (utf8 z acc)
            | None => None
            end
          else if is_printing n then quoted fuel' q cs' (c :: acc)
          else if n <? b128 then None
          else
            match utf8_rest n cs' (c :: acc) with
            | Some (acc', cs'') => quoted fuel' q cs'' acc'
            | None => None
            end
      end
  end.

(** The characters of a string in front of [acc], each the atom of
    its UTF-8 bytes. [bs] is the string's bytes, last first, and
    [tail] the bytes already seen of the character being read. *)
Fixpoint chars (bs : list ascii) (tail : list ascii) (acc : list term) : list term :=
  match bs with
  | [] => acc
  | b :: bs' =>
      if between b128 b191 (code b) then chars bs' (b :: tail) acc
      else chars bs' [] (TAtom (string_of_rev (rev_append tail [b])) :: acc)
  end.

(** * Terms *)

(** A term the reader is inside of, with what it has read of it: a
    compound with its name and the arguments so far, a list with the
    elements so far (both last first), or an infix `-` with its left
    side. *)
Inductive frame : Type :=
| FApp (f : string) (args : list term)
| FList (elems : list term)
| FMinus (a : term).

(** What the reader expects next. [MTerm first]: a term, or, when
    [first] holds, the `]` of an empty list. [MSep v lhs]: what may
    follow the term [v] just read, which is a comma, a closing
    bracket, a full stop or, when [lhs] holds, an infix `-`. *)
Inductive mode : Type :=
| MTerm (first : bool)
| MSep (v : term) (lhs : bool).

(** What one step of the reader gives: a refusal, the end of the
    text, a whole clause and the text after its full stop, or the
    text, the frames and the mode to go on with. *)
Inductive step : Type :=
| Fail
| Done
| Clause (t : term) (cs : list ascii)
| Next (cs : list ascii) (st : list frame) (m : mode).

(** The step after the term [v] has been read, [cs] being the text
    after it and [st] the frames: as the right side of an infix `-`
    it makes that term, after which no second `-` may come. *)
Definition value (v : term) (lhs : bool) (cs : list ascii) (st : list frame) : step :=
  match st with
  | FMinus a :: st' => Next cs st' (MSep (TApp "-" [a; v]) false)
  | _ => Next cs st (MSep v lhs)
  end.

(** The step after the name [name]: a compound's start when a `(`
    follows it at once, else the atom. [lhs] is whether the atom may
    be the left side of an infix `-`. *)
Definition named (name : string) (lhs : bool) (cs : list ascii) (st : list frame) : step :=
  match cs with
  | c :: cs' =>
      if code c =? c_lparen then Next cs' (FApp name [] :: st) (MTerm false)
      else value (TAtom name) lhs cs st
  | [] => value (TAtom name) lhs cs st
  end.

(** The names SWI-Prolog has as prefix operators. `table-x` is to it
    `table(-(x))`, so such an atom is not taken as the left side of
    an infix `-`. The symbol atoms that are prefix operators (`-`,
    `+`, `\`) are refused there with every other symbol atom. *)
Definition prefix_names : list string :=
  ["discontiguous"; "dynamic"; "initialization"; "meta_predicate"; "module_transparent";
   "multifile"; "public"; "table"; "thread_initialization"; "thread_local";
   "volatile"]%string.

(** Whether [v] is an atom SWI has as a prefix operator. *)
Definition is_prefix_name (v : term) : bool :=
  match v with
  | TAtom a => existsb (String.eqb a) prefix_names
  | _ => false
  end.

(** Whether [cs], the text after a `-` that follows a term, starts
    the right side of an infix `-` the reader takes: after layout and
    comments, a name, a quoted atom or a list. The character just
    after the `-` must not be a symbol character or a full stop, so
    the `-` is an atom of its own, nor a digit: a right side that is
    a number is refused. *)
Definition minus_right (cs : list ascii) : bool :=
  match cs with
  | [] => false
  | c :: _ =>
      if is_symbol (code c) || (code c =? c_dot) then false
      else
        match skip InLayout cs with
        | Some (d :: _) =>
            let n := code d in
            is_lower n || (n =? c_squote) || (n =? c_lbracket)
        | _ => false
        end
  end.

(** Whether [cs], the text after a full stop, makes that full stop a
    clause's end: the text ends there, or layout or a `%` follows. *)
Definition ends_clause (cs : list ascii) : bool :=
  match cs with
  | [] => true
  | c :: _ => is_layout (code c) || (code c =? c_percent)
  end.

(** The step from what follows the term [v], [cs] being the text
    after it from its first character that is not layout: a comma
    puts [v] in the compound or list it is in, a closing bracket ends
    that, a full stop ends the clause, and a `-` starts the right
    side of an infix `-`. Anything else is refused, so a term never
    runs into the token after it. *)
Definition sep_step (v : term) (lhs : bool) (cs : list ascii) (st : list frame) : step :=
  match cs with
  | [] => Fail
  | c :: cs' =>
      let n := code c in
      if n =? c_comma then
        match st with
        | FApp f args :: st' => Next cs' (FApp f (v :: args) :: st') (MTerm false)
        | FList elems :: st' => Next cs' (FList (v :: elems) :: st') (MTerm false)
        | _ => Fail
        end
      else if n =? c_rparen then
        match st with
        | FApp f args :: st' => value (TApp f (rev_append args [v])) true cs' st'
        | _ => Fail
        end
      else if n =? c_rbracket then
        match st with
        | FList elems :: st' => value (TList (rev_append elems [v])) true cs' st'
        | _ => Fail
        end
      else if n =? c_dot then
        match st with
        | [] => if ends_clause cs' then Clause v cs' else Fail
        | _ => Fail
        end
      else if n =? c_minus then
        if lhs && minus_right cs' && negb (is_prefix_name v)
        then Next cs' (FMinus v :: st) (MTerm false)
        else Fail
      else Fail
  end.

(** Whether [name] is a name whose compounds SWI-Prolog writes in a
    form of their own: `'[|]'(a, [])` is to it the list `[a]`, and
    `'{}'(a)` is `{a}`. A quoted atom of such a name is refused where
    a `(` follows it. *)
Definition is_special_name (name : string) : bool :=
  String.eqb name "[|]" || String.eqb name "{}".

(** The step from the start of a term, [cs] being the text from its
    first character that is not layout: a name, a quoted atom, a
    string, an integer (a `-` just before a digit makes it negative),
    a symbol atom, `!`, `;`, `{}`, or the `[` of a list. With [first]
    a `]` gives the empty list. At the end of the text the reader is
    done if it is inside no term. [fuel] is at least the length of
    [cs]. Any other character is refused: a capital letter or an
    underscore starts a variable. *)
Definition term_step (fuel : nat) (first : bool) (cs : list ascii) (st : list frame) : step :=
  match cs with
  | [] =>
      match st with
      | [] => Done
      | _ => Fail
      end
  | c :: cs' =>
      let n := code c in
      if is_lower n then
        let (name, cs'') := ident cs' [c] in named name true cs'' st
      else if is_digit n then
        let (z, cs'') := digits cs 0%Z in value (TInt z) true cs'' st
      else if n =? c_squote then
        match quoted fuel c_squote cs' [] with
        | Some (bs, cs'') =>
            let name := string_of_rev bs in
            if starts c_lparen cs'' && is_special_name name then Fail
            else named name true cs'' st
        | None => Fail
        end
      else if n =? c_dquote then
        match quoted fuel c_dquote cs' [] with
        | Some (bs, cs'') => value (TList (chars bs [] [])) true cs'' st
        | None => Fail
        end
      else if n =? c_lbracket then Next cs' (FList [] :: st) (MTerm true)
      else if n =? c_rbracket then
        match st with
        | FList [] :: st' => if first then value (TList []) true cs' st' else Fail
        | _ => Fail
        end
      else if (n =? c_minus) && is_digit (code (hd c cs')) then
        let (z, cs'') := digits cs' 0%Z in value (TInt (- z)) true cs'' st
      else if is_symbol n then
        match symbols cs' [c] with
        | Some (name, cs'') => named name false cs'' st
        | None => Fail
        end
      else if (n =? c_bang) || (n =? c_semicolon) then named (string_of_rev [c]) true cs' st
      else if (n =? c_lbrace) && starts c_rbrace cs' then value (TAtom "{}") true (tl cs') st
      else Fail
  end.

(** One step of the reader on the text [cs], inside the frames [st]
    and in the mode [m]. A step that is not the last takes at least
    one character of the text. *)
Definition read_step (fuel : nat) (cs : list ascii) (st : list frame) (m : mode) : step :=
  match skip InLayout cs with
  | None => Fail
  | Some cs' =>
      match m with
      | MTerm first => term_step fuel first cs' st
      | MSep v lhs => sep_step v lhs cs' st
      end
  end.

(** * Clauses *)

(** Whether [t] is the atom `end_of_file`, which ends the text where
    it is a clause, as the end of the file does. *)
Definition is_end_of_file (t : term) : bool :=
  match t with
  | TAtom a => String.eqb a "end_of_file"
  | _ => false
  end.

(** The clauses of the text [cs], last first and in front of [acc],
    the reader being inside the frames [st] in the mode [m]. Nothing
    when a step is refused. [fuel] is more than the length of [cs],
    and so never runs out. *)
Fixpoint clauses (fuel : nat) (cs : list ascii) (st : list frame) (m : mode) (acc : list term)
    : option (list term) :=
  match fuel with
  | O => None
  | S fuel' =>
      match read_step fuel' cs st m with
      | Fail => None
      | Done => Some acc
      | Clause t cs' =>
          if is_end_of_file t then Some acc else clauses fuel' cs' [] (MTerm false) (t :: acc)
      | Next cs' st' m' => clauses fuel' cs' st' m' acc
      end
  end.

(** The length of [cs] more than [n]. The standard library's [length]
    is not a tail call in the extracted code. *)
Fixpoint count (cs : list ascii) (n : nat) : nat :=
  match cs with
  | [] => n
  | _ :: cs' => count cs' (S n)
  end.

(** The clauses of the text [cs], last first, or nothing. *)
Definition rev_clauses (cs : list ascii) : option (list term) :=
  clauses (S (count cs 0)) cs [] (MTerm false) [].

(** The clauses of the text [cs] in order, up to its end or to a
    clause that is the atom `end_of_file`, as `read_term/3` reads
    them one after another. Nothing when SWI-Prolog would not read
    the text, and for the syntax this reader does not take. *)
Definition read_clauses (cs : list ascii) : option (list term) :=
  match rev_clauses cs with
  | Some r => Some (rev_append r [])
  | None => None
  end.

(** Whether [t] is a `run(Fn, Args)` clause, which is no item. *)
Definition is_run (t : term) : bool :=
  match t with
  | TApp f [_; _] => String.eqb f "run"
  | _ => false
  end.

(** Whether [t] is an item of a module: a `func/5`, `data/4`,
    `alias/3` or `context/2` term. *)
Definition is_item (t : term) : bool :=
  match t with
  | TApp f [_; _; _; _; _] => String.eqb f "func"
  | TApp f [_; _; _; _] => String.eqb f "data"
  | TApp f [_; _; _] => String.eqb f "alias"
  | TApp f [_; _] => String.eqb f "context"
  | _ => false
  end.

(** The items among the clauses [r], which are given last first, in
    order and in front of [acc]: a `run/2` clause is left out.
    Nothing when a clause is neither, where `read_ir_file/3`
    throws. *)
Fixpoint items (r : list term) (acc : list term) : option (list term) :=
  match r with
  | [] => Some acc
  | t :: r' =>
      if is_item t then items r' (t :: acc)
      else if is_run t then items r' acc
      else None
  end.

(** The module of the IR text [cs], `module(Items)`, as
    `read_ir_file/3` gives it and `nanofil read-terms` prints it:
    every item in order, not validated. Nothing when Prolog would
    throw, and for the syntax this reader does not take. *)
Definition read_module (cs : list ascii) : option term :=
  match rev_clauses cs with
  | Some r =>
      match items r [] with
      | Some l => Some (TApp "module" [TList l])
      | None => None
      end
  | None => None
  end.

(** * A text in pieces

    The list of a large file's bytes takes far more room than the
    file: 24 bytes a character in the extracted reader. So the
    driver gives the text a piece at a time, and the reader asks for
    the next piece when it has read the whole clauses of the ones it
    has. *)

(** A text in pieces: its end, or its next characters and the rest,
    which is made when asked for. *)
Inductive text : Type :=
| TextEnd
| TextPiece (cs : list ascii) (rest : unit -> text).

(** What reading the whole clauses of a piece gives: the clauses so
    far, last first, and either the end, at an `end_of_file` clause,
    or the text [rest] that is left, from the start of the first
    clause that is not whole. *)
Inductive piece_end : Type :=
| PieceStop (acc : list term)
| PieceMore (acc : list term) (rest : list ascii).

(** The whole clauses at the front of the text [start], which is not
    the text's end, in front of [acc]. The reader is at [cs] inside
    the frames [st] in the mode [m], within the clause that starts
    at [start]. A clause is whole when a character follows its full
    stop: then no more text changes how it is read. A refusal, or
    the end of the characters, is not taken as such here, since more
    text may follow: the clause is left to be read again. *)
Fixpoint piece_clauses (fuel : nat) (start cs : list ascii) (st : list frame) (m : mode)
    (acc : list term) : piece_end :=
  match fuel with
  | O => PieceMore acc start
  | S fuel' =>
      match read_step fuel' cs st m with
      | Fail | Done => PieceMore acc start
      | Clause t rest =>
          match rest with
          | [] => PieceMore acc start
          | _ :: _ =>
              if is_end_of_file t then PieceStop acc
              else piece_clauses fuel' rest rest [] (MTerm false) (t :: acc)
          end
      | Next cs' st' m' => piece_clauses fuel' start cs' st' m' acc
      end
  end.

(** The clauses of the text [p], last first and in front of [acc],
    [buf] being the characters before it that are not yet read.
    Only the last characters, with the text's end after them, are
    read as [clauses] reads a whole text. *)
Fixpoint text_clauses (p : text) (buf : list ascii) (acc : list term) : option (list term) :=
  match p with
  | TextEnd => clauses (S (count buf 0)) buf [] (MTerm false) acc
  | TextPiece cs rest =>
      let all := rev_append (rev_append buf []) cs in
      match piece_clauses (S (count all 0)) all all [] (MTerm false) acc with
      | PieceStop acc' => Some acc'
      | PieceMore acc' buf' => text_clauses (rest tt) buf' acc'
      end
  end.

(** The module of the IR text [p], as [read_module] gives it for the
    characters of [p]'s pieces one after another. That the two agree
    is not proved; tests/read.sh holds this one to Prolog with pieces
    of one character and of seven, and the examples below cut a text
    at every place. *)
Definition read_text (p : text) : option term :=
  match text_clauses p [] [] with
  | Some r =>
      match items r [] with
      | Some l => Some (TApp "module" [TList l])
      | None => None
      end
  | None => None
  end.

(** The text [cs] in pieces of [k] characters, for a [k] above zero
    and a [fuel] of at least the length of [cs]. *)
Fixpoint cut (fuel k : nat) (cs : list ascii) : text :=
  match fuel, cs with
  | S fuel', _ :: _ => TextPiece (firstn k cs) (fun _ => cut fuel' k (skipn k cs))
  | _, _ => TextEnd
  end.

(** * Examples *)

(** A run is left out, a comment is passed over, and a phi's edge is
    the one operator. *)
Example read_module_items :
  read_module (list_ascii_of_string
    "run(f, [1]). % a run
     context(a, [start-const(-2), 'two words', ""hi""]).")
  = Some (TApp "module" [TList [TApp "context" [TAtom "a";
      TList [TApp "-" [TAtom "start"; TApp "const" [TInt (-2)]]; TAtom "two words";
             TList [TAtom "h"; TAtom "i"]]]]]).
Proof. reflexivity. Qed.

(** An escape in a quoted atom is its character, in UTF-8. *)
Example read_module_escape :
  read_module (list_ascii_of_string "context(a, 'p\n\xe9\q').")
  = Some (TApp "module" [TList [TApp "context" [TAtom "a";
      TAtom (String "p" (String (byte 10) (String (byte 195) (String (byte 169) "q"))))]]]).
Proof. reflexivity. Qed.

(** A variable, an operator other than the infix `-`, a clause that
    is no item and a text with no full stop are refused. *)
Example read_module_refuses :
  map (fun s => read_module (list_ascii_of_string s))
    ["context(a, X)."; "context(a, 1 + 2)."; "foo(a)."; "context(a, b)"]%string
  = [None; None; None; None].
Proof. reflexivity. Qed.

(** A text read in pieces of every size from one character to forty
    is read as the whole text is: here two clauses with a comment, a
    quoted atom with a full stop in it and an `end_of_file` that
    hides a clause the reader would refuse. *)
Definition pieces_example : list ascii :=
  list_ascii_of_string
    "context('a. b', [x-y, ""s""]). /* c. */ data(d, local, 8, []).
     end_of_file. foo(X).".

Example read_text_pieces :
  forallb (fun k =>
      match read_text (cut (length pieces_example) (S k) pieces_example),
            read_module pieces_example with
      | Some a, Some b => term_eqb a b
      | _, _ => false
      end) (seq 0 40) = true.
Proof. vm_compute. reflexivity. Qed.

(** A text that is refused is refused in pieces too. *)
Example read_text_refuses :
  forallb (fun k =>
      match read_text (cut 40 (S k) (list_ascii_of_string "context(a, b). context(a, X).")) with
      | None => true
      | Some _ => false
      end) (seq 0 30) = true.
Proof. vm_compute. reflexivity. Qed.
