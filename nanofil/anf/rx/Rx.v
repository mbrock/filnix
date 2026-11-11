(** # PCRE2 bytecode to nanofil IR, in Gallina

    This file is experiments/regex-nanofil/rx.pl written again in
    Gallina, clause by clause, so that the regex compiler can be
    compiled into a Fil-C library through CertiRocq's λANF and run in
    the process of libpcre2 itself. rx.pl's header says what the
    compiler does. It reads the bytecode that pcre2_compile made of a
    pattern, decodes it into a tree, and turns the tree into one
    function of nanofil's unchecked IR. That function returns 1 with
    PCRE2's ovector filled in, 0 when there is no match, -1 when the
    backtrack stack is too small, and -2 when the step budget is spent.

    The port is held to the Prolog original byte for byte. run.sh gives
    each file of terms to `rx:rx_file/1` and to the extraction of this
    file, and requires the two outputs to be identical. So every fresh
    name is made in the order that rx.pl's grammar rules make it, and the
    IR is built as the [term] that IrText.v's reader reads from rx.pl's
    printed text.

    ## How the Prolog maps to Gallina

    | rx.pl | Here |
    |---|---|
    | `code_regex/4` and the decoding predicates | [code_regex], [nodes], [node_of], [bracket], [branches], each giving a [dres] |
    | the byte sets, lists of `Lo-Hi` ranges | lists of pairs of [Z] |
    | the DCG state `s(Counter, Current, Blocks, Slots)` | the record [st], threaded by hand |
    | a rule of the state that fails, such as `emit//1` with no open block | the flag [st_bad] |
    | `gen//4`, `greedy_loop//5`, `lazy_loop//5`, `top//3` | [gen], [greedy_loop], [lazy_loop], [top] |
    | `regex_func/3` and `reachable/2` | [regex_func] and [reachable] |
    | `rx_file/1` | [rx_outcomes], [outcome_lines] and [rx_file_text] |
    | `writeq/1` | [writeq_parts] and [writable] |

    A decoding predicate of rx.pl can succeed, fail, throw
    `unsupported(Why)` or raise an error, and the four differ: a failure
    inside a node becomes `unsupported(Op)` at the nearest enclosing
    branch, while an error ends the whole run. [dres] keeps the four
    apart. Code generation and the driver only succeed or fail, so they
    use the flag [st_bad] and [option].

    ## Where it departs from rx.pl

    Every departure concerns a text of terms that pcre2_rx_terms.h does
    not write. In each case this port gives [Failed], which says that
    rx.pl fails or raises an error at that pattern. The table says what
    rx.pl does instead.

    | Input | What rx.pl does |
    |---|---|
    | a text that IrText.v does not read | prints the patterns before the first clause it cannot read |
    | a byte or count that is an arithmetic expression or constant, such as `pi` or `-(1,2)` | computes with its value |
    | a `char` operand that is not an integer | compiles a class of that term as far as it can |
    | a repeat bound in `ops(Ops)` that is neither an integer nor `inf` | compiles it as far as it can |
    | a `dollar(D)` whose node is not one without operands | compiles that node |
    | a term to print with a byte outside ASCII or an operator | writes it with `writeq/1` |

    The last row only concerns [rx_file_text], which prints functions;
    [rx_outcomes] gives the function's term without printing it. *)

From Stdlib Require Import String ZArith List Bool Ascii.
From Nanofil Require Import Term Maps.
From Backend Require Text IrText.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * Terms *)

(** The temporary `tmp(A)` named [a]: a slot, a fresh temporary or a
    parameter. *)
Definition tmp_named (a : string) : term := TApp "tmp" [TAtom a].

(** The operand `const(N)`. *)
Definition const (n : Z) : term := TApp "const" [TInt n].

(** Whether [t] is the atom [a], as `T == a`. *)
Definition is_atom (a : string) (t : term) : bool :=
  match t with
  | TAtom b => String.eqb a b
  | _ => false
  end.

(** The argument [A] of [t] when [t] is the compound `F(A)` of the name
    [f], as unifying [t] with `F(A)` finds it. *)
Definition arg1 (f : string) (t : term) : option term :=
  match t with
  | TApp g [a] => if String.eqb f g then Some a else None
  | _ => None
  end.

(** The length of [l] more than [n], counted in a loop. *)
Fixpoint len {A : Type} (l : list A) (n : nat) : nat :=
  match l with
  | [] => n
  | _ :: l' => len l' (S n)
  end.

(** The images of the elements of [l] under [f], last first, in front of
    [acc]. *)
Fixpoint map_rev {A B : Type} (f : A -> B) (l : list A) (acc : list B) : list B :=
  match l with
  | [] => acc
  | x :: l' => map_rev f l' (f x :: acc)
  end.

(** The images of the elements of [l] under [f], in order. *)
Definition map_tr {A B : Type} (f : A -> B) (l : list A) : list B :=
  rev_append (map_rev f l []) [].

(** * Byte sets

    A set of bytes is a list of `Lo-Hi` ranges, here pairs of [Z]. The
    sets rx.pl makes are sorted, disjoint and not adjacent, within 0 to
    255. *)

(** Whether the range [r] is at most [q] in the standard order of terms
    on `A-B` pairs of integers: by the low end, then by the high end. *)
Definition range_le (r q : Z * Z) : bool :=
  let (a, b) := r in
  let (c, d) := q in
  (a <? c) || ((a =? c) && (b <=? d)).

(** The ranges [rs], which are sorted from the greatest down, with [r]
    put in its place. *)
Fixpoint insert_desc (r : Z * Z) (rs : list (Z * Z)) : list (Z * Z) :=
  match rs with
  | [] => [r]
  | q :: rs' => if range_le q r then r :: rs else q :: insert_desc r rs'
  end.

(** `msort/2` on ranges: [rs] sorted in the standard order of terms,
    duplicates kept. Ranges already in ascending order, as a bitmap
    gives them, each take one step. *)
Definition msort (rs : list (Z * Z)) : list (Z * Z) :=
  rev_append (fold_left (fun acc r => insert_desc r acc) rs []) [].

(** `merged/2` from the range [a]-[b] on, with the ranges [rs] after it
    and the ranges finished so far, last first, in [acc]: a range that
    starts at most one past the current one's end joins it. *)
Fixpoint merged_from (a b : Z) (rs : list (Z * Z)) (acc : list (Z * Z)) : list (Z * Z) :=
  match rs with
  | [] => rev_append ((a, b) :: acc) []
  | (c, d) :: rs' =>
      if c <=? b + 1 then merged_from a (Z.max b d) rs' acc
      else merged_from c d rs' ((a, b) :: acc)
  end.

(** `merged/2`: the sorted ranges [rs] with each run of overlapping or
    adjacent ranges joined. *)
Definition merged (rs : list (Z * Z)) : list (Z * Z) :=
  match rs with
  | [] => []
  | (a, b) :: rs' => merged_from a b rs' []
  end.

(** `normal/2`: the ranges [rs] sorted and merged. *)
Definition normal (rs : list (Z * Z)) : list (Z * Z) := merged (msort rs).

(** `complement/3`: the bytes from [lo] to 255 that the sorted ranges
    [rs] leave out. *)
Fixpoint complement_from (rs : list (Z * Z)) (lo : Z) : list (Z * Z) :=
  match rs with
  | [] => if lo <=? 255 then [(lo, 255)] else []
  | (a, b) :: rs' =>
      let rest := complement_from rs' (b + 1) in
      if lo <? a then (lo, a - 1) :: rest else rest
  end.

(** `complement/2`: the bytes the sorted ranges [rs] leave out. *)
Definition complement (rs : list (Z * Z)) : list (Z * Z) := complement_from rs 0.

(** `other_case/5`: the part of each range of [rs] that lies from [lo]
    to [hi], moved by [d]. *)
Fixpoint other_case (rs : list (Z * Z)) (lo hi d : Z) : list (Z * Z) :=
  match rs with
  | [] => []
  | (a, b) :: rs' =>
      let l := Z.max a lo in
      let h := Z.min b hi in
      if l <=? h then (l + d, h + d) :: other_case rs' lo hi d else other_case rs' lo hi d
  end.

(** `folded/2`: the ranges [rs] with the other case of each ASCII letter
    in them. *)
Definition folded (rs : list (Z * Z)) : list (Z * Z) :=
  normal (app rs (app (other_case rs 97 122 (-32)) (other_case rs 65 90 32))).

(** `type_bytes/2`: the bytes of `\d`, `\w` and `\s` in PCRE2's built-in
    tables, which are the C locale's, of a newline and of nothing. *)
Definition type_bytes (t : term) : option (list (Z * Z)) :=
  match t with
  | TAtom a =>
      if String.eqb a "digit" then Some [(48, 57)]
      else if String.eqb a "word" then Some [(48, 57); (65, 90); (95, 95); (97, 122)]
      else if String.eqb a "space" then Some [(9, 13); (32, 32)]
      else if String.eqb a "newline" then Some [(10, 10)]
      else if String.eqb a "none" then Some []
      else None
  | _ => None
  end.

(** The bytes of a word character, `type_bytes(word, Word)`. *)
Definition word_bytes : list (Z * Z) := [(48, 57); (65, 90); (95, 95); (97, 122)].

(** `type_set/3`: the bytes of the type [t], or with [sense] `no` the
    bytes outside it. *)
Definition type_set (t sense : term) : option (list (Z * Z)) :=
  if is_atom "yes" sense then type_bytes t
  else if is_atom "no" sense then
    match type_bytes t with
    | Some rs => Some (complement rs)
    | None => None
    end
  else None.

(** `byte_bits/5`: for the [k] bits from bit [i] of the bitmap byte [m],
    the byte [base] + I of each set bit I, last first, in front of
    [acc]. *)
Fixpoint byte_bits (k : nat) (i m base : Z) (acc : list (Z * Z)) : list (Z * Z) :=
  match k with
  | O => acc
  | S k' =>
      let acc' := if Z.land m (Z.shiftl 1 i) =? 0 then acc else (base + i, base + i) :: acc in
      byte_bits k' (i + 1) m base acc'
  end.

(** `bitmap_bytes/3`: the members of the class bitmap [ms] from the byte
    [base] on, as one-byte ranges, in front of [acc] (last first) and
    then in order. Nothing for an element that is not an integer, where
    rx.pl's `/\` raises an error. *)
Fixpoint bitmap_bytes (ms : list term) (base : Z) (acc : list (Z * Z)) : option (list (Z * Z)) :=
  match ms with
  | [] => Some (rev_append acc [])
  | TInt m :: ms' => bitmap_bytes ms' (base + 8) (byte_bits 8 0 m base acc)
  | _ :: _ => None
  end.

(** `bitmap_set/2`: the set of a class bitmap, which has bit C mod 8 of
    byte C // 8 set for each member C. Nothing where rx.pl raises an
    error. *)
Definition bitmap_set (ms : list term) : option (list (Z * Z)) :=
  match bitmap_bytes ms 0 [] with
  | Some cs => Some (normal cs)
  | None => None
  end.

(** * Decoding *)

(** How a repeat chooses: as many as it can, as few, or as many with no
    way back. *)
Inductive mode : Type := Greedy | Lazy | Possessive.

(** The tree that `code_regex/4` decodes, one constructor per node of
    the table in rx.pl's PlDoc; rx.pl's header says what each matches.
    [NStar a min None m] repeats with no upper bound (`inf`). [NOdd]
    stands for a node that rx.pl builds from a term this port does not
    model; compiling it is refused. *)
Inductive node : Type :=
| NClass (rs : list (Z * Z))
| NSeq (ns : list node)
| NAlt (ns : list node)
| NGroup (n : Z) (a : node)
| NOnce (a : node)
| NStar (a : node) (min : Z) (max : option Z) (m : mode)
| NLook (neg : bool) (a : node)
| NBack (n : Z)
| NBol
| NMbol
| NEol
| NEod
| NMeol
| NWordb (yes : bool)
| NOdd.

(** How a decoding predicate ends: [DOk x rest] when it succeeds with
    [x], [rest] being the bytes after what it read; [DFail] when it
    fails; [DUnsup why] when it throws `unsupported(Why)`; [DErr] when it
    raises an error, which only a malformed text makes it do. *)
Inductive dres (A : Type) : Type :=
| DOk (x : A) (rest : list term)
| DFail
| DUnsup (why : term)
| DErr.
Arguments DOk {A} x rest.
Arguments DFail {A}.
Arguments DUnsup {A} why.
Arguments DErr {A}.

(** How a predicate that cannot throw `unsupported` ends: with [x], by
    failing, or by raising an error. *)
Inductive cres (A : Type) : Type :=
| COk (x : A)
| CFail
| CErr.
Arguments COk {A} x.
Arguments CFail {A}.
Arguments CErr {A}.

(** What `opcode(D, B, Op)` finds for the byte B: the opcode [LOp op]
    that `ops(Ops)` names it, [LFail] when B is negative, past the end
    of Ops, or Ops is not a list, and [LErr] when B is not an integer,
    for which `nth0/3` raises a type error. *)
Inductive found : Type :=
| LOp (op : term)
| LFail
| LErr.

(** The element of [l] at the index [i], counting from 0. *)
Fixpoint nth0 (i : Z) (l : list term) : option term :=
  match l with
  | [] => None
  | t :: l' => if i =? 0 then Some t else nth0 (i - 1) l'
  end.

(** `opcode/3`: the name in [ops] of the opcode byte [b]. *)
Definition opcode (ops b : term) : found :=
  match b with
  | TInt i =>
      if i <? 0 then LFail
      else
        match ops with
        | TList l =>
            match nth0 i l with
            | Some op => LOp op
            | None => LFail
            end
        | _ => LFail
        end
  | _ => LErr
  end.

(** `count/3`: the two-byte number, high byte first, at the front of
    [bs], and the bytes after it. *)
Definition count (bs : list term) : dres Z :=
  match bs with
  | TInt h :: TInt l :: bs' => DOk (h * 256 + l) bs'
  | _ :: _ :: _ => DErr
  | _ => DFail
  end.

(** What decoding reads besides the bytes, rx.pl's `d(Ops, Dollar)`:
    the opcode names, and the node that `$` stands for. *)
Record dctx : Type := mk_dctx { d_ops : term; d_dollar : term }.

(** The node of `$`, rx.pl's `Dollar` from the header, which it puts
    in the tree as it is: `eol` or `eod` as pcre2_rx_terms.h writes it,
    or another node without operands. *)
Definition dollar_node (t : term) : node :=
  match t with
  | TAtom a =>
      if String.eqb a "bol" then NBol
      else if String.eqb a "mbol" then NMbol
      else if String.eqb a "eol" then NEol
      else if String.eqb a "eod" then NEod
      else if String.eqb a "meol" then NMeol
      else NOdd
  | _ =>
      match arg1 "wordb" t with
      | Some w => NWordb (is_atom "yes" w)
      | None => NOdd
      end
  end.

(** How the mode term [t] of a repeat of one byte acts in [gen]: `lazy`
    and `possessive` as themselves, and any other term as `greedy`,
    since `gen//4` only asks of such a repeat whether its mode is one of
    those two. *)
Definition mode_of (t : term) : mode :=
  if is_atom "lazy" t then Lazy else if is_atom "possessive" t then Possessive else Greedy.

(** The node `star(class(Rs), Min, Max, Mode)` of the class [c] with the
    bounds [min] and [max] as rx.pl reads them: [NOdd] when the class is
    odd or a bound is not an integer (or `inf` for [max]). *)
Definition class_star (c : node) (min max md : term) : node :=
  match c, min, max with
  | NClass rs, TInt mn, TInt mx => NStar (NClass rs) mn (Some mx) (mode_of md)
  | NClass rs, TInt mn, TAtom a => if String.eqb a "inf" then NStar (NClass rs) mn None (mode_of md) else NOdd
  | _, _, _ => NOdd
  end.

(** The class `node(char, ...)`, `chari`, `not` or `noti` makes of the
    operand byte [c], for the opcode named [a]; [CFail] for any other
    name. A `char` keeps its operand as it is, so one that is not an
    integer gives [NOdd]; the others compute with it. *)
Definition char_class (a : string) (c : term) : cres node :=
  if String.eqb a "char" then
    match c with TInt n => COk (NClass [(n, n)]) | _ => COk NOdd end
  else if String.eqb a "chari" then
    match c with TInt n => COk (NClass (folded [(n, n)])) | _ => CErr end
  else if String.eqb a "not" then
    match c with TInt n => COk (NClass (complement [(n, n)])) | _ => CErr end
  else if String.eqb a "noti" then
    match c with TInt n => COk (NClass (complement (folded [(n, n)]))) | _ => CErr end
  else CFail.

(** `node(Set, [B], [], D, class(Rs))`, the repeated byte of a repeat
    of the set [set]: the class of the byte [b]. Only the four opcodes
    of [char_class] succeed. `zero(_)` looks the byte up, so it raises
    an error for one that is not an integer. *)
Definition class_of_byte (d : dctx) (set b : term) : cres node :=
  match set with
  | TAtom a => char_class a b
  | _ =>
      match arg1 "zero" set with
      | Some _ => match opcode (d_ops d) b with LErr => CErr | _ => CFail end
      | None => CFail
      end
  end.

(** `node(Op, [], [], D, class(Rs))`, the type of a repeat of a type:
    the class of the opcode [op]. Only `type(T, Sense)` succeeds, and
    `doll` when `$` stands for a `class(_)` term, which is odd. *)
Definition class_of_type (d : dctx) (op : term) : cres node :=
  match op with
  | TApp f [t; sense] =>
      if String.eqb f "type" then
        match type_set t sense with
        | Some rs => COk (NClass rs)
        | None => CFail
        end
      else CFail
  | TAtom a =>
      if String.eqb a "doll" then
        match arg1 "class" (d_dollar d) with
        | Some _ => COk NOdd
        | None => CFail
        end
      else CFail
  | _ => CFail
  end.

(** The first [k] bytes of [bs] and the bytes after them, as
    `length(Map, K), append(Map, Rest, Bs)` splits [bs]; [acc] holds
    those taken so far, last first. *)
Fixpoint take (k : nat) (bs acc : list term) : option (list term * list term) :=
  match k with
  | O => Some (rev_append acc [], bs)
  | S k' =>
      match bs with
      | [] => None
      | b :: bs' => take k' bs' (b :: acc)
      end
  end.

(** `node(class, ...)`: a class's 32-byte bitmap at the front of [bs],
    then a repeat when the opcode after it is one, else the class alone
    with the bytes from that opcode on. *)
Definition class_node (d : dctx) (bs : list term) : dres node :=
  match take 32 bs [] with
  | None => DFail
  | Some (map, bs1) =>
      match bitmap_set map with
      | None => DErr
      | Some rs =>
          match bs1 with
          | [] => DFail
          | b :: bs2 =>
              match opcode (d_ops d) b with
              | LErr => DErr
              | LFail => DFail
              | LOp op =>
                  match op with
                  | TApp f [mn; mx; md] =>
                      if String.eqb f "crep" then DOk (class_star (NClass rs) mn mx md) bs2
                      else DOk (NClass rs) bs1
                  | TApp f [md] =>
                      if String.eqb f "crange" then
                        match count bs2 with
                        | DOk mn bs3 =>
                            match count bs3 with
                            | DOk mx0 bs4 =>
                                let mx := if mx0 =? 0 then None else Some mx0 in
                                DOk (NStar (NClass rs) mn mx (mode_of md)) bs4
                            | DFail => DFail
                            | DErr => DErr
                            | DUnsup w => DUnsup w
                            end
                        | DFail => DFail
                        | DErr => DErr
                        | DUnsup w => DUnsup w
                        end
                      else DOk (NClass rs) bs1
                  | _ => DOk (NClass rs) bs1
                  end
              end
          end
      end
  end.

(** `node(rep(Set, Min0, Max0, Mode), ...)`: a repeat of one byte, whose
    count follows the opcode when [max0] is `n` and whose minimum is
    that count when [min0] is `n`, then the byte, or the opcode of the
    type for a [set] of `type`. *)
Definition rep_node (d : dctx) (set min0 max0 md : term) (bs : list term) : dres node :=
  let maxr := if is_atom "n" max0 then
                match count bs with
                | DOk m bs1 => DOk (TInt m) bs1
                | DFail => DFail
                | DErr => DErr
                | DUnsup w => DUnsup w
                end
              else DOk max0 bs in
  match maxr with
  | DOk mx bs1 =>
      let mn := if is_atom "n" min0 then mx else min0 in
      match bs1 with
      | [] => DFail
      | b :: bs' =>
          let c := if is_atom "type" set then
                     match opcode (d_ops d) b with
                     | LOp op => class_of_type d op
                     | LFail => CFail
                     | LErr => CErr
                     end
                   else class_of_byte d set b in
          match c with
          | COk cls => DOk (class_star cls mn mx md) bs'
          | CFail => DFail
          | CErr => DErr
          end
      end
  | DFail => DFail
  | DErr => DErr
  | DUnsup w => DUnsup w
  end.

(** `repeated/4`: the group [a] under the zero-repeat opcode [zero]
    before its bracket (`none` for no opcode) and the ket [ket] after
    it. An optional group is an alternation with nothing. *)
Definition repeated (zero ket : term) (a : node) : option node :=
  if is_atom "skip" zero then Some (NSeq [])
  else if is_atom "none" zero then
    if is_atom "single" ket then Some a
    else if is_atom "greedy" ket then Some (NStar a 1 None Greedy)
    else if is_atom "lazy" ket then Some (NStar a 1 None Lazy)
    else if is_atom "possessive" ket then Some (NStar a 1 None Possessive)
    else None
  else if is_atom "greedy" zero then
    if is_atom "single" ket then Some (NAlt [a; NSeq []])
    else if is_atom "greedy" ket then Some (NStar a 0 None Greedy)
    else None
  else if is_atom "lazy" zero then
    if is_atom "single" ket then Some (NAlt [NSeq []; a])
    else if is_atom "lazy" ket then Some (NStar a 0 None Lazy)
    else None
  else if is_atom "possessive" zero then
    if is_atom "possessive" ket then Some (NStar a 0 None Possessive) else None
  else None.

(** `wrapped/4`: the group [a] as a bracket of the kind [kind] makes it,
    [n] being the capture number of a `capture` bracket. A lookaround
    whose sense is neither `pos` nor `neg` is odd. *)
Definition wrapped (kind : term) (n : Z) (a : node) : option node :=
  if is_atom "plain" kind then Some a
  else if is_atom "capture" kind then Some (NGroup n a)
  else if is_atom "once" kind then Some (NOnce a)
  else
    match arg1 "look" kind with
    | Some sense =>
        if is_atom "pos" sense then Some (NLook false a)
        else if is_atom "neg" sense then Some (NLook true a)
        else Some NOdd
    | None => None
    end.

(** Whether the opcode [op] ends a branch: `alt` or a `ket(_)`. *)
Definition ends_branch (op : term) : bool :=
  is_atom "alt" op || match arg1 "ket" op with Some _ => true | None => false end.

(** `nodes/4`, `node/5`, `bracket/6` and `branches/5`, which call each
    other. [fuel] bounds the depth of the calls; [decode_fuel] gives
    more than the bytes can use, so it never runs out.

    [nodes] gives the nodes of a branch, in front of those in [acc]
    (last first), up to the `alt` or `ket(_)` that the bytes it gives
    back begin with. A node that fails is `unsupported(Op)`, or
    `unsupported(Name)` for an opcode `x(Name)`. *)
Fixpoint nodes (fuel : nat) (d : dctx) (bs : list term) (acc : list node) {struct fuel}
    : dres (list node) :=
  match fuel with
  | O => DErr
  | S fuel' =>
      match bs with
      | [] => DFail
      | b :: bs1 =>
          match opcode (d_ops d) b with
          | LErr => DErr
          | LFail => DFail
          | LOp op =>
              if ends_branch op then DOk (rev_append acc []) bs
              else
                match node_of fuel' d op bs1 with
                | DOk n bs2 => nodes fuel' d bs2 (n :: acc)
                | DFail =>
                    DUnsup (match arg1 "x" op with Some name => name | None => op end)
                | DUnsup w => DUnsup w
                | DErr => DErr
                end
          end
      end
  end

(** [node_of] is `node/5`: the node of the opcode [op], whose operands
    [bs] begins with. *)
with node_of (fuel : nat) (d : dctx) (op : term) (bs : list term) {struct fuel} : dres node :=
  match fuel with
  | O => DErr
  | S fuel' =>
      match op with
      | TAtom a =>
          if String.eqb a "char" || String.eqb a "chari" || String.eqb a "not"
             || String.eqb a "noti" then
            match bs with
            | c :: bs' =>
                match char_class a c with
                | COk n => DOk n bs'
                | CFail => DFail
                | CErr => DErr
                end
            | [] => DFail
            end
          else if String.eqb a "class" then class_node d bs
          else if String.eqb a "bol" then DOk NBol bs
          else if String.eqb a "mbol" then DOk NMbol bs
          else if String.eqb a "doll" then DOk (dollar_node (d_dollar d)) bs
          else if String.eqb a "eol" then DOk NEol bs
          else if String.eqb a "eod" then DOk NEod bs
          else if String.eqb a "meol" then DOk NMeol bs
          else if String.eqb a "reverse" then
            match count bs with
            | DOk n bs' => DOk (NBack n) bs'
            | DFail => DFail
            | DErr => DErr
            | DUnsup w => DUnsup w
            end
          else DFail
      | TApp f [t; sense] =>
          if String.eqb f "type" then
            match type_set t sense with
            | Some rs => DOk (NClass rs) bs
            | None => DFail
            end
          else DFail
      | TApp f [set; min0; max0; md] =>
          if String.eqb f "rep" then rep_node d set min0 max0 md bs else DFail
      | TApp f [k] =>
          if String.eqb f "wordb" then DOk (NWordb (is_atom "yes" k)) bs
          else if String.eqb f "bra" then
            match bracket fuel' d k bs with
            | DOk (a, ket) bs' =>
                match repeated (TAtom "none") ket a with
                | Some n => DOk n bs'
                | None => DFail
                end
            | DFail => DFail
            | DUnsup w => DUnsup w
            | DErr => DErr
            end
          else if String.eqb f "zero" then
            match bs with
            | [] => DFail
            | b :: bs0 =>
                match opcode (d_ops d) b with
                | LErr => DErr
                | LFail => DFail
                | LOp bra =>
                    match arg1 "bra" bra with
                    | None => DFail
                    | Some kind =>
                        match bracket fuel' d kind bs0 with
                        | DOk (a, ket) bs' =>
                            match repeated k ket a with
                            | Some n => DOk n bs'
                            | None => DFail
                            end
                        | DFail => DFail
                        | DUnsup w => DUnsup w
                        | DErr => DErr
                        end
                    end
                end
            end
          else DFail
      | _ => DFail
      end
  end

(** [bracket] is `bracket/6`: the group whose opening opcode, of the
    kind [kind], precedes [bs], and the ket that ends it. The two link
    bytes are skipped; a capture's number follows them. *)
with bracket (fuel : nat) (d : dctx) (kind : term) (bs : list term) {struct fuel}
    : dres (node * term) :=
  match fuel with
  | O => DErr
  | S fuel' =>
      match bs with
      | _ :: _ :: bs0 =>
          let numbered := if is_atom "capture" kind then count bs0 else DOk 0 bs0 in
          match numbered with
          | DOk n bs1 =>
              match branches fuel' d bs1 [] with
              | DOk (alts, ket) bs' =>
                  let a := match alts with [a] => a | _ => NAlt alts end in
                  match wrapped kind n a with
                  | Some nd => DOk (nd, ket) bs'
                  | None => DFail
                  end
              | DFail => DFail
              | DUnsup w => DUnsup w
              | DErr => DErr
              end
          | DFail => DFail
          | DUnsup w => DUnsup w
          | DErr => DErr
          end
      | _ => DFail
      end
  end

(** [branches] is `branches/5`: the branches of a group, in front of
    those in [acc] (last first), and its ket. Each branch is the nodes
    up to an `alt` or a `ket(_)` and its two link bytes, and a branch of
    one node is that node. *)
with branches (fuel : nat) (d : dctx) (bs : list term) (acc : list node) {struct fuel}
    : dres (list node * term) :=
  match fuel with
  | O => DErr
  | S fuel' =>
      match nodes fuel' d bs [] with
      | DOk ns rest =>
          match rest with
          | b :: _ :: _ :: bs1 =>
              let a := match ns with [a] => a | _ => NSeq ns end in
              match opcode (d_ops d) b with
              | LOp op =>
                  if is_atom "alt" op then branches fuel' d bs1 (a :: acc)
                  else
                    match arg1 "ket" op with
                    | Some ket => DOk (rev_append (a :: acc) [], ket) bs1
                    | None => DFail
                    end
              | _ => DFail
              end
          | _ => DFail
          end
      | DFail => DFail
      | DUnsup w => DUnsup w
      | DErr => DErr
      end
  end.

(** Enough fuel for decoding the bytes [bs]: every chain of calls takes
    a byte at least every fourth call. *)
Definition decode_fuel (bs : list term) : nat := (4 * len bs 0 + 8)%nat.

(** Where a match can start, `start_set/2`'s `Start`: only at the start
    offset, anywhere, at a byte of a set, or at the one byte [b] of a
    `first(B, exact)`, which rx.pl only ever prints. *)
Inductive start : Type :=
| SAnchored
| SAny
| SSet (rs : list (Z * Z))
| SOne (b : term).

(** `start_set/2`: the start of the header term [t]. *)
Definition start_set (t : term) : cres start :=
  match t with
  | TAtom a =>
      if String.eqb a "anchored" then COk SAnchored
      else if String.eqb a "any" then COk SAny
      else CFail
  | TApp f [b; how] =>
      if String.eqb f "first" then
        if is_atom "exact" how then COk (SOne b)
        else if is_atom "caseless" how then
          match b with
          | TInt n => COk (SSet (folded [(n, n)]))
          | _ => CErr
          end
        else CFail
      else CFail
  | TApp f [m] =>
      if String.eqb f "bitmap" then
        match m with
        | TList ms =>
            match bitmap_set ms with
            | Some rs => COk (SSet rs)
            | None => CErr
            end
        | _ => CFail
        end
      else CFail
  | _ => CFail
  end.

(** The first argument of a compound `F(A)` of the name [f] among the
    terms [ts], as `memberchk(F(A), Ts)` finds it. *)
Fixpoint member_arg (f : string) (ts : list term) : option term :=
  match ts with
  | [] => None
  | t :: ts' =>
      match arg1 f t with
      | Some a => Some a
      | None => member_arg f ts'
      end
  end.

(** The same in [h], which must be a list. *)
Definition memberchk1 (f : string) (h : term) : option term :=
  match h with
  | TList ts => member_arg f ts
  | _ => None
  end.

(** What `code_regex/4` gives, `re(Ast, Groups, Start)`: the tree, the
    number of capturing groups as the header has it, and where a match
    can start. *)
Record re : Type := mk_re { re_ast : node; re_groups : term; re_start : start }.

(** `code_regex/4`: the regex of the header [header] and the bytecode
    [bytes], whose opcodes [ops] names. The first unsupported option in
    the header is thrown. The bytecode must be one plain bracket, with a
    `ket(single)`, followed by `end`. *)
Definition code_regex (ops header bytes : term) : dres re :=
  match bytes with
  | TList (b :: bytes') =>
      match memberchk1 "unsupported" header with
      | None => DFail
      | Some (TList (u :: _)) => DUnsup u
      | Some _ =>
          match memberchk1 "groups" header, memberchk1 "dollar" header,
                memberchk1 "start" header with
          | Some groups, Some dollar, Some start0 =>
              match start_set start0 with
              | CFail => DFail
              | CErr => DErr
              | COk st0 =>
                  let d := mk_dctx ops dollar in
                  match opcode ops b with
                  | LErr => DErr
                  | LFail => DFail
                  | LOp op =>
                      match arg1 "bra" op with
                      | Some k =>
                          if is_atom "plain" k then
                            match bracket (decode_fuel bytes') d k bytes' with
                            | DOk (ast, ket) rest =>
                                if is_atom "single" ket then
                                  match rest with
                                  | e :: _ =>
                                      match opcode ops e with
                                      | LOp o =>
                                          if is_atom "end" o then DOk (mk_re ast groups st0) []
                                          else DFail
                                      | LFail => DFail
                                      | LErr => DErr
                                      end
                                  | [] => DFail
                                  end
                                else DFail
                            | DFail => DFail
                            | DUnsup w => DUnsup w
                            | DErr => DErr
                            end
                          else DFail
                      | None => DFail
                      end
                  end
              end
          | _, _, _ => DFail
          end
      end
  | _ => DFail
  end.

(** `groups_in/2`: the capture numbers inside the node [n], in front of
    [acc]. *)
Fixpoint groups_in (n : node) (acc : list Z) : list Z :=
  match n with
  | NGroup k a => k :: groups_in a acc
  | NStar a _ _ _ => groups_in a acc
  | NLook _ a => groups_in a acc
  | NOnce a => groups_in a acc
  | NSeq ns | NAlt ns =>
      (fix all (ns : list node) (acc : list Z) : list Z :=
         match ns with
         | [] => acc
         | a :: ns' => groups_in a (all ns' acc)
         end) ns acc
  | _ => acc
  end.

(** * Emission state *)

(** How a block ends: `goto(L)`, `branch(V, Yes, No)` or `ret(V)`. *)
Inductive ending : Type :=
| Goto (l : string)
| Branch (v : term) (yes no : string)
| Ret (v : term).

(** A finished block `block(Label, [], Insts, Jump)`, with its
    instructions in order. *)
Record block : Type := mk_block { bl_label : string; bl_insts : list term; bl_jump : ending }.

(** The open block `b(Label, ReversedInsts)`, or `none`. *)
Inductive current : Type :=
| Closed
| Open (label : string) (rev_insts : list term).

(** The state `s(Counter, Current, Blocks, Slots)`: the counter of fresh
    names, the open block, the finished blocks (newest first) and the
    slot temporaries (newest first). [st_bad] records that a rule rx.pl
    would fail on was applied; nothing after it is used. *)
Record st : Type := mk_st {
  st_n : Z;
  st_cur : current;
  st_blocks : list block;
  st_slots : list term;
  st_bad : bool }.

(** The state [s] marked as failed. *)
Definition bad (s : st) : st := mk_st (st_n s) (st_cur s) (st_blocks s) (st_slots s) true.

(** `fresh/4`: the name [prefix] followed by the counter, which goes up
    by one. *)
Definition fresh (prefix : string) (s : st) : string * st :=
  (String.append prefix (Text.decimal (st_n s)),
   mk_st (st_n s + 1) (st_cur s) (st_blocks s) (st_slots s) (st_bad s)).

(** `tmp//1`: a fresh temporary `tmp(tN)`. *)
Definition tmp (s : st) : term * st :=
  let '(t, s) := fresh "t" s in (tmp_named t, s).

(** `lab//1`: a fresh label `bN`. *)
Definition lab (s : st) : string * st := fresh "b" s.

(** `slot//1`: a fresh slot `tmp(sN)`, which is added to the slots. *)
Definition slot (s : st) : term * st :=
  let '(t, s) := fresh "s" s in
  let v := tmp_named t in
  (v, mk_st (st_n s) (st_cur s) (st_blocks s) (v :: st_slots s) (st_bad s)).

(** `slots//1`: the slots so far, newest first. *)
Definition slots (s : st) : list term := st_slots s.

(** `emit//1`: the instruction [i] at the end of the open block. *)
Definition emit (i : term) (s : st) : st :=
  match st_cur s with
  | Open l ins => mk_st (st_n s) (Open l (i :: ins)) (st_blocks s) (st_slots s) (st_bad s)
  | Closed => bad s
  end.

(** `jump//1`: the open block ended by [j], and no block open. *)
Definition jump (j : ending) (s : st) : st :=
  match st_cur s with
  | Open l ins =>
      mk_st (st_n s) Closed (mk_block l (rev_append ins []) j :: st_blocks s) (st_slots s)
        (st_bad s)
  | Closed => bad s
  end.

(** `begin//1`: a new block [l] opened. *)
Definition begin (l : string) (s : st) : st :=
  match st_cur s with
  | Closed => mk_st (st_n s) (Open l []) (st_blocks s) (st_slots s) (st_bad s)
  | Open _ _ => bad s
  end.

(** `rd//2`: a fresh temporary loaded from the slot [sl]. *)
Definition rd (sl : term) (s : st) : term * st :=
  let '(v, s) := tmp s in
  (v, emit (TApp "let" [v; TAtom "l"; TApp "load" [TAtom "l"]; TList [sl]]) s).

(** `wr//2`: the value [v] stored in the slot [sl]. *)
Definition wr (sl v : term) (s : st) : st := emit (TApp "store" [TAtom "l"; v; sl]) s.

(** `calc//4`: a fresh temporary that is [a] [op] [b], on longs. *)
Definition calc (op : string) (a b : term) (s : st) : term * st :=
  let '(v, s) := tmp s in
  (v, emit (TApp "let" [v; TAtom "l"; TAtom op; TList [a; b]]) s).

(** `cond//6`: the block ended by a branch on [a] [c] [b], compared as
    the kind [k], to [yes] or [no]. *)
Definition cond (c k : string) (a b : term) (yes no : string) (s : st) : st :=
  let '(v, s) := tmp s in
  let s := emit (TApp "let" [v; TAtom "w"; TApp "cmp" [TAtom c; TAtom k]; TList [a; b]]) s in
  jump (Branch v yes no) s.

(** `check//5`: on to a new block if [a] [c] [b] holds, else to
    [fail]. *)
Definition check (c k : string) (a b : term) (fail : string) (s : st) : st :=
  let '(l, s) := lab s in
  let s := cond c k a b l fail s in
  begin l s.

(** `byte//2`: a fresh temporary holding the subject's byte at the
    offset [p]. *)
Definition byte_at (p : term) (s : st) : term * st :=
  let '(q, s) := tmp s in
  let s := emit (TApp "let" [q; TAtom "p"; TAtom "add"; TList [tmp_named "subject"; p]]) s in
  let '(c, s) := tmp s in
  (c, emit (TApp "let" [c; TAtom "w"; TApp "load" [TAtom "ub"]; TList [q]]) s).

(** `range//5`: to [yes] if the byte [c] is from [lo] to [hi], else to
    [no]. *)
Definition range (lo hi : Z) (c : term) (yes no : string) (s : st) : st :=
  if lo =? hi then cond "eq" "w" c (const lo) yes no s
  else
    let '(d, s) := tmp s in
    let s := emit (TApp "let" [d; TAtom "w"; TAtom "sub"; TList [c; const lo]]) s in
    cond "ule" "w" d (const (hi - lo)) yes no s.

(** `ranges//4`: to [yes] if the byte [c] is in one of the ranges [rs],
    tried in turn, else to [no]. *)
Fixpoint ranges (rs : list (Z * Z)) (c : term) (yes no : string) (s : st) : st :=
  match rs with
  | [] => jump (Goto no) s
  | [(lo, hi)] => range lo hi c yes no s
  | (lo, hi) :: rs' =>
      let '(next, s) := lab s in
      let s := range lo hi c yes next s in
      let s := begin next s in
      ranges rs' c yes no s
  end.

(** `class_test//4`: to [yes] if the byte [c] is in [rs], else to
    [no], testing the complement when it has fewer ranges. *)
Definition class_test (rs : list (Z * Z)) (c : term) (yes no : string) (s : st) : st :=
  let cs := complement rs in
  if Nat.ltb (len cs 0) (len rs 0) then ranges cs c no yes s else ranges rs c yes no s.

(** `test1//4`: to [yes] if the byte at [p] is in [rs], to [no] if it
    is not or [p] is the end. *)
Definition test1 (rs : list (Z * Z)) (p : term) (yes no : string) (s : st) : st :=
  let s := check "ult" "l" p (tmp_named "length") no s in
  let '(c, s) := byte_at p s in
  class_test rs c yes no s.

(** What [gen] compiles in, rx.pl's `ctx(Pos, Sp, Caps)`: the position
    and stack depth slots, and the start and end slots of each group. *)
Record ctx : Type := mk_ctx { x_pos : term; x_sp : term; x_caps : list (Z * term * term) }.

(** The start and end slots of the group [n], as `memberchk(cap(N, CS,
    CE), Caps)` finds them. *)
Fixpoint cap_of (n : Z) (caps : list (Z * term * term)) : option (term * term) :=
  match caps with
  | [] => None
  | (k, cs, ce) :: caps' => if k =? n then Some (cs, ce) else cap_of n caps'
  end.

(** `stack_address//3`: a fresh pointer to the long [i] past the depth
    [sv] of the backtrack stack. *)
Definition stack_address (sv : term) (i : Z) (s : st) : term * st :=
  let '(ix, s) := calc "add" sv (const i) s in
  let '(off, s) := tmp s in
  let s := emit (TApp "let" [off; TAtom "l"; TAtom "shl"; TList [ix; const 3]]) s in
  let '(q, s) := tmp s in
  (q, emit (TApp "let" [q; TAtom "p"; TAtom "add"; TList [tmp_named "stack"; off]]) s).

(** `push_each//3`: the slots [sls] stored from the long [i] past the
    depth [sv] on. *)
Fixpoint push_each (sls : list term) (sv : term) (i : Z) (s : st) : st :=
  match sls with
  | [] => s
  | sl :: sls' =>
      let '(v, s) := rd sl s in
      let '(q, s) := stack_address sv i s in
      let s := emit (TApp "store" [TAtom "l"; v; q]) s in
      push_each sls' sv (i + 1) s
  end.

(** `push//2`: the slots [sls] pushed on the backtrack stack, or to
    `overflow` when it has no room. *)
Definition push (sls : list term) (x : ctx) (s : st) : st :=
  let n := Z.of_nat (len sls 0) in
  let '(sv, s) := rd (x_sp x) s in
  let '(s1, s) := calc "add" sv (const n) s in
  let s := check "ule" "l" s1 (tmp_named "slimit") "overflow" s in
  let s := push_each sls sv 0 s in
  wr (x_sp x) s1 s.

(** `pop_each//3`: the slots [sls] loaded from the long [i] past the
    depth [sv] on. *)
Fixpoint pop_each (sls : list term) (sv : term) (i : Z) (s : st) : st :=
  match sls with
  | [] => s
  | sl :: sls' =>
      let '(q, s) := stack_address sv i s in
      let '(v, s) := tmp s in
      let s := emit (TApp "let" [v; TAtom "l"; TApp "load" [TAtom "l"]; TList [q]]) s in
      let s := wr sl v s in
      pop_each sls' sv (i + 1) s
  end.

(** `pop//2`: the slots [sls] popped from the backtrack stack. *)
Definition pop (sls : list term) (x : ctx) (s : st) : st :=
  let n := Z.of_nat (len sls 0) in
  let '(sv, s) := rd (x_sp x) s in
  let '(s1, s) := calc "sub" sv (const n) s in
  let s := wr (x_sp x) s1 s in
  pop_each sls s1 0 s.

(** `tick//0`: one step of the budget spent, or to `spent` when none is
    left. *)
Definition tick (s : st) : st :=
  let '(n, s) := rd (tmp_named "steps") s in
  let s := check "ne" "l" n (const 0) "spent" s in
  let '(n1, s) := calc "sub" n (const 1) s in
  wr (tmp_named "steps") n1 s.

(** * Code generation

    Each function below is a clause of `gen//4` or a rule it calls. It
    takes the label [f] that the code jumps to when the node cannot
    match (rx.pl's Fail0) and gives the label later code jumps to when
    it fails (Fail1), with the state. A function [gen_a] given to one is
    `gen(A, X)` for the node's child A. *)

(** `gen(class(Rs), ...)`: one byte of [rs] at the position. *)
Definition gen_class (rs : list (Z * Z)) (x : ctx) (f : string) (s : st) : string * st :=
  let pos := x_pos x in
  let '(p, s) := rd pos s in
  let '(ok, s) := lab s in
  let s := test1 rs p ok f s in
  let s := begin ok s in
  let '(p1, s) := calc "add" p (const 1) s in
  (f, wr pos p1 s).

(** `snapshot//3`: for each group of [ns], two fresh slots holding its
    start and end, paired with the group's own slots in the snapshot,
    after those in [acc] (last first). A group with no slots fails. *)
Fixpoint snapshot (ns : list Z) (caps : list (Z * term * term)) (acc : list (term * term))
    (s : st) : list (term * term) * st :=
  match ns with
  | [] => (rev_append acc [], s)
  | n :: ns' =>
      match cap_of n caps with
      | None => (rev_append acc [], bad s)
      | Some (cs, ce) =>
          let '(s1, s) := slot s in
          let '(e1, s) := slot s in
          let '(vs, s) := rd cs s in
          let s := wr s1 vs s in
          let '(ve, s) := rd ce s in
          let s := wr e1 ve s in
          snapshot ns' caps ((ce, e1) :: (cs, s1) :: acc) s
      end
  end.

(** `restore_caps//1`: each slot of the snapshot [snap] given back its
    saved value. *)
Fixpoint restore_caps (snap : list (term * term)) (s : st) : st :=
  match snap with
  | [] => s
  | (sl, saved) :: snap' =>
      let '(v, s) := rd saved s in
      let s := wr sl v s in
      restore_caps snap' s
  end.

(** `undo_caps//3`: a label that puts the captures of [snap] back and
    goes on to [f], or [f] itself when [snap] is empty. *)
Definition undo_caps (snap : list (term * term)) (f : string) (s : st) : string * st :=
  match snap with
  | [] => (f, s)
  | _ :: _ =>
      let '(undo, s) := lab s in
      let '(next, s) := lab s in
      let s := jump (Goto next) s in
      let s := begin undo s in
      let s := restore_caps snap s in
      let s := jump (Goto f) s in
      (undo, begin next s)
  end.

(** `gen(group(N, A), ...)`: A, which sets the start and end of the
    group [k] when it matches and puts back their old values when later
    code fails into it. *)
Definition gen_group (k : Z) (gen_a : string -> st -> string * st) (x : ctx) (f : string)
    (s : st) : string * st :=
  match cap_of k (x_caps x) with
  | None => (f, bad s)
  | Some (cs, ce) =>
      let pos := x_pos x in
      let '(gs, s) := slot s in
      let '(os, s) := slot s in
      let '(oe, s) := slot s in
      let '(p, s) := rd pos s in
      let s := wr gs p s in
      let '(fa, s) := gen_a f s in
      let '(vs0, s) := rd cs s in
      let s := wr os vs0 s in
      let '(ve0, s) := rd ce s in
      let s := wr oe ve0 s in
      let '(g, s) := rd gs s in
      let s := wr cs g s in
      let '(p1, s) := rd pos s in
      let s := wr ce p1 s in
      let '(undo, s) := lab s in
      let '(next, s) := lab s in
      let s := jump (Goto next) s in
      let s := begin undo s in
      let '(vs1, s) := rd os s in
      let s := wr cs vs1 s in
      let '(ve1, s) := rd oe s in
      let s := wr ce ve1 s in
      let s := jump (Goto fa) s in
      (undo, begin next s)
  end.

(** `gen(look(Sense, A), ...)` with `look//8`: a lookahead or lookbehind
    over A, negative when [neg] holds. It keeps nothing of A but its
    captures, the groups [ns]; failing past a positive one undoes
    them. *)
Definition gen_look (neg : bool) (ns : list Z) (gen_a : string -> st -> string * st) (x : ctx)
    (f : string) (s : st) : string * st :=
  let pos := x_pos x in
  let sp := x_sp x in
  let '(lpos, s) := slot s in
  let '(lsp, s) := slot s in
  let '(p, s) := rd pos s in
  let s := wr lpos p s in
  let '(v, s) := rd sp s in
  let s := wr lsp v s in
  let '(snap, s) := snapshot ns (x_caps x) [] s in
  if neg then
    let '(no, s) := lab s in
    let '(_, s) := gen_a no s in
    let s := restore_caps snap s in
    let '(v, s) := rd lsp s in
    let s := wr sp v s in
    let s := jump (Goto f) s in
    let s := begin no s in
    let '(p, s) := rd lpos s in
    (f, wr pos p s)
  else
    let '(_, s) := gen_a f s in
    let '(p, s) := rd lpos s in
    let s := wr pos p s in
    let '(v, s) := rd lsp s in
    let s := wr sp v s in
    undo_caps snap f s.

(** `gen(once(A), ...)`: A's first match, with what A pushed dropped so
    that nothing can resume it; its captures, the groups [ns], are
    undone when later code fails past it. *)
Definition gen_once (ns : list Z) (gen_a : string -> st -> string * st) (x : ctx) (f : string)
    (s : st) : string * st :=
  let sp := x_sp x in
  let '(lsp, s) := slot s in
  let '(v0, s) := rd sp s in
  let s := wr lsp v0 s in
  let '(snap, s) := snapshot ns (x_caps x) [] s in
  let '(_, s) := gen_a f s in
  let '(v, s) := rd lsp s in
  let s := wr sp v s in
  undo_caps snap f s.

(** `gen(back(N), ...)`: [n] bytes back, at the start of a lookbehind
    branch. *)
Definition gen_back (n : Z) (x : ctx) (f : string) (s : st) : string * st :=
  let pos := x_pos x in
  let '(p, s) := rd pos s in
  let s := check "uge" "l" p (const n) f s in
  let '(p1, s) := calc "sub" p (const n) s in
  (f, wr pos p1 s).

(** `gen(bol, ...)`: `^`, the start of the subject. *)
Definition gen_bol (x : ctx) (f : string) (s : st) : string * st :=
  let '(p, s) := rd (x_pos x) s in
  (f, check "eq" "l" p (const 0) f s).

(** `gen(mbol, ...)`: `^` in multiline mode, the start or after a
    newline that does not end the subject. *)
Definition gen_mbol (x : ctx) (f : string) (s : st) : string * st :=
  let '(p, s) := rd (x_pos x) s in
  let '(ok, s) := lab s in
  let '(inside, s) := lab s in
  let s := cond "eq" "l" p (const 0) ok inside s in
  let s := begin inside s in
  let s := check "ult" "l" p (tmp_named "length") f s in
  let '(p0, s) := calc "sub" p (const 1) s in
  let '(c, s) := byte_at p0 s in
  let s := cond "eq" "w" c (const 10) ok f s in
  (f, begin ok s).

(** `gen(eod, ...)`: `\z`, the end of the subject. *)
Definition gen_eod (x : ctx) (f : string) (s : st) : string * st :=
  let '(p, s) := rd (x_pos x) s in
  (f, check "eq" "l" p (tmp_named "length") f s).

(** `gen(meol, ...)`: `$` in multiline mode, the end or before a
    newline. *)
Definition gen_meol (x : ctx) (f : string) (s : st) : string * st :=
  let '(p, s) := rd (x_pos x) s in
  let '(ok, s) := lab s in
  let '(inside, s) := lab s in
  let s := cond "eq" "l" p (tmp_named "length") ok inside s in
  let s := begin inside s in
  let '(c, s) := byte_at p s in
  let s := cond "eq" "w" c (const 10) ok f s in
  (f, begin ok s).

(** `gen(eol, ...)`: `$`, the end or the newline that ends the
    subject. *)
Definition gen_eol (x : ctx) (f : string) (s : st) : string * st :=
  let '(p, s) := rd (x_pos x) s in
  let '(ok, s) := lab s in
  let '(inside, s) := lab s in
  let '(last, s) := lab s in
  let s := cond "eq" "l" p (tmp_named "length") ok inside s in
  let s := begin inside s in
  let '(p1, s) := calc "add" p (const 1) s in
  let s := cond "eq" "l" p1 (tmp_named "length") last f s in
  let s := begin last s in
  let '(c, s) := byte_at p s in
  let s := cond "eq" "w" c (const 10) ok f s in
  (f, begin ok s).

(** `gen(wordb(Want), ...)`: `\b` when [want] holds, else `\B`. *)
Definition gen_wordb (want : bool) (x : ctx) (f : string) (s : st) : string * st :=
  let '(before, s) := slot s in
  let '(after, s) := slot s in
  let '(p, s) := rd (x_pos x) s in
  let s := wr before (const 0) s in
  let '(b1, s) := lab s in
  let '(b2, s) := lab s in
  let '(b3, s) := lab s in
  let s := cond "ugt" "l" p (const 0) b1 b3 s in
  let s := begin b1 s in
  let '(p0, s) := calc "sub" p (const 1) s in
  let '(c0, s) := byte_at p0 s in
  let s := class_test word_bytes c0 b2 b3 s in
  let s := begin b2 s in
  let s := wr before (const 1) s in
  let s := jump (Goto b3) s in
  let s := begin b3 s in
  let s := wr after (const 0) s in
  let '(a1, s) := lab s in
  let '(a2, s) := lab s in
  let s := test1 word_bytes p a1 a2 s in
  let s := begin a1 s in
  let s := wr after (const 1) s in
  let s := jump (Goto a2) s in
  let s := begin a2 s in
  let '(vb, s) := rd before s in
  let '(va, s) := rd after s in
  (f, if want then check "ne" "l" vb va f s else check "eq" "l" vb va f s).

(** Whether the maximum [max] is the integer [min], as `Max == Min`. *)
Definition max_is (max : option Z) (min : Z) : bool :=
  match max with
  | Some m => m =? min
  | None => false
  end.

(** `gen(star(class(Rs), Min, Max, Mode), ...)` for a mode other than
    `lazy`: as many bytes of [rs] as there are, up to [max], then, unless
    [possessive] holds or [max] is [min], one fewer at a time down to
    [min] when later code fails. *)
Definition class_greedy (rs : list (Z * Z)) (min : Z) (max : option Z) (possessive : bool)
    (x : ctx) (f : string) (s : st) : string * st :=
  let pos := x_pos x in
  let '(strt, s) := slot s in
  let '(p0, s) := rd pos s in
  let s := wr strt p0 s in
  let '(scan, s) := lab s in
  let '(adv, s) := lab s in
  let '(done, s) := lab s in
  let s := jump (Goto scan) s in
  let s := begin scan s in
  let '(p, s) := rd pos s in
  let s := match max with
           | None => s
           | Some mx =>
               let '(s1, s) := rd strt s in
               let '(n1, s) := calc "sub" p s1 s in
               check "ult" "l" n1 (const mx) done s
           end in
  let s := test1 rs p adv done s in
  let s := begin adv s in
  let '(p1, s) := calc "add" p (const 1) s in
  let s := wr pos p1 s in
  let s := jump (Goto scan) s in
  let s := begin done s in
  let '(p2, s) := rd pos s in
  let '(s2, s) := rd strt s in
  let s := if min =? 0 then s
           else
             let '(n2, s) := calc "sub" p2 s2 s in
             check "uge" "l" n2 (const min) f s in
  if possessive || max_is max min then (f, s)
  else
    let '(cur, s) := slot s in
    let s := wr cur p2 s in
    let '(next, s) := lab s in
    let '(back, s) := lab s in
    let s := jump (Goto next) s in
    let s := begin back s in
    let s := tick s in
    let '(c, s) := rd cur s in
    let '(s3, s) := rd strt s in
    let '(m, s) := calc "add" s3 (const min) s in
    let s := check "ugt" "l" c m f s in
    let '(c1, s) := calc "sub" c (const 1) s in
    let s := wr cur c1 s in
    let s := wr pos c1 s in
    let s := jump (Goto next) s in
    (back, begin next s).

(** `gen(star(class(Rs), 0, Max, lazy), ...)`: no byte at first, then
    one more byte of [rs] each time later code fails, up to [max]. *)
Definition class_lazy0 (rs : list (Z * Z)) (max : option Z) (x : ctx) (f : string) (s : st)
    : string * st :=
  let pos := x_pos x in
  let '(strt, s) := slot s in
  let '(cur, s) := slot s in
  let '(p0, s) := rd pos s in
  let s := wr strt p0 s in
  let s := wr cur p0 s in
  let '(next, s) := lab s in
  let '(back, s) := lab s in
  let '(adv, s) := lab s in
  let s := jump (Goto next) s in
  let s := begin back s in
  let s := tick s in
  let '(c, s) := rd cur s in
  let s := match max with
           | None => s
           | Some mx =>
               let '(sv, s) := rd strt s in
               let '(n, s) := calc "sub" c sv s in
               check "ult" "l" n (const mx) f s
           end in
  let s := test1 rs c adv f s in
  let s := begin adv s in
  let '(c1, s) := calc "add" c (const 1) s in
  let s := wr cur c1 s in
  let s := wr pos c1 s in
  let s := jump (Goto next) s in
  (back, begin next s).

(** `body//6`: the loop body A, compiled with [gen_a] to fail to [f],
    the label to fail into it, and the slots one iteration must save to
    be resumed later: its start [istart], and the slots A made if A can
    be resumed at all. *)
Definition body (gen_a : string -> st -> string * st) (f : string) (istart : term) (s : st)
    : string * list term * st :=
  let old := slots s in
  let '(fb, s) := gen_a f s in
  let now := slots s in
  let saved := if String.eqb fb f then [istart]
               else istart :: firstn (len now 0 - len old 0) now in
  (fb, saved, s).

(** `greedy_loop//5`: as many iterations of A as match, at least [min]
    (0 or 1), each pushed on the stack so that later code failing into
    the loop resumes the last one; an iteration that matched nothing is
    the last. rx.pl's comment draws it. *)
Definition greedy_loop (gen_a : string -> st -> string * st) (min : Z) (x : ctx) (f : string)
    (s : st) : string * st :=
  let pos := x_pos x in
  let '(cnt, s) := slot s in
  let '(istart, s) := slot s in
  let s := wr cnt (const 0) s in
  let '(iter, s) := lab s in
  let '(iterfail, s) := lab s in
  let '(back, s) := lab s in
  let '(next, s) := lab s in
  let s := jump (Goto iter) s in
  let s := begin iter s in
  let '(p, s) := rd pos s in
  let s := wr istart p s in
  let '(fb, saved, s) := body gen_a iterfail istart s in
  let s := push saved x s in
  let '(c, s) := rd cnt s in
  let '(c1, s) := calc "add" c (const 1) s in
  let s := wr cnt c1 s in
  let '(p1, s) := rd pos s in
  let '(i1, s) := rd istart s in
  let s := cond "ne" "l" p1 i1 iter next s in
  let s := begin iterfail s in
  let '(i, s) := rd istart s in
  let s := wr pos i s in
  let s := if min =? 0 then jump (Goto next) s
           else
             let '(c2, s) := rd cnt s in
             cond "uge" "l" c2 (const min) next back s in
  let s := begin back s in
  let s := tick s in
  let '(c3, s) := rd cnt s in
  let s := check "ne" "l" c3 (const 0) f s in
  let s := pop saved x s in
  let '(c4, s) := calc "sub" c3 (const 1) s in
  let s := wr cnt c4 s in
  let s := jump (Goto fb) s in
  (back, begin next s).

(** `lazy_loop//5`: at least [min] (0 or 1) iterations of A, then one
    more each time later code fails into the loop, unless the last one
    matched nothing; when no further one matches, the last is resumed.
    rx.pl's comment draws it. *)
Definition lazy_loop (gen_a : string -> st -> string * st) (min : Z) (x : ctx) (f : string)
    (s : st) : string * st :=
  let pos := x_pos x in
  let '(cnt, s) := slot s in
  let '(istart, s) := slot s in
  let '(lpos, s) := slot s in
  let s := wr cnt (const 0) s in
  let '(p0, s) := rd pos s in
  let s := wr lpos p0 s in
  let s := wr istart (const (-1)) s in
  let '(next, s) := lab s in
  let '(back, s) := lab s in
  let '(iter, s) := lab s in
  let '(into, s) := lab s in
  let s := if min =? 0 then jump (Goto next) s else jump (Goto iter) s in
  let s := begin back s in
  let s := tick s in
  let '(l0, s) := rd lpos s in
  let '(i0, s) := rd istart s in
  let s := cond "ne" "l" l0 i0 iter into s in
  let s := begin iter s in
  let '(l, s) := rd lpos s in
  let s := wr pos l s in
  let s := wr istart l s in
  let '(fb, saved, s) := body gen_a into istart s in
  let s := push saved x s in
  let '(c, s) := rd cnt s in
  let '(c1, s) := calc "add" c (const 1) s in
  let s := wr cnt c1 s in
  let '(p1, s) := rd pos s in
  let s := wr lpos p1 s in
  let s := jump (Goto next) s in
  let s := begin into s in
  let '(c3, s) := rd cnt s in
  let s := check "ne" "l" c3 (const 0) f s in
  let s := pop saved x s in
  let '(c4, s) := calc "sub" c3 (const 1) s in
  let s := wr cnt c4 s in
  let s := jump (Goto fb) s in
  (back, begin next s).

(** `dispatch//2`: to the label paired with the arm number held in [w],
    testing each number but the last. *)
Fixpoint dispatch (fs : list (Z * string)) (w : term) (s : st) : st :=
  match fs with
  | [] => bad s
  | [(_, fa)] => jump (Goto fa) s
  | (k, fa) :: fs' =>
      let '(l, s) := lab s in
      let s := cond "eq" "l" w (const k) fa l s in
      let s := begin l s in
      dispatch fs' w s
  end.

(** `gen//4`: the code of the node [n], which falls through when [n]
    matches at the position and jumps to [f] when it cannot, and the
    label later code jumps to when it fails. The clauses are tried in
    rx.pl's order. A star of a class takes the clauses for one byte;
    rx.pl's clause for a lazy one with a minimum is its two halves in
    turn, a greedy exact count and a lazy rest. A star with a bound
    over anything else has no clause, and fails. *)
Fixpoint gen (n : node) (x : ctx) (f : string) (s : st) {struct n} : string * st :=
  match n with
  | NClass rs => gen_class rs x f s
  | NSeq ns =>
      (fix seq (ns : list node) (f : string) (s : st) : string * st :=
         match ns with
         | [] => (f, s)
         | a :: ns' => let '(fa, s) := gen a x f s in seq ns' fa s
         end) ns f s
  | NAlt ns =>
      let pos := x_pos x in
      let '(save, s) := slot s in
      let '(which, s) := slot s in
      let '(p, s) := rd pos s in
      let s := wr save p s in
      let '(join, s) := lab s in
      let '(resume, s) := lab s in
      let '(fs, s) :=
        (fix arms (ns : list node) (k : Z) (acc : list (Z * string)) (s : st)
             : list (Z * string) * st :=
           match ns with
           | [] => (rev_append acc [], bad s)
           | a :: ns' =>
               match ns' with
               | [] =>
                   let '(fa, s) := gen a x f s in
                   let s := wr which (const k) s in
                   (rev_append ((k, fa) :: acc) [], jump (Goto join) s)
               | _ :: _ =>
                   let '(tryl, s) := lab s in
                   let '(fa, s) := gen a x tryl s in
                   let s := wr which (const k) s in
                   let s := jump (Goto join) s in
                   let s := begin tryl s in
                   let '(p, s) := rd save s in
                   let s := wr pos p s in
                   arms ns' (k + 1) ((k, fa) :: acc) s
               end
           end) ns 1 [] s in
      let s := begin resume s in
      let s := tick s in
      let '(w, s) := rd which s in
      let s := dispatch fs w s in
      (resume, begin join s)
  | NGroup k a => gen_group k (gen a x) x f s
  | NLook neg a => gen_look neg (groups_in a []) (gen a x) x f s
  | NOnce a => gen_once (groups_in a []) (gen a x) x f s
  | NBack k => gen_back k x f s
  | NBol => gen_bol x f s
  | NMbol => gen_mbol x f s
  | NEod => gen_eod x f s
  | NMeol => gen_meol x f s
  | NEol => gen_eol x f s
  | NWordb want => gen_wordb want x f s
  | NStar a min max m =>
      match a with
      | NClass rs =>
          match m with
          | Lazy =>
              if 0 <? min then
                let max1 := match max with None => None | Some mx => Some (mx - min) end in
                let '(fa, s) := class_greedy rs min (Some min) false x f s in
                class_lazy0 rs max1 x fa s
              else if min =? 0 then class_lazy0 rs max x f s
              else
                match max with
                | None => lazy_loop (gen a x) min x f s
                | Some _ => (f, bad s)
                end
          | Greedy => class_greedy rs min max false x f s
          | Possessive => class_greedy rs min max true x f s
          end
      | _ =>
          match max with
          | None =>
              match m with
              | Possessive => gen_once (groups_in a []) (greedy_loop (gen a x) min x) x f s
              | Greedy => greedy_loop (gen a x) min x f s
              | Lazy => lazy_loop (gen a x) min x f s
              end
          | Some _ => (f, bad s)
          end
      end
  | NOdd => (f, bad s)
  end.

(** * The function *)

(** `caps//3`: the start and end slots of the groups [n] to [g], each
    set to -1, after those in [acc] (last first). [fuel] is more than
    the number of groups. *)
Fixpoint caps (fuel : nat) (n g : Z) (acc : list (Z * term * term)) (s : st)
    : list (Z * term * term) * st :=
  match fuel with
  | O => (rev_append acc [], bad s)
  | S fuel' =>
      if g <? n then (rev_append acc [], s)
      else
        let '(cs, s) := slot s in
        let '(ce, s) := slot s in
        let s := wr cs (const (-1)) s in
        let s := wr ce (const (-1)) s in
        caps fuel' (n + 1) g ((n, cs, ce) :: acc) s
  end.

(** `results//1`: the start and end of each group stored in the
    ovector, 16 bytes a group. *)
Fixpoint results (cs : list (Z * term * term)) (s : st) : st :=
  match cs with
  | [] => s
  | (n, cs0, ce) :: cs' =>
      let o1 := 16 * n in
      let o2 := o1 + 8 in
      let '(v, s) := rd cs0 s in
      let '(q1, s) := tmp s in
      let s := emit (TApp "let" [q1; TAtom "p"; TAtom "add"; TList [tmp_named "ovector"; const o1]]) s in
      let s := emit (TApp "store" [TAtom "l"; v; q1]) s in
      let '(e, s) := rd ce s in
      let '(q2, s) := tmp s in
      let s := emit (TApp "let" [q2; TAtom "p"; TAtom "add"; TList [tmp_named "ovector"; const o2]]) s in
      let s := emit (TApp "store" [TAtom "l"; e; q2]) s in
      results cs' s
  end.

(** The one byte a match can start with, when there is one: [SOne]'s,
    or the byte of a set that is one range of one byte, as `Start =
    set([B-B])` finds it. *)
Definition one_byte (st0 : start) : option term :=
  match st0 with
  | SOne b => Some b
  | SSet [(lo, hi)] => if lo =? hi then Some (TInt lo) else None
  | _ => None
  end.

(** `top//3`: the whole function body. It tries the match at each start
    offset in turn, or only the first for an anchored pattern, skipping
    offsets whose byte cannot begin a match, with `memchr` when only one
    byte can. [groups] must be an integer. *)
Definition top (ast : node) (groups : term) (st0 : start) (s : st) : st :=
  let '(pos, s) := slot s in
  let '(sp, s) := slot s in
  let '(scan, s) := slot s in
  let '(cs, s) := match groups with
                  | TInt g => caps (S (Z.to_nat (g + 1))) 0 g [] s
                  | _ => ([], bad s)
                  end in
  let x := mk_ctx pos sp cs in
  let s := wr scan (tmp_named "start") s in
  let s := wr (tmp_named "steps") (tmp_named "budget") s in
  let '(tryl, s) := lab s in
  let '(go, s) := lab s in
  let '(fail, s) := lab s in
  let '(stop, s) := lab s in
  let s := jump (Goto tryl) s in
  let s := begin tryl s in
  let '(sv, s) := rd scan s in
  let s :=
    match one_byte st0 with
    | Some b =>
        let s := check "ult" "l" sv (tmp_named "length") stop s in
        let '(q, s) := tmp s in
        let s := emit (TApp "let" [q; TAtom "p"; TAtom "add"; TList [tmp_named "subject"; sv]]) s in
        let '(lft, s) := calc "sub" (tmp_named "length") sv s in
        let '(r, s) := tmp s in
        let s := emit (TApp "call" [TApp "result" [r; TAtom "p"]; TApp "global" [TAtom "memchr"];
                         TList [TApp "arg" [TAtom "p"; q]; TApp "arg" [TAtom "w"; TApp "const" [b]];
                                TApp "arg" [TAtom "l"; lft]]]) s in
        let '(ra, s) := tmp s in
        let s := emit (TApp "let" [ra; TAtom "l"; TAtom "ptoi"; TList [r]]) s in
        let s := check "ne" "l" ra (const 0) stop s in
        let '(qa, s) := tmp s in
        let s := emit (TApp "let" [qa; TAtom "l"; TAtom "ptoi"; TList [q]]) s in
        let '(dv, s) := calc "sub" ra qa s in
        let '(s0, s) := calc "add" sv dv s in
        let s := wr scan s0 s in
        jump (Goto go) s
    | None =>
        match st0 with
        | SSet firsts =>
            let '(skip, s) := lab s in
            let s := check "ult" "l" sv (tmp_named "length") stop s in
            let '(c, s) := byte_at sv s in
            let s := class_test firsts c go skip s in
            let s := begin skip s in
            let '(s0, s) := calc "add" sv (const 1) s in
            let s := wr scan s0 s in
            jump (Goto tryl) s
        | _ => jump (Goto go) s
        end
    end in
  let s := begin go s in
  let '(s9, s) := rd scan s in
  let s := wr pos s9 s in
  let s := wr sp (const 0) s in
  let '(_, s) := gen (NGroup 0 ast) x fail s in
  let s := results cs s in
  let s := jump (Ret (const 1)) s in
  let s := begin fail s in
  let s := match st0 with
           | SAnchored => jump (Goto stop) s
           | _ =>
               let '(s1, s) := rd scan s in
               let '(s2, s) := calc "add" s1 (const 1) s in
               let s := wr scan s2 s in
               cond "ule" "l" s2 (tmp_named "length") tryl stop s
           end in
  let s := begin stop s in
  let s := jump (Ret (const 0)) s in
  let s := begin "overflow" s in
  let s := jump (Ret (const (-1))) s in
  let s := begin "spent" s in
  jump (Ret (const (-2))) s.

(** The blocks [bs] by label, each label to its first block, as
    `memberchk(block(L, _, _, J), Blocks)` finds it: the blocks are
    added last first, so an earlier block replaces a later one. The
    lists of reach/4 would take time quadratic in the blocks, which are
    thousands for a long pattern. *)
Definition block_map (bs : list block) : nmap block :=
  fold_left (fun m b => nm_add (TAtom (bl_label b)) b m) (rev_append bs []) nm_empty.

(** `targets/2`: the labels a block's ending [j] may go to. *)
Definition targets (j : ending) : list string :=
  match j with
  | Goto l => [l]
  | Branch _ y n => [y; n]
  | Ret _ => []
  end.

(** `reach/4`: the labels in [seen] and those that the blocks [bm]
    reach from the labels [ls], depth first. Nothing for a label with no
    block, where rx.pl fails. [fuel] is more than the steps it takes. *)
Fixpoint reach (fuel : nat) (ls : list string) (bm : nmap block) (seen : nmap unit)
    : option (nmap unit) :=
  match fuel with
  | O => None
  | S fuel' =>
      match ls with
      | [] => Some seen
      | l :: ls' =>
          if nm_mem (TAtom l) seen then reach fuel' ls' bm seen
          else
            match nm_find (TAtom l) bm with
            | Some b => reach fuel' (app (targets (bl_jump b)) ls') bm (nm_add (TAtom l) tt seen)
            | None => None
            end
      end
  end.

(** `include(seen_block(Seen), ...)`: the blocks of [bs] whose labels
    are in [seen], after those in [acc] (last first). *)
Fixpoint keep_seen (seen : nmap unit) (bs acc : list block) : list block :=
  match bs with
  | [] => rev_append acc []
  | b :: bs' => keep_seen seen bs' (if nm_mem (TAtom (bl_label b)) seen then b :: acc else acc)
  end.

(** `reachable/2`: the blocks [bs] without those no path from the first
    reaches (a Fail1 nothing came back to). *)
Definition reachable (bs : list block) : option (list block) :=
  match bs with
  | [] => None
  | b :: _ =>
      match reach (3 * len bs 0 + 3)%nat [bl_label b] (block_map bs) nm_empty with
      | Some seen => Some (keep_seen seen bs [])
      | None => None
      end
  end.

(** The term `goto(L)`, `branch(V, Yes, No)` or `ret(V)` of the ending
    [j]. *)
Definition ending_term (j : ending) : term :=
  match j with
  | Goto l => TApp "goto" [TAtom l]
  | Branch v y n => TApp "branch" [v; TAtom y; TAtom n]
  | Ret v => TApp "ret" [v]
  end.

(** The term `block(Label, [], Insts, Jump)` of the block [b]. *)
Definition block_term (b : block) : term :=
  TApp "block" [TAtom (bl_label b); TList []; TList (bl_insts b); ending_term (bl_jump b)].

(** The allocation `let(S, p, alloc(8), [const(8)])` of the slot
    [sl]. *)
Definition alloc_of (sl : term) : term :=
  TApp "let" [sl; TAtom "p"; TApp "alloc" [TInt 8]; TList [const 8]].

(** The parameters of every function rx.pl makes. *)
Definition params : list term :=
  [TApp "param" [TAtom "p"; tmp_named "subject"]; TApp "param" [TAtom "l"; tmp_named "length"];
   TApp "param" [TAtom "l"; tmp_named "start"]; TApp "param" [TAtom "p"; tmp_named "ovector"];
   TApp "param" [TAtom "p"; tmp_named "stack"]; TApp "param" [TAtom "l"; tmp_named "slimit"];
   TApp "param" [TAtom "l"; tmp_named "budget"]].

(** `regex_func/3`: the IR function [name] that matches the regex [r],
    with an entry block that allocates `steps` and every slot. Nothing
    where rx.pl fails or raises an error. *)
Definition regex_func (name : string) (r : re) : option term :=
  let s := top (re_ast r) (re_groups r) (re_start r) (mk_st 0 (Open "init" []) [] [] false) in
  if st_bad s then None
  else
    match st_cur s with
    | Open _ _ => None
    | Closed =>
        let blocks1 := rev_append (st_blocks s) [] in
        let sls := rev_append (st_slots s) [] in
        let allocs := map_tr alloc_of (tmp_named "steps" :: sls) in
        match reachable (mk_block "entry" allocs (Goto "init") :: blocks1) with
        | Some blocks =>
            Some (TApp "func" [TAtom name; TAtom "export"; TAtom "w"; TList params;
                               TList (map_tr block_term blocks)])
        | None => None
        end
    end.

(** * Writing terms as writeq does

    [writeq_parts] writes a term as SWI-Prolog's `writeq/1` does, for
    the terms that [writable] accepts: integers, atoms of ASCII
    characters, lists, and compounds that are not written with an
    operator. That covers every function rx.pl prints and every reason
    pcre2_rx_terms.h's terms can make it give. *)

(** Whether the code [n] is a lowercase ASCII letter. *)
Definition is_lower (n : nat) : bool := Nat.leb 97 n && Nat.leb n 122.

(** Whether the code [n] may follow the first letter of an unquoted
    atom: a letter, a digit or an underscore. *)
Definition is_alnum (n : nat) : bool :=
  is_lower n || (Nat.leb 65 n && Nat.leb n 90) || (Nat.leb 48 n && Nat.leb n 57) || Nat.eqb n 95.

(** The codes of Prolog's symbol characters, `#$&*+-./:<=>?@\^~`. *)
Definition symbol_codes : list nat :=
  [35; 36; 38; 42; 43; 45; 46; 47; 58; 60; 61; 62; 63; 64; 92; 94; 126]%nat.

(** Whether the code [n] is a symbol character. *)
Definition is_symbol (n : nat) : bool := existsb (Nat.eqb n) symbol_codes.

(** Whether the atom of the characters [cs] is written without quotes:
    a lowercase letter followed by letters, digits and underscores; a
    run of symbol characters that is not `.` and does not start with
    `/*`; or `!`, `;` or `{}`. *)
Definition bare (cs : list ascii) : bool :=
  match cs with
  | [] => false
  | c :: rest =>
      let n := IrText.code c in
      if is_lower n then forallb (fun c => is_alnum (IrText.code c)) rest
      else if is_symbol n then
        forallb (fun c => is_symbol (IrText.code c)) rest
        && negb (Nat.eqb n 46 && match rest with [] => true | _ => false end)
        && negb (Nat.eqb n 47 && match rest with d :: _ => Nat.eqb (IrText.code d) 42 | [] => false end)
      else
        match rest with
        | [] => Nat.eqb n 33 || Nat.eqb n 59
        | [d] => Nat.eqb n 123 && Nat.eqb (IrText.code d) 125
        | _ => false
        end
  end.

(** The hexadecimal digit [n], in upper case. *)
Definition hex_digit (n : nat) : ascii :=
  IrText.byte (if Nat.ltb n 10 then 48 + n else 55 + n)%nat.

(** The characters of [c] inside a quoted atom, last first, in front of
    [acc]: a quote or a backslash after a backslash, a control character
    as its escape, and any other character as itself. *)
Definition quoted_char (c : ascii) (acc : list ascii) : list ascii :=
  let n := IrText.code c in
  let bs := IrText.byte 92 in
  let esc (e : nat) := IrText.byte e :: bs :: acc in
  if Nat.eqb n 39 then esc 39%nat
  else if Nat.eqb n 92 then esc 92%nat
  else if Nat.eqb n 7 then esc 97%nat
  else if Nat.eqb n 8 then esc 98%nat
  else if Nat.eqb n 9 then esc 116%nat
  else if Nat.eqb n 10 then esc 110%nat
  else if Nat.eqb n 11 then esc 118%nat
  else if Nat.eqb n 12 then esc 102%nat
  else if Nat.eqb n 13 then esc 114%nat
  else if Nat.ltb n 32 || Nat.eqb n 127 then
    let hex := if Nat.ltb n 16 then [hex_digit n]
               else [hex_digit (Nat.modulo n 16); hex_digit (Nat.div n 16)] in
    bs :: app hex (IrText.byte 120 :: bs :: acc)
  else c :: acc.

(** The atom [a] as writeq writes it, quoted when it must be. *)
Definition atom_text (a : string) : string :=
  let cs := list_ascii_of_string a in
  if bare cs then a
  else
    let q := IrText.byte 39 in
    IrText.string_of_rev (q :: fold_left (fun acc c => quoted_char c acc) cs [q]).

(** Whether every character of [a] is ASCII. *)
Definition ascii_only (a : string) : bool :=
  forallb (fun c => Nat.ltb (IrText.code c) 128) (list_ascii_of_string a).

(** The names SWI-Prolog has as prefix operators, which make a
    compound of one argument be written as an operator. *)
Definition prefix_ops : list string :=
  ["$"; "+"; "-"; ":-"; "?-"; "\"; "\+"; "discontiguous"; "dynamic"; "initialization";
   "meta_predicate"; "module_transparent"; "multifile"; "public"; "table";
   "thread_initialization"; "thread_local"; "volatile"].

(** The names SWI-Prolog has as infix operators, which make a compound
    of two arguments be written as an operator. *)
Definition infix_ops : list string :=
  ["*"; "**"; "*->"; "+"; ","; "-"; "-->"; "->"; "."; "/"; "//"; "/\"; ":"; ":-"; ":<"; ":=";
   ";"; "<"; "<<"; "="; "=.."; "=:="; "=<"; "=="; "=>"; "=@="; "=\="; ">"; ">:<"; ">="; ">>";
   "@<"; "@=<"; "@>"; "@>="; "\/"; "\="; "\=="; "\=@="; "^"; "as"; "div"; "is"; "mod"; "rdiv";
   "rem"; "xor"; "|"].

(** Whether writeq writes the compound of the name [f] and the
    arguments [ts] in a form of its own rather than as `f(A1,...)`: with
    an operator, as `{A}`, as a list, as a variable for `'$VAR'(N)`, or
    with no arguments. *)
Definition special_compound (f : string) (ts : list term) : bool :=
  match ts with
  | [] => true
  | [_] => existsb (String.eqb f) prefix_ops || String.eqb f "{}" || String.eqb f "$VAR"
  | [_; _] => existsb (String.eqb f) infix_ops || String.eqb f "[|]"
  | _ => false
  end.

(** Whether [writeq_parts] writes [t] as writeq does: its atoms and
    names are ASCII and none of its compounds is special. *)
Fixpoint writable (t : term) : bool :=
  match t with
  | TInt _ => true
  | TAtom a => ascii_only a
  | TApp f ts =>
      ascii_only f && negb (special_compound f ts)
      && (fix all (ts : list term) : bool :=
            match ts with
            | [] => true
            | u :: ts' => writable u && all ts'
            end) ts
  | TList ts =>
      (fix all (ts : list term) : bool :=
         match ts with
         | [] => true
         | u :: ts' => writable u && all ts'
         end) ts
  end.

(** The parts of the text of [t] as writeq writes it, with no spaces,
    in front of [acc]. *)
Fixpoint writeq_parts (t : term) (acc : list string) : list string :=
  match t with
  | TInt n => Text.decimal n :: acc
  | TAtom a => atom_text a :: acc
  | TApp f ts =>
      atom_text f :: "("
        :: (fix elems (ts : list term) (acc : list string) : list string :=
              match ts with
              | [] => acc
              | [u] => writeq_parts u acc
              | u :: ts' => writeq_parts u ("," :: elems ts' acc)
              end) ts (")" :: acc)
  | TList ts =>
      "["
        :: (fix elems (ts : list term) (acc : list string) : list string :=
              match ts with
              | [] => acc
              | [u] => writeq_parts u acc
              | u :: ts' => writeq_parts u ("," :: elems ts' acc)
              end) ts ("]" :: acc)
  end.

(** The text of [t] as writeq writes it, when [writable] accepts it. *)
Definition writeq_text (t : term) : option string :=
  if writable t then Some (String.concat "" (writeq_parts t [])) else None.

(** * The driver *)

(** What rx.pl gives for one `rx(Name, Header, Bytes)` term: a function,
    which it prints with `writeq/1` and a full stop; an unsupported
    pattern, which it prints as the comment `% Name: unsupported: Why`
    with the texts of `write(Name)` and `writeq(Why)`; or a failure or
    an error, after which it prints nothing more. *)
Inductive outcome : Type :=
| Func (f : term)
| Unsupported (name why : string)
| Failed.

(** The text `write(Name)` writes for a pattern's name, an atom or an
    integer. *)
Definition name_text (name : term) : option string :=
  match name with
  | TAtom a => Some a
  | TInt n => Some (Text.decimal n)
  | _ => None
  end.

(** `rx_term/4`: the outcome of the term [t], with the opcode names
    [ops]. The function's name is `rx_Name`, which `atom_concat/3` makes
    before anything else, so a name that is not an atom or an integer
    fails at once. *)
Definition rx_term (ops t : term) : outcome :=
  match t with
  | TApp f [name; header; bytes] =>
      if String.eqb f "rx" then
        match name_text name with
        | None => Failed
        | Some nm =>
            match code_regex ops header bytes with
            | DOk r _ =>
                match regex_func (String.append "rx_" nm) r with
                | Some func => Func func
                | None => Failed
                end
            | DUnsup why =>
                match writeq_text why with
                | Some w => Unsupported nm w
                | None => Failed
                end
            | DFail | DErr => Failed
            end
        end
      else Failed
  | _ => Failed
  end.

(** `rx_terms/2`: the outcomes of the terms [ts], after those in [acc]
    (last first), up to the first failure. *)
Fixpoint rx_terms (ops : term) (ts : list term) (acc : list outcome) : list outcome :=
  match ts with
  | [] => rev_append acc []
  | t :: ts' =>
      match rx_term ops t with
      | Failed => rev_append (Failed :: acc) []
      | o => rx_terms ops ts' (o :: acc)
      end
  end.

(** The outcome of each pattern of a text of terms, [cs] being its
    bytes, as `rx_file/1` reads it: `ops(Ops)`, then the patterns up to
    the end or an `end_of_file`. The list ends at the first [Failed];
    it is only [Failed] when the text is not read or does not start
    with `ops(Ops)`. *)
Definition rx_outcomes (cs : list ascii) : list outcome :=
  match IrText.read_clauses cs with
  | Some (t :: ts) =>
      match arg1 "ops" t with
      | Some ops => rx_terms ops ts []
      | None => [Failed]
      end
  | _ => [Failed]
  end.

(** The line rx.pl prints for the function [f]. *)
Definition func_line (f : term) : string :=
  String.concat "" (writeq_parts f ["."; Text.nl]).

(** The lines rx.pl prints for the outcomes [os], after those in [acc]
    (last first), and whether it then succeeds: it stops at a failure.
    A function that [writable] refuses stops the lines too. *)
Fixpoint outcome_lines (os : list outcome) (acc : list string) : list string * bool :=
  match os with
  | [] => (rev_append acc [], true)
  | Func f :: os' =>
      if writable f then outcome_lines os' (func_line f :: acc) else (rev_append acc [], false)
  | Unsupported nm w :: os' =>
      outcome_lines os' (String.concat "" ["% "; nm; ": unsupported: "; w; Text.nl] :: acc)
  | Failed :: _ => (rev_append acc [], false)
  end.

(** What `rx_file/1` prints for the text of terms [cs], line by line,
    and whether it succeeds. *)
Definition rx_file_text (cs : list ascii) : list string * bool :=
  outcome_lines (rx_outcomes cs) [].
