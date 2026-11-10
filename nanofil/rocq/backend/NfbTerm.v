(** NFB, the bytecode of a nanofil module (docs/nfb.md), read and
    written at the level of Prolog [term]s: the Gallina twin of
    src/nfb.pl, which must write the very same words.

    As in nfb.pl, one table ([forms]) states every instruction: its
    opcode, its term as a [pat]tern with numbered holes, and the
    [field]s its words hold, each naming a hole. The writer matches
    an instruction against the patterns and writes the fields of the
    hole values; the reader reads the fields of the opcode's form and
    fills the holes of its pattern. A list of the term, such as a
    call's arguments or a phi's pairs, is written element by element,
    each element by a smaller pattern and its own fields.

    The words are integers below 2^32 ([Z]). The ids are as the
    document says: a temporary's is its place among first
    definitions, parameters first; a block's and a named local's
    their place in the stream. Without the NAMES section the reader
    names each by its id, an integer term. *)

From Stdlib Require Import String ZArith List Bool Ascii.
From Nanofil Require Import Term Maps Cfg.
From Backend Require Import Order.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** ## Words *)

(** 2^32, 2^64 and 2^96, hoisted so that extracted code does not
    rebuild them. *)
Definition two32 : Z := 4294967296.
Definition two64 : Z := 18446744073709551616.
Definition two96 : Z := 79228162514264337593543950336.

(** Whether n is a word, from 0 to 2^32 - 1. *)
Definition u32ok (n : Z) : bool := (0 <=? n) && (n <? two32).

(** Whether n is a signed 64-bit integer. *)
Definition i64ok (n : Z) : bool := (- (two64 / 2) <=? n) && (n <? two64 / 2).

(** Whether n is a signed 96-bit integer, what CONSTANTS can hold. *)
Definition wideok (n : Z) : bool := (- (two96 / 2) <=? n) && (n <? two96 / 2).

(** The signed 64-bit n as two words, low first, in two's complement. *)
Definition i64_words (n : Z) : list Z := let u := n mod two64 in [u mod two32; u / two32].

(** The signed 96-bit n as three words, low first. *)
Definition wide_words (n : Z) : list Z :=
  let u := n mod two96 in [u mod two32; (u / two32) mod two32; u / two64].

(** The integer two words, low first, stand for as a signed 64-bit one. *)
Definition i64_of (lo hi : Z) : Z :=
  let u := lo + hi * two32 in if u <? two64 / 2 then u else u - two64.

(** The integer three words stand for as a signed 96-bit one. *)
Definition wide_of (w0 w1 w2 : Z) : Z :=
  let u := w0 + w1 * two32 + w2 * two64 in if u <? two96 / 2 then u else u - two96.

(** 2^29: a constant from -2^29 to 2^29 - 1 is written inside its
    operand word. *)
Definition inline_bound : Z := 536870912.

(** Whether the constant n is written inline. *)
Definition inline (n : Z) : bool := (- inline_bound <=? n) && (n <? inline_bound).

(** ## Bytes *)

(** The bytes bs four to a word, low byte first, the last word padded
    with zero bytes. *)
Fixpoint pack (bs : list Z) : list Z :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: r => (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) :: pack r
  | [b0; b1; b2] => [b0 + b1 * 256 + b2 * 65536]
  | [b0; b1] => [b0 + b1 * 256]
  | [b0] => [b0]
  | [] => []
  end.

(** The four bytes of each word, low first. *)
Fixpoint unpack (ws : list Z) : list Z :=
  match ws with
  | [] => []
  | w :: ws' => (w mod 256) :: ((w / 256) mod 256) :: ((w / 65536) mod 256) :: (w / 16777216)
                :: unpack ws'
  end.

(** The length of bs, then bs packed: a string's or a `str` item's
    words. *)
Definition bytes_words (bs : list Z) : list Z := Z.of_nat (length bs) :: pack bs.

(** The bytes of the string s. *)
Definition string_bytes (s : string) : list Z :=
  map (fun c => Z.of_nat (nat_of_ascii c)) (list_ascii_of_string s).

(** The string of the bytes bs. *)
Definition bytes_string (bs : list Z) : string :=
  string_of_list_ascii (map (fun b => ascii_of_nat (Z.to_nat b)) bs).

(** The one-character atom of the code b, below 256, as the term
    reader makes it: one byte below 128, else two of UTF-8. *)
Definition code_char (b : Z) : term :=
  if b <? 128 then TAtom (String (ascii_of_nat (Z.to_nat b)) EmptyString)
  else TAtom (String (ascii_of_nat (Z.to_nat (192 + b / 64)))
                (String (ascii_of_nat (Z.to_nat (128 + b mod 64))) EmptyString)).

(** ## Small helpers *)

(** The arguments of t when it is the compound f with n arguments. *)
Definition app_args (f : string) (n : nat) (t : term) : option (list term) :=
  match t with
  | TApp g ts => if String.eqb f g && Nat.eqb n (length ts) then Some ts else None
  | _ => None
  end.

(** Whether t is the atom a. *)
Definition is_atom (a : string) (t : term) : bool :=
  match t with TAtom b => String.eqb a b | _ => false end.

(** The value of the string key s in the association list xs. *)
Fixpoint sassoc (s : string) (xs : list (string * Z)) : option Z :=
  match xs with
  | [] => None
  | (k, v) :: xs' => if String.eqb s k then Some v else sassoc s xs'
  end.

(** The key of the value z in the association list xs. *)
Fixpoint srassoc (z : Z) (xs : list (string * Z)) : option string :=
  match xs with
  | [] => None
  | (k, v) :: xs' => if Z.eqb z v then Some k else srassoc z xs'
  end.

(** Each element of xs through the partial f, or none if f fails on
    one. *)
Fixpoint mapo {X Y : Type} (f : X -> option Y) (xs : list X) : option (list Y) :=
  match xs with
  | [] => Some []
  | x :: xs' => let* y := f x in let* ys := mapo f xs' in Some (y :: ys)
  end.

(** The first n elements of xs and the rest, if xs has n. *)
Fixpoint take (n : nat) (xs : list Z) : option (list Z * list Z) :=
  match n with
  | O => Some ([], xs)
  | S n' => match xs with
            | [] => None
            | x :: xs' => let* p := take n' xs' in Some (x :: fst p, snd p)
            end
  end.

(** Whether xs has at least n elements; it looks at no more than n of
    them, so a reader can check a count against the words left in time
    proportional to the count, not to all the words. *)
Fixpoint at_least (n : nat) (xs : list Z) : bool :=
  match n with
  | O => true
  | S n' => match xs with [] => false | _ :: xs' => at_least n' xs' end
  end.

(** Insert x into the sorted list xs, by the order le; an x equal to
    an element (by eqb) is dropped. *)
Fixpoint insert_uniq {X : Type} (lt eqb : X -> X -> bool) (x : X) (xs : list X) : list X :=
  match xs with
  | [] => [x]
  | y :: ys => if eqb x y then xs else if lt x y then x :: xs else y :: insert_uniq lt eqb x ys
  end.

(** Merge two sorted lists without duplicates. *)
Fixpoint merge_uniq {X : Type} (lt eqb : X -> X -> bool) (xs : list X) : list X -> list X :=
  fix go ys :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xs', y :: ys' =>
        if eqb x y then x :: merge_uniq lt eqb xs' ys'
        else if lt x y then x :: merge_uniq lt eqb xs' ys
        else y :: go ys'
    end.

(** The runs of one element each, for [sort_uniq]. *)
Definition singletons {X : Type} (xs : list X) : list (list X) := map (fun x => [x]) xs.

(** Merge the runs rs in pairs. *)
Fixpoint merge_pairs {X : Type} (lt eqb : X -> X -> bool) (rs : list (list X)) : list (list X) :=
  match rs with
  | r1 :: r2 :: rs' => merge_uniq lt eqb r1 r2 :: merge_pairs lt eqb rs'
  | _ => rs
  end.

(** Merge the runs until one is left, at most fuel rounds. *)
Fixpoint merge_all {X : Type} (lt eqb : X -> X -> bool) (fuel : nat) (rs : list (list X)) : list X :=
  match rs with
  | [] => []
  | [r] => r
  | _ => match fuel with
         | O => concat rs
         | S f => merge_all lt eqb f (merge_pairs lt eqb rs)
         end
  end.

(** xs sorted by lt, each element once, as Prolog's sort/2 does with
    the order lt. *)
Definition sort_uniq {X : Type} (lt eqb : X -> X -> bool) (xs : list X) : list X :=
  merge_all lt eqb (length xs) (singletons xs).

(** The byte order of strings. *)
Definition str_lt (a b : string) : bool :=
  match atom_compare a b with Datatypes.Lt => true | _ => false end.

(** ## The enumerations *)

(** The tables of codes a field can hold, each a list of atoms and
    their words (nfb.pl's nfb_code/3). *)
Inductive enum : Type :=
| EClass | EWidth | ELoad | EExt | ECas | ECond | ERights | EBound | ESetjmp
| EEffect | EFlight | EMnemonic | ERegister.

Definition class_codes : list (string * Z) :=
  [("w", 1); ("l", 2); ("s", 3); ("d", 4); ("x", 5); ("p", 6); ("a", 7); ("f", 8)].
Definition width_codes : list (string * Z) :=
  [("w", 1); ("l", 2); ("s", 3); ("d", 4); ("x", 5); ("p", 6); ("b", 9); ("h", 10)].
Definition narrow_codes : list (string * Z) :=
  [("sw", 16); ("uw", 17); ("sh", 18); ("uh", 19); ("sb", 20); ("ub", 21)].
Definition load_codes : list (string * Z) :=
  [("l", 2); ("s", 3); ("d", 4); ("x", 5); ("p", 6)] ++ narrow_codes.
Definition ext_codes : list (string * Z) := [("s", 3); ("d", 4)] ++ narrow_codes.
Definition cas_codes : list (string * Z) := [("l", 2); ("p", 6)] ++ narrow_codes.
Definition cond_codes : list (string * Z) :=
  [("eq", 0); ("ne", 1); ("sle", 2); ("slt", 3); ("sge", 4); ("sgt", 5); ("ule", 6);
   ("ult", 7); ("uge", 8); ("ugt", 9); ("le", 10); ("lt", 11); ("ge", 12); ("gt", 13);
   ("o", 14); ("uo", 15)].
Definition rights_codes : list (string * Z) := [("read", 0); ("write", 1)].
Definition bound_codes : list (string * Z) := [("upper", 0); ("lower", 1)].
Definition setjmp_codes : list (string * Z) := [("setjmp", 0); ("_setjmp", 1); ("sigsetjmp", 2)].
Definition effect_codes : list (string * Z) :=
  [("aux_read", 0); ("lower_resolve", 1); ("address_read", 2); ("aux_ensure", 3);
   ("lower_barrier", 4); ("rooted_reload", 5); ("lower_write", 6); ("address_write", 7);
   ("atomic_read", 8); ("atomic_write", 9); ("atomic_cas", 10)].
Definition flight_codes : list (string * Z) := [("copy", 0); ("add", 1); ("sub", 2)].
Definition mnemonic_codes : list (string * Z) :=
  [("cpuid", 0); ("xgetbv", 1); ("rdtsc", 2); ("rdtscp", 3); ("lfence", 4); ("sfence", 5);
   ("pause", 6)].
Definition register_codes : list (string * Z) := [("a", 0); ("b", 1); ("c", 2); ("d", 3)].
Definition func_linkage_codes : list (string * Z) := [("export", 0); ("local", 1); ("weak", 2)].
Definition alias_linkage_codes : list (string * Z) := [("export", 0); ("weak", 2)].

(** The table of the enumeration e. *)
Definition codes (e : enum) : list (string * Z) :=
  match e with
  | EClass => class_codes | EWidth => width_codes | ELoad => load_codes
  | EExt => ext_codes | ECas => cas_codes | ECond => cond_codes
  | ERights => rights_codes | EBound => bound_codes | ESetjmp => setjmp_codes
  | EEffect => effect_codes | EFlight => flight_codes | EMnemonic => mnemonic_codes
  | ERegister => register_codes
  end.

(** The word of the atom t in the enumeration e. *)
Definition enc_code (e : enum) (t : term) : option Z :=
  match t with TAtom s => sassoc s (codes e) | _ => None end.

(** The atom of the word z in the enumeration e. *)
Definition dec_code (e : enum) (z : Z) : option term :=
  let* s := srassoc z (codes e) in Some (TAtom s).

(** ## The table of instructions *)

(** A pattern of a term: a numbered hole, an atom, a compound, or a
    list of a fixed length. *)
Inductive pat : Type :=
| PH (i : nat)
| PA (s : string)
| PC (f : string) (ps : list pat)
| PL (ps : list pat).

(** The values of a pattern's holes. *)
Definition env := list (nat * term).

(** The value of the hole i. *)
Fixpoint env_get (i : nat) (e : env) : option term :=
  match e with
  | [] => None
  | (j, t) :: e' => if Nat.eqb i j then Some t else env_get i e'
  end.

(** The holes' values that make the pattern p the term t, added to e. *)
Fixpoint match_pat (p : pat) (t : term) (e : env) {struct p} : option env :=
  match p with
  | PH i => Some ((i, t) :: e)
  | PA s => if is_atom s t then Some e else None
  | PC f ps =>
      match t with
      | TApp g ts =>
          if String.eqb f g then
            (fix go (ps : list pat) (ts : list term) (e : env) : option env :=
               match ps, ts with
               | [], [] => Some e
               | p :: ps', t :: ts' => let* e' := match_pat p t e in go ps' ts' e'
               | _, _ => None
               end) ps ts e
          else None
      | _ => None
      end
  | PL ps =>
      match t with
      | TList ts =>
          (fix go (ps : list pat) (ts : list term) (e : env) : option env :=
             match ps, ts with
             | [], [] => Some e
             | p :: ps', t :: ts' => let* e' := match_pat p t e in go ps' ts' e'
             | _, _ => None
             end) ps ts e
      | _ => None
      end
  end.

(** The term of the pattern p with its holes filled from e. *)
Fixpoint fill_pat (p : pat) (e : env) {struct p} : option term :=
  match p with
  | PH i => env_get i e
  | PA s => Some (TAtom s)
  | PC f ps =>
      let* ts := (fix go (ps : list pat) : option (list term) :=
                    match ps with
                    | [] => Some []
                    | p :: ps' => let* t := fill_pat p e in let* ts := go ps' in Some (t :: ts)
                    end) ps in
      Some (TApp f ts)
  | PL ps =>
      let* ts := (fix go (ps : list pat) : option (list term) :=
                    match ps with
                    | [] => Some []
                    | p :: ps' => let* t := fill_pat p e in let* ts := go ps' in Some (t :: ts)
                    end) ps in
      Some (TList ts)
  end.

(** A field of an instruction, holding the value of one hole:

    | Field | Words |
    |---|---|
    | [FDef] | none: the temporary takes the next id |
    | [FClass], [FEnum] | one code |
    | [FU32], [FI64] | one word, or two, signed |
    | [FOpnd] | an operand word |
    | [FLabel], [FTarget] | a block index; a target's shifted, bit 0 for `poll` |
    | [FLocal], [FLocalDef] | a local's id; the definition writes none |
    | [FStr] | a STRINGS id |
    | [FResult] | a call's result word, defining its temporaries |
    | [FLower] | 0 for `none`, or 1 and the operand of `lower(P)` |
    | [FFlightArg] | 1 and the operand of `address(P)`, or 0 and a value's |
    | [FCount], [FRest] | a list: its length then its elements, or its elements to the end |

    An element of a list is a smaller pattern with its own holes and
    fields. *)
Inductive field : Type :=
| FDef (i : nat) | FClass (i : nat) | FEnum (e : enum) (i : nat) | FU32 (i : nat) | FI64 (i : nat)
| FOpnd (i : nat) | FLabel (i : nat) | FTarget (i : nat) | FLocal (i : nat) | FLocalDef (i : nat)
| FStr (i : nat) | FResult (i : nat) | FLower (i : nat) | FFlightArg (i : nat).

(** A field, or a list of elements. *)
Inductive lfield : Type :=
| FOne (f : field)
| FCount (i : nat) (el : pat) (fs : list field)
| FRest (i : nat) (el : pat) (fs : list field).

(** An instruction's form: its opcode, its pattern and its fields. *)
Record form : Type := mkForm { f_code : Z; f_pat : pat; f_fields : list lfield }.

(** The pattern of a `let(tmp(D), K, Op, Args)`, D hole 0 and K hole
    1. *)
Definition plet (o : pat) (args : list pat) : pat :=
  PC "let" [PC "tmp" [PH 0]; PH 1; o; PL args].

(** The fields of a `let`'s definition and class, then fs. *)
Definition flet (fs : list field) : list lfield := map FOne (FDef 0 :: FClass 1 :: fs).

Definition binary_ops : list string :=
  ["add"; "sub"; "mul"; "div"; "udiv"; "rem"; "urem"; "and"; "or"; "xor"; "sar"; "shr"; "shl"].
Definition unary_ops : list string :=
  ["neg"; "copy"; "cast"; "truncd"; "truncx"; "ptoi"; "itop"; "stosi"; "stoui"; "dtosi";
   "dtoui"; "xtosi"; "xtoui"; "swtof"; "uwtof"; "sltof"; "ultof"].

(** The forms of the ops named ns, from the opcode c up, each made by
    mk. *)
Fixpoint op_forms (c : Z) (ns : list string) (mk : Z -> string -> form) : list form :=
  match ns with [] => [] | n :: ns' => mk c n :: op_forms (c + 1) ns' mk end.

(** The form of a `let` of a range op f: `f(Lo, Hi, Rights, Align)`
    on the operands of holes 6 on. *)
Definition range_form (c : Z) (f : string) (n : nat) : form :=
  mkForm c (plet (PC f [PH 2; PH 3; PH 4; PH 5]) (map PH (seq 6 n)))
    (flet ([FI64 2; FI64 3; FEnum ERights 4; FU32 5] ++ map FOpnd (seq 6 n))).

(** A call's or raw call's form. *)
Definition call_form (c : Z) (f : string) : form :=
  mkForm c (PC f [PH 0; PH 1; PH 2])
    [FOne (FResult 0); FOne (FOpnd 1); FRest 2 (PC "arg" [PH 0; PH 1]) [FClass 0; FOpnd 1]].

(** Every form, in nfb.pl's order. *)
Definition forms : list form :=
  [mkForm 8 (PC "phi" [PC "tmp" [PH 0]; PH 1; PH 2])
     [FOne (FDef 0); FOne (FClass 1); FRest 2 (PC "-" [PH 0; PH 1]) [FLabel 0; FOpnd 1]]]
  ++ op_forms 16 binary_ops (fun c n => mkForm c (plet (PA n) [PH 2; PH 3]) (flet [FOpnd 2; FOpnd 3]))
  ++ op_forms 32 unary_ops (fun c n => mkForm c (plet (PA n) [PH 2]) (flet [FOpnd 2]))
  ++ [mkForm 56 (plet (PC "cmp" [PH 2; PH 3]) [PH 4; PH 5])
        (flet [FEnum ECond 2; FClass 3; FOpnd 4; FOpnd 5]);
      mkForm 57 (plet (PC "ext" [PH 2]) [PH 3]) (flet [FEnum EExt 2; FOpnd 3]);
      mkForm 58 (plet (PC "load" [PH 2]) [PH 3]) (flet [FEnum ELoad 2; FOpnd 3]);
      mkForm 59 (plet (PC "alloc" [PH 2]) [PH 3]) (flet [FU32 2; FOpnd 3]);
      mkForm 60 (plet (PA "va_args") [PH 2]) (flet [FOpnd 2]);
      mkForm 61 (plet (PA "va_arg") [PH 2]) (flet [FOpnd 2]);
      mkForm 62 (plet (PC "setjmp" [PH 2]) [PH 3; PH 4]) (flet [FEnum ESetjmp 2; FOpnd 3; FOpnd 4]);
      mkForm 63 (plet (PC "atomic_load" [PA "p"]) [PH 2]) (flet [FOpnd 2]);
      mkForm 64 (plet (PC "cas" [PH 2]) [PH 3; PH 4; PH 5])
        (flet [FEnum ECas 2; FOpnd 3; FOpnd 4; FOpnd 5]);
      range_form 80 "check" 1;
      mkForm 81 (plet (PC "check_ahead" [PH 2; PH 3; PH 4; PH 5; PH 6]) [PH 7])
        (flet [FI64 2; FI64 3; FEnum ERights 4; FU32 5; FI64 6; FOpnd 7]);
      range_form 82 "renew" 2;
      range_form 83 "renew_hull" 3;
      mkForm 84 (plet (PC "half_check" [PH 2; PH 3; PH 4; PH 5; PH 6]) [PH 7; PH 8])
        (flet [FEnum EBound 2; FI64 3; FI64 4; FEnum ERights 5; FU32 6; FOpnd 7; FOpnd 8]);
      mkForm 85 (plet (PC "span_test" [PH 2; PH 3]) [PH 4]) (flet [FI64 2; FI64 3; FOpnd 4]);
      range_form 86 "renew_if" 2;
      mkForm 87 (plet (PC "limit" [PH 2]) [PH 3]) (flet [FU32 2; FOpnd 3]);
      range_form 88 "check_limit" 2;
      mkForm 89 (plet (PC "check_local" [PH 2; PH 3; PH 4; PH 5; PH 6]) [])
        (flet [FLocal 2; FI64 3; FI64 4; FEnum ERights 5; FU32 6]);
      mkForm 90 (plet (PA "check_function") [PH 2]) (flet [FOpnd 2]);
      mkForm 91 (plet (PC "raw_load" [PH 2; PH 3]) [PH 4]) (flet [FEnum ELoad 2; FI64 3; FOpnd 4]);
      mkForm 92 (plet (PC "raw_load_pointer" [PH 2; PH 3]) [PH 4])
        (flet [FI64 2; FOpnd 4] ++ [FRest 3 (PH 0) [FEnum EEffect 0]]);
      mkForm 93 (plet (PC "raw_cas" [PH 2; PH 3]) [PH 4; PH 5; PH 6])
        (flet [FEnum ECas 2; FI64 3; FOpnd 4; FOpnd 5; FOpnd 6]);
      mkForm 96 (PC "store" [PH 0; PH 1; PH 2]) (map FOne [FEnum EWidth 0; FOpnd 1; FOpnd 2]);
      mkForm 97 (PC "atomic_store" [PA "p"; PH 0; PH 1]) (map FOne [FOpnd 0; FOpnd 1]);
      mkForm 98 (PA "fence") [];
      mkForm 99 (PC "access" [PH 0; PH 1; PH 2; PH 3])
        (map FOne [FEnum ERights 0; FU32 2; FU32 3; FOpnd 1]);
      mkForm 100 (PC "local_alloc" [PH 0; PH 1]) (map FOne [FLocalDef 0; FI64 1]);
      mkForm 101 (PC "local_load" [PC "tmp" [PH 0]; PH 1; PH 2; PH 3; PH 4])
        (map FOne [FDef 0; FClass 1; FEnum ELoad 2; FLocal 3; FI64 4]);
      mkForm 102 (PC "local_store" [PH 0; PH 1; PH 2; PH 3])
        (map FOne [FEnum EWidth 0; FLocal 2; FI64 3; FOpnd 1]);
      call_form 103 "call";
      mkForm 104 (PC "asm_fixed" [PH 0; PH 1; PH 2])
        [FOne (FEnum EMnemonic 0);
         FCount 1 (PC "-" [PH 0; PH 1]) [FEnum ERegister 0; FOpnd 1];
         FRest 2 (PC "-" [PH 0; PC "tmp" [PH 1]]) [FEnum ERegister 0; FDef 1]];
      mkForm 105 (PC "loc" [PH 0; PH 1]) (map FOne [FStr 0; FU32 1]);
      mkForm 112 (PC "touch" [PH 0]) [FOne (FOpnd 0)];
      call_form 113 "raw_call";
      mkForm 114 (PC "flight" [PC "tmp" [PH 0]; PH 1; PH 2; PH 3])
        [FOne (FDef 0); FOne (FEnum EFlight 1); FOne (FLower 3); FRest 2 (PH 0) [FFlightArg 0]];
      mkForm 115 (PC "raw_store" [PH 0; PH 1; PH 2; PH 3])
        (map FOne [FEnum EWidth 0; FI64 1; FOpnd 2; FOpnd 3]);
      mkForm 116 (PC "raw_store_pointer" [PH 0; PH 1; PH 2; PH 3])
        [FOne (FI64 0); FOne (FOpnd 1); FOne (FOpnd 2); FRest 3 (PH 0) [FEnum EEffect 0]];
      mkForm 128 (PC "goto" [PH 0]) [FOne (FTarget 0)];
      mkForm 129 (PC "branch" [PH 0; PH 1; PH 2]) (map FOne [FOpnd 0; FTarget 1; FTarget 2]);
      mkForm 130 (PC "ret" [PH 0]) [FOne (FOpnd 0)];
      mkForm 131 (PC "rets" [PH 0]) [FRest 0 (PH 0) [FOpnd 0]];
      mkForm 132 (PA "ret") [];
      mkForm 133 (PA "unreachable") []].

(** The opcode that prefixes an instruction defining a temporary
    again. *)
Definition rebind_code : Z := 1.

(** The group of an opcode: 0 a phi, 2 a jump, 1 any other. *)
Definition group (c : Z) : Z := if Z.eqb c 8 then 0 else if 128 <=? c then 2 else 1.

(** The first form whose pattern t matches, with the holes' values. *)
Fixpoint find_form (fs : list form) (t : term) : option (form * env) :=
  match fs with
  | [] => None
  | f :: fs' => match match_pat (f_pat f) t [] with
                | Some e => Some (f, e)
                | None => find_form fs' t
                end
  end.

(** The form of the opcode c. *)
Fixpoint form_of_code (fs : list form) (c : Z) : option form :=
  match fs with
  | [] => None
  | f :: fs' => if Z.eqb (f_code f) c then Some f else form_of_code fs' c
  end.

(** ## What an instruction holds *)

(** The temporaries a call's result term r defines. *)
Definition result_defs (r : term) : option (list term) :=
  if is_atom "void" r then Some [] else
  match app_args "result" 2 r with
  | Some [d; _] => let* xs := app_args "tmp" 1 d in Some xs
  | _ =>
      let* xs := app_args "tuple" 1 r in
      match xs with
      | [TList rs] =>
          mapo (fun r => let* ys := app_args "result" 2 r in
                         match ys with
                         | [d; _] => let* zs := app_args "tmp" 1 d in
                                     match zs with [z] => Some z | _ => None end
                         | _ => None
                         end) rs
      | _ => None
      end
  end.

(** What a field holds besides words: the temporaries it defines, the
    symbols, constants and files it names. *)
Record parts : Type := mkParts { p_defs : list term; p_globals : list term; p_consts : list Z;
                                 p_files : list term }.

Definition no_parts : parts := mkParts [] [] [] [].
Definition parts_app (a b : parts) : parts :=
  mkParts (p_defs a ++ p_defs b) (p_globals a ++ p_globals b) (p_consts a ++ p_consts b)
    (p_files a ++ p_files b).

(** The symbols and constants a value names. *)
Definition value_parts (v : term) : parts :=
  match v with
  | TApp f [x] =>
      if String.eqb f "global" then mkParts [] [x] [] []
      else if String.eqb f "const" then
        match x with TInt n => mkParts [] [] [n] [] | _ => no_parts end
      else no_parts
  | _ => no_parts
  end.

(** What the field f holds, the holes' values e. *)
Definition field_parts (e : env) (f : field) : option parts :=
  match f with
  | FDef i => let* d := env_get i e in Some (mkParts [d] [] [] [])
  | FResult i => let* r := env_get i e in let* ds := result_defs r in Some (mkParts ds [] [] [])
  | FOpnd i => let* v := env_get i e in Some (value_parts v)
  | FStr i => let* a := env_get i e in Some (mkParts [] [] [] [a])
  | FLower i =>
      let* t := env_get i e in
      match app_args "lower" 1 t with Some [v] => Some (value_parts v) | _ => Some no_parts end
  | FFlightArg i =>
      let* t := env_get i e in
      match app_args "address" 1 t with Some [v] => Some (value_parts v) | _ => Some (value_parts t) end
  | _ => Some no_parts
  end.

(** What the fields fs hold. *)
Definition fields_parts (e : env) (fs : list field) : option parts :=
  let* ps := mapo (field_parts e) fs in Some (fold_right parts_app no_parts ps).

(** What the elements ts of a list hold, each the pattern el. *)
Definition elems_parts (el : pat) (fs : list field) (ts : list term) : option parts :=
  let* ps := mapo (fun t => let* e := match_pat el t [] in fields_parts e fs) ts in
  Some (fold_right parts_app no_parts ps).

(** What an instruction of the form whose fields are fs holds. *)
Definition inst_parts (e : env) (fs : list lfield) : option parts :=
  let* ps := mapo (fun lf =>
                     match lf with
                     | FOne f => field_parts e f
                     | FCount i el fs' | FRest i el fs' =>
                         let* t := env_get i e in
                         match t with TList ts => elems_parts el fs' ts | _ => None end
                     end) fs in
  Some (fold_right parts_app no_parts ps).

(** What the instruction, phi or jump t holds. *)
Definition term_parts (t : term) : option parts :=
  let* fe := find_form forms t in inst_parts (snd fe) (f_fields (fst fe)).

(** ## Writing an instruction *)

(** The tables a function's instructions are written with: the ids of
    its temporaries, labels and locals, and of the module's symbols,
    strings and wide constants. *)
Record wtab : Type := mkWtab {
  w_syms : nmap Z; w_strs : nmap Z; w_consts : ZMap.t Z;
  w_temps : nmap Z; w_labels : nmap Z; w_locals : nmap Z
}.

(** The words a field writes, the temporaries it defines, the ids of
    the temporaries it reads, and its targets' block indices with
    their poll bits. *)
Record wout : Type := mkWout { o_words : list Z; o_defs : list term; o_uses : list Z;
                               o_targets : list (Z * Z) }.

Definition wnil : wout := mkWout [] [] [] [].
Definition wapp (a b : wout) : wout :=
  mkWout (o_words a ++ o_words b) (o_defs a ++ o_defs b) (o_uses a ++ o_uses b)
    (o_targets a ++ o_targets b).
Definition wwords (ws : list Z) : wout := mkWout ws [] [] [].

(** The word of the constant n: inline, or a CONSTANTS index. *)
Definition const_word (c : ZMap.t Z) (n : Z) : option Z :=
  if inline n then Some ((n mod (2 * inline_bound)) * 4 + 1)
  else let* i := ZMap.find n c in Some (i * 4 + 2).

(** The operand word of the value v. *)
Definition opnd_out (w : wtab) (v : term) : option wout :=
  match v with
  | TApp f [x] =>
      if String.eqb f "tmp" then
        let* i := nm_find x (w_temps w) in Some (mkWout [i * 4] [] [i] [])
      else if String.eqb f "const" then
        match x with TInt n => let* z := const_word (w_consts w) n in Some (wwords [z]) | _ => None end
      else if String.eqb f "global" then
        let* i := nm_find x (w_syms w) in Some (wwords [i * 4 + 3])
      else None
  | _ => None
  end.

(** The word of a call's result term r, and what it defines. *)
Definition result_out (r : term) : option wout :=
  let* ds := result_defs r in
  if is_atom "void" r then Some (mkWout [0] [] [] []) else
  match app_args "result" 2 r with
  | Some [_; k] => let* c := enc_code EClass k in Some (mkWout [c] ds [] [])
  | _ =>
      match app_args "tuple" 1 r with
      | Some [TList [r1; r2]] =>
          match app_args "result" 2 r1, app_args "result" 2 r2 with
          | Some [_; k1], Some [_; k2] =>
              let* c1 := enc_code EClass k1 in let* c2 := enc_code EClass k2 in
              Some (mkWout [256 + 16 * c1 + c2] ds [] [])
          | _, _ => None
          end
      | _ => None
      end
  end.

(** The words of the field f, the holes' values e. *)
Definition field_out (w : wtab) (e : env) (f : field) : option wout :=
  match f with
  | FDef i => let* d := env_get i e in Some (mkWout [] [d] [] [])
  | FClass i => let* t := env_get i e in let* z := enc_code EClass t in Some (wwords [z])
  | FEnum en i => let* t := env_get i e in let* z := enc_code en t in Some (wwords [z])
  | FU32 i =>
      let* t := env_get i e in
      match t with TInt n => if u32ok n then Some (wwords [n]) else None | _ => None end
  | FI64 i =>
      let* t := env_get i e in
      match t with TInt n => if i64ok n then Some (wwords (i64_words n)) else None | _ => None end
  | FOpnd i => let* v := env_get i e in opnd_out w v
  | FLabel i => let* l := env_get i e in let* z := nm_find l (w_labels w) in Some (wwords [z])
  | FTarget i =>
      let* t := env_get i e in
      match app_args "poll" 1 t with
      | Some [l] => let* z := nm_find l (w_labels w) in Some (mkWout [z * 2 + 1] [] [] [(z, 1)])
      | _ => let* z := nm_find t (w_labels w) in Some (mkWout [z * 2] [] [] [(z, 0)])
      end
  | FLocal i => let* x := env_get i e in let* z := nm_find x (w_locals w) in Some (wwords [z])
  | FLocalDef _ => Some wnil
  | FStr i =>
      let* a := env_get i e in
      match a with TAtom _ => let* z := nm_find a (w_strs w) in Some (wwords [z]) | _ => None end
  | FResult i => let* r := env_get i e in result_out r
  | FLower i =>
      let* t := env_get i e in
      if is_atom "none" t then Some (wwords [0]) else
      match app_args "lower" 1 t with
      | Some [v] => let* o := opnd_out w v in Some (wapp (wwords [1]) o)
      | _ => None
      end
  | FFlightArg i =>
      let* t := env_get i e in
      match app_args "address" 1 t with
      | Some [v] => let* o := opnd_out w v in Some (wapp (wwords [1]) o)
      | _ => let* o := opnd_out w t in Some (wapp (wwords [0]) o)
      end
  end.

(** The words of the fields fs. *)
Fixpoint fields_out (w : wtab) (e : env) (fs : list field) : option wout :=
  match fs with
  | [] => Some wnil
  | f :: fs' => let* a := field_out w e f in let* b := fields_out w e fs' in Some (wapp a b)
  end.

(** The words of the elements ts of a list, each the pattern el. *)
Fixpoint elems_out (w : wtab) (el : pat) (fs : list field) (ts : list term) : option wout :=
  match ts with
  | [] => Some wnil
  | t :: ts' =>
      let* e := match_pat el t [] in let* a := fields_out w e fs in
      let* b := elems_out w el fs ts' in Some (wapp a b)
  end.

(** The words of an instruction's fields fs. *)
Fixpoint lfields_out (w : wtab) (e : env) (fs : list lfield) : option wout :=
  match fs with
  | [] => Some wnil
  | lf :: fs' =>
      let* a := match lf with
                | FOne f => field_out w e f
                | FCount i el fs1 =>
                    let* t := env_get i e in
                    match t with
                    | TList ts => let* o := elems_out w el fs1 ts in
                                  Some (wapp (wwords [Z.of_nat (length ts)]) o)
                    | _ => None
                    end
                | FRest i el fs1 =>
                    let* t := env_get i e in
                    match t with TList ts => elems_out w el fs1 ts | _ => None end
                end in
      let* b := lfields_out w e fs' in Some (wapp a b)
  end.

(** ## Reading an instruction *)

(** The tables a function's instructions are read with: names by id. *)
Record rtab : Type := mkRtab {
  r_syms : ZMap.t term; r_strs : ZMap.t term; r_consts : ZMap.t Z;
  r_temps : ZMap.t term; r_labels : ZMap.t term; r_locals : ZMap.t term
}.

(** The reader's state within an instruction: the words left, the
    rebind words left (none when there is no rebind prefix), the next
    temporary id and the next local id. *)
Record rst : Type := mkRst { s_words : list Z; s_rebinds : option (list Z); s_next : Z; s_local : Z }.

(** The next word. *)
Definition next_word (s : rst) : option (Z * rst) :=
  match s_words s with
  | [] => None
  | x :: xs => Some (x, mkRst xs (s_rebinds s) (s_next s) (s_local s))
  end.

(** The constant of the word z, an inline or CONSTANTS one. *)
Definition const_of (r : rtab) (z : Z) : option Z :=
  if Z.eqb (z mod 4) 1 then
    let p := z / 4 in Some (if p <? inline_bound then p else p - 2 * inline_bound)
  else if Z.eqb (z mod 4) 2 then ZMap.find (z / 4) (r_consts r)
  else None.

(** The value of the operand word z. *)
Definition value_of (r : rtab) (z : Z) : option term :=
  let tag := z mod 4 in
  if Z.eqb tag 0 then let* n := ZMap.find (z / 4) (r_temps r) in Some (TApp "tmp" [n])
  else if Z.eqb tag 3 then let* s := ZMap.find (z / 4) (r_syms r) in Some (TApp "global" [s])
  else let* n := const_of r z in Some (TApp "const" [TInt n]).

(** The name the next definition takes: the next id's, or the rebound
    id's. *)
Definition def_name (r : rtab) (s : rst) : option (term * rst) :=
  let take_id (w : Z) (rb : option (list Z)) :=
    if Z.eqb w 0 then
      let* n := ZMap.find (s_next s) (r_temps r) in
      Some (n, mkRst (s_words s) rb (s_next s + 1) (s_local s))
    else if w - 1 <? s_next s then
      let* n := ZMap.find (w - 1) (r_temps r) in Some (n, mkRst (s_words s) rb (s_next s) (s_local s))
    else None in
  match s_rebinds s with
  | None => take_id 0 None
  | Some (w :: ws) => take_id w (Some ws)
  | Some [] => None
  end.

(** The call result term of the word z, its temporaries named in turn. *)
Definition read_result (r : rtab) (z : Z) (s : rst) : option (term * rst) :=
  if Z.eqb z 0 then Some (TAtom "void", s)
  else if 256 <=? z then
    let* k1 := dec_code EClass ((z - 256) / 16) in let* k2 := dec_code EClass (z mod 16) in
    if (z - 256) / 16 <? 16 then
      let* p1 := def_name r s in let* p2 := def_name r (snd p1) in
      Some (TApp "tuple" [TList [TApp "result" [TApp "tmp" [fst p1]; k1];
                                 TApp "result" [TApp "tmp" [fst p2]; k2]]], snd p2)
    else None
  else
    let* k := dec_code EClass z in let* p := def_name r s in
    Some (TApp "result" [TApp "tmp" [fst p]; k], snd p).

(** Read the field f into the hole it names. *)
Definition read_field (r : rtab) (f : field) (e : env) (s : rst) : option (env * rst) :=
  match f with
  | FDef i => let* p := def_name r s in Some ((i, fst p) :: e, snd p)
  | FClass i => let* p := next_word s in let* t := dec_code EClass (fst p) in Some ((i, t) :: e, snd p)
  | FEnum en i => let* p := next_word s in let* t := dec_code en (fst p) in Some ((i, t) :: e, snd p)
  | FU32 i => let* p := next_word s in Some ((i, TInt (fst p)) :: e, snd p)
  | FI64 i =>
      let* p := next_word s in let* q := next_word (snd p) in
      Some ((i, TInt (i64_of (fst p) (fst q))) :: e, snd q)
  | FOpnd i => let* p := next_word s in let* v := value_of r (fst p) in Some ((i, v) :: e, snd p)
  | FLabel i => let* p := next_word s in let* l := ZMap.find (fst p) (r_labels r) in Some ((i, l) :: e, snd p)
  | FTarget i =>
      let* p := next_word s in let* l := ZMap.find (fst p / 2) (r_labels r) in
      Some ((i, if Z.eqb (fst p mod 2) 1 then TApp "poll" [l] else l) :: e, snd p)
  | FLocal i => let* p := next_word s in let* x := ZMap.find (fst p) (r_locals r) in Some ((i, x) :: e, snd p)
  | FLocalDef i =>
      let* x := ZMap.find (s_local s) (r_locals r) in
      Some ((i, x) :: e, mkRst (s_words s) (s_rebinds s) (s_next s) (s_local s + 1))
  | FStr i => let* p := next_word s in let* a := ZMap.find (fst p) (r_strs r) in Some ((i, a) :: e, snd p)
  | FResult i => let* p := next_word s in let* q := read_result r (fst p) (snd p) in Some ((i, fst q) :: e, snd q)
  | FLower i =>
      let* p := next_word s in
      if Z.eqb (fst p) 0 then Some ((i, TAtom "none") :: e, snd p)
      else if Z.eqb (fst p) 1 then
        let* q := next_word (snd p) in let* v := value_of r (fst q) in
        Some ((i, TApp "lower" [v]) :: e, snd q)
      else None
  | FFlightArg i =>
      let* p := next_word s in let* q := next_word (snd p) in let* v := value_of r (fst q) in
      if Z.eqb (fst p) 1 then Some ((i, TApp "address" [v]) :: e, snd q)
      else if Z.eqb (fst p) 0 then Some ((i, v) :: e, snd q)
      else None
  end.

(** Read the fields fs. *)
Fixpoint read_fields (r : rtab) (fs : list field) (e : env) (s : rst) : option (env * rst) :=
  match fs with
  | [] => Some (e, s)
  | f :: fs' => let* p := read_field r f e s in read_fields r fs' (fst p) (snd p)
  end.

(** Read n elements of the pattern el. *)
Fixpoint read_count (r : rtab) (el : pat) (fs : list field) (n : nat) (s : rst)
  : option (list term * rst) :=
  match n with
  | O => Some ([], s)
  | S n' =>
      let* p := read_fields r fs [] s in let* t := fill_pat el (fst p) in
      let* q := read_count r el fs n' (snd p) in Some (t :: fst q, snd q)
  end.

(** Read elements of the pattern el until no word is left, at most
    fuel of them. *)
Fixpoint read_rest (r : rtab) (el : pat) (fs : list field) (fuel : nat) (s : rst)
  : option (list term * rst) :=
  match s_words s with
  | [] => Some ([], s)
  | _ =>
      match fuel with
      | O => None
      | S f =>
          let* p := read_fields r fs [] s in let* t := fill_pat el (fst p) in
          let* q := read_rest r el fs f (snd p) in Some (t :: fst q, snd q)
      end
  end.

(** Read an instruction's fields fs into its holes. *)
Fixpoint read_lfields (r : rtab) (fs : list lfield) (e : env) (s : rst) : option (env * rst) :=
  match fs with
  | [] => Some (e, s)
  | FOne f :: fs' => let* p := read_field r f e s in read_lfields r fs' (fst p) (snd p)
  | FCount i el fs1 :: fs' =>
      let* p := next_word s in
      if Z.of_nat (length (s_words s)) <? fst p then None else
      let* q := read_count r el fs1 (Z.to_nat (fst p)) (snd p) in
      read_lfields r fs' ((i, TList (fst q)) :: e) (snd q)
  | FRest i el fs1 :: fs' =>
      let* q := read_rest r el fs1 (length (s_words s)) s in
      read_lfields r fs' ((i, TList (fst q)) :: e) (snd q)
  end.

(** ## Instructions *)

(** The rebind words of the definitions ds, n temporaries defined
    before them: 0 for a first definition, which takes the id n, or
    the id plus one; and the count after them. *)
Fixpoint rebinds (temps : nmap Z) (n : Z) (ds : list term) : option (list Z * Z) :=
  match ds with
  | [] => Some ([], n)
  | d :: ds' =>
      let* i := nm_find d temps in
      if Z.eqb i n then let* p := rebinds temps (n + 1) ds' in Some (0 :: fst p, snd p)
      else let* p := rebinds temps n ds' in Some ((i + 1) :: fst p, snd p)
  end.

(** The words of the instruction t, which must be of the group g, in
    the block b, n temporaries defined before it; the count after it;
    and whether it keeps the stream ordered: no temporary read before
    its first definition, outside a phi, and no edge to an earlier or
    the same block without a poll. *)
Definition inst_words (w : wtab) (g b n : Z) (t : term) : option (list Z * Z * bool) :=
  let* fe := find_form forms t in
  let f := fst fe in
  if negb (Z.eqb (group (f_code f)) g) then None else
  let* o := lfields_out w (snd fe) (f_fields f) in
  let* rb := rebinds (w_temps w) n (o_defs o) in
  let len := Z.of_nat (length (o_words o)) + 1 in
  if 65536 <=? len then None else
  let ordered := (Z.eqb g 0 || forallb (fun u => u <? n) (o_uses o))
                 && forallb (fun p => (b <? fst p) || Z.eqb (snd p) 1) (o_targets o) in
  let pre := if existsb (fun z => negb (Z.eqb z 0)) (fst rb)
             then (rebind_code + (Z.of_nat (length (fst rb)) + 1) * 65536) :: fst rb else [] in
  Some (pre ++ (f_code f + len * 65536) :: o_words o, snd rb, ordered).

(** The words of the instructions ts, all of the group g. *)
Fixpoint insts_words (w : wtab) (g b n : Z) (ts : list term) : option (list Z * Z * bool) :=
  match ts with
  | [] => Some ([], n, true)
  | t :: ts' =>
      let* x := inst_words w g b n t in
      let '(ws1, n1, o1) := x in
      let* y := insts_words w g b n1 ts' in
      let '(ws2, n2, o2) := y in
      Some (ws1 ++ ws2, n2, o1 && o2)
  end.

(** The parts of a block `block(L, Phis, Insts, Jump)`. *)
Definition block_parts (t : term) : option (term * list term * list term * term) :=
  match app_args "block" 4 t with
  | Some [l; TList phis; TList insts; j] => Some (l, phis, insts, j)
  | _ => None
  end.

(** The words of the blocks bs from the index b. *)
Fixpoint blocks_words (w : wtab) (b n : Z) (bs : list term) : option (list Z * Z * bool) :=
  match bs with
  | [] => Some ([], n, true)
  | bt :: bs' =>
      let* p := block_parts bt in
      let '(_, phis, insts, j) := p in
      if Z.eqb b 0 && negb (Nat.eqb (length phis) 0) then None else
      let* x1 := insts_words w 0 b n phis in
      let '(ws1, n1, o1) := x1 in
      let* x2 := insts_words w 1 b n1 insts in
      let '(ws2, n2, o2) := x2 in
      let* x3 := inst_words w 2 b n2 j in
      let '(ws3, n3, o3) := x3 in
      let* y := blocks_words w (b + 1) n3 bs' in
      let '(ws4, n4, o4) := y in
      Some (ws1 ++ ws2 ++ ws3 ++ ws4, n4, o1 && o2 && o3 && o4)
  end.

(** The names ns numbered from n in the map m, a name already there
    keeping its number; the names newly numbered, in order. *)
Fixpoint number (ns : list term) (m : nmap Z) (n : Z) (acc : list term) : nmap Z * Z * list term :=
  match ns with
  | [] => (m, n, rev acc)
  | x :: xs => if nm_mem x m then number xs m n acc else number xs (nm_add x n m) (n + 1) (x :: acc)
  end.

(** Each of the names ns numbered by its place from i, in the map m: a
    name that occurs twice keeps the place of its first occurrence, as
    the reader, which numbers every place, names it there. *)
Fixpoint first_ids (ns : list term) (i : Z) (m : nmap Z) : nmap Z :=
  match ns with
  | [] => m
  | x :: xs => first_ids xs (i + 1) (if nm_mem x m then m else nm_add x i m)
  end.

(** The temporary of a parameter `param(K, tmp(D))`, and K's code. *)
Definition param_parts (t : term) : option (term * Z) :=
  match app_args "param" 2 t with
  | Some [k; d] =>
      let* ds := app_args "tmp" 1 d in
      match ds with
      | [x] => if existsb (fun a => is_atom a k) ["w"; "l"; "p"; "s"; "d"]
               then let* c := enc_code EClass k in Some (x, c) else None
      | _ => None
      end
  | _ => None
  end.

(** The word of a function's return type. *)
Definition ret_word (r : term) : option Z :=
  if is_atom "void" r then Some 0 else
  match app_args "tuple" 1 r with
  | Some [TList [k1; k2]] =>
      let* c1 := enc_code EClass k1 in let* c2 := enc_code EClass k2 in Some (256 + 16 * c1 + c2)
  | _ => enc_code EClass r
  end.

(** The names of a function: its temporaries', labels' and locals', in
    id order. *)
Record fnames : Type := mkFnames { n_temps : list term; n_labels : list term; n_locals : list term }.

(** The words of a function's body, whether it is ordered, and its
    names; the module's tables are those of w. *)
Definition body_words (w : wtab) (ret : term) (params blocks : list term)
  : option (list Z * bool * fnames) :=
  let* rw := ret_word ret in
  let* ps := mapo param_parts params in
  let np := Z.of_nat (length ps) in
  let* bps := mapo block_parts blocks in
  let defs_of (t : term) := let* p := term_parts t in Some (p_defs p) in
  let* dss := mapo (fun bp => let '(_, phis, insts, _) := bp in mapo defs_of (phis ++ insts)) bps in
  let '(m0, n0, firsts0) := number (map fst ps) nm_empty 0 [] in
  if negb (Z.eqb n0 np) then None else
  let '(temps, nt, firsts) := number (concat (concat dss)) m0 n0 [] in
  let labels := map (fun bp => let '(l, _, _, _) := bp in l) bps in
  let '(lmap, nb, _) := number labels nm_empty 0 [] in
  if negb (Z.eqb nb (Z.of_nat (length labels))) then None else
  let locals := flat_map (fun bp => let '(_, _, insts, _) := bp in
                            flat_map (fun t => match app_args "local_alloc" 2 t with
                                               | Some [x; _] => [x]
                                               | _ => []
                                               end) insts) bps in
  let '(xmap, nl, _) := number locals nm_empty 0 [] in
  if negb (Z.eqb nl (Z.of_nat (length locals))) then None else
  let w' := mkWtab (w_syms w) (w_strs w) (w_consts w) temps lmap xmap in
  let* x := blocks_words w' 0 np blocks in
  let '(stream, _, ordered) := x in
  Some ([rw; np] ++ map snd ps ++ [nb; nt; nl] ++ stream, ordered,
        mkFnames (firsts0 ++ firsts) labels locals).

(** ## Stage and mode *)

(** The names of the ops of the checked stage, with their arities;
    `check_function` is an atom. *)
Definition checked_ops : list (string * nat) :=
  [("check", 4%nat); ("check_ahead", 5%nat); ("renew", 4%nat); ("renew_hull", 4%nat);
   ("half_check", 5%nat); ("span_test", 2%nat); ("renew_if", 4%nat); ("limit", 1%nat);
   ("check_limit", 4%nat); ("check_local", 5%nat); ("raw_load", 2%nat);
   ("raw_load_pointer", 2%nat); ("raw_cas", 2%nat)].

(** Whether t is the compound f of n arguments. *)
Definition is_app (f : string) (n : nat) (t : term) : bool :=
  match app_args f n t with Some _ => true | None => false end.

(** As ir.pl's `checked_inst/1`: the instruction is of the checked
    stage's vocabulary. *)
Definition checked_inst (t : term) : bool :=
  match app_args "let" 4 t with
  | Some [_; _; o; _] => is_atom "check_function" o || existsb (fun p => is_app (fst p) (snd p) o) checked_ops
  | _ => is_app "raw_store" 4 t || is_app "raw_store_pointer" 4 t || is_app "raw_call" 3 t
         || is_app "flight" 4 t || is_app "touch" 1 t
  end.

(** As `checked_jump/1`: the jump has a poll edge. *)
Definition checked_jump (t : term) : bool :=
  match app_args "goto" 1 t with
  | Some [l] => is_app "poll" 1 l
  | _ => match app_args "branch" 3 t with
         | Some [_; l1; l2] => is_app "poll" 1 l1 || is_app "poll" 1 l2
         | _ => false
         end
  end.

(** The blocks of a function term, if it is one. *)
Definition func_blocks (t : term) : list term :=
  match app_args "func" 5 t with Some [_; _; _; _; TList bs] => bs | _ => [] end.

(** As `module_stage/2`: checked when a function uses the checked
    vocabulary. *)
Definition module_checked (items : list term) : bool :=
  existsb (fun it => existsb (fun bt => match block_parts bt with
                                        | Some (_, _, insts, j) => existsb checked_inst insts || checked_jump j
                                        | None => false
                                        end) (func_blocks it)) items.

(** Whether the class term k is one of the atoms ks. *)
Definition class_in (ks : list string) (k : term) : bool := existsb (fun a => is_atom a k) ks.

(** As `pointer_inst/1`: the instruction produces, stores, passes or
    calls through a pointer, or converts one. *)
Definition pointer_inst (t : term) : bool :=
  match app_args "let" 4 t with
  | Some [_; k; o; _] =>
      class_in ["p"; "x"; "a"; "f"] k || is_atom "ptoi" o || is_app "setjmp" 1 o
      || is_app "raw_load_pointer" 2 o
  | _ =>
  match app_args "store" 3 t with
  | Some [wd; _; _] => class_in ["x"; "p"] wd
  | _ =>
  match app_args "call" 3 t with
  | Some [r; c; TList args] =>
      (match app_args "result" 2 r with Some [_; k] => is_atom "p" k | _ => false end)
      || is_app "tuple" 1 r || is_app "tmp" 1 c
      || existsb (fun a => match app_args "arg" 2 a with Some [k; _] => is_atom "p" k | _ => false end) args
  | _ =>
      is_app "atomic_store" 3 t || is_app "raw_store" 4 t || is_app "raw_store_pointer" 4 t
      || is_app "raw_call" 3 t || is_app "flight" 4 t || is_app "local_alloc" 2 t
      || is_app "local_load" 5 t || is_app "local_store" 4 t
  end end end.

(** As `pointer_item/1`: the item has a pointer somewhere, or is of a
    linkage only the filc mode models. *)
Definition pointer_item (it : term) : bool :=
  match app_args "func" 5 it with
  | Some [_; lk; ret; TList ps; TList bs] =>
      is_atom "weak" lk || is_atom "p" ret || is_app "tuple" 1 ret
      || existsb (fun p => match app_args "param" 2 p with Some [k; _] => is_atom "p" k | _ => false end) ps
      || existsb (fun bt => match block_parts bt with
                            | Some (_, phis, insts, _) =>
                                existsb (fun ph => match app_args "phi" 3 ph with
                                                   | Some [_; k; _] => is_atom "p" k
                                                   | _ => false
                                                   end) phis
                                || existsb pointer_inst insts
                            | None => false
                            end) bs
  | _ =>
  match app_args "data" 4 it with
  | Some [_; lk; _; TList its] =>
      is_app "ro" 1 lk || is_app "tls" 1 lk || is_atom "weak" lk || is_app "extern" 1 lk
      || existsb (fun x => match app_args "item" 2 x with Some [k; _] => is_atom "p" k | _ => false end) its
  | _ => is_app "alias" 3 it
  end end.

(** As `module_mode/2`: filc when an item has a pointer, or a function
    calls one the module does not define. *)
Definition module_filc (items : list term) : bool :=
  let funcs := flat_map (fun it => match app_args "func" 5 it with Some (n :: _) => [n] | _ => [] end) items in
  existsb pointer_item items
  || existsb (fun it =>
                existsb (fun bt =>
                           match block_parts bt with
                           | Some (_, _, insts, _) =>
                               existsb (fun i => match app_args "call" 3 i with
                                                 | Some [_; c; _] =>
                                                     match app_args "global" 1 c with
                                                     | Some [s] => negb (existsb (term_eqb s) funcs)
                                                     | _ => false
                                                     end
                                                 | _ => false
                                                 end) insts
                           | None => false
                           end) (func_blocks it)) items.

(** ## The module's tables *)

(** The name a function, data object or alias defines, and its symbol
    kind: 0, 1 or 2. *)
Definition item_symbol (it : term) : option (term * Z) :=
  match it with
  | TApp f (n :: _) =>
      if String.eqb f "func" then Some (n, 0)
      else if String.eqb f "data" then Some (n, 1)
      else if String.eqb f "alias" then Some (n, 2)
      else None
  | _ => None
  end.

(** What an item names: its instructions' parts, its data's symbols
    and constants, its alias's target. *)
Definition item_parts (it : term) : option parts :=
  match app_args "func" 5 it with
  | Some [_; _; _; _; TList bs] =>
      let* bps := mapo block_parts bs in
      let* ps := mapo term_parts (flat_map (fun bp => let '(_, phis, insts, j) := bp in
                                                       phis ++ insts ++ [j]) bps) in
      Some (fold_right parts_app no_parts ps)
  | _ =>
  match app_args "data" 4 it with
  | Some [_; _; _; TList its] =>
      Some (fold_right parts_app no_parts
              (map (fun x => match app_args "item" 2 x with
                             | Some [_; v] =>
                                 match app_args "sym" 2 v with
                                 | Some [s; _] => mkParts [] [s] [] []
                                 | _ => value_parts v
                                 end
                             | _ => no_parts
                             end) its))
  | _ =>
  match app_args "alias" 3 it with
  | Some [_; _; tg] => Some (mkParts [] [tg] [] [])
  | _ => None
  end end end.

(** The string of an atom. *)
Definition atom_string (t : term) : option string := match t with TAtom s => Some s | _ => None end.

(** A module's tables: its strings, wide constants and symbols (each a
    name, a kind, and the item that defines it, if any), and the ids
    of each. *)
Record mtab : Type := mkMtab {
  m_strs : list string; m_consts : list Z; m_syms : list (term * Z * option term);
  m_symids : nmap Z; m_strids : nmap Z; m_constids : ZMap.t Z
}.

(** The tables of the items. *)
Definition module_tables (items : list term) : option mtab :=
  let* defined := mapo (fun it => let* p := item_symbol it in Some (fst p, snd p, Some it)) items in
  let* pss := mapo item_parts items in
  let ps := fold_right parts_app no_parts pss in
  let defmap := fold_left (fun m d => let '(n, _, _) := d in nm_add n 0 m) defined nm_empty in
  let* defnames := mapo (fun d => let '(n, _, _) := d in atom_string n) defined in
  let* named := mapo atom_string (filter (fun g => negb (nm_mem g defmap)) (p_globals ps)) in
  let named := sort_uniq str_lt String.eqb named in
  let syms := defined ++ map (fun s => (TAtom s, 3, None)) named in
  let symids := first_ids (map (fun d => let '(n, _, _) := d in n) syms) 0 nm_empty in
  let* files := mapo atom_string (p_files ps) in
  let strs := sort_uniq str_lt String.eqb (defnames ++ named ++ files) in
  let '(strids, _, _) := number (map TAtom strs) nm_empty 0 [] in
  let consts := sort_uniq Z.ltb Z.eqb (filter (fun c => negb (inline c)) (p_consts ps)) in
  if negb (forallb wideok consts) then None else
  let constids := fst (fold_left (fun p c => (ZMap.add c (snd p) (fst p), snd p + 1)) consts (ZMap.empty Z, 0)) in
  Some (mkMtab strs consts syms symids strids constids).

(** The codes of the data linkages other than `init(_, P)` with an
    integer P. *)
Definition data_linkage_codes : list (term * Z) :=
  [(TAtom "export", 0); (TAtom "local", 1); (TAtom "weak", 2);
   (TApp "ro" [TAtom "export"], 3); (TApp "ro" [TAtom "local"], 4); (TApp "ro" [TAtom "weak"], 5);
   (TApp "tls" [TAtom "export"], 6); (TApp "tls" [TAtom "local"], 7);
   (TApp "init" [TAtom "ctor"; TAtom "none"], 10); (TApp "init" [TAtom "dtor"; TAtom "none"], 11);
   (TApp "extern" [TAtom "weak"], 12)].

(** The value of the term key t in the association list xs. *)
Fixpoint tassoc (t : term) (xs : list (term * Z)) : option Z :=
  match xs with
  | [] => None
  | (k, v) :: xs' => if term_eqb t k then Some v else tassoc t xs'
  end.

(** The key of the value z. *)
Fixpoint trassoc (z : Z) (xs : list (term * Z)) : option term :=
  match xs with
  | [] => None
  | (k, v) :: xs' => if Z.eqb z v then Some k else trassoc z xs'
  end.

(** A data linkage's code and the word beside it, a priority's. *)
Definition data_linkage_word (lk : term) : option (Z * Z) :=
  match app_args "init" 2 lk with
  | Some [wh; TInt p] =>
      if u32ok p then
        if is_atom "ctor" wh then Some (8, p) else if is_atom "dtor" wh then Some (9, p) else None
      else None
  | _ => let* c := tassoc lk data_linkage_codes in Some (c, 0)
  end.

(** A symbol's three words. *)
Definition symbol_words (t : mtab) (s : term * Z * option term) : option (list Z) :=
  let '(n, k, it) := s in
  let* sid := nm_find n (m_strids t) in
  match k, it with
  | 0, Some i =>
      let* xs := app_args "func" 5 i in
      let* lk := nth_error xs 1 in let* s := atom_string lk in
      let* c := sassoc s func_linkage_codes in Some [sid; c * 256; 0]
  | 1, Some i =>
      let* xs := app_args "data" 4 i in
      let* lk := nth_error xs 1 in let* p := data_linkage_word lk in
      Some [sid; 1 + fst p * 256; snd p]
  | 2, Some i =>
      let* xs := app_args "alias" 3 i in
      match xs with
      | [_; lk; tg] =>
          let* s := atom_string lk in let* c := sassoc s alias_linkage_codes in
          let* tid := nm_find tg (m_symids t) in Some [sid; 2 + c * 256; tid]
      | _ => None
      end
  | 3, None => Some [sid; 3; 0]
  | _, _ => None
  end.

(** The words of a data item. *)
Definition data_item_words (t : mtab) (x : term) : option (list Z) :=
  match app_args "item" 2 x with
  | Some [wd; v] =>
      match app_args "str" 1 v with
      | Some [TList cs] =>
          if is_atom "b" wd then
            let* bs := mapo (fun c => let* b := char_code c in
                                      if (b <? 256) && term_eqb (code_char b) c then Some b else None) cs in
            Some (1 :: bytes_words bs)
          else None
      | _ =>
      match app_args "const" 1 v with
      | Some [TInt n] =>
          let* c := enc_code EWidth wd in let* z := const_word (m_constids t) n in Some [0; c; z]
      | _ =>
      match app_args "sym" 2 v with
      | Some [s; TInt off] =>
          if (is_atom "l" wd || is_atom "p" wd) && i64ok off then
            let* c := enc_code EWidth wd in let* sid := nm_find s (m_symids t) in
            Some ([2; c; sid] ++ i64_words off)
          else None
      | _ => None
      end end end
  | _ =>
      match app_args "zero" 1 x with
      | Some [TInt n] => if i64ok n then Some (3 :: i64_words n) else None
      | _ => None
      end
  end.

(** The DATA words of a data item `data(N, Lk, Align, Items)`, or none
    for another item. *)
Definition data_words (t : mtab) (it : term) : option (list Z) :=
  match app_args "data" 4 it with
  | Some [_; _; TInt al; TList its] =>
      if u32ok al then
        let* ws := mapo (data_item_words t) its in
        Some ([al; Z.of_nat (length its)] ++ concat ws)
      else None
  | Some _ => None
  | None => Some []
  end.

(** The FUNCTIONS words of a function, whether it is ordered, and its
    names; nothing for another item. *)
Definition func_words (t : mtab) (it : term) : option (list Z * bool * list fnames) :=
  match app_args "func" 5 it with
  | Some [_; _; ret; TList ps; TList bs] =>
      let w := mkWtab (m_symids t) (m_strids t) (m_constids t) nm_empty nm_empty nm_empty in
      let* x := body_words w ret ps bs in
      let '(body, ordered, names) := x in
      Some (Z.of_nat (length body) :: body, ordered, [names])
  | Some _ => None
  | None => Some ([], true, [])
  end.

(** ## Side sections *)

(** Every atom and functor of the term t. *)
Fixpoint term_atoms (t : term) : list string :=
  match t with
  | TInt _ => []
  | TAtom a => [a]
  | TApp f ts => f :: flat_map term_atoms ts
  | TList ts => flat_map term_atoms ts
  end.

(** The words of a string table: the count, then each string. *)
Definition strings_words (ss : list string) : list Z :=
  Z.of_nat (length ss) :: flat_map (fun s => bytes_words (string_bytes s)) ss.

(** The words of the term t in a side section whose pool ids are ids:
    0 and an integer, 1 and an atom, 2 and a compound's functor, arity
    and arguments, 3 and a list's length and elements. *)
Fixpoint side_term_words (ids : nmap Z) (t : term) : option (list Z) :=
  match t with
  | TInt n => if wideok n then Some (0 :: wide_words n) else None
  | TAtom a => let* i := nm_find t ids in Some [1; i]
  | TApp f ts =>
      if Nat.eqb (length ts) 0 then None else
      let* i := nm_find (TAtom f) ids in
      let* ws := (fix go (ts : list term) : option (list Z) :=
                    match ts with
                    | [] => Some []
                    | t :: ts' => let* a := side_term_words ids t in let* b := go ts' in Some (a ++ b)
                    end) ts in
      Some ([2; i; Z.of_nat (length ts)] ++ ws)
  | TList ts =>
      let* ws := (fix go (ts : list term) : option (list Z) :=
                    match ts with
                    | [] => Some []
                    | t :: ts' => let* a := side_term_words ids t in let* b := go ts' in Some (a ++ b)
                    end) ts in
      Some ([3; Z.of_nat (length ts)] ++ ws)
  end.

(** The NAMES words of the functions' names: the pool, then each
    function's temporaries, labels and locals, each list its length
    and its terms. *)
Definition names_words (ns : list fnames) : option (list Z) :=
  let all := flat_map (fun f => n_temps f ++ n_labels f ++ n_locals f) ns in
  let pool := sort_uniq str_lt String.eqb (flat_map term_atoms all) in
  let '(ids, _, _) := number (map TAtom pool) nm_empty 0 [] in
  let list_words (ts : list term) :=
    let* ws := mapo (side_term_words ids) ts in Some (Z.of_nat (length ts) :: concat ws) in
  let* recs := mapo (fun f => let* a := list_words (n_temps f) in let* b := list_words (n_labels f) in
                              let* c := list_words (n_locals f) in Some (a ++ b ++ c)) ns in
  Some (strings_words pool ++ concat recs).

(** ## A module's words *)

Definition magic : Z := 4343374.
Definition version : Z := 1.

(** The words of the sections ss, each its id, length and payload. *)
Definition sections_words (ss : list (Z * list Z)) : list Z :=
  flat_map (fun s => fst s :: Z.of_nat (length (snd s)) :: snd s) ss.

(** The NFB of the module term `module(Items)` without `context/2`
    items, with the NAMES section when names is true. *)
Definition encode_term (names : bool) (m : term) : option (list Z) :=
  let* xs := app_args "module" 1 m in
  match xs with
  | [TList items] =>
      let* t := module_tables items in
      let* syms := mapo (symbol_words t) (m_syms t) in
      let* datas := mapo (data_words t) items in
      let* fs := mapo (func_words t) items in
      let fws := concat (map (fun x => let '(ws, _, _) := x in ws) fs) in
      let ordered := forallb (fun x => let '(_, o, _) := x in o) fs in
      let fnames := concat (map (fun x => let '(_, _, n) := x in n) fs) in
      let dws := concat datas in
      let* nws := if names && negb (Nat.eqb (length fnames) 0) then
                    let* ws := names_words fnames in Some [(256, ws)]
                  else Some [] in
      let core := (if Nat.eqb (length (m_strs t)) 0 then [] else [(1, strings_words (m_strs t))])
                  ++ (if Nat.eqb (length (m_consts t)) 0 then []
                      else [(2, Z.of_nat (length (m_consts t)) :: flat_map wide_words (m_consts t))])
                  ++ (if Nat.eqb (length (m_syms t)) 0 then []
                      else [(3, Z.of_nat (length (m_syms t)) :: concat syms)])
                  ++ (if Nat.eqb (length dws) 0 then [] else [(4, dws)])
                  ++ (if Nat.eqb (length fws) 0 then [] else [(5, fws)]) in
      let secs := core ++ nws in
      let flags := (if module_checked items then 1 else 0) + (if module_filc items then 2 else 0)
                   + (if ordered then 4 else 0) in
      Some ([magic; version; flags; Z.of_nat (length secs)] ++ sections_words secs)
  | _ => None
  end.

(** ## Reading a module *)

(** A reader of words: a value and the words after it, or none. *)
Definition reader (X : Type) : Type := list Z -> option (X * list Z).

(** Read n of what r reads. *)
Fixpoint read_n {X : Type} (n : nat) (r : reader X) : reader (list X) :=
  fun ws => match n with
            | O => Some ([], ws)
            | S n' => let* p := r ws in let* q := read_n n' r (snd p) in Some (fst p :: fst q, snd q)
            end.

(** Read a count, then that many of what r reads; a count beyond the
    words left is refused before anything is read. *)
Definition read_counted {X : Type} (r : reader X) : reader (list X) :=
  fun ws => match ws with
            | n :: ws' => if negb (at_least (Z.to_nat n) ws') then None else read_n (Z.to_nat n) r ws'
            | [] => None
            end.

(** Read one word. *)
Definition read_word : reader Z := fun ws => match ws with x :: xs => Some (x, xs) | [] => None end.

(** Read a byte string: its length, then its words. *)
Definition read_bytes : reader (list Z) :=
  fun ws => match ws with
            | n :: ws' =>
                if (n <? 0) || negb (at_least (Z.to_nat ((n + 3) / 4)) ws') then None else
                let* p := take (Z.to_nat ((n + 3) / 4)) ws' in
                Some (firstn (Z.to_nat n) (unpack (fst p)), snd p)
            | [] => None
            end.

(** Read a string table. *)
Definition read_strings : reader (list string) :=
  read_counted (fun ws => let* p := read_bytes ws in Some (bytes_string (fst p), snd p)).

(** Read a signed 96-bit integer. *)
Definition read_wide : reader Z :=
  fun ws => match ws with w0 :: w1 :: w2 :: ws' => Some (wide_of w0 w1 w2, ws') | _ => None end.

(** Read a signed 64-bit integer. *)
Definition read_i64 : reader Z :=
  fun ws => match ws with lo :: hi :: ws' => Some (i64_of lo hi, ws') | _ => None end.

(** Read a side section's term, at most fuel deep. *)
Fixpoint read_side_term (pool : ZMap.t term) (fuel : nat) : reader term :=
  fun ws =>
    match fuel with
    | O => None
    | S f =>
        match ws with
        | 0 :: ws' => let* p := read_wide ws' in Some (TInt (fst p), snd p)
        | 1 :: i :: ws' => let* a := ZMap.find i pool in Some (a, ws')
        | 2 :: i :: ws' =>
            let* fa := ZMap.find i pool in
            let* fn := atom_string fa in
            let* p := read_counted (read_side_term pool f) ws' in
            match fst p with [] => None | _ => Some (TApp fn (fst p), snd p) end
        | 3 :: ws' => let* p := read_counted (read_side_term pool f) ws' in Some (TList (fst p), snd p)
        | _ => None
        end
    end.

(** The map from 0, 1, ... to the elements of xs. *)
Definition index_map {X : Type} (xs : list X) : ZMap.t X :=
  fst (fold_left (fun p x => (ZMap.add (snd p) x (fst p), snd p + 1)) xs (ZMap.empty X, 0)).

(** Read the NAMES section: the pool, then each function's names, as
    many as the words hold, each term at most depth deep (the length
    of the section, measured once). *)
Fixpoint read_name_recs (pool : ZMap.t term) (depth fuel : nat) (ws : list Z) : option (list fnames) :=
  match ws with
  | [] => Some []
  | _ =>
      match fuel with
      | O => None
      | S f =>
          let rt := read_side_term pool depth in
          let* a := read_counted rt ws in let* b := read_counted rt (snd a) in
          let* c := read_counted rt (snd b) in
          let* rest := read_name_recs pool depth f (snd c) in
          Some (mkFnames (fst a) (fst b) (fst c) :: rest)
      end
  end.

(** The NAMES of the section's words. *)
Definition read_names (ws : list Z) : option (list fnames) :=
  let* p := read_strings ws in
  let n := length (snd p) in read_name_recs (index_map (map TAtom (fst p))) n n (snd p).

(** The opcode of the next instruction, after its rebind prefix, if any. *)
Definition next_opcode (ws : list Z) : option Z :=
  match ws with
  | h :: ws' =>
      if Z.eqb (h mod 65536) rebind_code then
        let* x := nth_error ws' (Z.to_nat (h / 65536 - 1)) in Some (x mod 65536)
      else Some (h mod 65536)
  | [] => None
  end.

(** Read one instruction of the group g, n temporaries and x locals
    defined before it; the counts after it. *)
Definition read_inst (r : rtab) (g : Z) (n x : Z) : reader (term * Z * Z) :=
  fun ws =>
    let* pre := match ws with
                | h :: ws' => if Z.eqb (h mod 65536) rebind_code then
                                if h / 65536 <? 2 then None else
                                let* p := take (Z.to_nat (h / 65536 - 1)) ws' in Some (Some (fst p), snd p)
                              else Some (None, ws)
                | [] => None
                end in
    let '(rb, ws1) := pre in
    match ws1 with
    | h :: ws2 =>
        let c := h mod 65536 in let len := h / 65536 in
        if (len <? 1) || negb (Z.eqb (group c) g) then None else
        let* f := form_of_code forms c in
        let* p := take (Z.to_nat (len - 1)) ws2 in
        let* q := read_lfields r (f_fields f) [] (mkRst (fst p) rb n x) in
        let '(e, s) := q in
        match s_words s, s_rebinds s with
        | [], (None | Some []) =>
            let* t := fill_pat (f_pat f) e in Some (t, s_next s, s_local s, snd p)
        | _, _ => None
        end
    | [] => None
    end.

(** Read the instructions of the group g that come next, at most fuel. *)
Fixpoint read_group (r : rtab) (g : Z) (fuel : nat) (n x : Z) : reader (list term * Z * Z) :=
  fun ws =>
    match next_opcode ws with
    | Some c =>
        if Z.eqb (group c) g then
          match fuel with
          | O => None
          | S f =>
              let* p := read_inst r g n x ws in
              let '(t, n1, x1, ws1) := p in
              let* q := read_group r g f n1 x1 ws1 in
              let '(ts, n2, x2, ws2) := q in
              Some (t :: ts, n2, x2, ws2)
          end
        else Some ([], n, x, ws)
    | None => Some ([], n, x, ws)
    end.

(** Read the blocks from the index i, k of them, fuel bounding each
    group. *)
Fixpoint read_blocks (r : rtab) (fuel : nat) (i : Z) (k : nat) (n x : Z) : reader (list term * Z * Z) :=
  fun ws =>
    match k with
    | O => Some ([], n, x, ws)
    | S k' =>
        let* l := ZMap.find i (r_labels r) in
        let* p := read_group r 0 fuel n x ws in
        let '(phis, n1, x1, ws1) := p in
        if Z.eqb i 0 && negb (Nat.eqb (length phis) 0) then None else
        let* q := read_group r 1 fuel n1 x1 ws1 in
        let '(insts, n2, x2, ws2) := q in
        let* u := read_inst r 2 n2 x2 ws2 in
        let '(j, n3, x3, ws3) := u in
        let* v := read_blocks r fuel (i + 1) k' n3 x3 ws3 in
        let '(bs, n4, x4, ws4) := v in
        Some (TApp "block" [l; TList phis; TList insts; j] :: bs, n4, x4, ws4)
    end.

(** The return type of its word. *)
Definition read_ret (z : Z) : option term :=
  if Z.eqb z 0 then Some (TAtom "void")
  else if 256 <=? z then
    if (z - 256) / 16 <? 16 then
      let* k1 := dec_code EClass ((z - 256) / 16) in let* k2 := dec_code EClass (z mod 16) in
      Some (TApp "tuple" [TList [k1; k2]])
    else None
  else dec_code EClass z.

(** The integers from 0 below n, as terms: the names without NAMES. *)
Definition id_names (n : Z) : list term := map (fun i => TInt (Z.of_nat i)) (seq 0 (Z.to_nat n)).

(** Read a function's body, of the symbol name n and linkage lk, its
    names from nm if NAMES has them. *)
Definition read_body (r : rtab) (nm : option fnames) (name lk : term) (ws : list Z) : option term :=
  match ws with
  | rw :: np :: ws1 =>
      let* ret := read_ret rw in
      let* p := take (Z.to_nat np) ws1 in
      if np <? 0 then None else
      let* pks := mapo (fun c => let* k := dec_code EClass c in
                                 if class_in ["w"; "l"; "p"; "s"; "d"] k then Some k else None) (fst p) in
      match snd p with
      | nb :: nt :: nl :: stream =>
          let left := Z.of_nat (length stream) in
          if (nb <? 0) || (nt <? np) || (nl <? 0) || (left <? nb) || (left <? nt - np) || (left <? nl)
          then None else
          let '(tn, ln, xn) := match nm with
                               | Some f => (n_temps f, n_labels f, n_locals f)
                               | None => (id_names nt, id_names nb, id_names nl)
                               end in
          if negb (Z.eqb (Z.of_nat (length tn)) nt && Z.eqb (Z.of_nat (length ln)) nb
                   && Z.eqb (Z.of_nat (length xn)) nl) then None else
          let r' := mkRtab (r_syms r) (r_strs r) (r_consts r) (index_map tn) (index_map ln) (index_map xn) in
          let params := map (fun q => TApp "param" [fst q; TApp "tmp" [snd q]]) (combine pks (firstn (length pks) tn)) in
          let* q := read_blocks r' (length stream) 0 (Z.to_nat nb) np 0 stream in
          let '(bs, n1, x1, rest) := q in
          match rest with
          | [] => if Z.eqb n1 nt && Z.eqb x1 nl
                  then Some (TApp "func" [name; lk; ret; TList params; TList bs]) else None
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(** Read a data item. *)
Definition read_data_item (r : rtab) : reader term :=
  fun ws =>
    match ws with
    | 1 :: ws' => let* p := read_bytes ws' in
                  Some (TApp "item" [TAtom "b"; TApp "str" [TList (map code_char (fst p))]], snd p)
    | 0 :: c :: z :: ws' =>
        let* wd := dec_code EWidth c in let* n := const_of r z in
        Some (TApp "item" [wd; TApp "const" [TInt n]], ws')
    | 2 :: c :: sid :: ws' =>
        let* wd := dec_code EWidth c in let* s := ZMap.find sid (r_syms r) in
        let* p := read_i64 ws' in
        Some (TApp "item" [wd; TApp "sym" [s; TInt (fst p)]], snd p)
    | 3 :: ws' => let* p := read_i64 ws' in Some (TApp "zero" [TInt (fst p)], snd p)
    | _ => None
    end.

(** The linkage of a data symbol, from its code and extra word. *)
Definition read_data_linkage (c extra : Z) : option term :=
  if Z.eqb c 8 then Some (TApp "init" [TAtom "ctor"; TInt extra])
  else if Z.eqb c 9 then Some (TApp "init" [TAtom "dtor"; TInt extra])
  else trassoc c data_linkage_codes.

(** Read the items of the symbols syms, in order: a function's body
    from fws and its names from nms, a data object's from dws, an
    alias from the symbol itself. *)
Fixpoint read_items (r : rtab) (syms : list (term * Z * Z)) (dws fws : list Z)
  (nms : option (list fnames)) : option (list term) :=
  match syms with
  | [] => match dws, fws, nms with [], [], (None | Some []) => Some [] | _, _, _ => None end
  | (name, kw, extra) :: syms' =>
      let k := kw mod 256 in let lc := kw / 256 in
      if Z.eqb k 0 then
        let* lks := srassoc lc func_linkage_codes in
        if negb (Z.eqb extra 0) then None else
        match fws with
        | len :: fws1 =>
            let* p := take (Z.to_nat len) fws1 in
            let* nm := match nms with
                       | None => Some (None, None)
                       | Some (f :: fs) => Some (Some f, Some fs)
                       | Some [] => None
                       end in
            let* f := read_body r (fst nm) name (TAtom lks) (fst p) in
            let* rest := read_items r syms' dws (snd p) (snd nm) in Some (f :: rest)
        | [] => None
        end
      else if Z.eqb k 1 then
        let* lk := read_data_linkage lc extra in
        match dws with
        | al :: ni :: dws1 =>
            if negb (at_least (Z.to_nat ni) dws1) then None else
            let* p := read_n (Z.to_nat ni) (read_data_item r) dws1 in
            let* rest := read_items r syms' (snd p) fws nms in
            Some (TApp "data" [name; lk; TInt al; TList (fst p)] :: rest)
        | _ => None
        end
      else if Z.eqb k 2 then
        let* lks := srassoc lc alias_linkage_codes in
        let* tg := ZMap.find extra (r_syms r) in
        let* rest := read_items r syms' dws fws nms in
        Some (TApp "alias" [name; TAtom lks; tg] :: rest)
      else if Z.eqb k 3 then read_items r syms' dws fws nms
      else None
  end.

(** Split the words into sections, each id with its payload. *)
Fixpoint read_sections (fuel : nat) (ws : list Z) : option (list (Z * list Z)) :=
  match ws with
  | [] => Some []
  | id :: len :: ws' =>
      match fuel with
      | O => None
      | S f => let* p := take (Z.to_nat len) ws' in
               let* rest := read_sections f (snd p) in Some ((id, fst p) :: rest)
      end
  | _ => None
  end.

(** Whether the section ids increase, each known: a core one from 1 to
    5, NAMES, CONTEXT, or a tool's from 0x200. *)
Fixpoint ids_ok (prev : Z) (ss : list (Z * list Z)) : bool :=
  match ss with
  | [] => true
  | (id, _) :: ss' =>
      (prev <? id) && (((1 <=? id) && (id <=? 5)) || Z.eqb id 256 || Z.eqb id 257 || (512 <=? id))
      && ids_ok id ss'
  end.

(** The payload of the section id, or none. *)
Fixpoint section (id : Z) (ss : list (Z * list Z)) : option (list Z) :=
  match ss with
  | [] => None
  | (i, ws) :: ss' => if Z.eqb i id then Some ws else section id ss'
  end.

(** The module term of the words ws, without its context items, and
    whether it had NAMES; the words are not yet checked against the
    module's own encoding ([decode_term] does that). *)
Definition read_term (ws : list Z) : option (term * bool) :=
  match ws with
  | m :: v :: flags :: nsecs :: ws' =>
      if negb (Z.eqb m magic && Z.eqb v version && (0 <=? flags) && (flags <? 8)) then None else
      let* ss := read_sections (length ws') ws' in
      if negb (Z.eqb (Z.of_nat (length ss)) nsecs && ids_ok 0 ss) then None else
      let or_empty (o : option (list Z)) (d : list Z) := match o with Some x => x | None => d end in
      let* sp := read_strings (or_empty (section 1 ss) [0]) in
      let* cp := read_counted read_wide (or_empty (section 2 ss) [0]) in
      let* yp := read_counted (fun ws => match ws with
                                         | a :: b :: c :: ws' => Some ((a, b, c), ws')
                                         | _ => None
                                         end) (or_empty (section 3 ss) [0]) in
      match snd sp, snd cp, snd yp with
      | [], [], [] =>
          let strs := index_map (map TAtom (fst sp)) in
          let* syms := mapo (fun y => let '(sid, kw, extra) := y in
                                      let* n := ZMap.find sid strs in Some (n, kw, extra)) (fst yp) in
          let symt := index_map (map (fun y => let '(n, _, _) := y in n) syms) in
          let* nms := match section 256 ss with
                      | Some ws => let* ns := read_names ws in Some (Some ns)
                      | None => Some None
                      end in
          let r := mkRtab symt strs (index_map (fst cp)) (ZMap.empty term) (ZMap.empty term) (ZMap.empty term) in
          let* items := read_items r syms (or_empty (section 4 ss) []) (or_empty (section 5 ss) []) nms in
          Some (TApp "module" [TList items], match nms with Some _ => true | None => false end)
      | _, _, _ => None
      end
  | _ => None
  end.

(** The words ws without their CONTEXT section and the sections of
    tools: those that do not say what the module is. *)
Definition module_words (ws : list Z) : option (list Z) :=
  match ws with
  | m :: v :: flags :: _ :: ws' =>
      let* ss := read_sections (length ws') ws' in
      let kept := filter (fun s => fst s <? 257) ss in
      Some ([m; v; flags; Z.of_nat (length kept)] ++ sections_words kept)
  | _ => None
  end.

(** Equality of two lists of words. *)
Fixpoint words_eqb (xs ys : list Z) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Z.eqb x y && words_eqb xs' ys'
  | _, _ => false
  end.

(** The module term the NFB ws encode, provided ws are exactly its
    encoding, CONTEXT and tools' sections aside. *)
Definition decode_term (ws : list Z) : option term :=
  let* p := read_term ws in
  let* ws1 := encode_term (snd p) (fst p) in
  let* ws2 := module_words ws in
  if words_eqb ws1 ws2 then Some (fst p) else None.
