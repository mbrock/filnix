(** The scalar instruction selection of the stack-homed emission:
    amd64.pl's `compute_op//4` with all it calls, its `store_insn/3`
    and `load_insn/3`, and filc_amd64.pl's x87 instructions for
    `long double`. Every operand is read from its slot below `%rbp`
    into `%rax`, `%rcx` or `%rdx`, and the result is left in `%rax`.

    The lines are the Prolog compiler's, in order. Where a Prolog
    clause fails (a class an operation does not take, a wrong number
    of arguments) the code holds a [todo] line, as in Layout.v. The
    examples at the end are lines the Prolog compiler printed
    (`nanofil --registers=stack asm-terms`). *)
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Maps.
From Backend Require Import Text Asm Plan PlanTerm Layout.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Registers and suffixes *)

(** Whether r is a short register of `reg_name/3`: `a`, `c`, `d`,
    `si`, `di`, `r8` or `r9`. *)
Definition short_reg (r : string) : bool :=
  String.eqb r "a" || String.eqb r "c" || String.eqb r "d" || String.eqb r "si"
  || String.eqb r "di" || String.eqb r "r8" || String.eqb r "r9".

(** Whether `reg_name/3` names the byte and the halfword of the short
    register r: only of `a`, `c` and `d`. *)
Definition narrow_reg (r : string) : bool :=
  String.eqb r "a" || String.eqb r "c" || String.eqb r "d".

(** The byte of the short register r: `al`, `cl` and `dl` as
    `reg_name/3` has them at `b`, and x86's names for the others
    (`sil`, `dil`, `r8b`, `r9b`), which `reg_name/3` lacks. *)
Definition reg8 (r : string) : string :=
  if String.eqb r "a" then "al" else if String.eqb r "c" then "cl"
  else if String.eqb r "d" then "dl" else if String.eqb r "si" then "sil"
  else if String.eqb r "di" then "dil" else r ++ "b".

(** The halfword of the short register r: `ax`, `cx` and `dx` as
    `reg_name/3` has them at `h`, and x86's names for the others
    (`si`, `di`, `r8w`, `r9w`), which `reg_name/3` lacks. *)
Definition reg16 (r : string) : string :=
  if String.eqb r "a" then "ax" else if String.eqb r "c" then "cx"
  else if String.eqb r "d" then "dx" else if String.eqb r "si" then "si"
  else if String.eqb r "di" then "di" else r ++ "w".

(** As `att_suffix/2` at a store width: the suffix of a move of that
    width. A pointer and an x87 float have none. *)
Definition width_suffix (w : width) : option string :=
  match w with
  | Wb => Some "b"
  | Wh => Some "w"
  | Ww | Ws => Some "l"
  | Wl | Wd => Some "q"
  | Wp | Wx => None
  end.

(** As `reg_name/3` at a store width: the name of the part of the
    short register r that a store of the width w writes. Only `a`,
    `c` and `d` have a byte and a halfword there. *)
Definition width_reg (r : string) (w : width) : option string :=
  if negb (short_reg r) then None
  else match w with
       | Wb => if narrow_reg r then Some (reg8 r) else None
       | Wh => if narrow_reg r then Some (reg16 r) else None
       | Ww | Ws => Some (reg32 r)
       | Wl | Wd => Some (reg64 r)
       | Wp | Wx => None
       end.

(** As `store_insn/3`: the store of the w-sized part of the short
    register r to `(%rax)`. *)
Definition store_insn (w : width) (r : string) : list line :=
  match width_suffix w, width_reg r w with
  | Some s, Some rn => [ins "mov" s [reg rn; mem 0 "rax"]]
  | _, _ => todo "store width"
  end.

(** ## Extensions and loads *)

(** As `ext_op/5`: the mnemonic and suffix of the move that extends
    the narrow type t to the class k, and its destination register.
    An unsigned byte or halfword extends the same way at every
    class; a word extends only to `l`. *)
Definition ext_op (t : narrow) (k : class) : option (string * string * string) :=
  match t, k with
  | Sb, W => Some ("movsb", "l", "eax")
  | Sb, L => Some ("movsb", "q", "rax")
  | Ub, _ => Some ("movzb", "l", "eax")
  | Sh, W => Some ("movsw", "l", "eax")
  | Sh, L => Some ("movsw", "q", "rax")
  | Uh, _ => Some ("movzw", "l", "eax")
  | Sw, L => Some ("movsl", "q", "rax")
  | Uw, L => Some ("mov", "l", "eax")
  | _, _ => None
  end.

(** As `ext_from/2`: the part of `%rax` that the narrow type t
    extends. *)
Definition ext_from (t : narrow) : string :=
  match t with
  | Sb | Ub => "al"
  | Sh | Uh => "ax"
  | Sw | Uw => "eax"
  end.

(** As `ext_insn/3`: the move that extends the low part of `%rax`
    that t names into `%rax` at the class k. *)
Definition ext_insn (t : narrow) (k : class) : list line :=
  match ext_op t k with
  | Some (op, s, to) => [ins op s [reg (ext_from t); reg to]]
  | None => todo "ext class"
  end.

(** As `sw_load_op/4`: a signed word loads at `w` with a 32-bit
    move, and at `l` as it extends. *)
Definition sw_load_op (k : class) : option (string * string * string) :=
  match k with
  | W => Some ("mov", "l", "eax")
  | L => ext_op Sw L
  | _ => None
  end.

(** As `load_op/5`: as [ext_op], for a load of the type t from
    memory at the class k. An `l`, `s` or `d` loads only at its own
    class, an unsigned word loads with a 32-bit move at every class,
    and an x87 float does not load into `%rax`. *)
Definition load_op (t : load_type) (k : class) : option (string * string * string) :=
  match t, k with
  | LdL, L => Some ("mov", "q", "rax")
  | LdS, Single => Some ("mov", "l", "eax")
  | LdD, Double => Some ("mov", "q", "rax")
  | LdNarrow Sw, _ => sw_load_op k
  | LdNarrow Uw, _ => Some ("mov", "l", "eax")
  | LdNarrow Sb, _ => ext_op Sb k
  | LdNarrow Ub, _ => ext_op Ub k
  | LdNarrow Sh, _ => ext_op Sh k
  | LdNarrow Uh, _ => ext_op Uh k
  | _, _ => None
  end.

(** As `load_insn/3`: the load of a value of the type t from
    `(%rax)` into `%rax`, extended to the class k. *)
Definition load_insn (t : load_type) (k : class) : list line :=
  match load_op t k with
  | Some (op, s, to) => [ins op s [mem 0 "rax"; reg to]]
  | None => todo "load type"
  end.

(** ## Integer arithmetic *)

(** As `alu//4`: the x86 two-operand instruction insn at the class k
    on the two arguments, the first in `%rax` and the second in
    `%rcx`. *)
Definition alu (cx : ctx) (insn : string) (k : class) (args : list value) : list line :=
  match args, class_half k with
  | [x; y], Some half =>
      load cx x k "a" ++ load cx y k "c"
      ++ [ins insn (class_suffix half) [reg (reg_name "c" half); reg (reg_name "a" half)]]
  | [_; _], None => todo "alu class"
  | _, _ => todo "alu arguments"
  end.

(** As `shift//4`: the x86 shift insn at the class k of the first
    argument by the second, a `w` count in `%cl`. *)
Definition shift (cx : ctx) (insn : string) (k : class) (args : list value) : list line :=
  match args, class_half k with
  | [x; y], Some half =>
      load cx x k "a" ++ load cx y W "c"
      ++ [ins insn (class_suffix half) [reg "cl"; reg (reg_name "a" half)]]
  | [_; _], None => todo "shift class"
  | _, _ => todo "shift arguments"
  end.

(** As `zero_divisor//4`: a zero divisor c becomes 1 and the
    dividend a becomes 0, so that quotient and remainder are 0. With
    e 1 if c is 0 and else 0, in d: c is c + e and a is a and
    e - 1. *)
Definition zero_divisor (s a c d : string) : list line :=
  [ins "test" s [reg c; reg c];
   ins0 "sete" [reg "dl"];
   ins "movzb" "l" [reg "dl"; reg "edx"];
   ins "add" s [reg d; reg c];
   ins "sub" s [imm 1; reg d];
   ins "and" s [reg d; reg a]].

(** As `minus_one_divisor//5`: a signed divisor c of -1 becomes 1
    and the dividend a its negation, which wraps the least integer
    to itself where `idiv` would fault. With e 1 if c is -1 and else
    0, in d: c is c + 2e and a is (a xor -e) + e. An unsigned
    division needs none of it. *)
Definition minus_one_divisor (sg : signedness) (s a c d : string) : list line :=
  match sg with
  | Unsigned => []
  | Signed =>
      [ins "cmp" s [imm (-1); reg c];
       ins0 "sete" [reg "dl"];
       ins "movzb" "l" [reg "dl"; reg "edx"];
       ins "add" s [reg d; reg c];
       ins "add" s [reg d; reg c];
       ins "neg" s [reg d];
       ins "xor" s [reg d; reg a];
       ins "sub" s [reg d; reg a]]
  end.

(** As `sign_extension/2`: the instruction that sign-extends `%eax`
    or `%rax` at the class k into `%edx` or `%rdx`. *)
Definition sign_extension (k : class) : option string :=
  match k with
  | W => Some "cltd"
  | L => Some "cqto"
  | _ => None
  end.

(** As `divide//4`: `%rdx:%rax` (or `%edx:%eax`) divided by the
    register c, the upper half extended from `%rax` by the
    signedness sg. *)
Definition divide (sg : signedness) (k : class) (s c : string) : list line :=
  match sg with
  | Signed =>
      match sign_extension k with
      | Some extend => [ins0 extend []; ins "idiv" s [reg c]]
      | None => todo "signed division class"
      end
  | Unsigned => [ins "xor" "l" [reg "edx"; reg "edx"]; ins "div" s [reg c]]
  end.

(** As `division_result//3`: for a remainder, its move from `%rdx`
    to `%rax`; the quotient is already there. *)
Definition division_result (remainder half : bool) : list line :=
  if remainder
  then [ins "mov" (class_suffix half) [reg (reg_name "d" half); reg (reg_name "a" half)]]
  else [].

(** As `division//5`: the division at the class k, signed or
    unsigned by sg, of the first argument by the second, leaving in
    `%rax` the remainder if remainder holds and else the quotient.
    It is total: the operands are first rewritten, without branches,
    so that the divide cannot fault. *)
Definition division (cx : ctx) (sg : signedness) (remainder : bool) (k : class)
    (args : list value) : list line :=
  match args, class_half k with
  | [x; y], Some half =>
      let s := class_suffix half in
      let a := reg_name "a" half in
      let c := reg_name "c" half in
      let d := reg_name "d" half in
      load cx x k "a" ++ load cx y k "c"
      ++ zero_divisor s a c d ++ minus_one_divisor sg s a c d
      ++ divide sg k s c ++ division_result remainder half
  | [_; _], None => todo "division class"
  | _, _ => todo "division arguments"
  end.

(** As `cond_code/2`: the x86 condition code of the integer
    comparison c. A float order has none. *)
Definition cond_code (c : cond) : option string :=
  match c with
  | Eq => Some "e"
  | Ne => Some "ne"
  | Slt => Some "l"
  | Sle => Some "le"
  | Sgt => Some "g"
  | Sge => Some "ge"
  | Ult => Some "b"
  | Ule => Some "be"
  | Ugt => Some "a"
  | Uge => Some "ae"
  | Le | Lt | Ge | Gt | Ord | Unord => None
  end.

(** As the `cmp(Cond, CmpClass)` clause of `compute_op//4`: 1 in
    `%eax` if the two arguments, read at the class ck, compare by
    the integer condition c, else 0. *)
Definition integer_compare (cx : ctx) (c : cond) (ck : class) (args : list value)
  : list line :=
  match args, class_half ck, cond_code c with
  | [x; y], Some half, Some cc =>
      load cx x ck "a" ++ load cx y ck "c"
      ++ [ins "cmp" (class_suffix half) [reg (reg_name "c" half); reg (reg_name "a" half)];
          ins0 ("set" ++ cc) [reg "al"];
          ins "movzb" "l" [reg "al"; reg "eax"]]
  | [_; _], None, _ => todo "cmp class"
  | [_; _], _, None => todo "cmp condition"
  | _, _, _ => todo "cmp arguments"
  end.

(** As the `alloc(Align)` clause of `compute_op//4`, which only the
    plain backend reaches: the size, rounded up to 16 bytes, taken
    from the stack, the stack pointer aligned further when align is
    more than 16, and the new stack pointer in `%rax`. *)
Definition stack_alloc (cx : ctx) (align : Z) (args : list value) : list line :=
  match args with
  | [size] =>
      load cx size L "a"
      ++ [ins "add" "q" [imm fifteen; reg "rax"];
          ins "and" "q" [imm (- sixteen); reg "rax"];
          ins "sub" "q" [reg "rax"; reg "rsp"]]
      ++ (if align >? sixteen then [ins "and" "q" [imm (- align); reg "rsp"]] else [])
      ++ [ins "mov" "q" [reg "rsp"; reg "rax"]]
  | _ => todo "alloc arguments"
  end.

(** ## SSE2 floats *)

(** As `float_suffix/2`: the suffix of a scalar SSE2 instruction at
    the float class k, `s` or `d`. *)
Definition float_suffix (k : class) : option string :=
  match k with
  | Single => Some "ss"
  | Double => Some "sd"
  | _ => None
  end.

(** As amd64.pl's `float_class/1`: whether k is `s` or `d`, the
    float classes SSE2 computes. *)
Definition sse_class (k : class) : bool :=
  match k with Single | Double => true | _ => false end.

(** As `float_bits/2`: the integer class as wide as the float class
    k. *)
Definition float_bits (k : class) : option class :=
  match k with
  | Single => Some W
  | Double => Some L
  | _ => None
  end.

(** As `float_compare/2`: the unordered compare at the float class
    k. *)
Definition float_compare (k : class) : option string :=
  match k with
  | Single => Some "ucomiss"
  | Double => Some "ucomisd"
  | _ => None
  end.

(** As `float_compute/2`: whether the op o at the class k is SSE2's:
    arithmetic at a float class, a comparison of floats, the
    conversions between `s` and `d`, between floats and integers,
    and a cast. *)
Definition float_compute (o : op) (k : class) : bool :=
  match o with
  | Add | Sub | Mul | Div | Neg => sse_class k
  | Cmp _ ck => sse_class ck
  | ExtF Single => class_eqb k Double
  | Truncd => class_eqb k Single
  | Cast => true
  | FloatToInt Single _ | FloatToInt Double _ => true
  | IntToFloat W _ | IntToFloat L _ => true
  | _ => false
  end.

(** As `float_load//4`: the bits of the value v of the float class k
    into the xmm register x, by way of `%rax`. *)
Definition float_load (cx : ctx) (v : value) (k : class) (x : string) : list line :=
  if sse_class k then load cx v k "a" ++ to_xmm k "a" x else todo "float class".

(** The mnemonic stem of the SSE2 arithmetic of the op o, which is
    its own name. *)
Definition float_arith (o : op) : option string :=
  match o with
  | Add => Some "add"
  | Sub => Some "sub"
  | Mul => Some "mul"
  | Div => Some "div"
  | _ => None
  end.

(** As `float_condition//1`: sets `%al` to the float comparison c
    after `ucomiss`, `ucomisd` or `fucomip` compared the operands.
    `eq`, `ne`, `lt` and `le` also read the parity flag, so that an
    unordered compare gives 0, or 1 for `ne`. Writes `%cl`. *)
Definition float_condition (c : cond) : list line :=
  match c with
  | Eq => [ins0 "sete" [reg "al"]; ins0 "setnp" [reg "cl"]; ins "and" "b" [reg "cl"; reg "al"]]
  | Ne => [ins0 "setne" [reg "al"]; ins0 "setp" [reg "cl"]; ins "or" "b" [reg "cl"; reg "al"]]
  | Lt => [ins0 "setb" [reg "al"]; ins0 "setnp" [reg "cl"]; ins "and" "b" [reg "cl"; reg "al"]]
  | Le => [ins0 "setbe" [reg "al"]; ins0 "setnp" [reg "cl"]; ins "and" "b" [reg "cl"; reg "al"]]
  | Gt => [ins0 "seta" [reg "al"]]
  | Ge => [ins0 "setae" [reg "al"]]
  | Ord => [ins0 "setnp" [reg "al"]]
  | Unord => [ins0 "setp" [reg "al"]]
  | _ => todo "float condition"
  end.

(** As `truncate_float//2`: the float of the class f in `%xmm0`,
    truncated to an integer of the class k in `%rax`. *)
Definition truncate_float (f k : class) : list line :=
  match float_suffix f, class_half k with
  | Some s, Some half =>
      [ins ("cvtt" ++ s ++ "2si") (class_suffix half) [reg "xmm0"; reg (reg_name "a" half)]]
  | _, _ => todo "truncate class"
  end.

(** The sign bit of an `s` and of a `d`, and 2^63 as the bits of an
    `s` and of a `d`. *)
Definition single_sign : Z := 2147483648.
Definition double_sign : Z := 9223372036854775808.
Definition single_two63 : Z := 1593835520.
Definition double_two63 : Z := 4890909195324358656.
Definition sixty_three : Z := 63.

(** As `float_integer//4`: the float of the class f in `%xmm0` to an
    integer of the class k in `%rax`, signed or unsigned by sg. An
    unsigned `w` is the low half of the signed `l`. SSE2 has no
    unsigned `l` conversion: a float of 2^63 or more has 2^63
    subtracted, is converted, and gets bit 63 back. *)
Definition float_integer (cx : ctx) (sg : signedness) (f k : class) : list line :=
  match sg, k with
  | Signed, _ => truncate_float f k
  | Unsigned, W => truncate_float f L ++ [ins "mov" "l" [reg "eax"; reg "eax"]]
  | Unsigned, L =>
      match float_compare f, float_suffix f with
      | Some cmp, Some s =>
          let bits := match f with Single => single_two63 | _ => double_two63 end in
          float_load cx (Const bits) f "xmm1"
          ++ [ins0 cmp [reg "xmm1"; reg "xmm0"];
              ins0 "jb" [sym "1f"];
              ins "sub" s [reg "xmm1"; reg "xmm0"]]
          ++ truncate_float f L
          ++ [ins "btc" "q" [imm sixty_three; reg "rax"];
              ins0 "jmp" [sym "2f"];
              label "1"]
          ++ truncate_float f L ++ [label "2"]
      | _, _ => todo "float class"
      end
  | Unsigned, _ => todo "unsigned conversion class"
  end.

(** As `convert_integer//2`: the integer of the class k in `%rax` to
    a float of the class f in `%xmm0`. *)
Definition convert_integer (k f : class) : list line :=
  match float_suffix f, class_half k with
  | Some s, Some half =>
      [ins ("cvtsi2" ++ s) (class_suffix half) [reg (reg_name "a" half); reg "xmm0"]]
  | _, _ => todo "convert class"
  end.

(** As `integer_float//3`: the integer of the class k in `%rax`,
    signed or unsigned by sg, to the nearest float of the class f in
    `%xmm0`. An unsigned `w` converts as the `l` it is. An unsigned
    `l` with bit 63 set is halved, keeping its low bit as a sticky
    bit, converted and doubled, which rounds correctly. *)
Definition integer_float (sg : signedness) (k f : class) : list line :=
  match sg, k with
  | Signed, _ => convert_integer k f
  | Unsigned, W => convert_integer L f
  | Unsigned, L =>
      match float_suffix f with
      | Some s =>
          [ins "test" "q" [reg "rax"; reg "rax"];
           ins0 "jns" [sym "1f"];
           ins "mov" "q" [reg "rax"; reg "rcx"];
           ins "and" "l" [imm 1; reg "ecx"];
           ins "shr" "q" [imm 1; reg "rax"];
           ins "or" "q" [reg "rcx"; reg "rax"]]
          ++ convert_integer L f
          ++ [ins "add" s [reg "xmm0"; reg "xmm0"];
              ins0 "jmp" [sym "2f"];
              label "1"]
          ++ convert_integer L f ++ [label "2"]
      | None => todo "float class"
      end
  | Unsigned, _ => todo "unsigned conversion class"
  end.

(** As `float_op//4`: the code of the SSE2 op o at the class k on
    args, its result's bits in `%rax`.

    - Arithmetic loads its operands into `%xmm0` and `%xmm1`.
    - A negation flips the sign bit in `%rax`.
    - A comparison, whose class is `w`, is 1 or 0 by
      [float_condition].
    - `ext(s)` widens an `s` to a `d` and `truncd` narrows a `d` to
      an `s`.
    - A cast is its operand's bits, read at the class k.
    - A float becomes an integer by [float_integer] and an integer
      a float by [integer_float]. *)
Definition float_op (cx : ctx) (o : op) (k : class) (args : list value) : list line :=
  match o, args with
  | (Add | Sub | Mul | Div), [x; y] =>
      match float_arith o, float_suffix k with
      | Some insn, Some s =>
          float_load cx x k "xmm0" ++ float_load cx y k "xmm1"
          ++ [ins insn s [reg "xmm1"; reg "xmm0"]] ++ from_xmm k "xmm0" "a"
      | _, _ => todo "float class"
      end
  | Neg, [x] =>
      match float_bits k with
      | Some b =>
          let mask := match k with Single => single_sign | _ => double_sign end in
          let half := match k with Single => true | _ => false end in
          load cx x k "a" ++ load cx (Const mask) b "c"
          ++ [ins "xor" (class_suffix half) [reg (reg_name "c" half); reg (reg_name "a" half)]]
      | None => todo "float class"
      end
  | Cmp c ck, [x; y] =>
      match k, float_compare ck with
      | W, Some cmp =>
          float_load cx x ck "xmm0" ++ float_load cx y ck "xmm1"
          ++ [ins0 cmp [reg "xmm1"; reg "xmm0"]]
          ++ float_condition c
          ++ [ins "movzb" "l" [reg "al"; reg "eax"]]
      | _, _ => todo "float cmp class"
      end
  | ExtF Single, [x] =>
      match k with
      | Double =>
          float_load cx x Single "xmm0"
          ++ [ins0 "cvtss2sd" [reg "xmm0"; reg "xmm0"]] ++ from_xmm Double "xmm0" "a"
      | _ => todo "ext class"
      end
  | Truncd, [x] =>
      match k with
      | Single =>
          float_load cx x Double "xmm0"
          ++ [ins0 "cvtsd2ss" [reg "xmm0"; reg "xmm0"]] ++ from_xmm Single "xmm0" "a"
      | _ => todo "truncd class"
      end
  | Cast, [x] => load cx x k "a"
  | FloatToInt f sg, [x] =>
      if sse_class f then float_load cx x f "xmm0" ++ float_integer cx sg f k
      else todo "float op"
  | IntToFloat ik sg, [x] =>
      match ik with
      | W | L =>
          if sse_class k
          then load cx x ik "a" ++ integer_float sg ik k ++ from_xmm k "xmm0" "a"
          else todo "float class"
      | _ => todo "float op"
      end
  | _, _ => todo "float op"
  end.

(** ## compute_op *)

(** As `compute_op//4`: the code that computes the op o at the class
    k on args into `%rax`, zero-extended for the class `w`. An SSE2
    op ([float_compute]) is [float_op]'s; the others are the integer
    clauses, one each. The `load(Type)` clause has no op here: it is
    [load_insn] after the load of the address into `%rax`. *)
Definition compute_op (cx : ctx) (o : op) (k : class) (args : list value) : list line :=
  if float_compute o k then float_op cx o k args
  else
    match o, args with
    | Copy, [x] => load cx x k "a"
    | Neg, [x] =>
        match class_half k with
        | Some half => load cx x k "a" ++ [ins "neg" (class_suffix half) [reg (reg_name "a" half)]]
        | None => todo "neg class"
        end
    | Select, [c; x; y] =>
        load cx y k "a" ++ load cx x k "c" ++ load cx c W "d"
        ++ [ins "test" "l" [reg "edx"; reg "edx"]; ins "cmovne" "q" [reg "rcx"; reg "rax"]]
    | Add, _ => alu cx "add" k args
    | Sub, _ => alu cx "sub" k args
    | Mul, _ => alu cx "imul" k args
    | And, _ => alu cx "and" k args
    | Or, _ => alu cx "or" k args
    | Xor, _ => alu cx "xor" k args
    | Shl, _ => shift cx "shl" k args
    | Shr, _ => shift cx "shr" k args
    | Sar, _ => shift cx "sar" k args
    | Div, _ => division cx Signed false k args
    | Rem, _ => division cx Signed true k args
    | Udiv, _ => division cx Unsigned false k args
    | Urem, _ => division cx Unsigned true k args
    | Cmp c ck, _ => integer_compare cx c ck args
    | Ext t, [x] => load cx x W "a" ++ ext_insn t k
    | Alloc align, _ => stack_alloc cx align args
    | _, _ => todo "compute_op"
    end.

(** ## x87 long double

    An `x` temporary has a 16-byte slot, of which `fldt` and `fstpt`
    use the first 10 bytes. Each instruction pushes its operands on
    the x87 stack, computes and pops the stack empty again. Scalars
    and constants go through the red zone below `%rsp`. *)

(** As `x87_op/3`: whether the op o at the class k is x87's: every
    op at the class `x`, a comparison of `x` values, `truncx`,
    `xtosi` and `xtoui`. The op's kind, which the Prolog relation
    also takes, is the op's own. *)
Definition x87_op (o : op) (k : class) : bool :=
  match k with
  | Extended => true
  | _ =>
      match o with
      | Cmp _ Extended => true
      | Truncx => true
      | FloatToInt Extended _ => true
      | _ => false
      end
  end.

(** The low 64 bits and the low 16 bits of an integer. *)
Definition mask64 : Z := 18446744073709551615.
Definition mask16 : Z := 65535.
Definition sixty_four : Z := 64.

(** As `x87_push//2`: push the `x` value v: a temporary from its
    slot, a constant's 10 bytes through the red zone, by `%rdx`. *)
Definition x87_push (cx : ctx) (v : value) : list line :=
  match v with
  | Tmp n => with_slot cx (KTmp n) (fun off => [ins "fld" "t" [mem (- off) "rbp"]])
  | Const n =>
      load cx (Const (Z.land n mask64)) L "d"
      ++ [ins "mov" "q" [reg "rdx"; mem (-16) "rsp"];
          ins "mov" "w" [imm (Z.land (Z.shiftr n sixty_four) mask16); mem (-8) "rsp"];
          ins "fld" "t" [mem (-16) "rsp"]]
  | Global _ => todo "x87 push of a global"
  end.

(** As `x87_suffix/3`: the suffix of an x87 load or store of the
    float class k, and of the integer move as wide. *)
Definition x87_suffix (k : class) : option (string * string) :=
  match k with
  | Single => Some ("s", "l")
  | Double => Some ("l", "q")
  | _ => None
  end.

(** As `x87_push_float//3`: push the value v of the float class f,
    `s` or `d`, widened exactly. *)
Definition x87_push_float (cx : ctx) (f : class) (v : value) : list line :=
  match x87_suffix f with
  | Some (s, _) =>
      load cx v f "a"
      ++ [ins "mov" "q" [reg "rax"; mem (-8) "rsp"]; ins "fld" s [mem (-8) "rsp"]]
  | None => todo "x87 ext class"
  end.

(** As `x87_pop//2`: pop `%st` into the wide slot of the temporary
    d. *)
Definition x87_pop (cx : ctx) (d : name) : list line :=
  with_slot cx (KTmp d) (fun off => [ins "fstp" "t" [mem (- off) "rbp"]]).

(** As `x87_fisttp//3`: truncate `%st` toward zero into the
    temporary d of the class k and pop it. *)
Definition x87_fisttp (cx : ctx) (k : class) (d : name) : list line :=
  let half := match k with W => true | _ => false end in
  [ins "fisttp" "ll" [mem (-8) "rsp"];
   ins "mov" (class_suffix half) [mem (-8) "rsp"; reg (reg_name "a" half)]]
  ++ slot_store cx "rax" (KTmp d).

(** As `x87_int_source//3`: the integer operand a of the conversion
    o in `%rax`, extended to 64 bits as o reads it. *)
Definition x87_int_source (cx : ctx) (o : op) (a : value) : list line :=
  match o with
  | IntToFloat W Signed => load cx a W "a" ++ [ins "movsl" "q" [reg "eax"; reg "rax"]]
  | IntToFloat W Unsigned => load cx a W "a" ++ [ins "mov" "l" [reg "eax"; reg "eax"]]
  | IntToFloat L _ => load cx a L "a"
  | _ => todo "x87 integer source"
  end.

(** 2^64 as the bits of an `s`. *)
Definition single_two64 : Z := 1602224128.

(** As `x87_unsigned_fix//1`: `fildll` read an unsigned `l` with bit
    63 set as negative; `ultof` adds 2^64 to it, exactly. *)
Definition x87_unsigned_fix (o : op) : list line :=
  match o with
  | IntToFloat L Unsigned =>
      [ins "test" "q" [reg "rax"; reg "rax"];
       ins0 "jns" [sym "1f"];
       ins "mov" "l" [imm single_two64; mem (-12) "rsp"];
       ins "fadd" "s" [mem (-12) "rsp"];
       label "1"]
  | _ => []
  end.

(** The x87 arithmetic of the op o. *)
Definition x87_arith (o : op) : option string :=
  match o with
  | Add => Some "fadd"
  | Sub => Some "fsub"
  | Mul => Some "fmul"
  | Div => Some "fdiv"
  | _ => None
  end.

(** As `x87_inst//5`: the code of the temporary d as the op o at the
    class k on args, with x87. Operands are pushed in reverse, so
    `%st` is the first and `%st(1)` the second.

    - Arithmetic, a negation and a copy leave an `x` in d's slot.
    - A comparison leaves 1 or 0 by [float_condition].
    - `ext(s)` and `ext(d)` widen to an `x`; `truncx` rounds an `x`
      to the class k, `s` or `d`.
    - `xtosi` and `xtoui` truncate an `x` to an integer; an unsigned
      `l` of 2^63 or more has 2^63 subtracted and bit 63 restored.
    - `swtof`, `uwtof`, `sltof` and `ultof` at `x` load the integer
      as 64 bits. *)
Definition x87_inst (cx : ctx) (o : op) (k : class) (args : list value) (d : name)
  : list line :=
  match o, k, args with
  | (Add | Sub | Mul | Div), Extended, [a; b] =>
      match x87_arith o with
      | Some insn =>
          x87_push cx b ++ x87_push cx a
          ++ [ins0 insn [reg "st(1)"; reg "st"]]
          ++ x87_pop cx d ++ [ins0 "fstp" [reg "st(0)"]]
      | None => todo "x87 op"
      end
  | Neg, Extended, [a] => x87_push cx a ++ [ins0 "fchs" []] ++ x87_pop cx d
  | Copy, Extended, [a] => x87_push cx a ++ x87_pop cx d
  | Cmp c Extended, W, [a; b] =>
      x87_push cx b ++ x87_push cx a
      ++ [ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]]
      ++ float_condition c
      ++ [ins "movzb" "l" [reg "al"; reg "eax"]]
      ++ slot_store cx "rax" (KTmp d)
  | ExtF f, Extended, [a] => x87_push_float cx f a ++ x87_pop cx d
  | Truncx, _, [a] =>
      match x87_suffix k with
      | Some (s, mov) =>
          x87_push cx a
          ++ [ins "fstp" s [mem (-8) "rsp"];
              ins "mov" mov [mem (-8) "rsp"; reg (if String.eqb mov "l" then "eax" else "rax")]]
          ++ slot_store cx "rax" (KTmp d)
      | None => todo "x87 truncx class"
      end
  | FloatToInt Extended Signed, _, [a] => x87_push cx a ++ x87_fisttp cx k d
  | FloatToInt Extended Unsigned, W, [a] => x87_push cx a ++ x87_fisttp cx W d
  | FloatToInt Extended Unsigned, L, [a] =>
      x87_push cx a
      ++ [ins "mov" "l" [imm single_two63; mem (-12) "rsp"];
          ins "fld" "s" [mem (-12) "rsp"];
          ins0 "fucomip" [reg "st(1)"; reg "st"];
          ins0 "ja" [sym "1f"];
          ins "fsub" "s" [mem (-12) "rsp"];
          ins "fisttp" "ll" [mem (-8) "rsp"];
          ins "mov" "q" [mem (-8) "rsp"; reg "rax"];
          ins "btc" "q" [imm sixty_three; reg "rax"];
          ins0 "jmp" [sym "2f"];
          label "1";
          ins "fisttp" "ll" [mem (-8) "rsp"];
          ins "mov" "q" [mem (-8) "rsp"; reg "rax"];
          label "2"]
      ++ slot_store cx "rax" (KTmp d)
  | IntToFloat (W | L) _, Extended, [a] =>
      x87_int_source cx o a
      ++ [ins "mov" "q" [reg "rax"; mem (-8) "rsp"]; ins "fild" "ll" [mem (-8) "rsp"]]
      ++ x87_unsigned_fix o
      ++ x87_pop cx d
  | _, _, _ => todo "x87 op"
  end.

(** ## Examples

    Each states that a definition gives the very lines the Prolog
    compiler gave. The lines are copied from its output, not from the
    code above. *)

(** The temporary of the name s. *)
Definition ex_tmp (s : string) : value := Tmp (TAtom s).

(** The slots m with the temporary s at `-off(%rbp)`. *)
Definition ex_slot (s : string) (off : Z) (m : nmap Z) : nmap Z :=
  nm_add (key_term (KTmp (TAtom s))) off m.

(** Whether the lines ls hold a [todo]. *)
Definition ex_todo (ls : list line) : bool :=
  existsb (fun l => match l with Ins o _ _ => String.eqb o todo_op | _ => false end) ls.

(** ### Integer ops

    `compute_op` on the instructions of a function `ints`, as
    `asm-terms` printed them in the stack-homed mode. *)

Definition int_cx : ctx :=
  mkCtx "ints"
    (ex_slot "a" 24
    (ex_slot "b" 8
    (ex_slot "c" 32
    (ex_slot "d" 16 nm_empty))))
    nm_empty 0 0 nm_empty.

(* let(tmp(t1), w, add, [tmp(a), tmp(b)]) *)
Example int_t1 :
  compute_op int_cx Add W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "add" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t2), l, add, [tmp(c), tmp(d)]) *)
Example int_t2 :
  compute_op int_cx Add L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "add" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t3), w, sub, [tmp(a), tmp(b)]) *)
Example int_t3 :
  compute_op int_cx Sub W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "sub" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t4), l, sub, [tmp(c), tmp(d)]) *)
Example int_t4 :
  compute_op int_cx Sub L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "sub" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t5), w, mul, [tmp(a), tmp(b)]) *)
Example int_t5 :
  compute_op int_cx Mul W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "imul" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t6), l, mul, [tmp(c), tmp(d)]) *)
Example int_t6 :
  compute_op int_cx Mul L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "imul" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t7), w, and, [tmp(a), tmp(b)]) *)
Example int_t7 :
  compute_op int_cx And W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "and" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t8), l, and, [tmp(c), tmp(d)]) *)
Example int_t8 :
  compute_op int_cx And L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "and" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t9), w, or, [tmp(a), tmp(b)]) *)
Example int_t9 :
  compute_op int_cx Or W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "or" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t10), l, or, [tmp(c), tmp(d)]) *)
Example int_t10 :
  compute_op int_cx Or L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "or" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t11), w, xor, [tmp(a), tmp(b)]) *)
Example int_t11 :
  compute_op int_cx Xor W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "xor" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t12), l, xor, [tmp(c), tmp(d)]) *)
Example int_t12 :
  compute_op int_cx Xor L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "xor" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t13), w, shl, [tmp(a), tmp(b)]) *)
Example int_t13 :
  compute_op int_cx Shl W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "shl" "l" [reg "cl"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t14), l, shl, [tmp(c), tmp(b)]) *)
Example int_t14 :
  compute_op int_cx Shl L [ex_tmp "c"; ex_tmp "b"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "shl" "q" [reg "cl"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t15), w, shr, [tmp(a), tmp(b)]) *)
Example int_t15 :
  compute_op int_cx Shr W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "shr" "l" [reg "cl"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t16), l, shr, [tmp(c), tmp(b)]) *)
Example int_t16 :
  compute_op int_cx Shr L [ex_tmp "c"; ex_tmp "b"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "shr" "q" [reg "cl"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t17), w, sar, [tmp(a), tmp(b)]) *)
Example int_t17 :
  compute_op int_cx Sar W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "sar" "l" [reg "cl"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t18), l, sar, [tmp(c), tmp(b)]) *)
Example int_t18 :
  compute_op int_cx Sar L [ex_tmp "c"; ex_tmp "b"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "sar" "q" [reg "cl"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t19), w, div, [tmp(a), tmp(b)]) *)
Example int_t19 :
  compute_op int_cx Div W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "test" "l" [reg "ecx"; reg "ecx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "l" [reg "edx"; reg "ecx"];
     ins "sub" "l" [imm 1; reg "edx"]; ins "and" "l" [reg "edx"; reg "eax"];
     ins "cmp" "l" [imm (-1); reg "ecx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "l" [reg "edx"; reg "ecx"];
     ins "add" "l" [reg "edx"; reg "ecx"]; ins "neg" "l" [reg "edx"];
     ins "xor" "l" [reg "edx"; reg "eax"]; ins "sub" "l" [reg "edx"; reg "eax"]; ins0 "cltd" [];
     ins "idiv" "l" [reg "ecx"]].
Proof. reflexivity. Qed.

(* let(tmp(t20), l, div, [tmp(c), tmp(d)]) *)
Example int_t20 :
  compute_op int_cx Div L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "test" "q" [reg "rcx"; reg "rcx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "q" [reg "rdx"; reg "rcx"];
     ins "sub" "q" [imm 1; reg "rdx"]; ins "and" "q" [reg "rdx"; reg "rax"];
     ins "cmp" "q" [imm (-1); reg "rcx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "q" [reg "rdx"; reg "rcx"];
     ins "add" "q" [reg "rdx"; reg "rcx"]; ins "neg" "q" [reg "rdx"];
     ins "xor" "q" [reg "rdx"; reg "rax"]; ins "sub" "q" [reg "rdx"; reg "rax"]; ins0 "cqto" [];
     ins "idiv" "q" [reg "rcx"]].
Proof. reflexivity. Qed.

(* let(tmp(t21), w, rem, [tmp(a), tmp(b)]) *)
Example int_t21 :
  compute_op int_cx Rem W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "test" "l" [reg "ecx"; reg "ecx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "l" [reg "edx"; reg "ecx"];
     ins "sub" "l" [imm 1; reg "edx"]; ins "and" "l" [reg "edx"; reg "eax"];
     ins "cmp" "l" [imm (-1); reg "ecx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "l" [reg "edx"; reg "ecx"];
     ins "add" "l" [reg "edx"; reg "ecx"]; ins "neg" "l" [reg "edx"];
     ins "xor" "l" [reg "edx"; reg "eax"]; ins "sub" "l" [reg "edx"; reg "eax"]; ins0 "cltd" [];
     ins "idiv" "l" [reg "ecx"]; ins "mov" "l" [reg "edx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t22), l, rem, [tmp(c), tmp(d)]) *)
Example int_t22 :
  compute_op int_cx Rem L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "test" "q" [reg "rcx"; reg "rcx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "q" [reg "rdx"; reg "rcx"];
     ins "sub" "q" [imm 1; reg "rdx"]; ins "and" "q" [reg "rdx"; reg "rax"];
     ins "cmp" "q" [imm (-1); reg "rcx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "q" [reg "rdx"; reg "rcx"];
     ins "add" "q" [reg "rdx"; reg "rcx"]; ins "neg" "q" [reg "rdx"];
     ins "xor" "q" [reg "rdx"; reg "rax"]; ins "sub" "q" [reg "rdx"; reg "rax"]; ins0 "cqto" [];
     ins "idiv" "q" [reg "rcx"]; ins "mov" "q" [reg "rdx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t23), w, udiv, [tmp(a), tmp(b)]) *)
Example int_t23 :
  compute_op int_cx Udiv W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "test" "l" [reg "ecx"; reg "ecx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "l" [reg "edx"; reg "ecx"];
     ins "sub" "l" [imm 1; reg "edx"]; ins "and" "l" [reg "edx"; reg "eax"];
     ins "xor" "l" [reg "edx"; reg "edx"]; ins "div" "l" [reg "ecx"]].
Proof. reflexivity. Qed.

(* let(tmp(t24), l, udiv, [tmp(c), tmp(d)]) *)
Example int_t24 :
  compute_op int_cx Udiv L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "test" "q" [reg "rcx"; reg "rcx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "q" [reg "rdx"; reg "rcx"];
     ins "sub" "q" [imm 1; reg "rdx"]; ins "and" "q" [reg "rdx"; reg "rax"];
     ins "xor" "l" [reg "edx"; reg "edx"]; ins "div" "q" [reg "rcx"]].
Proof. reflexivity. Qed.

(* let(tmp(t25), w, urem, [tmp(a), tmp(b)]) *)
Example int_t25 :
  compute_op int_cx Urem W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "test" "l" [reg "ecx"; reg "ecx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "l" [reg "edx"; reg "ecx"];
     ins "sub" "l" [imm 1; reg "edx"]; ins "and" "l" [reg "edx"; reg "eax"];
     ins "xor" "l" [reg "edx"; reg "edx"]; ins "div" "l" [reg "ecx"];
     ins "mov" "l" [reg "edx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t26), l, urem, [tmp(c), tmp(d)]) *)
Example int_t26 :
  compute_op int_cx Urem L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "mov" "q" [mem (-16) "rbp"; reg "rcx"];
     ins "test" "q" [reg "rcx"; reg "rcx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "q" [reg "rdx"; reg "rcx"];
     ins "sub" "q" [imm 1; reg "rdx"]; ins "and" "q" [reg "rdx"; reg "rax"];
     ins "xor" "l" [reg "edx"; reg "edx"]; ins "div" "q" [reg "rcx"];
     ins "mov" "q" [reg "rdx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t27), w, neg, [tmp(a)]) *)
Example int_t27 :
  compute_op int_cx Neg W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "neg" "l" [reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t28), l, neg, [tmp(c)]) *)
Example int_t28 :
  compute_op int_cx Neg L [ex_tmp "c"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "neg" "q" [reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t29), w, copy, [tmp(a)]) *)
Example int_t29 :
  compute_op int_cx Copy W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t30), l, copy, [tmp(c)]) *)
Example int_t30 :
  compute_op int_cx Copy L [ex_tmp "c"]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t31), w, add, [tmp(a), const(-1)]) *)
Example int_t31 :
  compute_op int_cx Add W [ex_tmp "a"; Const (-1)]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [imm 4294967295; reg "ecx"];
     ins "add" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t32), l, add, [tmp(c), const(-1)]) *)
Example int_t32 :
  compute_op int_cx Add L [ex_tmp "c"; Const (-1)]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"]; ins "movabs" "q" [imm (-1); reg "rcx"];
     ins "add" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t33), l, add, [tmp(c), const(9223372036854775807)]) *)
Example int_t33 :
  compute_op int_cx Add L [ex_tmp "c"; Const 9223372036854775807]
  = [ins "mov" "q" [mem (-32) "rbp"; reg "rax"];
     ins "movabs" "q" [imm 9223372036854775807; reg "rcx"]; ins "add" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.


(** ### Integer comparisons and extensions *)

Definition cmp_cx : ctx :=
  mkCtx "cmps"
    (ex_slot "a" 32
    (ex_slot "b" 8
    (ex_slot "c" 16
    (ex_slot "d" 24 nm_empty))))
    nm_empty 0 0 nm_empty.

(* let(tmp(t1), w, cmp(eq, w), [tmp(a), tmp(b)]) *)
Example cmp_t1 :
  compute_op cmp_cx (Cmp Eq W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "sete" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t2), w, cmp(eq, l), [tmp(c), tmp(d)]) *)
Example cmp_t2 :
  compute_op cmp_cx (Cmp Eq L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "sete" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t3), w, cmp(ne, w), [tmp(a), tmp(b)]) *)
Example cmp_t3 :
  compute_op cmp_cx (Cmp Ne W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "setne" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t4), w, cmp(ne, l), [tmp(c), tmp(d)]) *)
Example cmp_t4 :
  compute_op cmp_cx (Cmp Ne L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setne" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t5), w, cmp(slt, w), [tmp(a), tmp(b)]) *)
Example cmp_t5 :
  compute_op cmp_cx (Cmp Slt W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "setl" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t6), w, cmp(slt, l), [tmp(c), tmp(d)]) *)
Example cmp_t6 :
  compute_op cmp_cx (Cmp Slt L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setl" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t7), w, cmp(sle, w), [tmp(a), tmp(b)]) *)
Example cmp_t7 :
  compute_op cmp_cx (Cmp Sle W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "setle" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t8), w, cmp(sle, l), [tmp(c), tmp(d)]) *)
Example cmp_t8 :
  compute_op cmp_cx (Cmp Sle L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setle" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t9), w, cmp(sgt, w), [tmp(a), tmp(b)]) *)
Example cmp_t9 :
  compute_op cmp_cx (Cmp Sgt W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "setg" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t10), w, cmp(sgt, l), [tmp(c), tmp(d)]) *)
Example cmp_t10 :
  compute_op cmp_cx (Cmp Sgt L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setg" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t11), w, cmp(sge, w), [tmp(a), tmp(b)]) *)
Example cmp_t11 :
  compute_op cmp_cx (Cmp Sge W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "setge" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t12), w, cmp(sge, l), [tmp(c), tmp(d)]) *)
Example cmp_t12 :
  compute_op cmp_cx (Cmp Sge L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setge" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t13), w, cmp(ult, w), [tmp(a), tmp(b)]) *)
Example cmp_t13 :
  compute_op cmp_cx (Cmp Ult W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "setb" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t14), w, cmp(ult, l), [tmp(c), tmp(d)]) *)
Example cmp_t14 :
  compute_op cmp_cx (Cmp Ult L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setb" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t15), w, cmp(ule, w), [tmp(a), tmp(b)]) *)
Example cmp_t15 :
  compute_op cmp_cx (Cmp Ule W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "setbe" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t16), w, cmp(ule, l), [tmp(c), tmp(d)]) *)
Example cmp_t16 :
  compute_op cmp_cx (Cmp Ule L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setbe" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t17), w, cmp(ugt, w), [tmp(a), tmp(b)]) *)
Example cmp_t17 :
  compute_op cmp_cx (Cmp Ugt W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "seta" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t18), w, cmp(ugt, l), [tmp(c), tmp(d)]) *)
Example cmp_t18 :
  compute_op cmp_cx (Cmp Ugt L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "seta" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t19), w, cmp(uge, w), [tmp(a), tmp(b)]) *)
Example cmp_t19 :
  compute_op cmp_cx (Cmp Uge W) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "setae" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t20), w, cmp(uge, l), [tmp(c), tmp(d)]) *)
Example cmp_t20 :
  compute_op cmp_cx (Cmp Uge L) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setae" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t21), l, cmp(eq, w), [tmp(a), tmp(b)]) *)
Example cmp_t21 :
  compute_op cmp_cx (Cmp Eq W) L [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "sete" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t22), l, cmp(ult, l), [tmp(c), tmp(d)]) *)
Example cmp_t22 :
  compute_op cmp_cx (Cmp Ult L) L [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [mem (-24) "rbp"; reg "rcx"];
     ins "cmp" "q" [reg "rcx"; reg "rax"]; ins0 "setb" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t23), w, ext(sb), [tmp(a)]) *)
Example cmp_t23 :
  compute_op cmp_cx (Ext Sb) W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movsb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t24), l, ext(sb), [tmp(a)]) *)
Example cmp_t24 :
  compute_op cmp_cx (Ext Sb) L [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movsb" "q" [reg "al"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t25), w, ext(ub), [tmp(a)]) *)
Example cmp_t25 :
  compute_op cmp_cx (Ext Ub) W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t26), l, ext(ub), [tmp(a)]) *)
Example cmp_t26 :
  compute_op cmp_cx (Ext Ub) L [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t27), w, ext(sh), [tmp(a)]) *)
Example cmp_t27 :
  compute_op cmp_cx (Ext Sh) W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movsw" "l" [reg "ax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t28), l, ext(sh), [tmp(a)]) *)
Example cmp_t28 :
  compute_op cmp_cx (Ext Sh) L [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movsw" "q" [reg "ax"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t29), w, ext(uh), [tmp(a)]) *)
Example cmp_t29 :
  compute_op cmp_cx (Ext Uh) W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movzw" "l" [reg "ax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t30), l, ext(uh), [tmp(a)]) *)
Example cmp_t30 :
  compute_op cmp_cx (Ext Uh) L [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movzw" "l" [reg "ax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t31), l, ext(sw), [tmp(a)]) *)
Example cmp_t31 :
  compute_op cmp_cx (Ext Sw) L [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movsl" "q" [reg "eax"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t32), l, ext(uw), [tmp(a)]) *)
Example cmp_t32 :
  compute_op cmp_cx (Ext Uw) L [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [reg "eax"; reg "eax"]].
Proof. reflexivity. Qed.


(** ### SSE2 floats *)

Definition flt_cx : ctx :=
  mkCtx "flts"
    (ex_slot "a" 32
    (ex_slot "b" 8
    (ex_slot "c" 40
    (ex_slot "d" 16
    (ex_slot "i" 48
    (ex_slot "j" 24 nm_empty))))))
    nm_empty 0 0 nm_empty.

(* let(tmp(t1), s, add, [tmp(a), tmp(b)]) *)
Example flt_t1 :
  compute_op flt_cx Add Single [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins "add" "ss" [reg "xmm1"; reg "xmm0"]; ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t2), d, add, [tmp(c), tmp(d)]) *)
Example flt_t2 :
  compute_op flt_cx Add Double [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins "add" "sd" [reg "xmm1"; reg "xmm0"]; ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t3), s, sub, [tmp(a), tmp(b)]) *)
Example flt_t3 :
  compute_op flt_cx Sub Single [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins "sub" "ss" [reg "xmm1"; reg "xmm0"]; ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t4), d, sub, [tmp(c), tmp(d)]) *)
Example flt_t4 :
  compute_op flt_cx Sub Double [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins "sub" "sd" [reg "xmm1"; reg "xmm0"]; ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t5), s, mul, [tmp(a), tmp(b)]) *)
Example flt_t5 :
  compute_op flt_cx Mul Single [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins "mul" "ss" [reg "xmm1"; reg "xmm0"]; ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t6), d, mul, [tmp(c), tmp(d)]) *)
Example flt_t6 :
  compute_op flt_cx Mul Double [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins "mul" "sd" [reg "xmm1"; reg "xmm0"]; ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t7), s, div, [tmp(a), tmp(b)]) *)
Example flt_t7 :
  compute_op flt_cx Div Single [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins "div" "ss" [reg "xmm1"; reg "xmm0"]; ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t8), d, div, [tmp(c), tmp(d)]) *)
Example flt_t8 :
  compute_op flt_cx Div Double [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins "div" "sd" [reg "xmm1"; reg "xmm0"]; ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t9), s, neg, [tmp(a)]) *)
Example flt_t9 :
  compute_op flt_cx Neg Single [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [imm 2147483648; reg "ecx"];
     ins "xor" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t10), d, neg, [tmp(c)]) *)
Example flt_t10 :
  compute_op flt_cx Neg Double [ex_tmp "c"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"];
     ins "movabs" "q" [imm (-9223372036854775808); reg "rcx"];
     ins "xor" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t11), s, copy, [tmp(a)]) *)
Example flt_t11 :
  compute_op flt_cx Copy Single [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t12), d, copy, [tmp(c)]) *)
Example flt_t12 :
  compute_op flt_cx Copy Double [ex_tmp "c"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t13), w, cmp(eq, s), [tmp(a), tmp(b)]) *)
Example flt_t13 :
  compute_op flt_cx (Cmp Eq Single) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "sete" [reg "al"]; ins0 "setnp" [reg "cl"];
     ins "and" "b" [reg "cl"; reg "al"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t14), w, cmp(eq, d), [tmp(c), tmp(d)]) *)
Example flt_t14 :
  compute_op flt_cx (Cmp Eq Double) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "sete" [reg "al"]; ins0 "setnp" [reg "cl"];
     ins "and" "b" [reg "cl"; reg "al"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t15), w, cmp(ne, s), [tmp(a), tmp(b)]) *)
Example flt_t15 :
  compute_op flt_cx (Cmp Ne Single) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "setne" [reg "al"]; ins0 "setp" [reg "cl"];
     ins "or" "b" [reg "cl"; reg "al"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t16), w, cmp(ne, d), [tmp(c), tmp(d)]) *)
Example flt_t16 :
  compute_op flt_cx (Cmp Ne Double) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "setne" [reg "al"]; ins0 "setp" [reg "cl"];
     ins "or" "b" [reg "cl"; reg "al"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t17), w, cmp(lt, s), [tmp(a), tmp(b)]) *)
Example flt_t17 :
  compute_op flt_cx (Cmp Lt Single) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "setb" [reg "al"]; ins0 "setnp" [reg "cl"];
     ins "and" "b" [reg "cl"; reg "al"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t18), w, cmp(lt, d), [tmp(c), tmp(d)]) *)
Example flt_t18 :
  compute_op flt_cx (Cmp Lt Double) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "setb" [reg "al"]; ins0 "setnp" [reg "cl"];
     ins "and" "b" [reg "cl"; reg "al"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t19), w, cmp(le, s), [tmp(a), tmp(b)]) *)
Example flt_t19 :
  compute_op flt_cx (Cmp Le Single) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "setbe" [reg "al"]; ins0 "setnp" [reg "cl"];
     ins "and" "b" [reg "cl"; reg "al"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t20), w, cmp(le, d), [tmp(c), tmp(d)]) *)
Example flt_t20 :
  compute_op flt_cx (Cmp Le Double) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "setbe" [reg "al"]; ins0 "setnp" [reg "cl"];
     ins "and" "b" [reg "cl"; reg "al"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t21), w, cmp(gt, s), [tmp(a), tmp(b)]) *)
Example flt_t21 :
  compute_op flt_cx (Cmp Gt Single) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "seta" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t22), w, cmp(gt, d), [tmp(c), tmp(d)]) *)
Example flt_t22 :
  compute_op flt_cx (Cmp Gt Double) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "seta" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t23), w, cmp(ge, s), [tmp(a), tmp(b)]) *)
Example flt_t23 :
  compute_op flt_cx (Cmp Ge Single) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "setae" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t24), w, cmp(ge, d), [tmp(c), tmp(d)]) *)
Example flt_t24 :
  compute_op flt_cx (Cmp Ge Double) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "setae" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t25), w, cmp(o, s), [tmp(a), tmp(b)]) *)
Example flt_t25 :
  compute_op flt_cx (Cmp Ord Single) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "setnp" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t26), w, cmp(o, d), [tmp(c), tmp(d)]) *)
Example flt_t26 :
  compute_op flt_cx (Cmp Ord Double) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "setnp" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t27), w, cmp(uo, s), [tmp(a), tmp(b)]) *)
Example flt_t27 :
  compute_op flt_cx (Cmp Unord Single) W [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "setp" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t28), w, cmp(uo, d), [tmp(c), tmp(d)]) *)
Example flt_t28 :
  compute_op flt_cx (Cmp Unord Double) W [ex_tmp "c"; ex_tmp "d"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "setp" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t29), d, ext(s), [tmp(a)]) *)
Example flt_t29 :
  compute_op flt_cx (ExtF Single) Double [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins0 "cvtss2sd" [reg "xmm0"; reg "xmm0"]; ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t30), s, truncd, [tmp(c)]) *)
Example flt_t30 :
  compute_op flt_cx Truncd Single [ex_tmp "c"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins0 "cvtsd2ss" [reg "xmm0"; reg "xmm0"]; ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t31), w, cast, [tmp(a)]) *)
Example flt_t31 :
  compute_op flt_cx Cast W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t32), l, cast, [tmp(c)]) *)
Example flt_t32 :
  compute_op flt_cx Cast L [ex_tmp "c"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t33), s, cast, [tmp(i)]) *)
Example flt_t33 :
  compute_op flt_cx Cast Single [ex_tmp "i"]
  = [ins "mov" "l" [mem (-48) "rbp"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t34), d, cast, [tmp(j)]) *)
Example flt_t34 :
  compute_op flt_cx Cast Double [ex_tmp "j"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t35), w, stosi, [tmp(a)]) *)
Example flt_t35 :
  compute_op flt_cx (FloatToInt Single Signed) W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "cvttss2si" "l" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t36), w, stoui, [tmp(a)]) *)
Example flt_t36 :
  compute_op flt_cx (FloatToInt Single Unsigned) W [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "cvttss2si" "q" [reg "xmm0"; reg "rax"]; ins "mov" "l" [reg "eax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t37), w, dtosi, [tmp(c)]) *)
Example flt_t37 :
  compute_op flt_cx (FloatToInt Double Signed) W [ex_tmp "c"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "cvttsd2si" "l" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t38), w, dtoui, [tmp(c)]) *)
Example flt_t38 :
  compute_op flt_cx (FloatToInt Double Unsigned) W [ex_tmp "c"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "cvttsd2si" "q" [reg "xmm0"; reg "rax"]; ins "mov" "l" [reg "eax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t39), l, stosi, [tmp(a)]) *)
Example flt_t39 :
  compute_op flt_cx (FloatToInt Single Signed) L [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "cvttss2si" "q" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t40), l, stoui, [tmp(a)]) *)
Example flt_t40 :
  compute_op flt_cx (FloatToInt Single Unsigned) L [ex_tmp "a"]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [imm 1593835520; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins0 "ucomiss" [reg "xmm1"; reg "xmm0"]; ins0 "jb" [sym "1f"];
     ins "sub" "ss" [reg "xmm1"; reg "xmm0"]; ins "cvttss2si" "q" [reg "xmm0"; reg "rax"];
     ins "btc" "q" [imm 63; reg "rax"]; ins0 "jmp" [sym "2f"]; label "1";
     ins "cvttss2si" "q" [reg "xmm0"; reg "rax"]; label "2"].
Proof. reflexivity. Qed.

(* let(tmp(t41), l, dtosi, [tmp(c)]) *)
Example flt_t41 :
  compute_op flt_cx (FloatToInt Double Signed) L [ex_tmp "c"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "cvttsd2si" "q" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t42), l, dtoui, [tmp(c)]) *)
Example flt_t42 :
  compute_op flt_cx (FloatToInt Double Unsigned) L [ex_tmp "c"]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "movabs" "q" [imm 4890909195324358656; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins0 "ucomisd" [reg "xmm1"; reg "xmm0"]; ins0 "jb" [sym "1f"];
     ins "sub" "sd" [reg "xmm1"; reg "xmm0"]; ins "cvttsd2si" "q" [reg "xmm0"; reg "rax"];
     ins "btc" "q" [imm 63; reg "rax"]; ins0 "jmp" [sym "2f"]; label "1";
     ins "cvttsd2si" "q" [reg "xmm0"; reg "rax"]; label "2"].
Proof. reflexivity. Qed.

(* let(tmp(t43), s, swtof, [tmp(i)]) *)
Example flt_t43 :
  compute_op flt_cx (IntToFloat W Signed) Single [ex_tmp "i"]
  = [ins "mov" "l" [mem (-48) "rbp"; reg "eax"]; ins "cvtsi2ss" "l" [reg "eax"; reg "xmm0"];
     ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t44), s, uwtof, [tmp(i)]) *)
Example flt_t44 :
  compute_op flt_cx (IntToFloat W Unsigned) Single [ex_tmp "i"]
  = [ins "mov" "l" [mem (-48) "rbp"; reg "eax"]; ins "cvtsi2ss" "q" [reg "rax"; reg "xmm0"];
     ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t45), s, sltof, [tmp(j)]) *)
Example flt_t45 :
  compute_op flt_cx (IntToFloat L Signed) Single [ex_tmp "j"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "cvtsi2ss" "q" [reg "rax"; reg "xmm0"];
     ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t46), s, ultof, [tmp(j)]) *)
Example flt_t46 :
  compute_op flt_cx (IntToFloat L Unsigned) Single [ex_tmp "j"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "test" "q" [reg "rax"; reg "rax"];
     ins0 "jns" [sym "1f"]; ins "mov" "q" [reg "rax"; reg "rcx"]; ins "and" "l" [imm 1; reg "ecx"];
     ins "shr" "q" [imm 1; reg "rax"]; ins "or" "q" [reg "rcx"; reg "rax"];
     ins "cvtsi2ss" "q" [reg "rax"; reg "xmm0"]; ins "add" "ss" [reg "xmm0"; reg "xmm0"];
     ins0 "jmp" [sym "2f"]; label "1"; ins "cvtsi2ss" "q" [reg "rax"; reg "xmm0"]; label "2";
     ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t47), d, swtof, [tmp(i)]) *)
Example flt_t47 :
  compute_op flt_cx (IntToFloat W Signed) Double [ex_tmp "i"]
  = [ins "mov" "l" [mem (-48) "rbp"; reg "eax"]; ins "cvtsi2sd" "l" [reg "eax"; reg "xmm0"];
     ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t48), d, uwtof, [tmp(i)]) *)
Example flt_t48 :
  compute_op flt_cx (IntToFloat W Unsigned) Double [ex_tmp "i"]
  = [ins "mov" "l" [mem (-48) "rbp"; reg "eax"]; ins "cvtsi2sd" "q" [reg "rax"; reg "xmm0"];
     ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t49), d, sltof, [tmp(j)]) *)
Example flt_t49 :
  compute_op flt_cx (IntToFloat L Signed) Double [ex_tmp "j"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "cvtsi2sd" "q" [reg "rax"; reg "xmm0"];
     ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t50), d, ultof, [tmp(j)]) *)
Example flt_t50 :
  compute_op flt_cx (IntToFloat L Unsigned) Double [ex_tmp "j"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "test" "q" [reg "rax"; reg "rax"];
     ins0 "jns" [sym "1f"]; ins "mov" "q" [reg "rax"; reg "rcx"]; ins "and" "l" [imm 1; reg "ecx"];
     ins "shr" "q" [imm 1; reg "rax"]; ins "or" "q" [reg "rcx"; reg "rax"];
     ins "cvtsi2sd" "q" [reg "rax"; reg "xmm0"]; ins "add" "sd" [reg "xmm0"; reg "xmm0"];
     ins0 "jmp" [sym "2f"]; label "1"; ins "cvtsi2sd" "q" [reg "rax"; reg "xmm0"]; label "2";
     ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t51), s, add, [tmp(a), const(1069547520)]) *)
Example flt_t51 :
  compute_op flt_cx Add Single [ex_tmp "a"; Const 1069547520]
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm0"];
     ins "mov" "l" [imm 1069547520; reg "eax"]; ins0 "movd" [reg "eax"; reg "xmm1"];
     ins "add" "ss" [reg "xmm1"; reg "xmm0"]; ins0 "movd" [reg "xmm0"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t52), d, add, [tmp(c), const(4621819117588971520)]) *)
Example flt_t52 :
  compute_op flt_cx Add Double [ex_tmp "c"; Const 4621819117588971520]
  = [ins "mov" "q" [mem (-40) "rbp"; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm0"];
     ins "movabs" "q" [imm 4621819117588971520; reg "rax"]; ins0 "movq" [reg "rax"; reg "xmm1"];
     ins "add" "sd" [reg "xmm1"; reg "xmm0"]; ins0 "movq" [reg "xmm0"; reg "rax"]].
Proof. reflexivity. Qed.


(** ### Loads and stores

    The access itself of each raw load and store, after its checks. *)

(* let(tmp(t1), l, load(l), [tmp(p)]) *)
Example load_l_l :
  load_insn LdL L
  = [ins "mov" "q" [mem 0 "rax"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t2), s, load(s), [tmp(p)]) *)
Example load_s_s :
  load_insn LdS Single
  = [ins "mov" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t3), d, load(d), [tmp(p)]) *)
Example load_d_d :
  load_insn LdD Double
  = [ins "mov" "q" [mem 0 "rax"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t4), w, load(sw), [tmp(p)]) *)
Example load_sw_w :
  load_insn (LdNarrow Sw) W
  = [ins "mov" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t5), l, load(sw), [tmp(p)]) *)
Example load_sw_l :
  load_insn (LdNarrow Sw) L
  = [ins "movsl" "q" [mem 0 "rax"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t6), w, load(uw), [tmp(p)]) *)
Example load_uw_w :
  load_insn (LdNarrow Uw) W
  = [ins "mov" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t7), l, load(uw), [tmp(p)]) *)
Example load_uw_l :
  load_insn (LdNarrow Uw) L
  = [ins "mov" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t8), w, load(sh), [tmp(p)]) *)
Example load_sh_w :
  load_insn (LdNarrow Sh) W
  = [ins "movsw" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t9), l, load(sh), [tmp(p)]) *)
Example load_sh_l :
  load_insn (LdNarrow Sh) L
  = [ins "movsw" "q" [mem 0 "rax"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t10), w, load(uh), [tmp(p)]) *)
Example load_uh_w :
  load_insn (LdNarrow Uh) W
  = [ins "movzw" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t11), l, load(uh), [tmp(p)]) *)
Example load_uh_l :
  load_insn (LdNarrow Uh) L
  = [ins "movzw" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t12), w, load(sb), [tmp(p)]) *)
Example load_sb_w :
  load_insn (LdNarrow Sb) W
  = [ins "movsb" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t13), l, load(sb), [tmp(p)]) *)
Example load_sb_l :
  load_insn (LdNarrow Sb) L
  = [ins "movsb" "q" [mem 0 "rax"; reg "rax"]].
Proof. reflexivity. Qed.

(* let(tmp(t14), w, load(ub), [tmp(p)]) *)
Example load_ub_w :
  load_insn (LdNarrow Ub) W
  = [ins "movzb" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* let(tmp(t15), l, load(ub), [tmp(p)]) *)
Example load_ub_l :
  load_insn (LdNarrow Ub) L
  = [ins "movzb" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* store(b, tmp(a), tmp(p)) *)
Example store_b_d :
  store_insn Wb "d"
  = [ins "mov" "b" [reg "dl"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store(h, tmp(a), tmp(p)) *)
Example store_h_d :
  store_insn Wh "d"
  = [ins "mov" "w" [reg "dx"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store(w, tmp(a), tmp(p)) *)
Example store_w_d :
  store_insn Ww "d"
  = [ins "mov" "l" [reg "edx"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store(l, tmp(c), tmp(p)) *)
Example store_l_d :
  store_insn Wl "d"
  = [ins "mov" "q" [reg "rdx"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store(s, tmp(e), tmp(p)) *)
Example store_s_d :
  store_insn Ws "d"
  = [ins "mov" "l" [reg "edx"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store(d, tmp(f), tmp(p)) *)
Example store_d_d :
  store_insn Wd "d"
  = [ins "mov" "q" [reg "rdx"; mem 0 "rax"]].
Proof. reflexivity. Qed.


(** ### x87

    The context holds the operands and the slot of the one
    temporary d that the instruction defines. *)

Definition x87_cx (d : string) (off : Z) : ctx :=
  mkCtx "xs"
    (ex_slot d off
    (ex_slot "e" 8
    (ex_slot "f" 16
    (ex_slot "a" 32
    (ex_slot "c" 24
    (ex_slot "x" 56
    (ex_slot "y" 72 nm_empty)))))))
    nm_empty 0 0 nm_empty.

(* let(tmp(x), x, ext(s), [tmp(e)]) *)
Example x87_x :
  x87_inst (x87_cx "x" 56) (ExtF Single) Extended [ex_tmp "e"] (TAtom "x")
  = [ins "mov" "l" [mem (-8) "rbp"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rsp"];
     ins "fld" "s" [mem (-8) "rsp"]; ins "fstp" "t" [mem (-56) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(y), x, ext(d), [tmp(f)]) *)
Example x87_y :
  x87_inst (x87_cx "y" 72) (ExtF Double) Extended [ex_tmp "f"] (TAtom "y")
  = [ins "mov" "q" [mem (-16) "rbp"; reg "rax"]; ins "mov" "q" [reg "rax"; mem (-8) "rsp"];
     ins "fld" "l" [mem (-8) "rsp"]; ins "fstp" "t" [mem (-72) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t3), x, add, [tmp(x), tmp(y)]) *)
Example x87_t3 :
  x87_inst (x87_cx "t3" 88) Add Extended [ex_tmp "x"; ex_tmp "y"] (TAtom "t3")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fadd" [reg "st(1)"; reg "st"]; ins "fstp" "t" [mem (-88) "rbp"];
     ins0 "fstp" [reg "st(0)"]].
Proof. reflexivity. Qed.

(* let(tmp(t4), x, sub, [tmp(x), tmp(y)]) *)
Example x87_t4 :
  x87_inst (x87_cx "t4" 88) Sub Extended [ex_tmp "x"; ex_tmp "y"] (TAtom "t4")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fsub" [reg "st(1)"; reg "st"]; ins "fstp" "t" [mem (-88) "rbp"];
     ins0 "fstp" [reg "st(0)"]].
Proof. reflexivity. Qed.

(* let(tmp(t5), x, mul, [tmp(x), tmp(y)]) *)
Example x87_t5 :
  x87_inst (x87_cx "t5" 88) Mul Extended [ex_tmp "x"; ex_tmp "y"] (TAtom "t5")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fmul" [reg "st(1)"; reg "st"]; ins "fstp" "t" [mem (-88) "rbp"];
     ins0 "fstp" [reg "st(0)"]].
Proof. reflexivity. Qed.

(* let(tmp(t6), x, div, [tmp(x), tmp(y)]) *)
Example x87_t6 :
  x87_inst (x87_cx "t6" 88) Div Extended [ex_tmp "x"; ex_tmp "y"] (TAtom "t6")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fdiv" [reg "st(1)"; reg "st"]; ins "fstp" "t" [mem (-88) "rbp"];
     ins0 "fstp" [reg "st(0)"]].
Proof. reflexivity. Qed.

(* let(tmp(t7), x, neg, [tmp(x)]) *)
Example x87_t7 :
  x87_inst (x87_cx "t7" 88) Neg Extended [ex_tmp "x"] (TAtom "t7")
  = [ins "fld" "t" [mem (-56) "rbp"]; ins0 "fchs" []; ins "fstp" "t" [mem (-88) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t8), x, copy, [tmp(x)]) *)
Example x87_t8 :
  x87_inst (x87_cx "t8" 88) Copy Extended [ex_tmp "x"] (TAtom "t8")
  = [ins "fld" "t" [mem (-56) "rbp"]; ins "fstp" "t" [mem (-88) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t9), w, cmp(eq, x), [tmp(x), tmp(y)]) *)
Example x87_t9 :
  x87_inst (x87_cx "t9" 8) (Cmp Eq Extended) W [ex_tmp "x"; ex_tmp "y"] (TAtom "t9")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "sete" [reg "al"];
     ins0 "setnp" [reg "cl"]; ins "and" "b" [reg "cl"; reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t10), w, cmp(ne, x), [tmp(x), tmp(y)]) *)
Example x87_t10 :
  x87_inst (x87_cx "t10" 8) (Cmp Ne Extended) W [ex_tmp "x"; ex_tmp "y"] (TAtom "t10")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "setne" [reg "al"];
     ins0 "setp" [reg "cl"]; ins "or" "b" [reg "cl"; reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t11), w, cmp(lt, x), [tmp(x), tmp(y)]) *)
Example x87_t11 :
  x87_inst (x87_cx "t11" 8) (Cmp Lt Extended) W [ex_tmp "x"; ex_tmp "y"] (TAtom "t11")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "setb" [reg "al"];
     ins0 "setnp" [reg "cl"]; ins "and" "b" [reg "cl"; reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t12), w, cmp(le, x), [tmp(x), tmp(y)]) *)
Example x87_t12 :
  x87_inst (x87_cx "t12" 8) (Cmp Le Extended) W [ex_tmp "x"; ex_tmp "y"] (TAtom "t12")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "setbe" [reg "al"];
     ins0 "setnp" [reg "cl"]; ins "and" "b" [reg "cl"; reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t13), w, cmp(gt, x), [tmp(x), tmp(y)]) *)
Example x87_t13 :
  x87_inst (x87_cx "t13" 8) (Cmp Gt Extended) W [ex_tmp "x"; ex_tmp "y"] (TAtom "t13")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "seta" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t14), w, cmp(ge, x), [tmp(x), tmp(y)]) *)
Example x87_t14 :
  x87_inst (x87_cx "t14" 8) (Cmp Ge Extended) W [ex_tmp "x"; ex_tmp "y"] (TAtom "t14")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "setae" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t15), w, cmp(o, x), [tmp(x), tmp(y)]) *)
Example x87_t15 :
  x87_inst (x87_cx "t15" 8) (Cmp Ord Extended) W [ex_tmp "x"; ex_tmp "y"] (TAtom "t15")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "setnp" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t16), w, cmp(uo, x), [tmp(x), tmp(y)]) *)
Example x87_t16 :
  x87_inst (x87_cx "t16" 8) (Cmp Unord Extended) W [ex_tmp "x"; ex_tmp "y"] (TAtom "t16")
  = [ins "fld" "t" [mem (-72) "rbp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "setp" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t17), s, truncx, [tmp(x)]) *)
Example x87_t17 :
  x87_inst (x87_cx "t17" 8) Truncx Single [ex_tmp "x"] (TAtom "t17")
  = [ins "fld" "t" [mem (-56) "rbp"]; ins "fstp" "s" [mem (-8) "rsp"];
     ins "mov" "l" [mem (-8) "rsp"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t18), d, truncx, [tmp(x)]) *)
Example x87_t18 :
  x87_inst (x87_cx "t18" 8) Truncx Double [ex_tmp "x"] (TAtom "t18")
  = [ins "fld" "t" [mem (-56) "rbp"]; ins "fstp" "l" [mem (-8) "rsp"];
     ins "mov" "q" [mem (-8) "rsp"; reg "rax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t19), w, xtosi, [tmp(x)]) *)
Example x87_t19 :
  x87_inst (x87_cx "t19" 8) (FloatToInt Extended Signed) W [ex_tmp "x"] (TAtom "t19")
  = [ins "fld" "t" [mem (-56) "rbp"]; ins "fisttp" "ll" [mem (-8) "rsp"];
     ins "mov" "l" [mem (-8) "rsp"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t20), l, xtosi, [tmp(x)]) *)
Example x87_t20 :
  x87_inst (x87_cx "t20" 8) (FloatToInt Extended Signed) L [ex_tmp "x"] (TAtom "t20")
  = [ins "fld" "t" [mem (-56) "rbp"]; ins "fisttp" "ll" [mem (-8) "rsp"];
     ins "mov" "q" [mem (-8) "rsp"; reg "rax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t21), w, xtoui, [tmp(x)]) *)
Example x87_t21 :
  x87_inst (x87_cx "t21" 8) (FloatToInt Extended Unsigned) W [ex_tmp "x"] (TAtom "t21")
  = [ins "fld" "t" [mem (-56) "rbp"]; ins "fisttp" "ll" [mem (-8) "rsp"];
     ins "mov" "l" [mem (-8) "rsp"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t22), l, xtoui, [tmp(x)]) *)
Example x87_t22 :
  x87_inst (x87_cx "t22" 8) (FloatToInt Extended Unsigned) L [ex_tmp "x"] (TAtom "t22")
  = [ins "fld" "t" [mem (-56) "rbp"]; ins "mov" "l" [imm 1593835520; mem (-12) "rsp"];
     ins "fld" "s" [mem (-12) "rsp"]; ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "ja" [sym "1f"];
     ins "fsub" "s" [mem (-12) "rsp"]; ins "fisttp" "ll" [mem (-8) "rsp"];
     ins "mov" "q" [mem (-8) "rsp"; reg "rax"]; ins "btc" "q" [imm 63; reg "rax"];
     ins0 "jmp" [sym "2f"]; label "1"; ins "fisttp" "ll" [mem (-8) "rsp"];
     ins "mov" "q" [mem (-8) "rsp"; reg "rax"]; label "2";
     ins "mov" "q" [reg "rax"; mem (-8) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t23), x, swtof, [tmp(a)]) *)
Example x87_t23 :
  x87_inst (x87_cx "t23" 72) (IntToFloat W Signed) Extended [ex_tmp "a"] (TAtom "t23")
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "movsl" "q" [reg "eax"; reg "rax"];
     ins "mov" "q" [reg "rax"; mem (-8) "rsp"]; ins "fild" "ll" [mem (-8) "rsp"];
     ins "fstp" "t" [mem (-72) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t24), x, uwtof, [tmp(a)]) *)
Example x87_t24 :
  x87_inst (x87_cx "t24" 72) (IntToFloat W Unsigned) Extended [ex_tmp "a"] (TAtom "t24")
  = [ins "mov" "l" [mem (-32) "rbp"; reg "eax"]; ins "mov" "l" [reg "eax"; reg "eax"];
     ins "mov" "q" [reg "rax"; mem (-8) "rsp"]; ins "fild" "ll" [mem (-8) "rsp"];
     ins "fstp" "t" [mem (-72) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t25), x, sltof, [tmp(c)]) *)
Example x87_t25 :
  x87_inst (x87_cx "t25" 72) (IntToFloat L Signed) Extended [ex_tmp "c"] (TAtom "t25")
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "mov" "q" [reg "rax"; mem (-8) "rsp"];
     ins "fild" "ll" [mem (-8) "rsp"]; ins "fstp" "t" [mem (-72) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t26), x, ultof, [tmp(c)]) *)
Example x87_t26 :
  x87_inst (x87_cx "t26" 72) (IntToFloat L Unsigned) Extended [ex_tmp "c"] (TAtom "t26")
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "mov" "q" [reg "rax"; mem (-8) "rsp"];
     ins "fild" "ll" [mem (-8) "rsp"]; ins "test" "q" [reg "rax"; reg "rax"];
     ins0 "jns" [sym "1f"]; ins "mov" "l" [imm 1602224128; mem (-12) "rsp"];
     ins "fadd" "s" [mem (-12) "rsp"]; label "1"; ins "fstp" "t" [mem (-72) "rbp"]].
Proof. reflexivity. Qed.

(* let(tmp(t27), x, add, [tmp(x), const(302222231531620438900736)]) *)
Example x87_t27 :
  x87_inst (x87_cx "t27" 72) Add Extended [ex_tmp "x"; Const 302222231531620438900736]
    (TAtom "t27")
  = [ins "movabs" "q" [imm (-9223372036854775808); reg "rdx"];
     ins "mov" "q" [reg "rdx"; mem (-16) "rsp"]; ins "mov" "w" [imm 16383; mem (-8) "rsp"];
     ins "fld" "t" [mem (-16) "rsp"]; ins "fld" "t" [mem (-56) "rbp"];
     ins0 "fadd" [reg "st(1)"; reg "st"]; ins "fstp" "t" [mem (-72) "rbp"];
     ins0 "fstp" [reg "st(0)"]].
Proof. reflexivity. Qed.

(* let(tmp(t28), x, copy, [const(906708199769027163193345)]) *)
Example x87_t28 :
  x87_inst (x87_cx "t28" 72) Copy Extended [Const 906708199769027163193345] (TAtom "t28")
  = [ins "movabs" "q" [imm (-4611686018427387903); reg "rdx"];
     ins "mov" "q" [reg "rdx"; mem (-16) "rsp"]; ins "mov" "w" [imm 49152; mem (-8) "rsp"];
     ins "fld" "t" [mem (-16) "rsp"]; ins "fstp" "t" [mem (-72) "rbp"]].
Proof. reflexivity. Qed.


(** ### Cases no Fil-C module reaches

    These are what the Prolog predicates gave when called directly:
    the plain backend's `alloc`, classes and registers that the
    Fil-C backend does not ask for, and goals that fail, which are a
    [todo] here. *)

Definition direct_cx : ctx :=
  mkCtx "sw"
    (ex_slot "a" 24
    (ex_slot "b" 8
    (ex_slot "r" 40 nm_empty)))
    nm_empty 0 0 nm_empty.

(* compute_op(alloc(16), l, [tmp(a)]) *)
Example alloc_16 :
  compute_op direct_cx (Alloc 16) L [ex_tmp "a"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "add" "q" [imm 15; reg "rax"];
     ins "and" "q" [imm (-16); reg "rax"]; ins "sub" "q" [reg "rax"; reg "rsp"];
     ins "mov" "q" [reg "rsp"; reg "rax"]].
Proof. reflexivity. Qed.

(* compute_op(alloc(32), l, [tmp(a)]) *)
Example alloc_32 :
  compute_op direct_cx (Alloc 32) L [ex_tmp "a"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "add" "q" [imm 15; reg "rax"];
     ins "and" "q" [imm (-16); reg "rax"]; ins "sub" "q" [reg "rax"; reg "rsp"];
     ins "and" "q" [imm (-32); reg "rsp"]; ins "mov" "q" [reg "rsp"; reg "rax"]].
Proof. reflexivity. Qed.

(* compute_op(alloc(8), l, [tmp(a)]) *)
Example alloc_8 :
  compute_op direct_cx (Alloc 8) L [ex_tmp "a"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "add" "q" [imm 15; reg "rax"];
     ins "and" "q" [imm (-16); reg "rax"]; ins "sub" "q" [reg "rax"; reg "rsp"];
     ins "mov" "q" [reg "rsp"; reg "rax"]].
Proof. reflexivity. Qed.

(* compute_op(and, s, [tmp(a),tmp(b)]) *)
Example and_at_s :
  compute_op direct_cx And Single [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "and" "l" [reg "ecx"; reg "eax"]].
Proof. reflexivity. Qed.

(* compute_op(urem, d, [tmp(a),tmp(b)]) *)
Example urem_at_d :
  compute_op direct_cx Urem Double [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"]; ins "mov" "q" [mem (-8) "rbp"; reg "rcx"];
     ins "test" "q" [reg "rcx"; reg "rcx"]; ins0 "sete" [reg "dl"];
     ins "movzb" "l" [reg "dl"; reg "edx"]; ins "add" "q" [reg "rdx"; reg "rcx"];
     ins "sub" "q" [imm 1; reg "rdx"]; ins "and" "q" [reg "rdx"; reg "rax"];
     ins "xor" "l" [reg "edx"; reg "edx"]; ins "div" "q" [reg "rcx"];
     ins "mov" "q" [reg "rdx"; reg "rax"]].
Proof. reflexivity. Qed.

(* compute_op(cmp(eq,w), x, [tmp(a),tmp(b)]) *)
Example cmp_any_result_class :
  compute_op direct_cx (Cmp Eq W) Extended [ex_tmp "a"; ex_tmp "b"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "mov" "l" [mem (-8) "rbp"; reg "ecx"];
     ins "cmp" "l" [reg "ecx"; reg "eax"]; ins0 "sete" [reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* compute_op(ext(ub), d, [tmp(a)]) *)
Example ext_ub_at_d :
  compute_op direct_cx (Ext Ub) Double [ex_tmp "a"]
  = [ins "mov" "l" [mem (-24) "rbp"; reg "eax"]; ins "movzb" "l" [reg "al"; reg "eax"]].
Proof. reflexivity. Qed.

(* compute_op(add, l, [tmp(a),const(9223372036854775808)]) *)
Example add_l_const_2_63 :
  compute_op direct_cx Add L [ex_tmp "a"; Const 9223372036854775808]
  = [ins "mov" "q" [mem (-24) "rbp"; reg "rax"];
     ins "movabs" "q" [imm (-9223372036854775808); reg "rcx"];
     ins "add" "q" [reg "rcx"; reg "rax"]].
Proof. reflexivity. Qed.

(* compute_op(add, p, [tmp(a),tmp(b)]) *)
Example todo_add_p : ex_todo (compute_op direct_cx Add P [ex_tmp "a"; ex_tmp "b"]) = true.
Proof. reflexivity. Qed.

(* compute_op(add, w, [tmp(a)]) *)
Example todo_add_one_argument : ex_todo (compute_op direct_cx Add W [ex_tmp "a"]) = true.
Proof. reflexivity. Qed.

(* compute_op(rem, s, [tmp(a),tmp(b)]) *)
Example todo_rem_s : ex_todo (compute_op direct_cx Rem Single [ex_tmp "a"; ex_tmp "b"]) = true.
Proof. reflexivity. Qed.

(* compute_op(ext(sw), w, [tmp(a)]) *)
Example todo_ext_sw_w : ex_todo (compute_op direct_cx (Ext Sw) W [ex_tmp "a"]) = true.
Proof. reflexivity. Qed.

(* compute_op(cmp(lt,s), l, [tmp(a),tmp(b)]) *)
Example todo_float_cmp_l :
  ex_todo (compute_op direct_cx (Cmp Lt Single) L [ex_tmp "a"; ex_tmp "b"]) = true.
Proof. reflexivity. Qed.

(* compute_op(cmp(lt,w), w, [tmp(a),tmp(b)]) *)
Example todo_cmp_lt_w :
  ex_todo (compute_op direct_cx (Cmp Lt W) W [ex_tmp "a"; ex_tmp "b"]) = true.
Proof. reflexivity. Qed.

(* compute_op(stoui, s, [tmp(a)]) *)
Example todo_stoui_s :
  ex_todo (compute_op direct_cx (FloatToInt Single Unsigned) Single [ex_tmp "a"]) = true.
Proof. reflexivity. Qed.

(* compute_op(truncx, s, [tmp(a)]) *)
Example todo_truncx : ex_todo (compute_op direct_cx Truncx Single [ex_tmp "a"]) = true.
Proof. reflexivity. Qed.

(* compute_op(add, w, [tmp(nope),tmp(b)]) *)
Example todo_no_slot : ex_todo (compute_op direct_cx Add W [ex_tmp "nope"; ex_tmp "b"]) = true.
Proof. reflexivity. Qed.

(* store_insn(b, a) *)
Example store_b_a :
  store_insn Wb "a"
  = [ins "mov" "b" [reg "al"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store_insn(b, c) *)
Example store_b_c :
  store_insn Wb "c"
  = [ins "mov" "b" [reg "cl"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store_insn(h, c) *)
Example store_h_c :
  store_insn Wh "c"
  = [ins "mov" "w" [reg "cx"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store_insn(w, r8) *)
Example store_w_r8 :
  store_insn Ww "r8"
  = [ins "mov" "l" [reg "r8d"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store_insn(l, si) *)
Example store_l_si :
  store_insn Wl "si"
  = [ins "mov" "q" [reg "rsi"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store_insn(s, di) *)
Example store_s_di :
  store_insn Ws "di"
  = [ins "mov" "l" [reg "edi"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store_insn(d, r9) *)
Example store_d_r9 :
  store_insn Wd "r9"
  = [ins "mov" "q" [reg "r9"; mem 0 "rax"]].
Proof. reflexivity. Qed.

(* store_insn(b, si) *)
Example todo_store_b_si : ex_todo (store_insn Wb "si") = true.
Proof. reflexivity. Qed.

(* store_insn(h, r8) *)
Example todo_store_h_r8 : ex_todo (store_insn Wh "r8") = true.
Proof. reflexivity. Qed.

(* store_insn(p, a) *)
Example todo_store_p : ex_todo (store_insn Wp "a") = true.
Proof. reflexivity. Qed.

(* store_insn(x, a) *)
Example todo_store_x : ex_todo (store_insn Wx "a") = true.
Proof. reflexivity. Qed.

(* load_insn(uw, x) *)
Example load_uw_x :
  load_insn (LdNarrow Uw) Extended
  = [ins "mov" "l" [mem 0 "rax"; reg "eax"]].
Proof. reflexivity. Qed.

(* load_insn(x, x) *)
Example todo_load_x : ex_todo (load_insn LdX Extended) = true.
Proof. reflexivity. Qed.

(* load_insn(sw, s) *)
Example todo_load_sw_s : ex_todo (load_insn (LdNarrow Sw) Single) = true.
Proof. reflexivity. Qed.

(* load_insn(l, w) *)
Example todo_load_l_w : ex_todo (load_insn LdL W) = true.
Proof. reflexivity. Qed.

(* load_insn(sb, s) *)
Example todo_load_sb_s : ex_todo (load_insn (LdNarrow Sb) Single) = true.
Proof. reflexivity. Qed.

(* cond_code(ult) *)
Example cond_ult : cond_code Ult = Some "b".
Proof. reflexivity. Qed.

(* cond_code(sge) *)
Example cond_sge : cond_code Sge = Some "ge".
Proof. reflexivity. Qed.

(* cond_code(lt) *)
Example cond_lt : cond_code Lt = None.
Proof. reflexivity. Qed.

(* float_condition(le) *)
Example fcond_le :
  float_condition Le
  = [ins0 "setbe" [reg "al"]; ins0 "setnp" [reg "cl"]; ins "and" "b" [reg "cl"; reg "al"]].
Proof. reflexivity. Qed.

(* float_condition(uo) *)
Example fcond_uo :
  float_condition Unord
  = [ins0 "setp" [reg "al"]].
Proof. reflexivity. Qed.

(* float_condition(slt) *)
Example todo_fcond_slt : ex_todo (float_condition Slt) = true.
Proof. reflexivity. Qed.

(* reg_name(a, b) *)
Example reg8_a : reg8 "a" = "al".
Proof. reflexivity. Qed.

(* reg_name(c, h) *)
Example reg16_c : reg16 "c" = "cx".
Proof. reflexivity. Qed.

(* reg_name(d, b) *)
Example reg8_d : reg8 "d" = "dl".
Proof. reflexivity. Qed.

(* reg_name(d, h) *)
Example reg16_d : reg16 "d" = "dx".
Proof. reflexivity. Qed.

(* x87_inst(xtosi, d, [tmp(a)]) *)
Example x87_xtosi_d :
  x87_inst direct_cx (FloatToInt Extended Signed) Double [ex_tmp "a"] (TAtom "r")
  = [ins "fld" "t" [mem (-24) "rbp"]; ins "fisttp" "ll" [mem (-8) "rsp"];
     ins "mov" "q" [mem (-8) "rsp"; reg "rax"]; ins "mov" "q" [reg "rax"; mem (-40) "rbp"]].
Proof. reflexivity. Qed.

(* x87_inst(copy, x, [const(-1)]) *)
Example x87_copy_const :
  x87_inst direct_cx Copy Extended [Const (-1)] (TAtom "r")
  = [ins "movabs" "q" [imm (-1); reg "rdx"]; ins "mov" "q" [reg "rdx"; mem (-16) "rsp"];
     ins "mov" "w" [imm 65535; mem (-8) "rsp"]; ins "fld" "t" [mem (-16) "rsp"];
     ins "fstp" "t" [mem (-40) "rbp"]].
Proof. reflexivity. Qed.

(* x87_inst(cmp(lt,x), w, [tmp(a),const(906708199769027163193345)]) *)
Example x87_cmp_const :
  x87_inst direct_cx (Cmp Lt Extended) W [ex_tmp "a"; Const 906708199769027163193345] (TAtom "r")
  = [ins "movabs" "q" [imm (-4611686018427387903); reg "rdx"];
     ins "mov" "q" [reg "rdx"; mem (-16) "rsp"]; ins "mov" "w" [imm 49152; mem (-8) "rsp"];
     ins "fld" "t" [mem (-16) "rsp"]; ins "fld" "t" [mem (-24) "rbp"];
     ins0 "fucomip" [reg "st(1)"; reg "st"]; ins0 "fstp" [reg "st(0)"]; ins0 "setb" [reg "al"];
     ins0 "setnp" [reg "cl"]; ins "and" "b" [reg "cl"; reg "al"];
     ins "movzb" "l" [reg "al"; reg "eax"]; ins "mov" "q" [reg "rax"; mem (-40) "rbp"]].
Proof. reflexivity. Qed.

(* x87_inst(truncx, w, [tmp(a)]) *)
Example todo_x87_truncx_w : ex_todo (x87_inst direct_cx Truncx W [ex_tmp "a"] (TAtom "r")) = true.
Proof. reflexivity. Qed.

(* x87_inst(cmp(eq,x), l, [tmp(a),tmp(b)]) *)
Example todo_x87_cmp_l :
  ex_todo (x87_inst direct_cx (Cmp Eq Extended) L [ex_tmp "a"; ex_tmp "b"] (TAtom "r")) = true.
Proof. reflexivity. Qed.

(* x87_inst(add, w, [tmp(a),tmp(b)]) *)
Example todo_x87_add_w :
  ex_todo (x87_inst direct_cx Add W [ex_tmp "a"; ex_tmp "b"] (TAtom "r")) = true.
Proof. reflexivity. Qed.

(* x87_inst(ext(s), d, [tmp(a)]) *)
Example todo_x87_ext_d :
  ex_todo (x87_inst direct_cx (ExtF Single) Double [ex_tmp "a"] (TAtom "r")) = true.
Proof. reflexivity. Qed.

(* x87_op(add, x) *)
Example x87_op_add_x : x87_op Add Extended = true.
Proof. reflexivity. Qed.

(* x87_op(add, d) *)
Example x87_op_add_d : x87_op Add Double = false.
Proof. reflexivity. Qed.

(* x87_op(cmp(lt,x), w) *)
Example x87_op_cmp_x : x87_op (Cmp Lt Extended) W = true.
Proof. reflexivity. Qed.

(* x87_op(cmp(lt,d), w) *)
Example x87_op_cmp_d : x87_op (Cmp Lt Double) W = false.
Proof. reflexivity. Qed.

(* x87_op(truncx, s) *)
Example x87_op_truncx : x87_op Truncx Single = true.
Proof. reflexivity. Qed.

(* x87_op(truncd, s) *)
Example x87_op_truncd : x87_op Truncd Single = false.
Proof. reflexivity. Qed.

(* x87_op(xtoui, l) *)
Example x87_op_xtoui : x87_op (FloatToInt Extended Unsigned) L = true.
Proof. reflexivity. Qed.

(* x87_op(dtoui, l) *)
Example x87_op_dtoui : x87_op (FloatToInt Double Unsigned) L = false.
Proof. reflexivity. Qed.
