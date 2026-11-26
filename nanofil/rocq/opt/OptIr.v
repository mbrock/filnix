(** This module collects the shared IR classifications and integer ALU
    evaluation tables used across the middle-end optimizer passes, matching the
    corresponding predicates in `ir.pl`, `escape.pl`, and `interp.pl`.

    Sharing one classification table for operation kinds, argument classes,
    class moduli, load widths, and constant evaluation ensures that alias
    analysis, simplification, local-storage selection, and the top-level driver
    agree on every opcode and edge case such as total integer division. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Ops Semantics.
From Backend Require Import Pizlonate TermCfg.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** String equality uses [String.eqb] throughout the optimizer. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** ## Classes and moduli

    Integer operations evaluate modulo two to the class bit width, and signed
    comparisons or arithmetic right shifts interpret values in two's complement
    with the corresponding sign threshold. *)

(** Testing whether [k] is an integer class recognizes `w` and `l`. *)
Definition is_int_class (k : term) : bool :=
  is_atom "w" k || is_atom "l" k.

(** Computing the bit width of numeric class [k] matches `ir:class_bits/2`. *)
Definition class_bits (k : term) : option Z :=
  match k with
  | TAtom a =>
      if (a == "w") || (a == "s") then Some 32
      else if (a == "l") || (a == "d") then Some 64
      else if a == "x" then Some 80
      else None
  | _ => None
  end.

(** Computing the modulus of class [k] returns two to its bit width, matching
    `ir:modulus/2` for `w`, `l`, `p`, `s`, `d`, and `x`. *)
Definition class_modulus (k : term) : option Z :=
  match k with
  | TAtom a =>
      if (a == "w") || (a == "s") then Some 4294967296
      else if (a == "l") || (a == "p") || (a == "d") then Some 18446744073709551616
      else if a == "x" then Some (Z.shiftl 1 80)
      else None
  | _ => None
  end.

(** Computing the sign threshold of integer class [k] returns half its modulus,
    matching `ir:half_modulus/2`. *)
Definition class_half_modulus (k : term) : option Z :=
  match k with
  | TAtom a =>
      if a == "w" then Some 2147483648
      else if a == "l" then Some 9223372036854775808
      else None
  | _ => None
  end.

(** Testing whether [t] is a load type supported by local-storage selection
    matches `escape:load_width/2`, which excludes floating-point loads. *)
Definition load_width (t : term) : option term :=
  match t with
  | TAtom a =>
      if (a == "l") || (a == "p") then Some t
      else if (a == "sw") || (a == "uw") then Some (TAtom "w")
      else if (a == "sh") || (a == "uh") then Some (TAtom "h")
      else if (a == "sb") || (a == "ub") then Some (TAtom "b")
      else None
  | _ => None
  end.

(** ## Operation kinds and argument classes

    Every unchecked or checked operation belongs to one syntactic kind in
    `ir:op_kind/2`. Simplification uses these kinds to identify pure and
    constant-foldable instructions, and alias analysis uses them to identify
    address-deriving instructions. *)

(** The syntactic kind of an IR operation mirrors `ir:op_kind/2`. *)
Inductive op_kind_t : Type :=
| OkAdditive
| OkAlu
| OkShift
| OkNeg
| OkSelect
| OkCopy
| OkPtoi
| OkItop
| OkVaArgs
| OkVaArg
| OkSetjmp
| OkFloatConvert
| OkFloatToInt
| OkIntToFloat
| OkCast
| OkCmp
| OkExt
| OkLoad
| OkAtomicLoad
| OkCas
| OkRawCas
| OkAlloc
| OkCheck
| OkCheckAhead
| OkRenew
| OkRenewHull
| OkHalfCheck
| OkSpanTest
| OkRenewIf
| OkLimit
| OkCheckLimit
| OkCheckLocal
| OkCheckFunction
| OkLd
| OkLdPointer.

(** Classifying an operation term [op] returns its [op_kind_t], matching
    `ir:op_kind/2`. *)
Definition op_kind (op : term) : option op_kind_t :=
  match op with
  | TAtom a =>
      if (a == "add") || (a == "sub") then Some OkAdditive
      else if (a == "mul") || (a == "div") || (a == "udiv") || (a == "rem")
              || (a == "urem") || (a == "and") || (a == "or") || (a == "xor")
      then Some OkAlu
      else if (a == "sar") || (a == "shr") || (a == "shl") then Some OkShift
      else if a == "neg" then Some OkNeg
      else if a == "select" then Some OkSelect
      else if a == "copy" then Some OkCopy
      else if a == "ptoi" then Some OkPtoi
      else if a == "itop" then Some OkItop
      else if a == "va_args" then Some OkVaArgs
      else if a == "va_arg" then Some OkVaArg
      else if (a == "truncd") || (a == "truncx") || (a == "sqrt") then Some OkFloatConvert
      else if (a == "xtosi") || (a == "xtoui") || (a == "stosi")
              || (a == "stoui") || (a == "dtosi") || (a == "dtoui")
      then Some OkFloatToInt
      else if (a == "swtof") || (a == "uwtof") || (a == "sltof") || (a == "ultof")
      then Some OkIntToFloat
      else if a == "cast" then Some OkCast
      else if a == "check_function" then Some OkCheckFunction
      else None
  | TApp f xs =>
      if f == "setjmp" then
        match xs with
        | [TAtom k] =>
            if (k == "setjmp") || (k == "_setjmp") || (k == "sigsetjmp")
            then Some OkSetjmp else None
        | _ => None
        end
      else if f == "ext" then
        match xs with
        | [TAtom t] =>
            if (t == "s") || (t == "d") then Some OkFloatConvert
            else match narrow_bytes t with Some _ => Some OkExt | None => None end
        | _ => None
        end
      else if f == "cmp" then
        if arity 2 xs then Some OkCmp else None
      else if f == "load" then
        if arity 1 xs then Some OkLoad else None
      else if f == "atomic_load" then
        match xs with [t] => if is_atom "p" t then Some OkAtomicLoad else None | _ => None end
      else if f == "cas" then
        if arity 1 xs then Some OkCas else None
      else if f == "raw_cas" then
        if arity 2 xs then Some OkRawCas else None
      else if f == "alloc" then
        if arity 1 xs then Some OkAlloc else None
      else if f == "check" then
        if arity 4 xs then Some OkCheck else None
      else if f == "check_ahead" then
        if arity 5 xs then Some OkCheckAhead else None
      else if f == "renew" then
        if arity 4 xs then Some OkRenew else None
      else if f == "renew_hull" then
        if arity 4 xs then Some OkRenewHull else None
      else if f == "half_check" then
        if arity 5 xs then Some OkHalfCheck else None
      else if f == "span_test" then
        if arity 2 xs then Some OkSpanTest else None
      else if f == "renew_if" then
        if arity 4 xs then Some OkRenewIf else None
      else if f == "limit" then
        if arity 1 xs then Some OkLimit else None
      else if f == "check_limit" then
        if arity 4 xs then Some OkCheckLimit else None
      else if f == "check_local" then
        if arity 5 xs then Some OkCheckLocal else None
      else if f == "raw_load" then
        if arity 2 xs then Some OkLd else None
      else if f == "raw_load_pointer" then
        if arity 2 xs then Some OkLdPointer else None
      else None
  | _ => None
  end.

(** Computing the operand classes of an integer-foldable operation [op] at
    result class [k] matches `ir:op_arg_classes/4` for every kind that
    simplification folds. *)
Definition op_arg_classes (op k : term) (filc : bool) : option (list term) :=
  let* kind := op_kind op in
  match kind with
  | OkAdditive =>
      match k with
      | TAtom a =>
          if a == "p" then Some [TAtom "p"; TAtom "l"]
          else if (a == "w") || (a == "l") || (a == "s") || (a == "d") || (a == "x")
          then Some [k; k]
          else None
      | _ => None
      end
  | OkAlu => Some [k; k]
  | OkShift => Some [k; TAtom "w"]
  | OkNeg => Some [k]
  | OkSelect => Some [TAtom "w"; k; k]
  | OkCopy => Some [k]
  | OkCmp =>
      match op with
      | TApp _ [_; ck] => Some [ck; ck]
      | _ => None
      end
  | OkExt => Some [TAtom "w"]
  | OkPtoi => Some [TAtom "p"]
  | OkItop => Some [TAtom "l"]
  | OkLoad => Some [TAtom (if filc then "p" else "l")]
  | OkAlloc => Some [TAtom "l"]
  | _ => None
  end.

(** ## Integer ALU evaluation

    Constant folding delegates to the exact total integer semantics of
    `interp:alu/4`. Division and remainder by zero yield zero, signed division
    truncates toward zero, and arithmetic right shift divides with flooring. *)

(** Interpreting [u] as a signed two's-complement integer of modulus [m] and
    sign threshold [h] matches `interp:sign_extension/4`. *)
Definition sign_extension (m h u : Z) : Z :=
  let l := u mod m in
  if h <=? l then l - m else l.

(** Reading [u] as a signed integer of class [k] matches `interp:signed/3`. *)
Definition signed_val (k : term) (u : Z) : option Z :=
  let* m := class_modulus k in
  let* h := class_half_modulus k in
  Some (sign_extension m h u).

(** Extracting and sign- or zero-extending the low bits named by narrow type
    [t] matches `interp:extension/3`. *)
Definition extension_val (t : string) (x : Z) : option Z :=
  if t == "sb" then Some (sign_extension 256 128 x)
  else if t == "ub" then Some (x mod 256)
  else if t == "sh" then Some (sign_extension 65536 32768 x)
  else if t == "uh" then Some (x mod 65536)
  else if t == "sw" then Some (sign_extension 4294967296 2147483648 x)
  else if t == "uw" then Some (x mod 4294967296)
  else None.

(** Computing the shift factor two to the reduced shift count matches
    `interp:shift_factor/3`. *)
Definition shift_factor (k : term) (y : Z) : option Z :=
  let* bits := class_bits k in
  Some (Z.shiftl 1 (y mod bits)).

(** Evaluating an integer comparison condition returns one when the relation
    holds and zero otherwise, matching `interp:cond_bit/5`. *)
Definition cond_bit (cond : string) (ck : term) (x y : Z) : option Z :=
  let bit (b : bool) : Z := if b then 1 else 0 in
  if cond == "eq" then Some (bit (x =? y))
  else if cond == "ne" then Some (bit (negb (x =? y)))
  else if cond == "ult" then Some (bit (x <? y))
  else if cond == "ule" then Some (bit (x <=? y))
  else if cond == "ugt" then Some (bit (y <? x))
  else if cond == "uge" then Some (bit (y <=? x))
  else
    let* sx := signed_val ck x in
    let* sy := signed_val ck y in
    if cond == "slt" then Some (bit (sx <? sy))
    else if cond == "sle" then Some (bit (sx <=? sy))
    else if cond == "sgt" then Some (bit (sy <? sx))
    else if cond == "sge" then Some (bit (sy <=? sx))
    else None.

(** Evaluating a constant integer operation [op] at class [k] on already-reduced
    integer operands [xs] returns the resulting unsigned integer, matching
    `interp:alu/4` on integer operands. *)
Definition eval_alu (op k : term) (xs : list Z) : option Z :=
  match op with
  | TAtom a =>
      if a == "add" then
        match xs with
        | [x; y] => let* m := class_modulus k in Some ((x + y) mod m)
        | _ => None
        end
      else if a == "sub" then
        match xs with
        | [x; y] => let* m := class_modulus k in Some ((x - y) mod m)
        | _ => None
        end
      else if a == "mul" then
        match xs with
        | [x; y] => let* m := class_modulus k in Some ((x * y) mod m)
        | _ => None
        end
      else if a == "neg" then
        match xs with
        | [x] => let* m := class_modulus k in Some ((- x) mod m)
        | _ => None
        end
      else if a == "copy" then
        match xs with [x] => Some x | _ => None end
      else if a == "select" then
        match xs with [c; x; y] => Some (if c =? 0 then y else x) | _ => None end
      else if a == "and" then
        match xs with [x; y] => Some (Z.land x y) | _ => None end
      else if a == "or" then
        match xs with [x; y] => Some (Z.lor x y) | _ => None end
      else if a == "xor" then
        match xs with [x; y] => Some (Z.lxor x y) | _ => None end
      else if a == "udiv" then
        match xs with
        | [x; y] => Some (if y =? 0 then 0 else Z.quot x y)
        | _ => None
        end
      else if a == "urem" then
        match xs with
        | [x; y] => Some (if y =? 0 then 0 else x mod y)
        | _ => None
        end
      else if a == "div" then
        match xs with
        | [x; y] =>
            let* sx := signed_val k x in
            let* sy := signed_val k y in
            if sy =? 0 then Some 0
            else let* m := class_modulus k in Some ((Z.quot sx sy) mod m)
        | _ => None
        end
      else if a == "rem" then
        match xs with
        | [x; y] =>
            let* sx := signed_val k x in
            let* sy := signed_val k y in
            if sy =? 0 then Some 0
            else let* m := class_modulus k in Some ((Z.rem sx sy) mod m)
        | _ => None
        end
      else if a == "shl" then
        match xs with
        | [x; y] =>
            let* p := shift_factor k y in
            let* m := class_modulus k in
            Some ((x * p) mod m)
        | _ => None
        end
      else if a == "shr" then
        match xs with
        | [x; y] =>
            let* p := shift_factor k y in
            Some (Z.quot x p)
        | _ => None
        end
      else if a == "sar" then
        match xs with
        | [x; y] =>
            let* p := shift_factor k y in
            let* sx := signed_val k x in
            let* m := class_modulus k in
            Some ((Z.div sx p) mod m)
        | _ => None
        end
      else None
  | TApp f args =>
      if f == "ext" then
        match args, xs with
        | [TAtom t], [x] =>
            let* s := extension_val t x in
            let* m := class_modulus k in
            Some (s mod m)
        | _, _ => None
        end
      else if f == "cmp" then
        match args, xs with
        | [TAtom c; ck], [x; y] => cond_bit c ck x y
        | _, _ => None
        end
      else None
  | _ => None
  end.

(** ## Local storage predicate

    The top-level optimizer leaves modules that already contain `local_alloc/2`
    instructions unchanged because earlier passes consume ordinary addresses. *)

(** Testing whether a function's blocks define any `local_alloc/2` instruction
    matches checking `ir:local_objects/2` for non-emptiness. *)
Definition func_has_local_objects (bs : list tblock) : bool :=
  existsb (fun b => existsb is_local_alloc (tb_insts b)) bs.

(** Testing whether any function in a module's item list defines a local object
    matches `opt:has_local_storage/1`. *)
Definition module_has_local_storage (items : list term) : bool :=
  existsb
    (fun it =>
       existsb
         (fun b =>
            match block_parts b with
            | Some (_, insts, _) => existsb is_local_alloc insts
            | None => false
            end)
         (func_blocks it))
    items.
