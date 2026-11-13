(** In Fil-C, integer division never faults. Division by zero returns
    0, and dividing the least signed integer by -1 wraps back to the
    least signed integer. The x86-64 instructions `div` and `idiv`
    raise a divide error in both cases. The backend therefore rewrites
    the two operands before it divides, without a branch, so that the
    divide cannot fault and still returns the IR's result.

    This module is the arithmetic of that rewriting, apart from any
    register or instruction. It defines the rewritten operands as
    functions on integers, and it states two things about them. The
    processor's division rule of Amd64Word.v accepts the rewritten
    operands, and the quotient and remainder that the rule returns are
    the ones that the IR model of Ops.v defines for the original
    operands. *)

From Stdlib Require Import ZArith List Bool Lia.
From Nanofil Require Import Syntax Values.
From Nanofil Require Ops.
From Backend Require Import Amd64Word.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Classes and operations

    The IR names an integer's width by its [[class]], and it has one
    operation for each combination of signedness and of quotient or
    remainder. This section maps both to the terms that the machine
    semantics uses. *)

(** The function [class_size] returns the operand size at which the
    backend computes an integer of the class k. Only the two integer
    classes have one. *)
Definition class_size (k : class) : option size :=
  match k with
  | W => Some S32
  | L => Some S64
  | _ => None
  end.

(** The function [division_op] returns the IR operation that divides
    with the signedness sg and yields the remainder when remainder
    holds, and the quotient otherwise. *)
Definition division_op (sg : signedness) (remainder : bool) : op :=
  match sg, remainder with
  | Signed, false => Div
  | Signed, true => Rem
  | Unsigned, false => Udiv
  | Unsigned, true => Urem
  end.

(** ## The rewritten operands

    The emitted code rewrites the operands in two stages. The first
    stage removes a zero divisor, and the second stage, which only a
    signed division has, removes a divisor of -1. Each stage is a pair
    of functions, one for the divisor and one for the dividend. *)

(** The function [nonzero_divisor] replaces a zero divisor by 1 and
    keeps every other divisor. *)
Definition nonzero_divisor (c : Z) : Z := if c =? 0 then 1 else c.

(** The function [nonzero_dividend] replaces the dividend by 0 when the
    divisor c is zero. Together with [nonzero_divisor], this turns a
    division by zero into 0 divided by 1, whose quotient and remainder
    are both 0. *)
Definition nonzero_dividend (a c : Z) : Z := if c =? 0 then 0 else a.

(** The function [positive_divisor] replaces the pattern of -1 at the
    size z by 1 and keeps every other divisor. *)
Definition positive_divisor (z : size) (c : Z) : Z :=
  if c =? size_modulus z - 1 then 1 else c.

(** The function [negated_dividend] negates the dividend at the size z
    when the divisor c is the pattern of -1. Dividing by -1 is a
    negation, so the negated dividend divided by 1 has the same
    quotient, and the negation wraps the least integer to itself where
    `idiv` would fault. *)
Definition negated_dividend (z : size) (a c : Z) : Z :=
  if c =? size_modulus z - 1 then wrap z (- a) else a.

(** The function [safe_divisor] is the divisor that reaches the divide
    instruction: the original divisor c after the stages that the
    signedness sg requires. *)
Definition safe_divisor (sg : signedness) (z : size) (c : Z) : Z :=
  match sg with
  | Signed => positive_divisor z (nonzero_divisor c)
  | Unsigned => nonzero_divisor c
  end.

(** The function [safe_dividend] is the dividend that reaches the
    divide instruction, from the original dividend a and divisor c. *)
Definition safe_dividend (sg : signedness) (z : size) (a c : Z) : Z :=
  match sg with
  | Signed => negated_dividend z (nonzero_dividend a c) (nonzero_divisor c)
  | Unsigned => nonzero_dividend a c
  end.

(** ## What the divide instruction computes

    Once its operands are safe, a divide instruction returns an
    ordinary quotient and remainder. This section names those results
    and the condition on the divisor under which the instruction does
    not fault. *)

(** The function [machine_quotient] is the quotient pattern that a
    divide instruction leaves for the dividend a and the divisor c. A
    signed divide reads both in two's complement and truncates toward
    zero. *)
Definition machine_quotient (sg : signedness) (z : size) (a c : Z) : Z :=
  match sg with
  | Signed => wrap z (Z.quot (signed_at z a) (signed_at z c))
  | Unsigned => a / c
  end.

(** The function [machine_remainder] is the remainder pattern that the
    same divide instruction leaves. *)
Definition machine_remainder (sg : signedness) (z : size) (a c : Z) : Z :=
  match sg with
  | Signed => wrap z (Z.rem (signed_at z a) (signed_at z c))
  | Unsigned => a mod c
  end.

(** A divisor pattern is [divisor_safe] when no dividend can make the
    divide instruction fault. An unsigned divisor must be nonzero. A
    signed divisor must also differ from the pattern of -1, since the
    least integer divided by -1 does not fit. *)
Definition divisor_safe (sg : signedness) (z : size) (c : Z) : Prop :=
  match sg with
  | Signed => 0 < c < size_modulus z - 1
  | Unsigned => 0 < c < size_modulus z
  end.

(** ## The rewritten operands are valid and safe

    The divide instruction reads its operands from registers, so the
    rewritten operands must be valid patterns, and the divisor must be
    safe. These lemmas establish both for every pair of valid
    patterns. *)

(** The divisor after the first stage is a nonzero valid pattern. *)
Lemma nonzero_divisor_range (z : size) (c : Z) :
  0 <= c < size_modulus z -> 0 < nonzero_divisor c < size_modulus z.
Proof.
Admitted.

(** The dividend after the first stage is a valid pattern. *)
Lemma nonzero_dividend_range (z : size) (a c : Z) :
  0 <= a < size_modulus z -> 0 <= nonzero_dividend a c < size_modulus z.
Proof.
Admitted.

(** The divisor after the second stage is nonzero and is not the
    pattern of -1. *)
Lemma positive_divisor_range (z : size) (c : Z) :
  0 < c < size_modulus z -> 0 < positive_divisor z c < size_modulus z - 1.
Proof.
Admitted.

(** The dividend after the second stage is a valid pattern. *)
Lemma negated_dividend_range (z : size) (a c : Z) :
  0 <= a < size_modulus z -> 0 <= negated_dividend z a c < size_modulus z.
Proof.
Admitted.

(** The divisor that reaches the divide instruction is safe. *)
Lemma safe_divisor_safe (sg : signedness) (z : size) (c : Z) :
  0 <= c < size_modulus z -> divisor_safe sg z (safe_divisor sg z c).
Proof.
Admitted.

(** The dividend that reaches the divide instruction is a valid
    pattern. *)
Lemma safe_dividend_range (sg : signedness) (z : size) (a c : Z) :
  0 <= a < size_modulus z -> 0 <= safe_dividend sg z a c < size_modulus z.
Proof.
Admitted.

(** ## The divide instruction does not fault

    The processor's rule [divide_words] returns `None` where the
    processor raises a divide error. These lemmas show that the rule
    returns the expected quotient and remainder instead whenever the
    divisor is safe and the upper half of the dividend was prepared as
    the emitted code prepares it. *)

(** An unsigned divide of a dividend with a zero upper half by a
    nonzero divisor succeeds, and it returns the ordinary quotient and
    remainder. *)
Lemma divide_words_unsigned (z : size) (a c : Z) :
  0 <= a < size_modulus z -> divisor_safe Unsigned z c ->
  divide_words false z 0 a c
  = Some (machine_quotient Unsigned z a c, machine_remainder Unsigned z a c).
Proof.
Admitted.

(** A signed divide of a dividend extended by its own sign succeeds
    when the divisor is neither zero nor -1. The quotient then has no
    larger magnitude than the dividend, so it fits. *)
Lemma divide_words_signed (z : size) (a c : Z) :
  0 <= a < size_modulus z -> divisor_safe Signed z c ->
  divide_words true z (sign_fill z a) a c
  = Some (machine_quotient Signed z a c, machine_remainder Signed z a c).
Proof.
Admitted.

(** The quotient that a divide instruction leaves for a safe divisor
    is a valid pattern. *)
Lemma machine_quotient_range (sg : signedness) (z : size) (a c : Z) :
  0 <= a < size_modulus z -> divisor_safe sg z c ->
  0 <= machine_quotient sg z a c < size_modulus z.
Proof.
Admitted.

(** The remainder that a divide instruction leaves for a safe divisor
    is a valid pattern. *)
Lemma machine_remainder_range (sg : signedness) (z : size) (a c : Z) :
  0 <= a < size_modulus z -> divisor_safe sg z c ->
  0 <= machine_remainder sg z a c < size_modulus z.
Proof.
Admitted.

(** ## The results are the IR's

    These lemmas are the reason the rewriting is correct. For every
    pair of valid operand patterns, the quotient and the remainder
    that the divide instruction computes from the rewritten operands
    are the values that the IR operation defines for the original
    operands. *)

(** The quotient of the rewritten operands is the result of the IR's
    `div` or `udiv`. *)
Lemma total_quotient_agrees (sg : signedness) (k : class) (z : size) (x y : Z) :
  class_size k = Some z ->
  0 <= x < size_modulus z -> 0 <= y < size_modulus z ->
  Ops.alu (division_op sg false) k [WInt x; WInt y]
  = Some (WInt (machine_quotient sg z (safe_dividend sg z x y) (safe_divisor sg z y))).
Proof.
Admitted.

(** The remainder of the rewritten operands is the result of the IR's
    `rem` or `urem`. *)
Lemma total_remainder_agrees (sg : signedness) (k : class) (z : size) (x y : Z) :
  class_size k = Some z ->
  0 <= x < size_modulus z -> 0 <= y < size_modulus z ->
  Ops.alu (division_op sg true) k [WInt x; WInt y]
  = Some (WInt (machine_remainder sg z (safe_dividend sg z x y) (safe_divisor sg z y))).
Proof.
Admitted.
