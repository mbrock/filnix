(** The function `division` of EmitOps.v emits the code for the IR's
    four division operations. After it loads the two operands into
    `%rax` and `%rcx`, the code is a straight-line sequence that
    computes only in `%rax`, `%rcx` and `%rdx`. This module takes that
    sequence apart into the fragments that the emitter appends, and
    it states what each fragment computes.

    A theorem is useful only when it is about the code that the
    backend prints. The function [division_lines] therefore calls the
    same four emitter functions that `division` calls after its loads,
    so its lines are the printed lines. Each fragment also has a typed
    form for the execution model of Amd64Step.v, and the reading of
    Amd64Asm.v maps the emitted lines to that typed form.

    Each fragment's specification is stated with the relation
    [establishes]: every execution of the fragment completes, whatever
    values the undefined flags take, and the final registers hold the
    stated functions of the initial registers. The functions are the
    rewritten operands of Amd64Total.v. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Syntax.
From Backend Require Import Asm Layout EmitOps.
From Backend Require Import Amd64Word Amd64Machine Amd64Step Amd64Asm Amd64Total.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## The emitted lines

    The emitter's `division` first loads its operands from the frame,
    which needs memory, and then computes in registers. This section
    names the register part and shows that `division` is the two loads
    followed by it. *)

(** The function [division_lines] is the code that `division` emits
    after its two loads: the two operand rewritings, the divide and
    the move of the result. It is empty for a class that has no
    integer register form. *)
Definition division_lines (sg : signedness) (remainder : bool) (k : class) : list line :=
  match class_half k with
  | Some half =>
      let s := class_suffix half in
      let a := reg_name "a" half in
      let c := reg_name "c" half in
      let d := reg_name "d" half in
      zero_divisor s a c d ++ minus_one_divisor sg s a c d
      ++ divide sg k s c ++ division_result remainder half
  | None => []
  end.

(** The emitter's code for a division of two values at an integer class
    is the load of each operand followed by [division_lines]. *)
Lemma division_split (cx : ctx) (sg : signedness) (remainder : bool) (k : class)
    (z : size) (x y : value) :
  class_size k = Some z ->
  division cx sg remainder k [x; y]
  = load cx x k "a" ++ load cx y k "c" ++ division_lines sg remainder k.
Proof.
  intros Hk. destruct k; try discriminate; reflexivity.
Qed.

(** ## The typed fragments

    Each fragment of the emitted code has a typed form at the operand
    size z. This section defines the four fragments and their
    concatenation, and shows that the emitted lines read as that
    concatenation. *)

(** The fragment [zero_divisor_code] sets `%rdx` to 1 when the divisor
    in `%rcx` is zero and to 0 otherwise. It adds that bit to the
    divisor, and it clears the dividend in `%rax` with a mask when the
    bit is 1. *)
Definition zero_divisor_code (z : size) : list instr :=
  [IBinary BTest z (SReg RCX) RCX;
   ISet CondE RDX;
   IMovzx S8 S32 RDX RDX;
   IBinary BAdd z (SReg RDX) RCX;
   IBinary BSub z (SImm 1) RDX;
   IBinary BAnd z (SReg RDX) RAX].

(** The fragment [minus_one_divisor_code] is empty for an unsigned
    division. For a signed division it sets `%rdx` to 1 when the
    divisor is -1, adds that bit to the divisor twice, and negates the
    dividend by a complement and an increment when the bit is 1. *)
Definition minus_one_divisor_code (sg : signedness) (z : size) : list instr :=
  match sg with
  | Unsigned => []
  | Signed =>
      [IBinary BCmp z (SImm (-1)) RCX;
       ISet CondE RDX;
       IMovzx S8 S32 RDX RDX;
       IBinary BAdd z (SReg RDX) RCX;
       IBinary BAdd z (SReg RDX) RCX;
       IUnary UNeg z RDX;
       IBinary BXor z (SReg RDX) RAX;
       IBinary BSub z (SReg RDX) RAX]
  end.

(** The fragment [divide_code] prepares the upper half of the dividend
    in `%rdx` and divides. A signed division fills the upper half with
    the sign of `%rax`. An unsigned division clears it with a 32-bit
    `xor`, which clears all of `%rdx` at either operand size. *)
Definition divide_code (sg : signedness) (z : size) : list instr :=
  match sg with
  | Signed => [IExtend z; IDivide true z RCX]
  | Unsigned => [IBinary BXor S32 (SReg RDX) RDX; IDivide false z RCX]
  end.

(** The fragment [result_code] moves the remainder from `%rdx` to
    `%rax` when the operation is a remainder. The quotient is already
    in `%rax`, so the fragment is empty for a quotient. *)
Definition result_code (remainder : bool) (z : size) : list instr :=
  if remainder then [IMov z (SReg RDX) RAX] else [].

(** The sequence [division_code] is the four fragments in the order in
    which the emitter appends them. *)
Definition division_code (sg : signedness) (remainder : bool) (z : size) : list instr :=
  zero_divisor_code z ++ minus_one_divisor_code sg z
  ++ divide_code sg z ++ result_code remainder z.

(** Every line that the backend emits for an integer division has a
    typed reading, so the model covers the whole sequence. The reading
    of the lines is [division_code] at the size of the class. *)
Lemma division_lines_decode (sg : signedness) (remainder : bool) (k : class) (z : size) :
  class_size k = Some z ->
  decode_lines (division_lines sg remainder k) = Some (division_code sg remainder z).
Proof.
  intros Hk.
  destruct k; try discriminate; inversion Hk; subst;
    destruct sg, remainder; reflexivity.
Qed.

(** ## What each fragment computes

    The specifications below describe the registers after a fragment
    as functions of the registers before it. Each one gives the whole
    64-bit content of a result register, which shows that a 32-bit
    result is zero-extended, and each one says that the fragment
    changes no register other than its three scratch registers. *)

(** The predicate [word_size] holds of the two operand sizes at which
    the backend computes IR integers. A write at either size replaces
    the whole register. *)
Definition word_size (z : size) : Prop := z = S32 \/ z = S64.

(** The relation [scratch_only] holds of two states when every register
    other than `%rax`, `%rcx` and `%rdx` has the same content in
    both. *)
Definition scratch_only (s s' : machine) : Prop :=
  forall r, r <> RAX -> r <> RCX -> r <> RDX -> regs s' r = regs s r.

(** Register reads can be simplified before executing the next instruction.
    This tactic keeps the machine abstract while removing completed writes. *)
Local Ltac division_regs :=
  repeat first
    [ rewrite get_reg_set_flags
    | rewrite regs_set_flags
    | rewrite get_set_reg_other by congruence
    | rewrite regs_set_reg_other by congruence
    | rewrite get_set_reg_same by (cbn; lia)
    | rewrite get_64_set_32
    | rewrite regs_set_reg_32
    | rewrite regs_set_reg_64
    | rewrite wrap_wrap ].

(** Only closed arithmetic is evaluated while simplifying masks.
    Symbolic operands remain intact for the word lemmas. *)
Local Ltac division_closed v :=
  lazymatch v with
  | Z0 => idtac
  | Zpos ?p => is_ground p
  | Zneg ?p => is_ground p
  | wrap _ ?x => division_closed x
  | Z.sub ?x ?y => division_closed x; division_closed y
  | Z.add ?x ?y => division_closed x; division_closed y
  | Z.opp ?x => division_closed x
  end.

(** Constant masks reduce without expanding a symbolic register read. *)
Local Ltac division_constants :=
  repeat match goal with |- context [wrap ?z ?v] =>
    division_closed v;
    let n := eval vm_compute in (wrap z v) in
    progress change (wrap z v) with n
  end.

(** Each instruction receives its own undefined flags during symbolic execution.
    A completed step leaves only the execution of the remaining instructions. *)
Local Ltac division_step :=
  match goal with
  | H : runs (_ :: _) _ _ |- _ =>
      let h := fresh "h" in let t := fresh "t" in
      let E := fresh "E" in let R := fresh "R" in
      apply runs_cons_inv in H;
      destruct H as [h [[t [E R]] | [t [E R]]]];
      cbv beta iota zeta delta
        [step source_value binary_writes binary_value size_ltb size_bits] in E;
      revert E; division_regs; intro E;
      [ injection E as E; subst t | discriminate E ]
  end.

(** The first fragment leaves the first-stage dividend in `%rax` and
    the first-stage divisor in `%rcx`. It needs no precondition. *)
Lemma zero_divisor_spec (z : size) :
  word_size z ->
  establishes (fun _ => True) (zero_divisor_code z)
    (fun s s' =>
       regs s' RAX = nonzero_dividend (get_reg z RAX s) (get_reg z RCX s)
       /\ regs s' RCX = nonzero_divisor (get_reg z RCX s)
       /\ scratch_only s s').
Proof.
  intros [-> | ->] s o _ H; unfold zero_divisor_code in H;
    do 6 division_step;
    match goal with H : runs [] _ _ |- _ => apply runs_nil_inv in H; subst o end;
    eexists; (split; [reflexivity |]);
    cbn beta; unfold scratch_only; repeat split; intros;
    division_regs.
  all: cbn [condition_holds flags set_flags binary_flags binary_value logic_flags].
  all: try reflexivity.
  all: try rewrite Z.land_diag.
  all: unfold nonzero_dividend, nonzero_divisor;
    match goal with |- context [get_reg ?z RCX ?st] =>
      destruct (get_reg z RCX st =? 0) eqn:C
    end;
    cbv beta iota; division_constants.
  all: try rewrite Z.land_0_r.
  all: try reflexivity.
  all: try (rewrite Z.add_0_r; apply wrap_small, get_reg_range).
  all: try (apply Z.eqb_eq in C; rewrite C; reflexivity).
  - change 4294967295 with (size_modulus S32 - 1).
    rewrite land_ones by apply get_reg_range.
    apply wrap_small, get_reg_range.
  - change 18446744073709551615 with (size_modulus S64 - 1).
    rewrite land_ones by apply get_reg_range.
    apply wrap_small, get_reg_range.
Qed.

(** Comparing a valid pattern with -1 sets zero exactly for the all-ones pattern.
    This identifies the bit that the second fragment copies with `sete`. *)
Lemma compare_minus_one (z : size) (c : Z) :
  0 <= c < size_modulus z ->
  (wrap z (c - wrap z (-1)) =? 0) = (c =? size_modulus z - 1).
Proof.
  intros Hc. rewrite wrap_sub_r.
  replace (c - -1) with (c + 1) by lia.
  destruct (c =? size_modulus z - 1) eqn:C.
  - apply Z.eqb_eq in C. rewrite C.
    replace (size_modulus z - 1 + 1) with (size_modulus z) by lia.
    unfold wrap. rewrite Z.mod_same by (pose proof (size_modulus_pos z); lia).
    reflexivity.
  - apply Z.eqb_neq in C. rewrite wrap_small by lia.
    apply Z.eqb_neq. lia.
Qed.

(** The second fragment of a signed division leaves the second-stage
    dividend in `%rax` and the second-stage divisor in `%rcx`. It needs
    no precondition either. *)
Lemma minus_one_divisor_spec (z : size) :
  word_size z ->
  establishes (fun _ => True) (minus_one_divisor_code Signed z)
    (fun s s' =>
       regs s' RAX = negated_dividend z (get_reg z RAX s) (get_reg z RCX s)
       /\ regs s' RCX = positive_divisor z (get_reg z RCX s)
       /\ scratch_only s s').
Proof.
  intros [-> | ->] s o _ H; unfold minus_one_divisor_code in H;
    do 8 division_step;
    match goal with H : runs [] _ _ |- _ => apply runs_nil_inv in H; subst o end;
    eexists; (split; [reflexivity |]);
    cbn beta; unfold scratch_only; repeat split; intros;
    division_regs.
  all: cbn [condition_holds flags set_flags binary_flags binary_value arith_flags].
  all: try reflexivity.
  all: rewrite compare_minus_one by apply get_reg_range;
    unfold negated_dividend, positive_divisor;
    match goal with |- context [get_reg ?z RCX ?st] =>
      destruct (get_reg z RCX st =? size_modulus z - 1) eqn:C
    end;
    cbv beta iota; division_constants;
    try rewrite Z.lxor_0_r;
    repeat rewrite wrap_add_l;
    repeat rewrite wrap_sub_l;
    repeat rewrite Z.add_0_r;
    try rewrite Z.sub_0_r;
    try (apply wrap_small, get_reg_range);
    try (apply Z.eqb_eq in C; rewrite C; reflexivity).
  - change 4294967295 with (size_modulus S32 - 1).
    rewrite lxor_ones by apply get_reg_range.
    f_equal. lia.
  - change 18446744073709551615 with (size_modulus S64 - 1).
    rewrite lxor_ones by apply get_reg_range.
    f_equal. lia.
Qed.

(** The divide fragment requires a safe divisor in `%rcx`. It then
    completes without a divide error and leaves the quotient in `%rax`
    and the remainder in `%rdx`. *)
Lemma divide_spec (sg : signedness) (z : size) :
  word_size z ->
  establishes (fun s => divisor_safe sg z (get_reg z RCX s)) (divide_code sg z)
    (fun s s' =>
       regs s' RAX = machine_quotient sg z (get_reg z RAX s) (get_reg z RCX s)
       /\ regs s' RDX = machine_remainder sg z (get_reg z RAX s) (get_reg z RCX s)
       /\ scratch_only s s').
Proof.
  intros [-> | ->] s o Hsafe H; destruct sg;
    unfold divide_code in H; division_step;
    apply runs_cons_inv in R;
    destruct R as [hd [[t [E R]] | [f [E R]]]];
    cbv beta iota zeta delta [step] in E;
    revert E; division_regs;
    try rewrite Z.lxor_nilpotent;
    division_constants;
    try rewrite wrap_small by apply sign_fill_range;
    first [rewrite divide_words_signed by (try apply get_reg_range; assumption)
          |rewrite divide_words_unsigned by (try apply get_reg_range; assumption)];
    intro E; try discriminate E;
    injection E as E; subst t;
    apply runs_nil_inv in R; subst o;
    eexists; (split; [reflexivity |]);
    cbn beta; unfold scratch_only; repeat split; intros; division_regs;
    cbn [fst snd]; try reflexivity;
    apply wrap_small;
    first [apply machine_quotient_range | apply machine_remainder_range];
    try apply get_reg_range; assumption.
Qed.

(** The result fragment of a remainder copies the low part of `%rdx`
    to `%rax` and changes no other register. *)
Lemma result_spec (z : size) :
  word_size z ->
  establishes (fun _ => True) (result_code true z)
    (fun s s' =>
       regs s' RAX = get_reg z RDX s
       /\ forall r, r <> RAX -> regs s' r = regs s r).
Proof.
  intros [-> | ->] s o _ H; unfold result_code in H;
    division_step; apply runs_nil_inv in R; subst o;
    eexists; (split; [reflexivity |]); split.
  - division_regs. apply wrap_small, get_reg_range.
  - intros r Hr. division_regs. reflexivity.
  - division_regs. apply wrap_small, get_reg_range.
  - intros r Hr. division_regs. reflexivity.
Qed.

(** ## Executions on concrete operands

    These examples execute the typed sequence on the operands where a
    raw divide would fault or where sign matters, and compare the
    content of `%rax` with the result that the IR defines. They are
    evaluations of the model, which test it apart from the proofs. *)

(** The state [operands] holds the dividend a in `%rax` and the divisor
    c in `%rcx`. Every other register holds a pattern with all bits
    set, and every flag is set, so that an instruction that wrongly
    reads stale state does not read zero. *)
Definition operands (a c : Z) : machine :=
  mkMachine
    (fun r =>
       match r with
       | RAX => a
       | RCX => c
       | _ => 18446744073709551615
       end)
    (fun _ => true).

(** The function [result] returns the content of `%rax` after a
    completed execution, and `None` after a fault. *)
Definition result (o : outcome) : option Z :=
  match o with
  | Next s => Some (regs s RAX)
  | Fault _ => None
  end.

(** The function [divided] executes [division_code] on two operands
    with every undefined flag set, and returns the result. *)
Definition divided (sg : signedness) (remainder : bool) (z : size) (a c : Z) : option Z :=
  result (run (fun _ => true) (division_code sg remainder z) (operands a c)).

(** A 32-bit signed division by zero returns 0. *)
Example divided_by_zero : divided Signed false S32 7 0 = Some 0.
Proof. vm_compute. reflexivity. Qed.

(** A 32-bit signed remainder by zero returns 0. *)
Example remainder_by_zero : divided Signed true S32 7 0 = Some 0.
Proof. vm_compute. reflexivity. Qed.

(** The least 32-bit integer divided by -1 wraps to itself. *)
Example least_by_minus_one :
  divided Signed false S32 2147483648 4294967295 = Some 2147483648.
Proof. vm_compute. reflexivity. Qed.

(** The least 64-bit integer divided by -1 wraps to itself, and the
    remainder is 0. *)
Example least_by_minus_one_64 :
  divided Signed false S64 9223372036854775808 18446744073709551615
  = Some 9223372036854775808
  /\ divided Signed true S64 9223372036854775808 18446744073709551615 = Some 0.
Proof. vm_compute. split; reflexivity. Qed.

(** The 32-bit division of -7 by 2 truncates toward zero to -3, and
    the remainder -1 has the sign of the dividend. Both results are
    zero-extended to 64 bits. *)
Example signed_truncates :
  divided Signed false S32 4294967289 2 = Some 4294967293
  /\ divided Signed true S32 4294967289 2 = Some 4294967295.
Proof. vm_compute. split; reflexivity. Qed.

(** An unsigned division reads the same patterns as large positive
    integers. *)
Example unsigned_reads_patterns :
  divided Unsigned false S32 4294967289 2 = Some 2147483644
  /\ divided Unsigned true S32 4294967289 2 = Some 1
  /\ divided Unsigned false S64 18446744073709551615 0 = Some 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A 32-bit division ignores the upper halves of its operand
    registers, which the loads do not always clear. *)
Example upper_halves_ignored :
  divided Signed false S32 (4294967296 * 5 + 100) (4294967296 * 9 + 7) = Some 14.
Proof. vm_compute. reflexivity. Qed.

(** A raw signed divide of the same operands faults, which is the
    behavior that the rewriting removes. *)
Example raw_divide_faults :
  result (run (fun _ => true) (divide_code Signed S32) (operands 2147483648 4294967295))
  = None
  /\ result (run (fun _ => true) (divide_code Signed S32) (operands 7 0)) = None.
Proof. vm_compute. split; reflexivity. Qed.
