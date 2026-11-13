(** The integer code that the nanofil backend emits computes in the
    sixteen general-purpose registers of x86-64 and tests the six
    arithmetic flags. This module defines that part of the processor
    state, and the two operations through which every instruction
    touches a register: reading a part of it and writing a part of it.

    A register name such as `%eax` or `%dl` selects the low 32 or 8
    bits of a 64-bit register. Reading a part is a truncation. Writing
    a part follows a rule that surprises many readers of assembly: a
    32-bit write clears the upper half of the register, while an 8-bit
    or 16-bit write preserves all the bits it does not name. The
    function [set_reg] states that rule once, so that no instruction
    can apply it differently.

    The state has no memory and no instruction pointer yet. The first
    theorem about emitted code, in Amd64Division.v, concerns a
    straight-line sequence that computes only in registers. Byte memory
    and control flow are later additions to the record [machine]. *)

From Stdlib Require Import ZArith Bool Lia.
From Backend Require Import Amd64Word.
Local Open Scope Z_scope.

(** ## Registers and flags

    The state of the integer machine is a 64-bit pattern for each
    general-purpose register and one bit for each arithmetic flag.
    This section names the registers and the flags and defines the
    record that holds them. *)

(** A [gpr] names one of the sixteen 64-bit general-purpose registers.
    The partial registers, such as `%eax` and `%al`, are views of
    these and are selected by an operand [size]. *)
Inductive gpr : Type :=
| RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
| R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15.

(** The function [gpr_index] numbers the registers as the instruction
    encoding does. *)
Definition gpr_index (r : gpr) : Z :=
  match r with
  | RAX => 0 | RCX => 1 | RDX => 2 | RBX => 3
  | RSP => 4 | RBP => 5 | RSI => 6 | RDI => 7
  | R8 => 8 | R9 => 9 | R10 => 10 | R11 => 11
  | R12 => 12 | R13 => 13 | R14 => 14 | R15 => 15
  end.

(** The function [gpr_eqb] decides whether two names denote the same
    register. *)
Definition gpr_eqb (r r' : gpr) : bool := gpr_index r =? gpr_index r'.

(** A [flag] names one of the six arithmetic status flags: carry,
    parity, auxiliary carry, zero, sign and overflow. *)
Inductive flag : Type := CF | PF | AF | ZF | SF | OF.

(** A [machine] is the integer state of the processor. The field
    [regs] gives the 64-bit content of each register, and the field
    [flags] gives the value of each arithmetic flag. *)
Record machine : Type := mkMachine {
  regs : gpr -> Z;
  flags : flag -> bool
}.

(** ## Reading and writing a part of a register

    An instruction at operand size z reads the low bits of its source
    registers and writes the low bits of its destination. This section
    defines both operations for every size, including the rule that a
    32-bit write clears the upper half of its register. *)

(** The function [get_reg] reads the low part of a register at the
    given size, as an unsigned integer. *)
Definition get_reg (z : size) (r : gpr) (s : machine) : Z := wrap z (regs s r).

(** The function [merge_reg] computes the 64-bit content of a register
    after a write of the value v at the given size, where old is the
    earlier content. A 64-bit write replaces the content, and a 32-bit
    write also clears the upper half. An 8-bit or 16-bit write replaces
    only the low part and preserves the remaining bits. *)
Definition merge_reg (z : size) (old v : Z) : Z :=
  match z with
  | S64 | S32 => wrap z v
  | S16 | S8 => wrap S64 old - wrap z old + wrap z v
  end.

(** The function [set_reg] writes the value v to the low part of the
    register r at the given size. It leaves every other register and
    every flag as it was. *)
Definition set_reg (z : size) (r : gpr) (v : Z) (s : machine) : machine :=
  mkMachine
    (fun r' => if gpr_eqb r' r then merge_reg z (regs s r) v else regs s r')
    (flags s).

(** ## Flag effects and undefined flags

    The processor manual gives each instruction one of three effects
    on each flag: the instruction leaves the flag alone, sets it to a
    stated value, or leaves it undefined. An undefined flag has some
    value afterwards, but the manual does not say which, and different
    processors choose differently. Treating that value as zero would
    let a proof depend on a choice that real hardware does not make.

    The semantics therefore takes the values of undefined flags from a
    parameter, and a theorem about emitted code must hold for every
    such parameter. Code whose result changes with an undefined flag
    then has no provable result. *)

(** A [flag_effect] is what one instruction does to one flag. *)
Inductive flag_effect : Type :=
| Keep (* the instruction does not change the flag *)
| Defined (b : bool) (* the instruction sets the flag to b *)
| Undefined. (* the manual leaves the flag's new value unspecified *)

(** A [havoc] supplies the value that each flag takes when an
    instruction leaves it undefined. A statement about emitted code
    quantifies over every havoc. *)
Definition havoc : Type := flag -> bool.

(** The function [set_flags] applies an instruction's effect on every
    flag, taking the value of each undefined flag from the havoc h. It
    leaves the registers as they were. *)
Definition set_flags (h : havoc) (e : flag -> flag_effect) (s : machine) : machine :=
  mkMachine
    (regs s)
    (fun f =>
       match e f with
       | Keep => flags s f
       | Defined b => b
       | Undefined => h f
       end).

(** ## Well-formed states

    A register holds 64 bits, so the content of every register in a
    real state is below two to the 64. The functions above never rely
    on that bound, because [get_reg] truncates what it reads. The bound
    is still worth stating, since it shows that [set_reg] never
    produces a content that no processor could hold. *)

(** A machine is [well_formed] when every register content is a valid
    64-bit pattern. *)
Definition well_formed (s : machine) : Prop :=
  forall r, 0 <= regs s r < size_modulus S64.

(** ## Facts about register names

    The function [gpr_eqb] is a comparison of encoding numbers, and a
    proof needs it to agree with equality of register names. *)

(** Two registers have the same number exactly when they are the same
    register. *)
Lemma gpr_eqb_eq (r r' : gpr) : gpr_eqb r r' = true <-> r = r'.
Proof.
Admitted.

(** Every register is equal to itself under [gpr_eqb]. *)
Lemma gpr_eqb_refl (r : gpr) : gpr_eqb r r = true.
Proof.
Admitted.

(** Distinct registers are distinct under [gpr_eqb]. *)
Lemma gpr_eqb_neq (r r' : gpr) : r <> r' -> gpr_eqb r r' = false.
Proof.
Admitted.

(** ## Facts about reading after writing

    A proof about a sequence of instructions follows each register
    through each write. These lemmas say what a read returns after a
    write to the same register or to another one, and they are the
    whole interface that later proofs use to reason about [set_reg]
    and [set_flags]. *)

(** A read always returns a valid pattern of its size. *)
Lemma get_reg_range (z : size) (r : gpr) (s : machine) :
  0 <= get_reg z r s < size_modulus z.
Proof.
Admitted.

(** A 64-bit write leaves exactly the wrapped value in the register. *)
Lemma regs_set_reg_64 (r : gpr) (v : Z) (s : machine) :
  regs (set_reg S64 r v s) r = wrap S64 v.
Proof.
Admitted.

(** A 32-bit write leaves the wrapped value in the register with a
    clear upper half. *)
Lemma regs_set_reg_32 (r : gpr) (v : Z) (s : machine) :
  regs (set_reg S32 r v s) r = wrap S32 v.
Proof.
Admitted.

(** A write does not change the content of any other register. *)
Lemma regs_set_reg_other (z : size) (r r' : gpr) (v : Z) (s : machine) :
  r' <> r -> regs (set_reg z r v s) r' = regs s r'.
Proof.
Admitted.

(** A read of a part that is no wider than the part just written
    returns the written value, truncated to the size of the read. *)
Lemma get_set_reg_same (z z' : size) (r : gpr) (v : Z) (s : machine) :
  size_bits z <= size_bits z' ->
  get_reg z r (set_reg z' r v s) = wrap z v.
Proof.
Admitted.

(** A 64-bit read after a 32-bit write returns the written value, since
    the write cleared the upper half. *)
Lemma get_64_set_32 (r : gpr) (v : Z) (s : machine) :
  get_reg S64 r (set_reg S32 r v s) = wrap S32 v.
Proof.
Admitted.

(** A read of one register is unaffected by a write to another. *)
Lemma get_set_reg_other (z z' : size) (r r' : gpr) (v : Z) (s : machine) :
  r' <> r -> get_reg z r' (set_reg z' r v s) = get_reg z r' s.
Proof.
Admitted.

(** A write to a register does not change any flag. *)
Lemma flags_set_reg (z : size) (r : gpr) (v : Z) (s : machine) (f : flag) :
  flags (set_reg z r v s) f = flags s f.
Proof.
Admitted.

(** A flag update does not change the content of any register. *)
Lemma regs_set_flags (h : havoc) (e : flag -> flag_effect) (s : machine) (r : gpr) :
  regs (set_flags h e s) r = regs s r.
Proof.
Admitted.

(** A flag update does not change what any read of a register
    returns. *)
Lemma get_reg_set_flags (h : havoc) (e : flag -> flag_effect) (z : size) (r : gpr)
    (s : machine) :
  get_reg z r (set_flags h e s) = get_reg z r s.
Proof.
Admitted.

(** A flag that an instruction defines has the defined value
    afterwards, whatever the havoc is. *)
Lemma flags_set_flags_defined (h : havoc) (e : flag -> flag_effect) (s : machine)
    (f : flag) (b : bool) :
  e f = Defined b -> flags (set_flags h e s) f = b.
Proof.
Admitted.

(** A flag that an instruction keeps has its earlier value
    afterwards. *)
Lemma flags_set_flags_keep (h : havoc) (e : flag -> flag_effect) (s : machine)
    (f : flag) :
  e f = Keep -> flags (set_flags h e s) f = flags s f.
Proof.
Admitted.

(** ## Facts about well-formed states

    These lemmas show that the two state updates keep every register
    content within 64 bits, so every state reached from a well-formed
    state is well-formed. *)

(** A merged register content is a valid 64-bit pattern, whatever the
    earlier content and the written value are. *)
Lemma merge_reg_range (z : size) (old v : Z) :
  0 <= merge_reg z old v < size_modulus S64.
Proof.
Admitted.

(** A write to a register keeps a well-formed state well-formed. *)
Lemma set_reg_well_formed (z : size) (r : gpr) (v : Z) (s : machine) :
  well_formed s -> well_formed (set_reg z r v s).
Proof.
Admitted.

(** A flag update keeps a well-formed state well-formed. *)
Lemma set_flags_well_formed (h : havoc) (e : flag -> flag_effect) (s : machine) :
  well_formed s -> well_formed (set_flags h e s).
Proof.
Admitted.
