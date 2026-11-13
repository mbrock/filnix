(** The backend builds its assembly as the [line] terms of Asm.v, in
    which a mnemonic, a suffix and a register name are strings. The
    execution model of Amd64Step.v is defined on typed instructions
    instead. This module connects the two: the function [decode_line]
    reads one line as a typed instruction, and it refuses every line
    that the model does not describe.

    The refusal matters as much as the reading. A theorem about emitted
    code is stated on the lines that the emitter produces, so it holds
    only when those lines decode. A line with an operand that the
    model does not cover, such as an indexed memory operand or a
    high-byte register, has no typed form and therefore no theorem.

    The reading checks what an assembler would check. The size that a
    suffix names must agree with the size that each register name
    selects, and an immediate must fit the field that the instruction
    encodes it in. This is a specification of what the text means, and
    it is separate from Encode.v, which produces the bytes. *)

From Stdlib Require Import String ZArith List Bool.
From Backend Require Import Asm Amd64Word Amd64Machine Amd64Step.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Register names

    A register name selects both a register and a part of it, so
    `%eax` and `%al` name the same register at two sizes. This section
    reads a name as that pair. The four high-byte names, such as `%ah`,
    are absent because the model has no operand that selects bits 8 to
    15 of a register. *)

(** The table [register_rows] gives the names of each register from the
    widest part to the narrowest: the 64-bit, 32-bit, 16-bit and 8-bit
    names in that order. *)
Definition register_rows : list (gpr * list string) :=
  [(RAX, ["rax"; "eax"; "ax"; "al"]);
   (RCX, ["rcx"; "ecx"; "cx"; "cl"]);
   (RDX, ["rdx"; "edx"; "dx"; "dl"]);
   (RBX, ["rbx"; "ebx"; "bx"; "bl"]);
   (RSP, ["rsp"; "esp"; "sp"; "spl"]);
   (RBP, ["rbp"; "ebp"; "bp"; "bpl"]);
   (RSI, ["rsi"; "esi"; "si"; "sil"]);
   (RDI, ["rdi"; "edi"; "di"; "dil"]);
   (R8, ["r8"; "r8d"; "r8w"; "r8b"]);
   (R9, ["r9"; "r9d"; "r9w"; "r9b"]);
   (R10, ["r10"; "r10d"; "r10w"; "r10b"]);
   (R11, ["r11"; "r11d"; "r11w"; "r11b"]);
   (R12, ["r12"; "r12d"; "r12w"; "r12b"]);
   (R13, ["r13"; "r13d"; "r13w"; "r13b"]);
   (R14, ["r14"; "r14d"; "r14w"; "r14b"]);
   (R15, ["r15"; "r15d"; "r15w"; "r15b"])].

(** The list [row_sizes] gives the sizes of the names in a row of
    [register_rows], in the same order. *)
Definition row_sizes : list size := [S64; S32; S16; S8].

(** The function [name_size] finds a name in a row and returns the size
    at the same position of the size list. *)
Fixpoint name_size (name : string) (names : list string) (sizes : list size)
    : option size :=
  match names, sizes with
  | n :: names', z :: sizes' =>
      if String.eqb n name then Some z else name_size name names' sizes'
  | _, _ => None
  end.

(** The function [register_in] searches the rows of a table for a name
    and returns the size and the register that the name selects. *)
Fixpoint register_in (name : string) (rows : list (gpr * list string))
    : option (size * gpr) :=
  match rows with
  | [] => None
  | (r, names) :: rows' =>
      match name_size name names row_sizes with
      | Some z => Some (z, r)
      | None => register_in name rows'
      end
  end.

(** The function [register] reads a register name as the size and the
    register that it selects, or returns `None` for a name that the
    model does not have. *)
Definition register (name : string) : option (size * gpr) :=
  register_in name register_rows.

(** ## Operands

    An instruction's suffix fixes its operand size, and every operand
    must agree with it. This section reads a register operand and a
    source operand at a required size and refuses any operand of a
    different size or a different kind. *)

(** The function [suffix_size] reads an AT&T size suffix. *)
Definition suffix_size (suffix : string) : option size :=
  if String.eqb suffix "b" then Some S8
  else if String.eqb suffix "w" then Some S16
  else if String.eqb suffix "l" then Some S32
  else if String.eqb suffix "q" then Some S64
  else None.

(** The function [sized_register] reads an operand as a register whose
    name selects exactly the size z. *)
Definition sized_register (z : size) (o : operand) : option gpr :=
  match o with
  | OReg name =>
      match register name with
      | Some (z', r) => if size_eqb z' z then Some r else None
      | None => None
      end
  | _ => None
  end.

(** The function [immediate_fits] decides whether an assembler accepts
    the integer n as an immediate of an instruction at the size z. A
    byte, word or long immediate may be written as a signed or an
    unsigned number of its size. A quad instruction encodes a 32-bit
    immediate that the processor sign-extends, so only a signed 32-bit
    number fits. *)
Definition immediate_fits (z : size) (n : Z) : bool :=
  match z with
  | S64 => fits_signed S32 n
  | S8 | S16 | S32 => (- (size_modulus z / 2) <=? n) && (n <? size_modulus z)
  end.

(** The function [sized_source] reads an operand as a source at the
    size z: an integer immediate that fits, or a register of that
    size. *)
Definition sized_source (z : size) (o : operand) : option source :=
  match o with
  | OImm (ELit (LInt n)) => if immediate_fits z n then Some (SImm n) else None
  | _ =>
      match sized_register z o with
      | Some r => Some (SReg r)
      | None => None
      end
  end.

(** The function [memory_operand] reads an operand of the form
    `d(%b)` as an address. The base must be a 64-bit register name and
    the displacement must be an integer that fits the signed 32-bit
    field that the instruction encodes it in. A symbolic displacement
    and an indexed operand have no typed form. *)
Definition memory_operand (o : operand) : option address :=
  match o with
  | OMem (LInt d) b =>
      match register b with
      | Some (S64, r) => if fits_signed S32 d then Some (mkAddress r d) else None
      | _ => None
      end
  | _ => None
  end.

(** The function [wide_immediate_fits] decides whether an assembler
    accepts the integer n as the 64-bit immediate of a `movabs`. The
    integer may be written as a signed or an unsigned 64-bit number. *)
Definition wide_immediate_fits (n : Z) : bool :=
  (- (size_modulus S64 / 2) <=? n) && (n <? size_modulus S64).

(** ## Mnemonics

    The mnemonics of the modeled instructions fall into a few families
    that share an operand shape. This section reads the name of a
    member of each family. *)

(** The function [binary_named] reads the mnemonic of a two-operand
    arithmetic or logic instruction. *)
Definition binary_named (op : string) : option binary :=
  if String.eqb op "add" then Some BAdd
  else if String.eqb op "sub" then Some BSub
  else if String.eqb op "and" then Some BAnd
  else if String.eqb op "or" then Some BOr
  else if String.eqb op "xor" then Some BXor
  else if String.eqb op "cmp" then Some BCmp
  else if String.eqb op "test" then Some BTest
  else None.

(** The function [unary_named] reads the mnemonic of a one-operand
    instruction that rewrites its register. *)
Definition unary_named (op : string) : option unary :=
  if String.eqb op "neg" then Some UNeg
  else if String.eqb op "not" then Some UNot
  else None.

(** The function [extension_named] reads the mnemonic of an extending
    move. It returns whether the move sign-extends and the size of the
    source, which the mnemonic's last letter names. The suffix of the
    line gives the size of the destination. *)
Definition extension_named (op : string) : option (bool * size) :=
  if String.eqb op "movzb" then Some (false, S8)
  else if String.eqb op "movzw" then Some (false, S16)
  else if String.eqb op "movsb" then Some (true, S8)
  else if String.eqb op "movsw" then Some (true, S16)
  else if String.eqb op "movsl" then Some (true, S32)
  else None.

(** The function [condition_named] reads a condition suffix, as it
    follows `set` in a mnemonic. *)
Definition condition_named (cc : string) : option condition :=
  if String.eqb cc "e" then Some CondE
  else if String.eqb cc "ne" then Some CondNE
  else if String.eqb cc "b" then Some CondB
  else if String.eqb cc "be" then Some CondBE
  else if String.eqb cc "a" then Some CondA
  else if String.eqb cc "ae" then Some CondAE
  else if String.eqb cc "l" then Some CondL
  else if String.eqb cc "le" then Some CondLE
  else if String.eqb cc "g" then Some CondG
  else if String.eqb cc "ge" then Some CondGE
  else if String.eqb cc "s" then Some CondS
  else if String.eqb cc "ns" then Some CondNS
  else if String.eqb cc "o" then Some CondO
  else if String.eqb cc "no" then Some CondNO
  else if String.eqb cc "p" then Some CondP
  else if String.eqb cc "np" then Some CondNP
  else None.

(** The function [set_condition] reads a `setcc` mnemonic and returns
    its condition. *)
Definition set_condition (op : string) : option condition :=
  if String.prefix "set" op
  then condition_named (String.substring 3 (String.length op - 3) op)
  else None.

(** ## Lines

    A line of the backend is a mnemonic, an optional suffix and a list
    of operands in AT&T order, with the destination last. This section
    reads a line by its shape: a suffixed line with two operands or
    with one, and an unsuffixed line with one operand or with none. *)

(** The function [decode_move] reads the two operands of a `mov`. A
    memory operand on the left makes the line a load, and a memory
    operand on the right makes it a store of a register. With no
    memory operand the line is a move of an immediate or a register
    into a register. A move between two memory operands does not
    exist, and a store of an immediate is outside the model. *)
Definition decode_move (z : size) (a d : operand) : option instr :=
  match memory_operand a, memory_operand d with
  | Some m, None =>
      match sized_register z d with
      | Some r => Some (ILoad z m r)
      | None => None
      end
  | None, Some m =>
      match sized_register z a with
      | Some r => Some (IStore z r m)
      | None => None
      end
  | None, None =>
      match sized_source z a, sized_register z d with
      | Some x, Some r => Some (IMov z x r)
      | _, _ => None
      end
  | Some _, Some _ => None
  end.

(** The function [decode_wide_move] reads the two operands of a
    `movabs`, which loads a full 64-bit immediate into a 64-bit
    register. It reads as the same typed move as a `mov` of an
    immediate, because the typed immediate is an integer of any
    width. *)
Definition decode_wide_move (z : size) (a d : operand) : option instr :=
  match z, a, sized_register S64 d with
  | S64, OImm (ELit (LInt n)), Some r =>
      if wide_immediate_fits n then Some (IMov S64 (SImm n) r) else None
  | _, _, _ => None
  end.

(** The function [decode_two] reads a suffixed instruction with a
    source and a destination: a move, a binary operation or an
    extending move. *)
Definition decode_two (op : string) (z : size) (a d : operand) : option instr :=
  if String.eqb op "mov" then decode_move z a d
  else if String.eqb op "movabs" then decode_wide_move z a d
  else
    match binary_named op, extension_named op with
    | Some o, _ =>
        match sized_source z a, sized_register z d with
        | Some x, Some r => Some (IBinary o z x r)
        | _, _ => None
        end
    | None, Some (sx, za) =>
        match sized_register za a, sized_register z d with
        | Some x, Some r => Some (if sx then IMovsx za z x r else IMovzx za z x r)
        | _, _ => None
        end
    | None, None => None
    end.

(** The function [decode_one] reads a suffixed instruction with one
    register operand: a negation, a complement or a division. *)
Definition decode_one (op : string) (z : size) (d : operand) : option instr :=
  match sized_register z d with
  | Some r =>
      if String.eqb op "idiv" then Some (IDivide true z r)
      else if String.eqb op "div" then Some (IDivide false z r)
      else
        match unary_named op with
        | Some o => Some (IUnary o z r)
        | None => None
        end
  | None => None
  end.

(** The function [decode_bare] reads an instruction without a suffix.
    With no operand it is a sign extension of the accumulator, and
    with one byte register it is a `setcc`. *)
Definition decode_bare (op : string) (os : list operand) : option instr :=
  match os with
  | [] =>
      if String.eqb op "cwtd" then Some (IExtend S16)
      else if String.eqb op "cltd" then Some (IExtend S32)
      else if String.eqb op "cqto" then Some (IExtend S64)
      else None
  | [d] =>
      match set_condition op, sized_register S8 d with
      | Some c, Some r => Some (ISet c r)
      | _, _ => None
      end
  | _ => None
  end.

(** The function [decode_line] reads one line of the backend as a typed
    instruction. It returns `None` for a label, a directive, a fixed
    instruction and every instruction form outside the model. *)
Definition decode_line (l : line) : option instr :=
  match l with
  | Ins op (Some suffix) os =>
      match suffix_size suffix, os with
      | Some z, [a; d] => decode_two op z a d
      | Some z, [d] => decode_one op z d
      | _, _ => None
      end
  | Ins op None os => decode_bare op os
  | Label _ | Fixed _ | Dir _ => None
  end.

(** The function [decode_lines] reads a list of lines as a straight-line
    sequence of typed instructions. One line outside the model makes
    the whole list unreadable. *)
Fixpoint decode_lines (ls : list line) : option (list instr) :=
  match ls with
  | [] => Some []
  | l :: ls' =>
      match decode_line l, decode_lines ls' with
      | Some i, Some code => Some (i :: code)
      | _, _ => None
      end
  end.

(** ## Facts about reading lists

    The emitter builds an instruction's code by appending fragments,
    and a proof handles each fragment separately. This lemma lets the
    reading follow that structure. *)

(** Two readable lists of lines read, when appended, as the two typed
    sequences appended. *)
Lemma decode_lines_app (ls ls' : list line) (code code' : list instr) :
  decode_lines ls = Some code ->
  decode_lines ls' = Some code' ->
  decode_lines (ls ++ ls') = Some (code ++ code').
Proof.
  revert code; induction ls as [|l ls IH]; intros code H H'; simpl in *.
  - inversion H; subst; exact H'.
  - destruct (decode_line l) as [i|] eqn:E;
      destruct (decode_lines ls) as [rest|] eqn:Er; try discriminate.
    inversion H; subst code; rewrite (IH _ eq_refl H'); reflexivity.
Qed.

(** ## Examples

    These examples read lines as the Prolog compiler prints them and
    show a refusal for each kind of mismatch that the reading checks. *)

(** A 32-bit `test` of a register with itself reads as a binary
    operation that only sets flags. *)
Example decode_test :
  decode_line (Ins "test" (Some "l") [OReg "ecx"; OReg "ecx"])
  = Some (IBinary BTest S32 (SReg RCX) RCX).
Proof. reflexivity. Qed.

(** A `sete` of `%dl` reads as a byte write to the register `%rdx`. *)
Example decode_sete :
  decode_line (Ins "sete" None [OReg "dl"]) = Some (ISet CondE RDX).
Proof. reflexivity. Qed.

(** A `movzbl` reads as a zero extension from a byte to a long. *)
Example decode_movzbl :
  decode_line (Ins "movzb" (Some "l") [OReg "dl"; OReg "edx"])
  = Some (IMovzx S8 S32 RDX RDX).
Proof. reflexivity. Qed.

(** A comparison with the immediate -1 keeps the immediate as written.
    The instruction reduces it to its operand size when it executes. *)
Example decode_cmp :
  decode_line (Ins "cmp" (Some "q") [OImm (ELit (LInt (-1))); OReg "rcx"])
  = Some (IBinary BCmp S64 (SImm (-1)) RCX).
Proof. reflexivity. Qed.

(** A signed 64-bit division reads with its divisor register. *)
Example decode_idiv :
  decode_line (Ins "idiv" (Some "q") [OReg "rcx"]) = Some (IDivide true S64 RCX).
Proof. reflexivity. Qed.

(** A register whose size disagrees with the suffix is refused. *)
Example decode_size_mismatch :
  decode_line (Ins "add" (Some "q") [OReg "edx"; OReg "rcx"]) = None.
Proof. reflexivity. Qed.

(** A 32-bit `mov` from a frame slot reads as a load at a negative
    displacement from `%rbp`. *)
Example decode_load :
  decode_line (Ins "mov" (Some "l") [OMem (LInt (-8)) "rbp"; OReg "eax"])
  = Some (ILoad S32 (mkAddress RBP (-8)) RAX).
Proof. reflexivity. Qed.

(** A 64-bit `mov` to a frame slot reads as a store of a register. *)
Example decode_store :
  decode_line (Ins "mov" (Some "q") [OReg "rax"; OMem (LInt (-24)) "rbp"])
  = Some (IStore S64 RAX (mkAddress RBP (-24))).
Proof. reflexivity. Qed.

(** A `movabs` reads as a 64-bit move of an immediate that a `mov`
    would refuse. *)
Example decode_movabs :
  decode_line (Ins "movabs" (Some "q") [OImm (ELit (LInt 4294967296)); OReg "rcx"])
  = Some (IMov S64 (SImm 4294967296) RCX).
Proof. reflexivity. Qed.

(** A load whose register disagrees with the suffix is refused. *)
Example decode_load_mismatch :
  decode_line (Ins "mov" (Some "l") [OMem (LInt (-8)) "rbp"; OReg "rax"]) = None.
Proof. reflexivity. Qed.

(** A memory operand with a 32-bit base register is refused. *)
Example decode_narrow_base :
  decode_line (Ins "mov" (Some "q") [OMem (LInt (-8)) "ebp"; OReg "rax"]) = None.
Proof. reflexivity. Qed.

(** A displacement that does not fit 32 signed bits is refused. *)
Example decode_wide_displacement :
  decode_line (Ins "mov" (Some "q") [OMem (LInt 2147483648) "rbp"; OReg "rax"]) = None.
Proof. reflexivity. Qed.

(** An indexed memory operand is refused, because the model has no
    index register. *)
Example decode_indexed :
  decode_line (Ins "mov" (Some "q") [OMemIndex (LInt 0) "rax" "rcx"; OReg "rdx"]) = None.
Proof. reflexivity. Qed.

(** A store of an immediate is refused. *)
Example decode_store_immediate :
  decode_line (Ins "mov" (Some "q") [OImm (ELit (LInt 0)); OMem (LInt (-8)) "rbp"]) = None.
Proof. reflexivity. Qed.

(** A quad immediate that does not fit 32 signed bits is refused. *)
Example decode_wide_immediate :
  decode_line (Ins "mov" (Some "q") [OImm (ELit (LInt 4294967296)); OReg "rax"]) = None.
Proof. reflexivity. Qed.

(** A mnemonic outside the model is refused. *)
Example decode_unknown :
  decode_line (Ins "imul" (Some "l") [OReg "ecx"; OReg "eax"]) = None.
Proof. reflexivity. Qed.
