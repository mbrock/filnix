(** x86-64 assembly as the backend builds it, and its printer as GNU
    as (AT&T) text: asm.pl's line terms as inductives, and asm.pl's
    grammar as functions. The text is asm.pl's byte for byte, which
    the backend's gate checks on every line the Prolog compiler emits
    for the corpus (asm.sh).

    Mnemonics, suffixes and register names are strings, as they are
    atoms in asm.pl: the set is whatever instruction selection uses,
    and this file only prints. *)

From Stdlib Require Import String ZArith List Ascii Bool.
From Backend Require Import Text.
Import ListNotations.
Local Open Scope string_scope.

(** What asm.pl prints with `literal//1`: an integer or an atom. *)
Inductive lit : Type :=
| LInt (n : Z) (* an integer, in decimal *)
| LSym (s : string). (* an atom, as it is *)

(** An expression: a literal or a sum. *)
Inductive expr : Type :=
| ELit (a : lit)
| EAdd (a b : expr). (* `A+B`; a left operand that is a sum is parenthesized *)

(** An operand. Registers are named concretely (`eax`, `cl`, `r9d`),
    so mixed widths need no bookkeeping. *)
Inductive operand : Type :=
| OImm (e : expr) (* `$E` *)
| OReg (r : string) (* `%R` *)
| OMem (d : lit) (b : string) (* `D(%B)`, D omitted when it is 0 *)
| OMemIndex (d : lit) (b i : string) (* `D(%B,%I)`, D omitted when it is 0 *)
| ORip (e : expr) (* `E(%rip)` *)
| OGotpcrel (s : lit) (* `S@GOTPCREL(%rip)` *)
| OPlt (s : lit) (* `S@PLT` *)
| OGottpoff (s : lit) (* `S@GOTTPOFF(%rip)` *)
| OFs (o : operand) (* `%fs:O` *)
| OSym (e : expr) (* `E`, a jump or call target *)
| OInd (o : operand). (* `*O` *)

(** A section. *)
Inductive section : Type :=
| SText
| SData
| SRodata
| SBss
| STbss (* thread-local, zeroed *)
| SDataRelRo
| SNoteGnuStack
| SInit (ctor : bool) (prio : option lit). (* .init_array or .fini_array, with `.Prio` if any *)

(** A directive. *)
Inductive directive : Type :=
| DSection (s : section)
| DP2align (n : lit)
| DBalign (n : lit)
| DGlobl (s : lit)
| DWeak (s : lit)
| DHidden (s : lit)
| DType (s t : lit) (* `.type S, @T` *)
| DSize (s : lit) (* `.size S, .-S` *)
| DSizeOf (s n : lit) (* `.size S, N` *)
| DSet (s : lit) (e : expr)
| DQuad (e : expr)
| DLong (n : lit)
| DInt (n : lit)
| DShort (n : lit)
| DByte (n : lit) (ns : list lit) (* `.byte` and a non-empty list *)
| DZero (n : lit)
| DAscii (cs : list ascii) (* `.ascii` and the bytes, escaped *)
| DAsciz (a : lit). (* `.asciz` and the atom, as it is *)

(** A fixed-register instruction from the emitter's own table
    (docs/asm-fixed.md). *)
Inductive fixed : Type :=
| Cpuid
| Xgetbv
| Rdtsc
| Rdtscp
| Lfence
| Sfence
| Pause.

(** A line. *)
Inductive line : Type :=
| Label (s : lit) (* `S:` *)
| Fixed (m : fixed)
| Ins (op : string) (suffix : option string) (os : list operand)
  (* Op, then the suffix if any, then the operands in AT&T order *)
| Dir (d : directive).

(** ## The printer *)

(** The text of a literal. *)
Definition lit_text (a : lit) : string :=
  match a with
  | LInt n => decimal n
  | LSym s => s
  end.

Fixpoint expr_parts (e : expr) (k : parts) : parts :=
  match e with
  | ELit a => lit_text a :: k
  | EAdd a b =>
      let rest := "+" :: expr_parts b k in
      match a with
      | EAdd _ _ => "(" :: expr_parts a (")" :: rest)
      | ELit _ => expr_parts a rest
      end
  end.

(** A displacement; 0 is omitted. *)
Definition disp_parts (d : lit) (k : parts) : parts :=
  match d with
  | LInt Z0 => k
  | _ => lit_text d :: k
  end.

Fixpoint operand_parts (o : operand) (k : parts) : parts :=
  match o with
  | OImm e => "$" :: expr_parts e k
  | OReg r => "%" :: r :: k
  | OMem d b => disp_parts d ("(%" :: b :: ")" :: k)
  | OMemIndex d b i => disp_parts d ("(%" :: b :: ",%" :: i :: ")" :: k)
  | ORip e => expr_parts e ("(%rip)" :: k)
  | OGotpcrel s => lit_text s :: "@GOTPCREL(%rip)" :: k
  | OPlt s => lit_text s :: "@PLT" :: k
  | OGottpoff s => lit_text s :: "@GOTTPOFF(%rip)" :: k
  | OFs o' => "%fs:" :: operand_parts o' k
  | OSym e => expr_parts e k
  | OInd o' => "*" :: operand_parts o' k
  end.

Fixpoint more_operands (os : list operand) (k : parts) : parts :=
  match os with
  | [] => k
  | o :: os' => ", " :: operand_parts o (more_operands os' k)
  end.

(** The operands after a mnemonic: a space, then the operands with
    commas between them, or nothing. *)
Definition operands_parts (os : list operand) (k : parts) : parts :=
  match os with
  | [] => k
  | o :: os' => " " :: operand_parts o (more_operands os' k)
  end.

Fixpoint more_bytes (ns : list lit) (k : parts) : parts :=
  match ns with
  | [] => k
  | n :: ns' => ", " :: lit_text n :: more_bytes ns' k
  end.

(** A byte in three octal digits. *)
Definition octal (n : nat) : string :=
  digit (n / 64) ++ digit (n / 8 mod 8) ++ digit (n mod 8).

(** One byte inside an .ascii string: printable ASCII as itself except
    quote and backslash, which are escaped, newline and tab as `\n`
    and `\t`, any other byte as a backslash and three octal digits. *)
Definition ascii_char_text (c : ascii) : string :=
  let n := nat_of_ascii c in
  if (n =? 34)%nat then "\"""
  else if (n =? 92)%nat then "\\"
  else if (n =? 10)%nat then "\n"
  else if (n =? 9)%nat then "\t"
  else if ((32 <=? n) && (n <=? 126))%nat then String c EmptyString
  else "\" ++ octal n.

Fixpoint ascii_parts (cs : list ascii) (k : parts) : parts :=
  match cs with
  | [] => k
  | c :: cs' => ascii_char_text c :: ascii_parts cs' k
  end.

Definition section_parts (s : section) (k : parts) : parts :=
  match s with
  | SText => ".text" :: k
  | SData => ".data" :: k
  | SRodata => ".section .rodata" :: k
  | SBss => ".bss" :: k
  | STbss => ".section .tbss,""awT"",@nobits" :: k
  | SDataRelRo => ".section .data.rel.ro,""aw"",@progbits" :: k
  | SNoteGnuStack => ".section .note.GNU-stack,"""",@progbits" :: k
  | SInit ctor prio =>
      let array := if ctor then "init_array" else "fini_array" in
      let rest := ",""aw"",@" :: array :: k in
      ".section ." :: array ::
        match prio with
        | None => rest
        | Some p => "." :: lit_text p :: rest
        end
  end.

Definition directive_parts (d : directive) (k : parts) : parts :=
  match d with
  | DSection s => section_parts s k
  | DP2align n => ".p2align " :: lit_text n :: k
  | DBalign n => ".balign " :: lit_text n :: k
  | DGlobl s => ".globl " :: lit_text s :: k
  | DWeak s => ".weak " :: lit_text s :: k
  | DHidden s => ".hidden " :: lit_text s :: k
  | DType s t => ".type " :: lit_text s :: ", @" :: lit_text t :: k
  | DSize s => ".size " :: lit_text s :: ", .-" :: lit_text s :: k
  | DSizeOf s n => ".size " :: lit_text s :: ", " :: lit_text n :: k
  | DSet s e => ".set " :: lit_text s :: ", " :: expr_parts e k
  | DQuad e => ".quad " :: expr_parts e k
  | DLong n => ".long " :: lit_text n :: k
  | DInt n => ".int " :: lit_text n :: k
  | DShort n => ".short " :: lit_text n :: k
  | DByte n ns => ".byte " :: lit_text n :: more_bytes ns k
  | DZero n => ".zero " :: lit_text n :: k
  | DAscii cs => ".ascii """ :: ascii_parts cs ("""" :: k)
  | DAsciz a => ".asciz """ :: lit_text a :: """" :: k
  end.

Definition fixed_name (m : fixed) : string :=
  match m with
  | Cpuid => "cpuid"
  | Xgetbv => "xgetbv"
  | Rdtsc => "rdtsc"
  | Rdtscp => "rdtscp"
  | Lfence => "lfence"
  | Sfence => "sfence"
  | Pause => "pause"
  end.

(** cpuid writes rbx, which may hold a register home: it is kept in
    rsi, and cpuid's b result is brought out in edi. *)
Definition cpuid_text : string :=
  tab ++ "movq %rbx, %rsi" ++ nl ++ tab ++ "cpuid" ++ nl
  ++ tab ++ "movl %ebx, %edi" ++ nl ++ tab ++ "movq %rsi, %rbx" ++ nl.

Definition line_parts (l : line) (k : parts) : parts :=
  match l with
  | Label s => lit_text s :: ":" :: nl :: k
  | Fixed Cpuid => cpuid_text :: k
  | Fixed m => tab :: fixed_name m :: nl :: k
  | Ins op suffix os =>
      let rest := operands_parts os (nl :: k) in
      tab :: op ::
        match suffix with
        | None => rest
        | Some s => s :: rest
        end
  | Dir d => tab :: directive_parts d (nl :: k)
  end.

(** The parts of the lines in [rev], which is the lines in reverse,
    in front of [k]. A loop, so a module of any length prints in
    constant stack. *)
Fixpoint rev_lines_parts (rev : list line) (k : parts) : parts :=
  match rev with
  | [] => k
  | l :: rev' => rev_lines_parts rev' (line_parts l k)
  end.

(** The text of [ls]. *)
Definition lines_parts (ls : list line) : parts :=
  rev_lines_parts (rev' ls) [].

Example print_mov :
  String.concat "" (lines_parts
    [Label (LSym "f");
     Ins "mov" (Some "q") [OMem (LInt (-8)) "rbp"; OReg "rax"];
     Ins "lea" (Some "q") [ORip (EAdd (EAdd (ELit (LSym "x")) (ELit (LInt 8))) (ELit (LInt 4))); OReg "rdi"];
     Ins "ret" None [];
     Dir (DAscii ["a"; """"; "\"; "010"; "200"]%char)])
  = "f:" ++ nl ++ tab ++ "movq -8(%rbp), %rax" ++ nl
    ++ tab ++ "leaq (x+8)+4(%rip), %rdi" ++ nl
    ++ tab ++ "ret" ++ nl
    ++ tab ++ ".ascii ""a\""\\\n\310""" ++ nl.
Proof. reflexivity. Qed.
