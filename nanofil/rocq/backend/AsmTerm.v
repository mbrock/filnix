(** Asm.v's lines from the terms asm.pl prints them from: the decoder
    of what `nanofil asm-terms FILE` writes, one line term each. It is
    how the printer is checked against asm.pl before any pass that
    builds lines exists, and how a later pass's lines are compared
    with the Prolog compiler's, term by term.

    A term that asm.pl would refuse (`bad_asm_line`) decodes to
    nothing. *)

From Stdlib Require Import String ZArith List Ascii Bool.
From Nanofil Require Import Term.
From Backend Require Import Asm.
Import ListNotations.
Local Open Scope string_scope.

(** Option binding: `let* x := e in b` is b with x the value of e, or
    nothing when e has none. *)
Local Notation "'let*' x ':=' e 'in' b" :=
  (match e with Some x => b | None => None end)
  (at level 200, x pattern, e at level 200, b at level 200).

(** [f] of every element, or nothing if any has none. *)
Fixpoint all_some {A B : Type} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs' => let* y := f x in let* ys := all_some f xs' in Some (y :: ys)
  end.

(** A literal: an integer or an atom. *)
Definition dlit (t : term) : option lit :=
  match t with
  | TInt n => Some (LInt n)
  | TAtom a => Some (LSym a)
  | _ => None
  end.

(** The name of an atom. *)
Definition dname (t : term) : option string :=
  match t with
  | TAtom a => Some a
  | _ => None
  end.

(** String equality, written as Prolog's `==`. The decoders compare
    names with it rather than match string patterns, which extract to
    a decision tree over the bits of every character. *)
Local Notation "a == b" := (String.eqb a b) (at level 70).

(** An expression: `A+B` or a literal. *)
Fixpoint dexpr (t : term) : option expr :=
  match t with
  | TApp f [a; b] =>
      if f == "+" then let* a' := dexpr a in let* b' := dexpr b in Some (EAdd a' b')
      else None
  | _ => let* a := dlit t in Some (ELit a)
  end.

Fixpoint doperand (t : term) : option operand :=
  match t with
  | TApp f [x] =>
      if f == "imm" then let* e := dexpr x in Some (OImm e)
      else if f == "reg" then let* r := dname x in Some (OReg r)
      else if f == "rip" then let* e := dexpr x in Some (ORip e)
      else if f == "gotpcrel" then let* s := dlit x in Some (OGotpcrel s)
      else if f == "plt" then let* s := dlit x in Some (OPlt s)
      else if f == "gottpoff" then let* s := dlit x in Some (OGottpoff s)
      else if f == "fs" then let* o := doperand x in Some (OFs o)
      else if f == "sym" then let* e := dexpr x in Some (OSym e)
      else if f == "ind" then let* o := doperand x in Some (OInd o)
      else None
  | TApp f [d; b] =>
      if f == "mem" then let* d' := dlit d in let* b' := dname b in Some (OMem d' b')
      else None
  | TApp f [d; b; i] =>
      if f == "mem" then
        let* d' := dlit d in let* b' := dname b in let* i' := dname i in
        Some (OMemIndex d' b' i')
      else None
  | _ => None
  end.

(** One byte of an `ascii` list: a one-character atom of a code below
    256. *)
Definition dbyte (t : term) : option ascii :=
  let* n := char_code t in
  if (n <? 256)%Z then Some (ascii_of_nat (Z.to_nat n)) else None.

Definition dsection (t : term) : option section :=
  match t with
  | TAtom a =>
      if a == "text" then Some SText
      else if a == "data" then Some SData
      else if a == "rodata" then Some SRodata
      else if a == "bss" then Some SBss
      else if a == "tbss" then Some STbss
      else if a == "data_rel_ro" then Some SDataRelRo
      else if a == "note_gnu_stack" then Some SNoteGnuStack
      else None
  | TApp f [TAtom kind; prio] =>
      if f == "init" then
        let* ctor :=
          if kind == "ctor" then Some true
          else if kind == "dtor" then Some false else None in
        let* p := dlit prio in
        match p with
        | LSym s => if s == "none" then Some (SInit ctor None) else Some (SInit ctor (Some p))
        | LInt _ => Some (SInit ctor (Some p))
        end
      else None
  | _ => None
  end.

Definition ddirective (t : term) : option directive :=
  match t with
  | TApp f [x] =>
      if f == "section" then let* s := dsection x in Some (DSection s)
      else if f == "p2align" then let* n := dlit x in Some (DP2align n)
      else if f == "balign" then let* n := dlit x in Some (DBalign n)
      else if f == "globl" then let* s := dlit x in Some (DGlobl s)
      else if f == "weak" then let* s := dlit x in Some (DWeak s)
      else if f == "hidden" then let* s := dlit x in Some (DHidden s)
      else if f == "size" then let* s := dlit x in Some (DSize s)
      else if f == "quad" then let* e := dexpr x in Some (DQuad e)
      else if f == "long" then let* n := dlit x in Some (DLong n)
      else if f == "int" then let* n := dlit x in Some (DInt n)
      else if f == "short" then let* n := dlit x in Some (DShort n)
      else if f == "zero" then let* n := dlit x in Some (DZero n)
      else if f == "asciz" then let* a := dlit x in Some (DAsciz a)
      else if f == "byte" then
        match x with
        | TList (n :: ns) =>
            let* n' := dlit n in let* ns' := all_some dlit ns in Some (DByte n' ns')
        | _ => None
        end
      else if f == "ascii" then
        match x with
        | TList cs => let* cs' := all_some dbyte cs in Some (DAscii cs')
        | _ => None
        end
      else None
  | TApp f [x; y] =>
      if f == "type" then let* s := dlit x in let* k := dlit y in Some (DType s k)
      else if f == "size" then let* s := dlit x in let* n := dlit y in Some (DSizeOf s n)
      else if f == "set" then let* s := dlit x in let* e := dexpr y in Some (DSet s e)
      else None
  | _ => None
  end.

Definition dfixed (t : term) : option fixed :=
  let* a := dname t in
  if a == "cpuid" then Some Cpuid
  else if a == "xgetbv" then Some Xgetbv
  else if a == "rdtsc" then Some Rdtsc
  else if a == "rdtscp" then Some Rdtscp
  else if a == "lfence" then Some Lfence
  else if a == "sfence" then Some Sfence
  else if a == "pause" then Some Pause
  else None.

(** The instruction `ins(Op, Suffix, Operands)`, if [t] is one. *)
Definition dins (t : term) : option line :=
  match t with
  | TApp f [op; suffix; TList os] =>
      if f == "ins" then
        let* op' := dlit op in
        let* s := dname suffix in
        let* os' := all_some doperand os in
        Some (Ins (lit_text op') (if s == "none" then None else Some s) os')
      else None
  | _ => None
  end.

(** A line. The cases are disjoint: no directive is named `label`,
    `asm_fixed` or `ins`. *)
Definition dline (t : term) : option line :=
  match t with
  | TApp f [x] =>
      if f == "label" then let* s := dlit x in Some (Label s)
      else if f == "asm_fixed" then let* m := dfixed x in Some (Fixed m)
      else let* d := ddirective t in Some (Dir d)
  | TApp f [_; _; _] => dins t
  | _ => let* d := ddirective t in Some (Dir d)
  end.

Example decode_mov :
  dline (TApp "ins" [TAtom "mov"; TAtom "q";
                     TList [TApp "mem" [TInt (-8); TAtom "rbp"]; TApp "reg" [TAtom "rax"]]])
  = Some (Ins "mov" (Some "q") [OMem (LInt (-8)) "rbp"; OReg "rax"]).
Proof. reflexivity. Qed.
