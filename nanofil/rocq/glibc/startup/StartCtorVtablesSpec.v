(** The constructor `c: check_stdfiles_vtables` runs before main and
    checks that each of the three standard streams points at glibc's own
    table of stream operations. A stream whose table pointer lies
    elsewhere would make the check fail. The runner of constructors needs
    only what one call does, so this module states that contract, and
    [StartCtorVtables](StartCtorVtables.v) proves it.

    ## What the check reads

    A stream finds its read and write operations through a pointer to a
    table of functions. glibc keeps all such tables in one array, so the
    check only has to see that each pointer lands inside that array. In
    the linked image each stream's pointer, at offset 216, points 336
    bytes into the array. The check writes nothing. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic.
From Glibc Require Import FileInv.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section specs.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** This assertion lets the check read the stream at f and the stream's
    table pointer. The pointer lands 336 bytes into the array of tables
    at vb. *)
Definition vt_ok (dq : dfrac) (f : Z) (freg : region) (vb : Z) : iProp Σ :=
  liveq dq f freg ∗ pcellq dq f 216 (mkPtr (vb + 336) (Ro vb)).

(** A stream object at f is large enough to hold its table pointer, is
    aligned, and lies in the low half of the address space. *)
Definition stream_ok (f : Z) (freg : region) : Prop :=
  0 < f /\ f mod 8 = 0 /\ f + 224 <= r_end freg <= 2 ^ 48.

(** The three streams and the table are the globals that the program
    names `c: _IO_2_1_stdin_`, `c: _IO_2_1_stdout_`,
    `c: _IO_2_1_stderr_` and `c: __io_vtables`. *)
Definition vtables_globals (fi fo fe vb : Z) : Prop :=
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some (mkPtr fi (Obj fi)) /\
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some (mkPtr fo (Obj fo)) /\
  lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some (mkPtr fe (Obj fe)) /\
  lookup (TAtom "__io_vtables") (ge_globals ge) = Some (mkPtr vb (Ro vb)) /\
  0 <= vb < 2 ^ 48.

(** A call of `c: check_stdfiles_vtables()` returns and gives back the
    three streams and the table unchanged. *)
Definition check_vtables_spec : fspec Σ :=
  FSpec (Z * region * Z * region * Z * region * Z * region * dfrac) (fun _ => [])
    (fun '(fi, fireg, fo, foreg, fe, fereg, vb, vreg, dq) =>
       ⌜vtables_globals fi fo fe vb /\ stream_ok fi fireg /\ stream_ok fo foreg /\ stream_ok fe fereg⌝ ∗
       vt_ok dq fi fireg vb ∗ vt_ok dq fo foreg vb ∗ vt_ok dq fe fereg vb ∗ liveq dq vb vreg)%I
    (fun '(fi, fireg, fo, foreg, fe, fereg, vb, vreg, dq) o =>
       ⌜o = RetVoid⌝ ∗ vt_ok dq fi fireg vb ∗ vt_ok dq fo foreg vb ∗ vt_ok dq fe fereg vb ∗ liveq dq vb vreg)%I.

End specs.
