(** When GNU Hello reports an error, glibc's `c: error` flushes stdout
    before it prints the report and flushes stderr after it. The proof
    of that call needs a contract for `c: fflush` before anyone proves
    glibc's code against it. This file states that contract by itself,
    so a caller can assume it now and a later proof can discharge it.
    It shares its read-only part with the contract of `c: fputs` in
    [LibioFputsSpec](LibioFputsSpec.v). *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileIdle LibioFputsSpec.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** A call of `c: fflush` is described by the four values below. *)
Record fflush_in : Type := FflushIn {
  ff_vb : Z;          (* the stream jump tables, `c: __io_vtables` *)
  ff_fp : ptr;        (* the stream *)
  ff_fd : Z;          (* the stream's descriptor *)
  ff_eb : Z           (* errno *)
}.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## The contract

    The call `c: fflush (fp)` writes any output that waits in the
    buffer of the stream fp to its descriptor, so that descriptor must
    be open. A failed write sets errno, so the caller lends errno too.
    Flushing never allocates a buffer, so the contract does not ask for
    the allocator. The call reaches the stream's sync function through
    the jump table's sync slot, which [fputs_ro] covers. The call
    returns 0 when it wrote everything and
    `c: EOF` otherwise; the callers in Hello ignore the result.
    Afterwards the stream is idle again on the same descriptor. *)
Definition fflush_spec : fspec Σ :=
  FSpec fflush_in
    (fun x => [WPtr (ff_fp x)])
    (fun x =>
       ⌜ow_errno w0 = Some (mkPtr (ff_eb x) (Obj (ff_eb x))) /\ In (ff_fd x) (ow_fds w0)⌝ ∗
       file_idle (ff_vb x) (ow_self w0) (ff_fp x) (ff_fd x) ∗
       errno_any (ff_eb x) ∗ fputs_ro (ff_vb x))%I
    (fun x o =>
       ∃ r, ⌜o = Ret (WInt r) /\ (r = 0 \/ r = 2 ^ 32 - 1)⌝ ∗
       file_idle (ff_vb x) (ow_self w0) (ff_fp x) (ff_fd x) ∗
       errno_any (ff_eb x))%I.

End spec.
