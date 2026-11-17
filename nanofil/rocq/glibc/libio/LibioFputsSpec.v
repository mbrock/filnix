(** GNU Hello prints its version text and its bug-report address with
    `c: fputs`, which writes a string to a stream. The proofs of those
    callers need a contract for the call before anyone proves glibc's
    code against it. This file states that contract by itself, so a
    caller can assume it now and a later proof can discharge it. That
    proof will build on [wp_glibc__IO_fputs] in LibioFputs.v. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileIdle WordString.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** A call of `c: fputs` is described by the seven values below. *)
Record fputs_in : Type := FputsIn {
  fi_vb : Z;          (* the stream jump tables, `c: __io_vtables` *)
  fi_p : ptr;         (* the string *)
  fi_dq : dfrac;      (* the caller's share of the string *)
  fi_s : list Z;      (* the string's bytes, without the terminator *)
  fi_fp : ptr;        (* the stream *)
  fi_fd : Z;          (* the stream's descriptor *)
  fi_eb : Z           (* errno *)
}.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## The contract

    The contract takes an idle stream and gives one back. The caller
    also lends the string and errno for the length of the call. *)

(** `c: fputs` reads the jump tables to find the stream's functions,
    and it reads `c: __libc_single_threaded` to pick the lock macros'
    single-thread path. Both are read-only, so the caller keeps them
    across the call. *)
Definition fputs_ro (vb : Z) : iProp Σ :=
  ∃ vreg sb sreg, vtables_ro ge vb vreg ∗ single_ro ge sb sreg.

#[global] Instance fputs_ro_persistent vb : Persistent (fputs_ro vb).
Proof using Type. unfold fputs_ro. apply _. Qed.

(** The call `c: fputs (s, fp)` writes the string s to the stream fp.
    A full buffer makes it write to the stream's descriptor, so that
    descriptor must be open. A failed write sets errno, so the caller
    lends errno too. The call returns 1 when it wrote the whole string
    and `c: EOF` otherwise. Afterwards the stream is idle again. *)
Definition fputs_spec : fspec Σ :=
  FSpec fputs_in
    (fun x => [WPtr (fi_p x); WPtr (fi_fp x)])
    (fun x =>
       ⌜ow_errno w0 = Some (mkPtr (fi_eb x) (Obj (fi_eb x))) /\ In (fi_fd x) (ow_fds w0)⌝ ∗
       word_string (fi_dq x) (fi_p x) (fi_s x) ∗
       file_idle (fi_vb x) (ow_self w0) (fi_fp x) (fi_fd x) ∗
       errno_any (fi_eb x) ∗ fputs_ro (fi_vb x))%I
    (fun x o =>
       ∃ r, ⌜o = Ret (WInt r) /\ (r = 1 \/ r = 2 ^ 32 - 1)⌝ ∗
       word_string (fi_dq x) (fi_p x) (fi_s x) ∗
       file_idle (fi_vb x) (ow_self w0) (fi_fp x) (fi_fd x) ∗
       errno_any (fi_eb x))%I.

End spec.
