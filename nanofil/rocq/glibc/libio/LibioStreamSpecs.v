(** Buffered output calls borrow source bytes and return the stream's new
    buffer state. These contracts use the stream invariants without importing
    their execution proofs, so callers can share the same named contract. *)

From Glibc Require Import Unit_libio_fileops_os.
From Glibc Require Import GlibcProgram GlibcSpec FileInv LibioLogic
  LibioDefaultXsputnBuf.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap ExternalCalls Runtime Logic MemLogic.
Import FileInv.ML Fix.LG0 Fix.LG0.L ListNotations ProgramAbbreviations.
Open Scope Z_scope.

Section contracts.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Generic string output returns its byte count and preserves the borrowed source.
    A nonempty request leaves a buffer, even when output fails. *)
Definition default_xsputn_spec : fspec Σ :=
  FSpec ((Z -> option (Z * Z) -> iProp Σ) * Z * region * Z * region *
      option (Z * Z) * ptr * ptr * dfrac * Z * region * Z * cap * list Z)
    (fun '(_, fb, _, _, _, _, _, _, _, b, _, so, c, ys) =>
      [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + so) c); WInt (Z.of_nat (length ys))])
    (fun '(os, fb, freg, vb, vreg, nb, wp, we, dq, b, reg, so, c, ys) =>
      ⌜overflow_spec w0 registry ge os /\ ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow /\
        0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\
        (c = Obj b \/ c = Ro b) /\ b mod 8 = 0 /\ 0 <= so /\
        b + so + Z.of_nat (length ys) <= r_end reg /\ r_end reg <= 2 ^ 63 /\
        Forall (fun y => 0 <= y < 256) ys⌝ ∗
      vtables_ro ge vb vreg ∗ live fb freg ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗
      wbuf fb nb wp we ∗ os fb nb ∗ liveq dq b reg ∗ bytesq dq b so ys)%I
    (fun '(os, fb, freg, vb, _, _, _, _, dq, b, reg, so, _, ys) v => ∃ k nb wp we,
      ⌜v = Ret (WInt k) /\ 0 <= k <= Z.of_nat (length ys) /\
        (0 < Z.of_nat (length ys) -> nb <> None)⌝ ∗
      live fb freg ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗
      wbuf fb nb wp we ∗ os fb nb ∗ liveq dq b reg ∗ bytesq dq b so ys)%I.

End contracts.
