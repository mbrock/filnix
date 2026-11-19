(** Closing a wide stream drops both of its buffers but leaves its wide
    jump table installed. When error reporting later flushes stdout, the
    flush therefore calls the wide sync function, `c: _IO_wfile_sync`,
    rather than the narrow one that [FileSyncClosed](FileSyncClosed.v)
    covers. This module proves that call on the closed stream.

    The wide sync function compares the wide write pointer with the wide
    write base, and the wide read pointer with the wide read end. After
    the close all of these are null, so it neither flushes nor converts
    a pending read position. It resets the offset and returns zero
    without using the descriptor, errno, cancellation state or any
    external callee. *)
From Glibc Require Import Unit_libio_wfileops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps LibioWIdle Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Section sync.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation objp b := (mkPtr b (Obj b)).

(** A wide data object without a wide buffer has all eleven of its
    pointers null. The proof below reads four of them, so it needs the
    pointer list in that form. *)
Lemma wbuf_none_ptrs wd ps : wbuf_ptrs_ok wd WbNone ps -> ps = replicate 11 null.
Proof using Type.
  intros (_ & Hd & Ht). rewrite -(take_drop 8 ps) Ht Hd. reflexivity.
Qed.

(** The rule reads the stream's wide data pointer and, through it, the
    wide write and read cursors, which all hold null. It writes only the
    offset field. The caller keeps every other resource in E, so a flush
    that holds the stream's lock can call it. *)
Lemma wp_wfile_sync_closed fr fb freg off vb tw tm wd (E : iProp Σ) Φ :
  call_frame Unit_libio_wfileops_os.fn___GI__IO_wfile_sync [WPtr (objp fb)] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 168 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  live fb freg -∗ pcell fb off_wide (objp wd) -∗ icell fb 144 off -∗
  wide_data vb tw tm wd WbNone -∗ E -∗
  ▷ (live fb freg -∗ pcell fb off_wide (objp wd) -∗ icell fb 144 (2 ^ 64 - 1) -∗
    wide_data vb tw tm wd WbNone -∗ E -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hreg.
  iIntros "Hl Hwp Hoff Hwd HE HK".
  iDestruct "Hwd" as (wreg ps ib ie ob oe ifl icnt ofl ocnt sb scs) "(%Hw & Hw & Hps & Hrest)".
  pose proof Hw as (Hwd0 & Hwal & Hwend & Hwreg & Hptrs & _).
  pose proof (wbuf_none_ptrs _ _ Hptrs) as ->.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & Ps)".
  unfold woff_ptr; cbn [Z.of_nat Pos.of_succ_nat Z.mul].
  cbn in Hfr. injection Hfr as <-. unfold off_wide.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hw"). iIntros ([Hw0 Hw48]) "Hw".
  (* The wide write pointer and write base are both null, so no flush. *)
  step. step. check "Hl". load "Hl" "Hwp" "Hw". step. check "Hw". load_null "Hw" "P4".
  load "Hl" "Hwp" "Hw". step. check "Hw". load_null "Hw" "P3". step. step. step. branch_as true.
  (* The wide read pointer equals the read end, so no seek. *)
  step. step. check "Hl". load "Hl" "Hwp" "Hw". check "Hw". load_null "Hw" "P0".
  load "Hl" "Hwp" "Hw". step. check "Hw". load_null "Hw" "P1".
  step. step. step. step. step. branch_as true.
  (* The result is zero, so the offset becomes unknown. *)
  step. step. branch_as false. step. step. check "Hl". store_long "Hl" "Hoff". step. step.
  iApply wp_ret; [reflexivity | vx |]. iNext.
  change (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1).
  change ((0 mod 2 ^ 32) mod 2 ^ 32) with 0.
  iApply ("HK" with "Hl Hwp Hoff [-HE] HE").
  iExists wreg, (replicate 11 null), ib, ie, ob, oe, ifl, icnt, ofl, ocnt, sb. iExists scs.
  iFrame "Hw Hrest". iSplit; [done |]. unfold woff_ptr. cbn [big_opL replicate]. iFrame.
Qed.
End sync.
