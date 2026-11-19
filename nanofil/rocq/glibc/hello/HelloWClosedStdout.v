(** Hello makes stdout wide before it writes, so closing stdout at exit
    runs the wide close path. That path frees both buffers but leaves
    the wide jump table installed. If the close fails, error reporting
    flushes stdout again, and that flush calls the wide sync function
    rather than the narrow one. This module states the part of the
    closed wide stream that the flush reads and proves the flush on it.

    The flush needs the stream's memory to stay alive, so the caller
    keeps its lifetime as a separate resource. The same lifetime also
    lets the caller load the stdout pointer before the flush. The flush
    reads no descriptor, narrow cursor, errno or cancellation state.
    [HelloClosedStdout](HelloClosedStdout.v) proves the same flush for a
    narrow stream. *)
From Glibc Require Import Unit_libio_iofflush_os Unit_libio_wfileops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  LibioWIdle WFileSyncClosed FflushClosed Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section retained.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation objp b := (mkPtr b (Obj b)).

(** These are the fields of the closed wide stdout that the flush reads
    or writes, with the free lock it takes for the call. The flags are
    the value fclose leaves after it unlinks the stream. The wide data
    has no wide buffer, which is what the wide close leaves. *)
Definition closed_wide_fields fb vb lb lbreg (tw tm : ptr) wd : iProp Σ :=
  int_cell fb 0 4222428172 ∗ pcell fb 136 (objp lb) ∗ lock_state lb lbreg 0 0 null ∗
  pcell fb 216 (mkPtr (vb + vt_wfile) (Ro vb)) ∗ icell fb 144 (2 ^ 64 - 1) ∗
  pcell fb off_wide (objp wd) ∗ wide_data vb tw tm wd WbNone.

(** The closed wide stdout is its lifetime together with these fields. *)
Definition closed_wide fb freg vb lb lbreg (tw tm : ptr) wd : iProp Σ :=
  live fb freg ∗ closed_wide_fields fb vb lb lbreg tw tm wd.

(** The flush takes the lock, calls the wide sync slot through
    [wp_fflush_closed_with], and runs the wide sync body of
    [wp_wfile_sync_closed]. It returns the stream's lifetime, its fields
    and the caller's other resources unchanged. *)
Lemma wp_closed_wide_fflush (Hreg : holds_os registry) (Hext : sys_external ge)
    (Hsync : ge_fn ge "__GI__IO_wfile_sync" Unit_libio_wfileops_os.fn___GI__IO_wfile_sync)
    fr fb freg vb lb lbreg tw tm wd sb sreg vreg (E : iProp Σ) :
  call_frame Unit_libio_iofflush_os.fn___GI__IO_fflush [WPtr (objp fb)] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ptr_addr (ow_self w0) <> 0 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ single_ro ge sb sreg -∗ live fb freg -∗
  (closed_wide_fields fb vb lb lbreg tw tm wd ∗ E) -∗
  WP (ERun fr : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
    live fb freg ∗ (closed_wide_fields fb vb lb lbreg tw tm wd ∗ E) }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hregion Hself.
  iIntros "#Hvt #Hwv #Hs Hl ((Hfl & Hlp & Hlk & Hvtp & Hoff & Hwp & Hwd) & HE)".
  iPoseProof (wvtables_slot _ _ slot_sync "__GI__IO_wfile_sync" with "Hwv") as "Hslot";
    [cbn; tauto |].
  iApply (wp_fflush_closed_with Hreg Hext vt_wfile _ _ _ _ _ _ _ _ _ _ _ _ _
    (pcell fb off_wide (objp wd) ∗ icell fb 144 (2 ^ 64 - 1) ∗ wide_data vb tw tm wd WbNone ∗ E)%I
    (pcell fb off_wide (objp wd) ∗ icell fb 144 (2 ^ 64 - 1) ∗ wide_data vb tw tm wd WbNone ∗ E)%I
    with "Hvt Hslot Hs Hl Hfl Hvtp Hlp Hlk [$Hwp $Hoff $Hwd $HE] [] [-]");
    try exact Hsync; try reflexivity; try assumption; try lia.
  - iIntros (Ψ) "Hl Hfl (Hwp & Hoff & Hwd & HE) HK".
    iApply (wp_wfile_sync_closed with "Hl Hwp Hoff Hwd [Hfl HE]"); try close_side; try lia.
    { iCombine "Hfl HE" as "H". iExact "H". }
    iNext. iIntros "Hl Hwp Hoff Hwd (Hfl & HE)". iApply ("HK" with "Hl Hfl [$]").
  - iNext. iIntros "Hl Hfl Hvtp Hlp Hlk (Hwp & Hoff & Hwd & HE)".
    iExists 0. iSplit; [done |]. unfold closed_wide_fields. iFrame.
Qed.
End retained.
