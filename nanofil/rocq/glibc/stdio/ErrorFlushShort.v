(** After printing its final newline, error flushes stderr before returning.
    This proof handles a stream whose read and write pointers all point to
    its own short buffer. The formatter must still prove that these pointers
    are equal; printing a newline does not prove that stderr has no pending
    output. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Semantics Run Pieces Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FflushCode FileSyncCode FileSyncShort FflushShort ErrorNewline.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section adapter.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Flushing also needs permission to read the buffer pointers and vtable.
    The formatter must return those permissions alongside the flags, mode
    and lock. Both calls use the same FILE lifetime. *)
Definition error_short_flush_resources fb off vb vreg sb sreg : iProp Σ :=
  short_sync_fields fb off ∗ pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) ∗
  vtables_ro ge vb vreg ∗
  pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") ∗ single_ro ge sb sreg.

(** The original formatting result and actual mode remain in the returned
    state. The flush returns zero and changes only the cached offset;
    arbitrary errno, descriptor and cancellation resources stay framed. *)
Lemma wp_error_flush_short (Hreg : holds_os registry) (Hext : sys_external ge)
    (Hsync : ge_fn ge "_IO_new_file_sync" glibc__IO_new_file_sync)
    fr fb freg fl off lb lbreg nn nr vb vreg sb sreg (E : iProp Σ) :
  call_frame glibc__IO_fflush [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> Z.land fl 256 = 0 -> ptr_addr (ow_self w0) <> 0 ->
  live fb freg -∗ error_newline_done fb fl lb lbreg nn nr
    (fun _ md => ⌜md = 0 \/ md = 2 ^ 32 - 1⌝ ∗ error_short_flush_resources fb off vb vreg sb sreg ∗ E)%I -∗
  WP (ERun fr : gexpr) {{ v, ∃ k, ⌜v = Ret (WInt k) /\ k = 0⌝ ∗ live fb freg ∗
    error_newline_done fb fl lb lbreg nn nr
      (fun _ md => ⌜md = 0 \/ md = 2 ^ 32 - 1⌝ ∗
        error_short_flush_resources fb (2 ^ 64 - 1) vb vreg sb sreg ∗ E)%I }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hregion Huser Hbackup Hself.
  iIntros "Hl Hdone". iDestruct "Hdone" as (r md) "[(Hfl & Hlp & Hlk & Hmd & Hfmt & Hbytes) [%Hnarrow [HR HE]]]".
  iDestruct "HR" as "(Hfields & Hvtp & #Hvt & #Hslot & #Hs)".
  iApply (wp_fflush_short_empty Hreg Hext Hsync fr fb freg fl off md lb lbreg sb sreg vb vreg
    (live_capq DfracDiscarded (Ro nn) nr ∗ bytesq DfracDiscarded nn 0 [10;0] ∗ E)%I
    with "Hvt Hslot Hs Hl Hfl Hfields Hmd Hvtp Hlp Hlk [$Hfmt $Hbytes $HE]"); try assumption.
  iNext. iIntros "Hl Hfl Hfields Hmd Hvtp Hlp Hlk (Hfmt & Hbytes & HE)".
  iExists 0. iSplit; [done |]. iFrame "Hl". iExists r, md.
  iSplitL "Hfl Hlp Hlk Hmd Hfmt Hbytes"; [unfold error_newline_fields; iFrame |].
  iSplit; [done |]. unfold error_short_flush_resources. iFrame. iFrame "Hvt Hslot Hs".
Qed.
End adapter.
