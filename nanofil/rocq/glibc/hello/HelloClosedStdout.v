(** Closing stdout frees its heap buffer, but not its static FILE object.
    This module records the part of that object needed to flush it again
    during error reporting. The ownership contains one FILE lifetime and
    one free lock, without descriptor ownership or an open-stream claim.

    The flush rule does not read cancellation state. A caller that disabled
    cancellation keeps its flag and saved old value separately; this rule
    does not recreate the enabled cleanup invariant. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  LibioCloseItEnd FflushCode FileSyncCode FflushClosed Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

(** Fclose clears the linked bit after setting the closed flags. The result
    does not depend on the flags left by a successful or failed write. *)
Lemma stdout_closed_flags fl : Z.land (closed_flags fl) 4294967167 = 4222428172.
Proof.
  unfold closed_flags. rewrite Z.land_lor_distr_l -Z.land_assoc.
  change (Z.lor (Z.land fl 0) 4222428172 = 4222428172).
  rewrite Z.land_0_r. reflexivity.
Qed.

Section retained.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Flushing the closed object reads these fields and temporarily takes its
    lock. The lifetime stays separate because loading the stdout pointer
    and flushing it must share the same ownership. *)
Definition closed_stdout_fields fb vb lb lbreg : iProp Σ :=
  int_cell fb 0 4222428172 ∗ pcell fb 8 null ∗ pcell fb 16 null ∗
  pcell fb 32 null ∗ pcell fb 40 null ∗ icell fb 144 (2 ^ 64 - 1) ∗
  pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) ∗
  pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null.
Definition closed_stdout fb freg vb lb lbreg : iProp Σ :=
  live fb freg ∗ closed_stdout_fields fb vb lb lbreg.

(** The retained fields supply ErrorEntry's flush contract. The caller lends
    the separate sync slot and links it to the actual checked function.
    This rule does not implement the rest of error reporting. *)
Lemma wp_closed_stdout_fflush (Hreg : holds_os registry) (Hext : sys_external ge)
    (Hsync : ge_fn ge "_IO_new_file_sync" glibc__IO_new_file_sync)
    fr fb freg vb lb lbreg sb sreg vreg (E : iProp Σ) :
  call_frame glibc__IO_fflush [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ptr_addr (ow_self w0) <> 0 ->
  vtables_ro ge vb vreg -∗ pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") -∗
  single_ro ge sb sreg -∗ live fb freg -∗ (closed_stdout_fields fb vb lb lbreg ∗ E) -∗
  WP (ERun fr : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
    live fb freg ∗ (closed_stdout_fields fb vb lb lbreg ∗ E) }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hregion Hself.
  iIntros "#Hvt #Hslot #Hs Hl ((Hfl & H8 & H16 & H32 & H40 & Hoff & Hvtp & Hlp & Hlk) & HE)".
  iApply (wp_fflush_closed Hreg Hext Hsync with "Hvt Hslot Hs Hl Hfl H8 H16 H32 H40 Hoff Hvtp Hlp Hlk HE");
    try close_side; try assumption; try reflexivity.
  iNext. iIntros "Hl Hfl H8 H16 H32 H40 Hoff Hvtp Hlp Hlk HE".
  iExists 0. iSplit; [done |]. unfold closed_stdout_fields. iFrame.
Qed.
End retained.
