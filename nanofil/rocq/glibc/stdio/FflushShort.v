(** Flushing an empty in-object short buffer acquires the stream lock,
    validates its narrow vtable and calls the actual sync function.
    The call resets the offset and releases the lock without inspecting
    the descriptor or errno. Pending output and unread input are excluded. *)
From Glibc Require Import Unit_libio_fileops_os Unit_libio_iofflush_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FileSyncShort FflushAcquire FflushUnlock Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section flush.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hsync : ge_fn ge "_IO_new_file_sync" Unit_libio_fileops_os.fn__IO_new_file_sync).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The sync slot is supplied separately from the existing vtable resource.
    Cancellation, descriptor and errno ownership may remain in the frame.
    The mode is not read on this route, but this endpoint requires the
    actual narrow mode rather than claiming support for a wide stream. *)
Lemma wp_fflush_short_empty fr fb freg fl off md lb lbreg sb sreg vb vreg (E : iProp Σ) Φ :
  call_frame Unit_libio_iofflush_os.fn___GI__IO_fflush [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> Z.land fl 256 = 0 -> ptr_addr (ow_self w0) <> 0 ->
  md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") -∗
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  short_sync_fields fb off -∗ int_cell fb 192 md -∗
  pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ E -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗ short_sync_fields fb (2 ^ 64 - 1) -∗ int_cell fb 192 md -∗
    pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗
    pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ E -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hregion Huser Hbackup Hself Hmd.
  iIntros "#Hvt #Hslot #Hs Hl Hfl Hfields Hmd Hvtp Hlp Hlk HE HK".
  iApply (wp_fflush_acquire Hreg Hext with "Hs Hl Hfl Hlp Hlk"); try close_side; try assumption.
  iIntros (e [Hv0 Hc0]) "Hl Hfl Hlp Hlk".
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_sync")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hsync). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true.
  step. step. check_read_dq "Hvl'" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hslot Hfc");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hsync) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hsync) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hsync) | apply (ge_fn_check _ _ _ Hsync) | vx |
    apply (ge_fn_find _ _ _ Hsync) | reflexivity | reflexivity |]. iNext.
  iApply (wp_file_sync_short_empty with "Hl Hfl Hfields HE"); try close_side.
  iNext. iIntros "Hl Hfl Hfields HE". resume.
  branch_as true. step. step.
  iApply (wp_fflush_unlock _ _ _ _ _ _ _ _ _ _
    (short_sync_fields fb (2 ^ 64 - 1) ∗ int_cell fb 192 md ∗
     pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) ∗ E)%I
    with "Hs Hl Hfl Hlp Hlk [$Hfields $Hmd $Hvtp $HE]"); try close_side.
  { left. auto. }
  iNext. iIntros "Hl Hfl Hlp Hlk (Hfields & Hmd & Hvtp & HE)".
  iApply ("HK" with "Hl Hfl Hfields Hmd Hvtp Hlp Hlk HE").
Qed.
End flush.
