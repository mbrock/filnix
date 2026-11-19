(** Flushing a closed static stream still acquires its lock and calls its
    vtable's sync function. The cleared read and write pointers let that
    function return zero without touching the closed descriptor. This module
    composes those actual instructions, including the final unlock.

    Hello can report an error after closing stdout, but its current proof
    forgets the stream's memory when it closes it. Applying this rule will
    require keeping that memory and the lock available. The proof also needs
    the sync pointer stored in the vtable. The existing vtables_ro assertion
    omits that slot, so the caller supplies it separately. *)
From Glibc Require Import Unit_libio_fileops_os Unit_libio_iofflush_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FileSyncClosed FflushAcquire FflushUnlock Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section closed.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hsync : ge_fn ge "_IO_new_file_sync" Unit_libio_fileops_os.fn__IO_new_file_sync).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A closed stream still points at a jump table, and fflush calls that
    table's sync function. A closed narrow stream points at the narrow
    file table, and a closed wide stream points at the wide one. This
    rule covers both: the caller names the table offset and the function
    in its sync slot. The caller also proves what that function does on
    the closed stream. The rule then unlocks the stream and returns
    zero. *)
Lemma wp_fflush_closed_dispatch_with vo sn f fr e fb freg fl lb lbreg sb sreg vb vreg (S T : iProp Σ) Φ :
  ge_fn ge sn f -> fn_params f = fn_params Unit_libio_fileops_os.fn__IO_new_file_sync ->
  fn_ret f = fn_ret Unit_libio_fileops_os.fn__IO_new_file_sync -> variadic_func f = false ->
  call_frame f [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> vo = vt_file \/ vo = vt_wfile ->
  vtables_ro ge vb vreg -∗ pcellq DfracDiscarded vb (vo + 96) (sym_ptr ge sn) -∗
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 216 (mkPtr (vb + vo) (Ro vb)) -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗ S -∗
  (∀ Ψ, live fb freg -∗ int_cell fb 0 fl -∗ S -∗
    ▷ (live fb freg -∗ int_cell fb 0 fl -∗ T -∗ Ψ (Ret (WInt 0))) -∗ WP (ERun fr : gexpr) {{ Ψ }}) -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 216 (mkPtr (vb + vo) (Ro vb)) -∗
    pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ T -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (mkFrame Unit_libio_iofflush_os.fn___GI__IO_fflush e [] None
    (Enter (TAtom "L22") (Some (TAtom "L32")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hf Hfp Hfr Hvar Hcf Hv0 Hc0 Hfb Hal Hend Hregion Huser Hvo.
  iIntros "#Hvt #Hslot #Hs Hl Hfl Hvtp Hlp Hlk HS Hsp HK".
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge sn)) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hf). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; destruct Hvo as [-> | ->]; unfold vt_file, vt_wfile; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step.
  assert (Hvr : 0 <= vo /\ vo + 168 <= 2352) by (destruct Hvo as [-> | ->]; unfold vt_file, vt_wfile; lia).
  assert (Hv8 : vo mod 8 = 0) by (destruct Hvo as [-> | ->]; reflexivity).
  assert (Hm : (((vb + vo) mod 2 ^ 64 - vb mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64 = vo) by (Z.div_mod_to_equations; lia).
  assert (Hlt : (2352 mod 2 ^ 64 <=? vo) = false) by (apply Z.leb_gt; change (2352 mod 2 ^ 64) with 2352; lia).
  iStartProof. eapply step_wand; [eapply wp_branch; inst; vx |].
  rewrite Hm Hlt. change ((0 mod 2 ^ 32 =? 0)) with true. cbn [edge_label].
  step. step. check_read_dq "Hvl'" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hslot Hfc");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hf) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hf) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hf) | apply (ge_fn_check _ _ _ Hf) | vx |
    apply (ge_fn_find _ _ _ Hf) | unfold indirect_call_conv; rewrite Hfp Hfr; reflexivity |
    rewrite Hvar; exact Hcf |]. iNext.
  iApply ("Hsp" with "Hl Hfl HS").
  iNext. iIntros "Hl Hfl HS". resume.
  branch_as true. step. step.
  iApply (wp_fflush_unlock _ _ _ _ _ _ _ _ _ _
    (pcell fb 216 (mkPtr (vb + vo) (Ro vb)) ∗ T)%I
    with "Hs Hl Hfl Hlp Hlk [Hvtp HS]"); try close_side.
  { left. auto. }
  { iFrame. }
  iNext. iIntros "Hl Hfl Hlp Hlk (Hvtp & HS)".
  iApply ("HK" with "Hl Hfl Hvtp Hlp Hlk HS").
Qed.

(** On a closed narrow stream the sync slot holds the narrow file sync
    function. Its closed-state rule needs no descriptor or errno resource
    and preserves arbitrary caller resources through the unlock. *)
Lemma wp_fflush_closed_dispatch e fb freg fl off lb lbreg sb sreg vb vreg (E : iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> Z.land fl 256 = 0 ->
  vtables_ro ge vb vreg -∗ pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") -∗
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
  icell fb 144 off -∗ pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗ E -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗
    pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
    icell fb 144 (2 ^ 64 - 1) -∗ pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗
    pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ E -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (mkFrame Unit_libio_iofflush_os.fn___GI__IO_fflush e [] None
    (Enter (TAtom "L22") (Some (TAtom "L32")))) : gexpr) {{ Φ }}.
Proof using Hsync.
  intros Hv0 Hc0 Hfb Hal Hend Hregion Huser Hbackup.
  iIntros "#Hvt #Hslot #Hs Hl Hfl H8 H16 H32 H40 Hoff Hvtp Hlp Hlk HE HK".
  iApply (wp_fflush_closed_dispatch_with vt_file _ _ _ _ _ _ _ _ _ _ _ _ _
    (pcell fb 8 null ∗ pcell fb 16 null ∗ pcell fb 32 null ∗ pcell fb 40 null ∗ icell fb 144 off ∗ E)%I
    (pcell fb 8 null ∗ pcell fb 16 null ∗ pcell fb 32 null ∗ pcell fb 40 null ∗
     icell fb 144 (2 ^ 64 - 1) ∗ E)%I
    with "Hvt Hslot Hs Hl Hfl Hvtp Hlp Hlk [$H8 $H16 $H32 $H40 $Hoff $HE] [] [HK]");
    try eassumption; try reflexivity; [by left | |].
  - iIntros (Ψ) "Hl Hfl (H8 & H16 & H32 & H40 & Hoff & HE) HK".
    iApply (wp_file_sync_closed with "Hl Hfl H8 H16 H32 H40 Hoff HE"); try close_side.
    iNext. iIntros "Hl Hfl H8 H16 H32 H40 Hoff HE". iApply ("HK" with "Hl Hfl [$]").
  - iNext. iIntros "Hl Hfl Hvtp Hlp Hlk (H8 & H16 & H32 & H40 & Hoff & HE)".
    iApply ("HK" with "Hl Hfl H8 H16 H32 H40 Hoff Hvtp Hlp Hlk HE").
Qed.

(** This endpoint runs the entire nonnull fflush body. It admits a disabled
    cancellation flag in E, without reconstructing enabled cleanup state.
    Retaining these exact resources after fclose remains a separate task. *)
Lemma wp_fflush_closed fr fb freg fl off lb lbreg sb sreg vb vreg (E : iProp Σ) Φ :
  call_frame Unit_libio_iofflush_os.fn___GI__IO_fflush [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> Z.land fl 256 = 0 -> ptr_addr (ow_self w0) <> 0 ->
  vtables_ro ge vb vreg -∗ pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") -∗
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
  icell fb 144 off -∗ pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ E -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗
    pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
    icell fb 144 (2 ^ 64 - 1) -∗ pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗
    pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ E -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hregion Huser Hbackup Hself.
  iIntros "#Hvt #Hslot #Hs Hl Hfl H8 H16 H32 H40 Hoff Hvtp Hlp Hlk HE HK".
  iApply (wp_fflush_acquire Hreg Hext with "Hs Hl Hfl Hlp Hlk"); try close_side; try assumption.
  iIntros (e [Hv0 Hc0]) "Hl Hfl Hlp Hlk".
  iApply (wp_fflush_closed_dispatch with "Hvt Hslot Hs Hl Hfl H8 H16 H32 H40 Hoff Hvtp Hlp Hlk HE HK");
    try close_side.
Qed.
(** The whole nonnull fflush body on a closed stream of either kind takes
    the same lock and dispatch steps. A caller supplies the table offset,
    the sync slot share and the sync function's rule, as in
    [wp_fflush_closed_dispatch_with]. *)
Lemma wp_fflush_closed_with vo sn f sfr fr fb freg fl lb lbreg sb sreg vb vreg (S T : iProp Σ) Φ :
  ge_fn ge sn f -> fn_params f = fn_params Unit_libio_fileops_os.fn__IO_new_file_sync ->
  fn_ret f = fn_ret Unit_libio_fileops_os.fn__IO_new_file_sync -> variadic_func f = false ->
  call_frame f [WPtr (mkPtr fb (Obj fb))] = Some sfr ->
  call_frame Unit_libio_iofflush_os.fn___GI__IO_fflush [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> ptr_addr (ow_self w0) <> 0 -> vo = vt_file \/ vo = vt_wfile ->
  vtables_ro ge vb vreg -∗ pcellq DfracDiscarded vb (vo + 96) (sym_ptr ge sn) -∗
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 216 (mkPtr (vb + vo) (Ro vb)) -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ S -∗
  (∀ Ψ, live fb freg -∗ int_cell fb 0 fl -∗ S -∗
    ▷ (live fb freg -∗ int_cell fb 0 fl -∗ T -∗ Ψ (Ret (WInt 0))) -∗ WP (ERun sfr : gexpr) {{ Ψ }}) -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 216 (mkPtr (vb + vo) (Ro vb)) -∗
    pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ T -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Hreg Hext.
  intros Hf Hfp Hfr Hvar Hcf Hfr' Hfb Hal Hend Hregion Huser Hself Hvo.
  iIntros "#Hvt #Hslot #Hs Hl Hfl Hvtp Hlp Hlk HS Hsp HK".
  iApply (wp_fflush_acquire Hreg Hext with "Hs Hl Hfl Hlp Hlk"); try close_side; try assumption.
  iIntros (e [Hv0 Hc0]) "Hl Hfl Hlp Hlk".
  iApply (wp_fflush_closed_dispatch_with with "Hvt Hslot Hs Hl Hfl Hvtp Hlp Hlk HS Hsp HK");
    eassumption.
Qed.
End closed.
