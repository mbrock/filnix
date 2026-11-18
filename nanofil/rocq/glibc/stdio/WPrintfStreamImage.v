(** When Hello's wide formatter fills its staging buffer, the file
    writer copies whole characters to stdout and calls overflow if it
    needs more room. This proof checks the writer, the overflow jump
    and their allocation calls against Hello's executable. It leaves
    the conversion and write of the pending characters to the rule for
    `c: _IO_wdo_write`. *)

From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics ExternalCalls Pieces Heap.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic LibioWIdle LibioReadCode LibioWAllocCode
  HelloGlibcDebts HelloGlibcLibsT HelloImageModule HelloImageLoad HelloImageLayout HiAtexitAlloc
  LibioWOverflowDispatch LibioWOverflowWrite LibioWOverflowAllocate LibioWOverflow LibioWXsputn WPrintfFileFlush.
From Glibc Require LibioCleanupExit.
Open Scope Z_scope.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance stream_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation o := hello_image_objs.
Local Abbreviation vb := (ho_vb o).
Local Abbreviation eb := (ho_eb o).
Local Abbreviation self := (ow_self w).
Local Abbreviation M := (hi_malloc_state DfracDiscarded (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o)).
Local Ltac image_fn n := exists (img_addr n); split; [vm_compute; reflexivity|split; [vm_compute; reflexivity|split; vm_compute; congruence]].

(** The writer borrows both jump tables, the allocator's idle cache
    and errno. Only errno can change. The caller recovers its other
    resources even when the stream reports a short write. *)
Lemma hello_wprintf_xsputn_image (E : iProp Σ) : hello_link hge o ->
  ow_errno w = Some (mkPtr eb (Obj eb)) -> In 1 (ow_fds w) ->
  (E ⊢ vtables_ro hge vb (ho_vreg o) ∗ wvtables_ro hge vb ∗ M ∗ errno_any eb ∗ (errno_any eb -∗ E)) ->
  wdo_pending_spec vb self 1 E -> wprintf_xsputn_call_spec vb self E.
Proof using Type*.
  intros Link Err Fd Loan Write. destruct (hk_frees _ _ Link) as (Free & Zfn & Zg).
  assert (FileStat : ge_fn hge "__GI__IO_file_stat" glibc__IO_file_stat) by image_fn "__GI__IO_file_stat".
  assert (Alloc : ge_fn hge "_IO_wfile_doallocate" glibc__IO_wfile_doallocate) by image_fn "_IO_wfile_doallocate".
  assert (Target : ge_fn hge "__GI__IO_wfile_overflow" wfile_overflow_fn) by image_fn "__GI__IO_wfile_overflow".
  assert (Env : wo_alloc_env vb E DfracDiscarded (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o)).
  { iIntros "HE". iDestruct (Loan with "HE") as "(HV & HW & HM & He & HK)".
    iExists (ho_vreg o), eb. iSplit; [iPureIntro; exact (conj Err Fd)|]. iFrame "HV HW He HM". iIntros "He _". by iApply "HK". }
  assert (Tables : E ⊢ vtables_ro hge vb (ho_vreg o) ∗ wvtables_ro hge vb ∗ E).
  { iIntros "HE". iDestruct (Loan with "HE") as "(HV & HW & _ & He & HK)". iFrame "HV HW". by iApply "HK". }
  assert (FileOv : woverflow_spec vb self E wfile_overflow_fn).
  { refine (@wp_wfile_overflow _ _ stream_program vb self E _ Write _ _ _ LibioCleanupExit.holds_os_glibc (hk_sys _ _ Link) FileStat
      _ _ _ _ (hk_free _ _ Link) Free Zfn Zg (hk_malloc _ _ Link) (hk_malloc2 _ _ Link) _ _ Alloc
      DfracDiscarded _ _ _ _ _ _ (hk_mp _ _ Link) (hk_tc _ _ Link) Env); unfold Defines; vm_compute; reflexivity. }
  pose proof (woverflow_dispatch_spec (glibc_program := stream_program) vb self E (ho_vreg o) Target Tables FileOv) as Overflow.
  refine (@wfile_xsputn_has_spec _ _ stream_program vb self E _ Write eq_refl _ _ _ _ _ _ _ Overflow);
    vm_compute; reflexivity.
Qed.
End image.
