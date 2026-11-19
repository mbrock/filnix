(** Error ends its report with a newline and a flush of stderr. It
    then restores the cancellation flag before returning to close_stdout.
    These operations borrow the thread lifetime, errno and stderr from
    the same state that strerror used to translate its message. *)

From Glibc Require Import Unit_io_write_os Unit_libio_fileops_os Unit_libio_iofflush_os Unit_misc_error_os Unit_stdioZ2dcommon_fxprintf_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  Pieces Heap Language Logic MemLogic HelloLeaf.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv FileIdle LibioLogic LibioCloseSteps SysWrappers
  WordString NarrowArgs PrintfSpec LibioFputsSpec LibioFflushSpec LibioFflushIdle LibioCleanupExit
  FxprintfNormalCall
  ErrorEntry ErrorTail HelloErrorOperand HelloVersionLits HelloEmitBug HelloGlibcDebts HelloGlibcLibsT
  HelloImageLayout HelloImageModule HelloImageLoad StartImageEarly HelloStartFacts HelloGetoptDiagTcb
  HelloCloseReportLocale HelloCloseReportPrint Fix.
Import ListNotations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps SysWrappers.
Open Scope Z_scope.

Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
Lemma report_sync_link : ge_fn hge "_IO_new_file_sync" Unit_libio_fileops_os.fn__IO_new_file_sync.
Proof. exists (img_addr "_IO_new_file_sync"). split; [vm_compute; reflexivity|split; [vm_compute; reflexivity|split; vm_compute; congruence]]. Qed.

Section finish.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
#[local] Instance finish_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation fe := (img_a "_IO_2_1_stderr_").
Local Abbreviation St := (file_idle (ho_vb ob) (ow_self w) (ho_err ob) 2).
Local Abbreviation nl := (sym_ptr hge "glibc_error#str.254").
Local Abbreviation gexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Context (Herr : ow_errno w = Some (mkPtr eb (Obj eb))) (Hfd : In 2 (ow_fds w)).
Context `{Hvf : !HasSpec glibc_os_registry (os_wi w) hge (TAtom "__vfprintf_internal")
  (vfprintf_spec (glibc_program := finish_program))}.

(** The image links the sync and write methods used by an open
    stream. Flushing stderr therefore needs no external fflush contract. *)
Local Lemma report_fflush (Hself : ptr_addr (ow_self w) <> 0) :
  HasSpec glibc_os_registry (os_wi w) hge (TAtom "__GI__IO_fflush") (fflush_spec (glibc_program := finish_program)).
Proof using Type.
  assert (Hfw : ge_fn hge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
    by (exists (img_addr "_IO_new_file_write"); split; [vm_compute; reflexivity|split; [vm_compute; reflexivity|split; vm_compute; congruence]]).
  assert (Dw : Defines hge "__GI___write" Unit_io_write_os.fn___GI___libc_write) by (vm_compute; reflexivity).
  assert (Dd : Defines hge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write) by (vm_compute; reflexivity).
  assert (Dff : Defines hge "__GI__IO_fflush" Unit_libio_iofflush_os.fn___GI__IO_fflush) by (vm_compute; reflexivity).
  exact (fflush_has_spec (glibc_program := finish_program) holds_os_glibc (hk_sys _ _ (hello_link_all _ R.free_succeeds))
    report_sync_link Hfw Hself).
Qed.

Lemma wp_report_finish tb tr v tid treg e from k fmt ap cb Φ :
  dtx_tcb_at (glibc_program := finish_program) tb tr -> error_inputs e 0 k fmt ap 0 cb ->
  let G := report_locale w R.free tb tr v tid treg in
  hello_ro hge ob -∗ G -∗ int_cell tb 792 1 -∗ live cb (mkRegion cb (cb+16) Heap Live) -∗ int_cell cb 0 0 -∗
  (G -∗ int_cell tb 792 0 -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None (Enter (TAtom "iw_2.L92") (Some from))) : gexpr) {{ Φ }}.
Proof using Herr Hfd Hvf.
  intros (Hself & Htb & Hta & Hte & Htr) Hin G. change (ow_self w = mkPtr tb (Obj tb)) in Hself.
  unfold off_cancelhandling in Hte. assert (Ht796 : tb+796 <= r_end tr) by lia.
  assert (Hsr : 0 < ptr_addr (ow_self w) < 2^64) by (rewrite Hself; cbn [ptr_addr]; lia).
  destruct (report_fflush ltac:(lia) (FflushIn (ho_vb ob) (ho_err ob) 2 eb)) as (gf & Hgf & [cf Hcf] & Hff).
  iIntros "#Hro HG Hflag Hcl Hsave HK". iDestruct (report_locale_lend with "HG") as "(Ht & He & Herr & W)".
  iPoseProof "Hro" as "(_ & _ & _ & _ & #Hsl & #Hsp & _)".
  iApply (wp_error_tail_lend (glibc_program := finish_program) holds_os_glibc (hk_sys _ _ (hello_link_all _ R.free_succeeds))
    (dqs := DfracDiscarded) tb tr 0 (ho_se ob) (ho_sereg ob) (ho_err ob)
    nl Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf (fxprintf_normal_frame null nl []) gf cf St
    (errno_any eb ∗ hello_ro hge ob)%I (errno_any eb ∗ hello_ro hge ob)%I (errno_any eb)%I True%I
    e from 0 k fmt ap 0 cb with "Ht Hflag Hcl Hsave Hsl Hsp Herr [$He $Hro] [//]");
    [left; reflexivity|exact Hself|exact Htb|exact Hta|exact Ht796|exact Htr|vm_compute; reflexivity|
     vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; discriminate|
     split; vm_compute; congruence|vm_compute; reflexivity|vm_compute; reflexivity|reflexivity|exact Hgf|exact Hcf|
     |iApply (file_idle_lend (glibc_program := finish_program) _ fe 2)| |exact Hin|lia|].
  - iIntros "#Hsl' #Hsp' Herr [He #Hro']".
    iDestruct (version_lit hge ob ("glibc_error#str.254", [10]) with "Hro'") as "#Hnl";
      [cbn [version_lits]; repeat first [left; reflexivity|right]|].
    iApply (wp_report_fx w Herr Hfd nl [10] _ [] with "Hro' Hnl [] Herr He");
      [exact Hsr|reflexivity|reflexivity|apply narrow_fits_all; apply args_literal; constructor|done|].
    iNext. iIntros (n) "Herr He". iExists _. iSplit; [done|]. iSplitR; [iExact "Hsl'"|]. iSplitR; [iExact "Hsp'"|].
    iSplitL "Herr"; [iExact "Herr"|]. iSplitL "He"; [iExact "He"|iExact "Hro'"].
  - iIntros "Herr [He #Hro']". iPoseProof "Hro'" as "(#Hvt & #Hsg & _)".
    iApply (Hff cf with "[Herr He]"); [exact Hcf| |].
    + cbn [fs_pre fflush_spec ff_vb ff_fp ff_fd ff_eb]. iSplit; [done|]. iFrame "Herr He". iExists _,_,_. iFrame "Hvt Hsg".
    + iIntros (r) "(%n & [-> _] & Herr & He)". iExists n. by iFrame.
  - iSplit; last (iIntros (e' Hnz); contradiction).
    iIntros "Ht Hflag _ _ _ _ Herr He _". iApply ("HK" with "[Ht He Herr W] Hflag"). iApply ("W" with "Ht He Herr").
Qed.
End finish.
