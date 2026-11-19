(** When Hello exits, gnulib's `c: close_stdout` closes stdout and
    stderr, and it reports an error if a close fails. Main's exit path
    asks for a contract that says so. This module proves that contract
    for a narrow stdout. It joins two earlier proofs: one walks the
    callback's code, and the other prints the error report. The
    callback also reads three small globals, which startup leaves in
    the private state, so the contract holds for every private state
    that has the shape startup builds. *)

From Glibc Require Import Unit_io_close_nocancel_os Unit_io_write_os Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_fileops_os.
From Glibc Require Import Unit_libio_genops_os Unit_libio_iofclose_os Unit_misc_error_os Unit_nptl_libcZ2dcleanup_os Unit_posix__exit_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  Pieces Heap Language Logic MemLogic.
From Glibc Require Import HelloBodies.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic SysWrappers
  WordString PrintfSpec LibioCleanupExit ErrorCall HelloGlibcDebts HelloGlibcLibsT
  HelloImageLayout HelloImageModule HelloImageLoad StartImageCpu HelloStartFacts HelloStartHdGetopt
  HelloImageCloseObjs HelloLocaleState LeavesLogic AllocLogic
  HelloCloseStdoutIdle HelloGetoptDiagImage HelloCloseReport Fix.
From Glibc Require LibioFcloseTail LibioFlushBody.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic SysWrappers.
Open Scope Z_scope.

Section call.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance close_call_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation fmt := (hello_sym "closeout#str.55").
Local Abbreviation text := (hello_sym "closeout#str.53").
Local Notation dq := DfracDiscarded.

(** The error report needs a few facts about the running thread. Its
    own object sits at tb, errno is the world's errno, descriptors 1 and
    2 are open, and glibc's formatter keeps its contract. *)
Context (tb : Z) (Herr : ow_errno w = Some (mkPtr eb (Obj eb))) (Hfd1 : In 1 (ow_fds w)) (Hfd2 : In 2 (ow_fds w)).
Context `{Hvf : !HasSpec glibc_os_registry (os_wi w) hge (TAtom "__vfprintf_internal")
  (vfprintf_spec (glibc_program := close_call_program))}.

(** Eight zero bytes without capabilities hold a null pointer. *)
Local Lemma zero_ptr_cell b : bytes b 0 (repeat 0 8%nat) -∗ auxes b 0 (repeat CNone 8%nat) -∗ pcell b 0 null.
Proof using Type.
  assert (E1 : StringLogic.byte_ps b 0 (repeat 0 8%nat) = cell b 0 (ptr_addr null)) by reflexivity.
  assert (E2 : aux_ps b 0 (repeat CNone 8%nat) = (PAux b 0, VAux (ptr_cap null)) :: aux_ps b 1 (repeat CNone 7%nat))
    by reflexivity.
  rewrite /bytes /auxes /pcell E1 E2 (pts_app [_] (aux_ps _ _ _)). iIntros "H [A _]".
  rewrite (pts_app [_] (cell _ _ _)). iFrame.
Qed.

(** Startup leaves gnulib's three close globals as their C
    initializers set them: `c: exit_failure` holds 1, `c: ignore_EPIPE`
    holds false and `c: file_name` holds null. The conversion lock
    beside them is not needed here. *)
Local Lemma close_cells :
  pts hello_close_rest_ps ⊢
    (live (img_a "exit_failure") (img_gd "exit_failure") ∗ int_cell (img_a "exit_failure") 0 1) ∗
    (live (img_a "closeout#ignore_EPIPE") (img_gd "closeout#ignore_EPIPE") ∗ bytes (img_a "closeout#ignore_EPIPE") 0 [0]) ∗
    (live (img_a "closeout#file_name") (img_gd "closeout#file_name") ∗ pcell (img_a "closeout#file_name") 0 null).
Proof using Type.
  rewrite /hello_close_rest_ps !pts_app !obj_ps_own. cbn [fst snd].
  iIntros "((Lx & Bx & _) & (Li & Bi & _) & (Ln & Bn & An) & _)".
  iFrame "Lx Li Bi Ln". iSplitL "Bx"; [iSplit; [iPureIntro; lia | iExact "Bx"]|].
  iApply (zero_ptr_cell with "Bn An").
Qed.

(** The callback closes stdout and stderr, and it leaves stdin open
    for exit's cleanup. If closing stdout fails, the callback prints an
    error and calls `c: _exit`. The report reads the closed stdout, the
    error counter, the program name and the option parser's warning
    state. The proof freezes the report's strings as read-only,
    because nothing after `c: _exit` needs them back. The contract holds for
    any private state priv that holds the warning state and
    [hello_priv_rest]. *)
Lemma hello_close_stdout_narrow (N1 N2 priv : iProp Σ) :
  (priv ⊣⊢ N1 ∗ hello_hd_getopt w R.free tb ∗ (N2 ∗ hello_priv_rest w R.free)) ->
  HelloGlibcDebts.fn_triple w hge (TAtom "close_stdout") []
    (hello_ro hge ob ∗ hello_stdio w hge ob ∗ priv ∗ names ob)%I
    (fun r => ⌜r = RetVoid⌝ ∗ exit_io w hge ob)%I.
Proof using Herr Hfd1 Hfd2 Hvf.
  intros Hpriv. pose proof (hello_link_all R.free R.free_succeeds) as L.
  exists close_stdout_fn. split; [exact (hk_close_stdout _ _ L)|]. split; [eexists; reflexivity|].
  intros f Φ Hf. cbn in Hf. injection Hf as <-.
  iIntros "(#Hro & (Hout & Hse & (Hin & Hinx) & Hio & Htcb & He & Hec) & Hp & Hnames) HK".
  iDestruct (Hpriv with "Hp") as "(_ & Hg & _ & _ & _ & _ & Hrest & Hcro & #Hel)".
  iDestruct (close_cells with "Hrest") as "((Hxl & Hxc) & (Hil & Hib) & (Hnl & Hnp))".
  iDestruct "Hec" as (cb creg n Hc) "[Hcl Hcnt]".
  iPoseProof "Hro" as "(#Hvt & #Hsg & #Hol & #Hop & #Hsl & #Hsp & _)".
  pose proof Hc as (Hn & Hna & Hne & Hnr).
  assert (D0 : Defines hge "__fpending" Unit_libio___fpending_os.fn___fpending) by (vm_compute; reflexivity).
  assert (D1 : Defines hge "ferror" Unit_libio_ferror_os.fn__IO_ferror) by (vm_compute; reflexivity).
  assert (D2 : Defines hge "fclose" Unit_libio_iofclose_os.fn__IO_new_fclose) by (vm_compute; reflexivity).
  assert (D3 : Defines hge "__GI___write" Unit_io_write_os.fn___GI___libc_write) by (vm_compute; reflexivity).
  assert (D4 : Defines hge "free" free_fn) by (vm_compute; reflexivity).
  assert (D5 : Defines hge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel) by (vm_compute; reflexivity).
  assert (D6 : Defines hge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb) by (vm_compute; reflexivity).
  assert (D7 : Defines hge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write) by (vm_compute; reflexivity).
  assert (D8 : Defines hge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers) by (vm_compute; reflexivity).
  assert (D9 : Defines hge "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer) by (vm_compute; reflexivity).
  assert (D10 : Defines hge "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore) by (vm_compute; reflexivity).
  assert (D11 : Defines hge "__GI__IO_un_link" Unit_libio_genops_os.fn___GI__IO_un_link) by (vm_compute; reflexivity).
  assert (D12 : Defines hge "__GI__IO_default_finish" Unit_libio_genops_os.fn___GI__IO_default_finish) by (vm_compute; reflexivity).
  assert (D13 : Defines hge "_IO_file_close_maybe_unlink" Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink) by (vm_compute; reflexivity).
  assert (D14 : Defines hge "__errno_location" LeavesLogic.errno_location_fn) by (vm_compute; reflexivity).
  assert (D15 : Defines hge "close_stream" close_stream_fn) by (vm_compute; reflexivity).
  assert (D16 : Defines hge "_exit" Unit_posix__exit_os.fn___GI__exit) by (vm_compute; reflexivity).
  assert (Hfw : ge_fn hge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write) by (exists (img_addr "_IO_new_file_write");
    split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; vm_compute; congruence]]).
  assert (Hfc : ge_fn hge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close) by (exists (img_addr "__GI__IO_file_close");
    split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; vm_compute; congruence]]).
  assert (Hff : ge_fn hge "_IO_new_file_finish" Unit_libio_fileops_os.fn__IO_new_file_finish) by (exists (img_addr "_IO_new_file_finish");
    split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; vm_compute; congruence]]).
  assert (Hzf : find_fn hge zgc_free_name = None) by (vm_compute; reflexivity).
  assert (Hzg : lookup zgc_free_name (ge_globals hge) = None) by (vm_compute; reflexivity).
  set (M := fun fb freg lb lr count => report_state w tb fb freg (ho_vb ob) lb lr cb creg count).
  set (R := (hello_ro hge ob ∗ pts hello_close_ro_ps ∗ ptsq dq HelloCloseReportImage.hello_errlist_ps ∗
    ∃ fb freg lb lr, ⌜ho_out ob = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ fb + 224 <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
      M fb freg lb lr n)%I).
  set (Q := (∃ fb freg lb lr, M fb freg lb lr ((n + 1) mod 2 ^ 32))%I).
  set (E := (LibioFlushBody.exit_stream false (ho_in ob) ∗ pts hello_close_ro_ps ∗ hello_hd_getopt w R.free tb ∗
    names ob ∗ live cb creg ∗ int_cell cb 0 n)%I).
  iApply (wp_close_stdout_idle (glibc_program := close_call_program) holds_os_glibc (hk_sys _ _ L)
    Hfw R.free_succeeds Hzf Hzg Hfc Hff
    (ho_out ob) (ho_err ob) (ho_in ob) (ho_fcp ob) (ho_vb ob) (ho_vreg ob) (ho_sb ob) (ho_sreg ob) eb
    (ho_so ob) (ho_soreg ob) (ho_se ob) (ho_sereg ob)
    (img_a "exit_failure") (img_gd "exit_failure") 1 (img_a "closeout#ignore_EPIPE") (img_gd "closeout#ignore_EPIPE") 0
    (img_a "closeout#file_name") (img_gd "closeout#file_name") fmt text (hello_sym "closeout#str.52") Unit_misc_error_os.fn___error
    (fun k => error_frame 0 k fmt [WPtr text]) R Q E Φ
    with "Hvt Hsg Htcb Hol Hop Hsl Hsp Hxl Hxc Hil Hib Hnl Hnp Hout Hse He Hio [Hin] [Hinx Hcro Hg Hnames Hcl Hcnt] [HK]").
  1-23, 25-38: try first [exact Herr | exact Hfd1 | exact Hfd2 | (intros; reflexivity) | (vm_compute; reflexivity) |
    (vm_compute; lia) | (cbn; lia)].
  1-2: vm_compute; repeat split; (reflexivity || discriminate).
  - intros k Hk. iIntros "He (#Hro2 & Hcro & #Hel2 & HM)".
    iEval (rewrite pts_ptsq) in "Hcro". iMod (ptsq_persist with "Hcro") as "#Hcro".
    iDestruct "HM" as (fb freg lb lr (Hout & Hfa & Hfe & Hfr)) "HM".
    pose proof (wp_close_write_error w Herr Hfd2 tb fb freg (ho_vb ob) lb lr cb creg Hout eq_refl Hfa Hfe Hfr Hn Hne Hnr
      k n Hk) as W.
    iApply (wp_wand with "[He HM]").
    { iApply (W with "He").
      iSplitR "HM"; [iSplit; [iExact "Hro2" | iSplit; [iExact "Hcro" | iExact "Hel2"]] | iExact "HM"]. }
    iIntros (r) "(-> & He & HM)". iSplit; [done|]. iSplitL "He"; [iExact "He"|].
    iExists fb, freg, lb, lr. iExact "HM".
  - iDestruct "Hin" as (gb greg Hg) "Hl". iExists gb, greg. iSplit; [done | iExact "Hl"].
  - unfold E. iFrame "Hinx Hcro Hg Hnames Hcl Hcnt".
  - assert (Hfs : file_size = 224) by (vm_compute; reflexivity).
    iSplit.
    + iIntros "(%fb & %freg & %lb & %lbreg & %Hfb & Hc) Hse Htcb (Hinx & Hcro & Hg & Hnames & Hcl & Hcnt)".
      unfold R. iSplitR; [iExact "Hro"|]. iSplitL "Hcro"; [iExact "Hcro"|]. iSplitR; [iExact "Hel"|].
      iExists fb, freg, lb, lbreg. destruct Hfb as (Ho & Ha & Hfe & Hr). rewrite Hfs in Hfe.
      iSplit; [iPureIntro; exact (conj Ho (conj Ha (conj Hfe Hr)))|].
      rewrite /M /report_state. iFrame "Hc Hse Htcb Hg Hnames Hcl Hcnt".
    + iIntros "Htcb Hio Hin (Hinx & _)". iApply "HK". iSplit; [done|]. rewrite /exit_io.
      iSplitR; [iExact "Hsg"|]. iSplitL "Htcb"; [iExact "Htcb"|]. iSplitL "Hio"; [iExact "Hio"|]. cbn [big_opL].
      iSplitL; [|done]. iSplitR "Hinx"; [|iExact "Hinx"].
      iDestruct "Hin" as (gb greg Hg) "Hl". iExists gb, greg. iSplit; [done | iExact "Hl"].
Qed.

End call.
