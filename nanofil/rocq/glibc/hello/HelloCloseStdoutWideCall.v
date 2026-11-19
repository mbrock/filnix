(** Hello prints its greeting as wide characters, and that print
    usually makes stdout wide. When Hello exits, gnulib's
    `c: close_stdout` must then close a wide stdout. This module proves
    that the callback does so safely in the program as it is loaded.
    One earlier proof walks the callback's code, and another prints the
    error report when the close fails. The narrow case is proved the
    same way in [HelloCloseStdoutCall](HelloCloseStdoutCall.v).

    Before the close, glibc converts the characters left in the buffer
    to bytes. The conversion finds the C locale through the thread's
    locale pointer, which Hello keeps with the state for getopt's
    warnings. The proof borrows that pointer for the close and returns
    it before the error report runs. The write of the converted bytes
    is assumed here, because its own proof has not landed yet. *)

From Glibc Require Import HelloObjects HelloWConvConsts Unit_io_close_nocancel_os Unit_io_write_os
  Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_fileops_os Unit_libio_genops_os
  Unit_libio_iofclose_os Unit_libio_wgenops_os Unit_misc_error_os Unit_nptl_libcZ2dcleanup_os
  Unit_posix__exit_os GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  Pieces Heap Language Logic MemLogic.
From Glibc Require Import HelloBodies.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv FileIdle LibioLogic SysWrappers
  WordString PrintfSpec LibioCleanupExit ErrorCall HelloGlibcDebts HelloGlibcLibsT
  HelloImageLayout HelloImageModule HelloImageLoad StartImageCpu HelloStartFacts HelloStartHdGetopt
  HelloImageCloseObjs HelloLocaleState LeavesLogic AllocLogic
  LibioWOverflowWrite LibioWCloseIt LibioWConvAscii LibioWFwide Mbrtowc
  HelloImageWideObjs HelloImageWFwideObjs HelloImageWReleaseObjs HelloImageWConvObjs HelloConvObjects
  DcgettextRealV HelloGetoptDiagLock HelloGetoptDiagTcb HelloGetoptDiagGettext HelloStartGetoptRules
  HelloWClosedStdout HelloWideState HelloCloseStdoutWide HelloGetoptDiagImage HelloCloseReport StreamSetb StartCtypeInitSpec StartImageEarly HelloImageEarly
  RdlockLogic DcgettextRwlock LibioWIdle LibioSetb Fix.
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
Local Abbreviation tw := (mkPtr (img_a "glibc_wcsmbsload#to_wc") (Ro (img_a "glibc_wcsmbsload#to_wc"))).
Local Abbreviation tm := (mkPtr (img_a "glibc_wcsmbsload#to_mb") (Ro (img_a "glibc_wcsmbsload#to_mb"))).
Local Abbreviation lt := (ct_lt hello_ct_objs).
Local Abbreviation ltreg := (ct_ltreg hello_ct_objs).
Local Abbreviation gl := (ct_gl hello_ct_objs).
Local Abbreviation glreg := (ct_glreg hello_ct_objs).
Local Abbreviation self := (ow_self w).
Local Abbreviation err_idle := (file_idle (ho_vb ob) self (ho_err ob) 2).
Local Notation dq := DfracDiscarded.
Local Ltac image_defines := vm_compute; reflexivity.
Local Ltac image_fn n := exists (img_addr n);
  split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; vm_compute; congruence]].

(** The error report needs a few facts about the running thread. Its
    own object sits at tb, errno is the world's errno, descriptors 1 and
    2 are open, and glibc's formatter keeps its contract. *)
Context (tb : Z) (Herr : ow_errno w = Some (mkPtr eb (Obj eb))) (Hfd1 : In 1 (ow_fds w)) (Hfd2 : In 2 (ow_fds w)).
Context `{Hvf : !HasSpec glibc_os_registry (os_wi w) hge (TAtom "__vfprintf_internal")
  (vfprintf_spec (glibc_program := close_call_program))}.

(** Closing stdout writes the wide characters left in its buffer with
    `c: _IO_wdo_write`. Until that function's proof lands, this section
    assumes what the close needs from it. The write must keep any
    [[frame]] that holds the conversion's read-only tables and can lend
    the thread's locale cells to the conversion. *)
Context (Hwrite : forall E : iProp Σ, (E ⊢ □ wconv_ro) -> (E ⊢ wlocale (DfracOwn 1) ∗ (wlocale (DfracOwn 1) -∗ E)) ->
  forall fb freg wd, wclose_write_rule 1 (ho_vb ob) fb (ho_vreg ob) freg eb wd tw tm E).

(** ## Lending the locale out of getopt's warning state

    Hello keeps the thread's locale pointer with the state that
    getopt's warnings use. That state also needs the cleanup fields,
    errno and stderr before it can be opened. The close needs the
    stream resources and the locale cells at the same time, so these
    lemmas take the locale cells out and leave the rest of the state
    waiting for them. *)

(** The warning resources split into the stream resources, the locale
    cells and the rest, which takes both back. *)
Lemma dgx_locale_lend v tid treg : hello_dgx w R.free tb v tid treg ⊢
  tcb_cleanup_inv self ∗ errno_any eb ∗ err_idle ∗
  (live lt ltreg ∗ pcell lt 0 (mkPtr gl (Obj gl)) ∗ live gl glreg) ∗
  (tcb_cleanup_inv self ∗ errno_any eb ∗ err_idle -∗
   live lt ltreg ∗ pcell lt 0 (mkPtr gl (Obj gl)) ∗ live gl glreg -∗ hello_dgx w R.free tb v tid treg).
Proof using Hfd2.
  rewrite /hello_dgx /hello_dg_G /dlk_G /dlk_G0 /dtx_G /dtx_G0 /dgx_G /dgx_before /dcg_before_v /rw_held /rw_self /dgx_stream.
  iIntros "(%s1 & %s2 & %s3 & %Hr & %tbreg & %jb & %Hc & Hcl & Hj & Hx & ((%bs & H1 & (Hk1 & Hl1 & Hi1) &
    (Hk2 & Hl2 & Hi2) & (Hk3 & Hl3 & Hi3) & H5 & (Hlt & Hlp & Hlg & H6) & H7 & He) & (#Hso & _ & Hps & #HF)
    & HL))".
  iAssert (live tb tbreg) with "[Hl1 Hl2 Hl3]" as "Hl".
  { iPoseProof (dtx_live_split (glibc_program := close_call_program) tb tbreg) as "[_ Hb]". iApply "Hb".
    iFrame "Hl1 Hl2 Hl3". }
  iSplitL "Hcl Hj Hx Hl".
  { iExists tb, tbreg, jb. iSplit; [iPureIntro; exact Hc|]. iFrame "Hcl Hj Hx Hl". }
  iSplitL "He"; [iExists bs; iExact "He"|].
  iSplitL "Hps"; [iExact "Hps"|].
  iSplitL "Hlt Hlp Hlg"; [rewrite /live /pcell !pts_ptsq; iFrame "Hlt Hlp Hlg"|].
  iIntros "((%tb2 & %tbreg2 & %jb2 & %Hc2 & Hl & Hcl & Hj & Hx) & (%bs2 & He) & Hps) (Hlt & Hlp & Hlg)".
  destruct Hc as (Hs & Hc). destruct Hc2 as (Hs2 & Hc2). rewrite Hs in Hs2. injection Hs2 as <-.
  iPoseProof (dtx_live_split (glibc_program := close_call_program) tb tbreg2) as "[Hb _]".
  iDestruct ("Hb" with "Hl") as "(Hl1 & Hl2 & Hl3)".
  iExists s1, s2, s3. iSplit; [done|]. iExists tbreg2, jb2. iSplit; [iPureIntro; split; [exact Hs | exact Hc2]|].
  iSplitL "Hcl"; [iExact "Hcl"|]. iSplitL "Hj"; [iExact "Hj"|]. iSplitL "Hx"; [iExact "Hx"|].
  iSplitL "H1 Hk1 Hl1 Hi1 Hk2 Hl2 Hi2 Hk3 Hl3 Hi3 H5 Hlt Hlp Hlg H6 H7 He".
  { iExists bs2. iSplitL "H1"; [iExact "H1"|]. iSplitL "Hk1 Hl1 Hi1"; [iFrame "Hk1 Hl1 Hi1"|].
    iSplitL "Hk2 Hl2 Hi2"; [iFrame "Hk2 Hl2 Hi2"|]. iSplitL "Hk3 Hl3 Hi3"; [iFrame "Hk3 Hl3 Hi3"|].
    iSplitL "H5"; [iExact "H5"|]. iSplitL "Hlt Hlp Hlg H6"; [iFrame "Hlt Hlp Hlg H6"|].
    iSplitL "H7"; [iExact "H7"|]. iExact "He". }
  iSplitL "Hps"; [|iExact "HL"]. iSplit; [iExact "Hso"|]. iSplit; [done|].
  iSplitL "Hps"; [iExact "Hps"|]. iExact "HF".
Qed.

(** The thread can open the warning state with its streams, take the
    locale cells out and keep its streams. Returning the cells gives
    back a closed warning state, which accepts the streams again at the
    next warning. *)
Lemma hd_locale_lend :
  hello_hd_getopt w R.free tb ∗ tcb_cleanup_inv self ∗ errno_any eb ∗ err_idle ⊢
  (live lt ltreg ∗ pcell lt 0 (mkPtr gl (Obj gl)) ∗ live gl glreg) ∗
  tcb_cleanup_inv self ∗ errno_any eb ∗ err_idle ∗
  (live lt ltreg ∗ pcell lt 0 (mkPtr gl (Obj gl)) ∗ live gl glreg -∗ hello_hd_getopt w R.free tb).
Proof using Hfd2.
  iIntros "((%x & %Hx & W) & Ht & He & Hs)". iDestruct ("W" with "[$Ht $He $Hs]") as "HG".
  iDestruct (dgx_locale_lend with "HG") as "(Ht & He & Hs & Hc & W)". iFrame "Hc Ht He Hs".
  iIntros "Hc". iExists x. iSplit; [done|]. iIntros "S". iApply ("W" with "S Hc").
Qed.

(** The conversion's read-only tables come from two persistent parts
    of the private state. The locale part holds the C character data's
    lifetime, and the conversion part holds the converter path and the
    wide constants. *)
Lemma hello_wconv_ro : ct_ro hello_ct_objs ∗ hello_conv_ro ⊢ wconv_ro.
Proof using Type.
  iIntros "[#Hct #Hconv]". iPoseProof "Hct" as "[#Hcc _]". iPoseProof (hello_conv_tables with "Hconv") as "#Htab".
  iPoseProof "Hconv" as "[_ Hwo]". iEval (rewrite /hello_wide_objs_ps (ptsq_app _ hello_wfwide_ps)
    (ptsq_app _ hello_wrelease_ps) (ptsq_app _ hello_wc_tables_ps) (ptsq_app _ hello_wc_words_ps)
    (ptsq_app _ hello_wc_tails_ps)) in "Hwo".
  iDestruct "Hwo" as "(#Hwf & _ & #Hwt & #Hww & #Hwl & _)".
  iSplit; [iSplit; [iExact "Hcc" | iExact "Htab"]|].
  iSplit; [iExact "Hwf"|]. iSplit; [iExact "Hwt"|]. iSplit; [iExact "Hww" | iExact "Hwl"].
Qed.

(** ## The callback's globals

    The callback reads gnulib's three close globals, and the close of a
    wide stdout takes glibc's conversion lock. Startup leaves all four
    in one list of the private state. *)

(** Eight zero bytes without capabilities hold a null pointer. *)
Local Lemma zero_ptr_cell b : bytes b 0 (repeat 0 8%nat) -∗ auxes b 0 (repeat CNone 8%nat) -∗ pcell b 0 null.
Proof using Type.
  assert (E1 : StringLogic.byte_ps b 0 (repeat 0 8%nat) = cell b 0 (ptr_addr null)) by reflexivity.
  assert (E2 : aux_ps b 0 (repeat CNone 8%nat) = (PAux b 0, VAux (ptr_cap null)) :: aux_ps b 1 (repeat CNone 7%nat))
    by reflexivity.
  rewrite /bytes /auxes /pcell E1 E2 (pts_app [_] (aux_ps _ _ _)). iIntros "H [A _]".
  rewrite (pts_app [_] (cell _ _ _)). iFrame.
Qed.

(** Startup leaves each of these globals as its C initializer sets
    it: `c: exit_failure` holds 1, `c: ignore_EPIPE` holds false,
    `c: file_name` holds null and the conversion lock is free. *)
Local Lemma close_cells_wide :
  pts hello_close_rest_ps ⊢
    (live (img_a "exit_failure") (img_gd "exit_failure") ∗ int_cell (img_a "exit_failure") 0 1) ∗
    (live (img_a "closeout#ignore_EPIPE") (img_gd "closeout#ignore_EPIPE") ∗ bytes (img_a "closeout#ignore_EPIPE") 0 [0]) ∗
    (live (img_a "closeout#file_name") (img_gd "closeout#file_name") ∗ pcell (img_a "closeout#file_name") 0 null) ∗
    gconv_lock_free.
Proof using Type.
  rewrite /hello_close_rest_ps !pts_app !obj_ps_own. cbn [fst snd].
  iIntros "((Lx & Bx & _) & (Li & Bi & _) & (Ln & Bn & An) & (Ll & Bl & _))".
  iFrame "Lx Li Bi Ln". iSplitL "Bx"; [iSplit; [iPureIntro; lia | iExact "Bx"]|].
  iSplitL "Bn An"; [iApply (zero_ptr_cell with "Bn An")|].
  iSplitL "Ll"; [iExact "Ll"|]. iSplit; [iPureIntro; lia|]. iExact "Bl".
Qed.

(** ## The contract

    The callback closes wide stdout and then stderr, and it leaves stdin
    open for exit's cleanup. The conversion borrows the frame
    wconv_ro ∗ wlocale, which holds the read-only tables and the locale
    cells. If closing stdout fails, the callback reports the error on
    stderr and calls `c: _exit`; the report needs getopt's warning state
    whole, so the proof returns the locale cells to it first. *)

(** The contract holds for every private state that splits the way
    startup builds it, as in the narrow case. *)
Lemma hello_close_stdout_wide (N1 N2 priv : iProp Σ) :
  (priv ⊣⊢ N1 ∗ hello_hd_getopt w R.free tb ∗ (N2 ∗ hello_priv_rest w R.free)) ->
  HelloGlibcDebts.fn_triple w hge (TAtom "close_stdout") []
    (hello_ro hge ob ∗ hello_stdio_wide w hge ob (file_wide hge (ho_vb ob) (ow_self w) (ho_out ob) 1) ∗ priv ∗ names ob)%I
    (fun r => ⌜r = RetVoid⌝ ∗ exit_io w hge ob)%I.
Proof using Herr Hfd1 Hfd2 Hvf Hwrite.
  intros Hpriv. pose proof (hello_link_all R.free R.free_succeeds) as L.
  exists close_stdout_fn. split; [exact (hk_close_stdout _ _ L)|]. split; [eexists; reflexivity|].
  intros f Φ Hf. cbn in Hf. injection Hf as <-.
  iIntros "(#Hro & (Hout & Hse & (Hin & Hinx) & Hio & Htcb & He & Hec) & Hp & Hnames) HK".
  iDestruct (Hpriv with "Hp") as "(_ & Hg & _ & Hloc & #Hconv & _ & Hrest & Hcro & #Hel)".
  iDestruct (close_cells_wide with "Hrest") as "((Hxl & Hxc) & (Hil & Hib) & (Hnl & Hnp) & Hlk)".
  iDestruct (hd_locale_lend with "[$Hg $Htcb $He $Hse]") as "((Hlt & Hlp & Hlg) & Htcb & He & Hse & Wg)".
  iDestruct "Hloc" as "(Hcat & _ & _ & _ & _ & #Hct & _)".
  iAssert wconv_ro as "#Hwc".
  { iApply hello_wconv_ro. iSplit; [iExact "Hct" | iExact "Hconv"]. } iPoseProof "Hwc" as "(#Hmb & #Hwf & _)".
  iPoseProof "Hconv" as "[_ Hwo]". iEval (rewrite /hello_wide_objs_ps (ptsq_app _ hello_wfwide_ps)
    (ptsq_app _ hello_wrelease_ps)) in "Hwo". iDestruct "Hwo" as "(_ & #Hwr & _)".
  iAssert (wconv_ro ∗ wlocale (DfracOwn 1))%I with "[Hlt Hlp Hlg Hcat]" as "HL".
  { iSplit; [iExact "Hwc"|].
    iSplitL "Hlt"; [iExact "Hlt"|]. iSplitL "Hlp"; [iExact "Hlp"|]. iSplitL "Hlg"; [iExact "Hlg"|].
    rewrite /pcellq -pts_ptsq. iExact "Hcat". }
  iDestruct "Hec" as (cb creg n Hc) "[Hcl Hcnt]".
  iPoseProof "Hro" as "(#Hvt & #Hsg & #Hol & #Hop & #Hsl & #Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hwv & _)".
  pose proof Hc as (Hn & Hna & Hne & Hnr).
  destruct (hk_frees _ _ L) as (Hfh & Hzf & Hzg).
  pose proof (hi_free_rule (glibc_program := close_call_program) (Hfree_fn := hk_free _ _ L) Hfh Hzf Hzg) as Hfree.
  assert (D0 : Defines hge "__fpending" Unit_libio___fpending_os.fn___fpending) by image_defines.
  assert (D1 : Defines hge "ferror" Unit_libio_ferror_os.fn__IO_ferror) by image_defines.
  assert (D2 : Defines hge "fclose" Unit_libio_iofclose_os.fn__IO_new_fclose) by image_defines.
  assert (D3 : Defines hge "__GI___write" Unit_io_write_os.fn___GI___libc_write) by image_defines.
  assert (D4 : Defines hge "free" free_fn) by image_defines.
  assert (D5 : Defines hge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel) by image_defines.
  assert (D6 : Defines hge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb) by image_defines.
  assert (D7 : Defines hge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write) by image_defines.
  assert (D8 : Defines hge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers) by image_defines.
  assert (D9 : Defines hge "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer) by image_defines.
  assert (D10 : Defines hge "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore) by image_defines.
  assert (D11 : Defines hge "__GI__IO_un_link" Unit_libio_genops_os.fn___GI__IO_un_link) by image_defines.
  assert (D12 : Defines hge "__GI__IO_default_finish" Unit_libio_genops_os.fn___GI__IO_default_finish) by image_defines.
  assert (D13 : Defines hge "_IO_file_close_maybe_unlink" Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink) by image_defines.
  assert (D14 : Defines hge "__GI__IO_wsetb" Unit_libio_wgenops_os.fn___GI__IO_wsetb) by image_defines.
  assert (D15 : Defines hge "__GI__IO_wdo_write" wdo_write_fn) by image_defines.
  assert (D16 : Defines hge "__errno_location" LeavesLogic.errno_location_fn) by image_defines.
  assert (D17 : Defines hge "close_stream" close_stream_fn) by image_defines.
  assert (D18 : Defines hge "_exit" Unit_posix__exit_os.fn___GI__exit) by image_defines.
  assert (Hfw : ge_fn hge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write) by image_fn "_IO_new_file_write".
  assert (Hfc : ge_fn hge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close) by image_fn "__GI__IO_file_close".
  assert (Hff : ge_fn hge "_IO_new_file_finish" Unit_libio_fileops_os.fn__IO_new_file_finish) by image_fn "_IO_new_file_finish".
  set (M := fun fb freg lb lr wd count =>
    report_state_for w tb fb freg (closed_wide_fields fb (ho_vb ob) lb lr tw tm wd) cb creg count).
  set (R := (hello_ro hge ob ∗ pts hello_close_ro_ps ∗ ptsq dq HelloCloseReportImage.hello_errlist_ps ∗
    ∃ fb freg lb lr wd, ⌜ho_out ob = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ fb + 224 <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
      M fb freg lb lr wd n)%I).
  set (Q := (∃ fb freg lb lr wd, M fb freg lb lr wd ((n + 1) mod 2 ^ 32))%I).
  set (E := (LibioFlushBody.exit_stream false (ho_in ob) ∗ pts hello_close_ro_ps ∗
    (live lt ltreg ∗ pcell lt 0 (mkPtr gl (Obj gl)) ∗ live gl glreg -∗ hello_hd_getopt w R.free tb) ∗
    names ob ∗ live cb creg ∗ int_cell cb 0 n)%I).
  iApply (wp_close_stdout_wide (glibc_program := close_call_program) holds_os_glibc (hk_sys _ _ L) Hfree
    Hfw Hfh Hzf Hzg Hfc Hff
    (ho_out ob) (ho_err ob) (ho_in ob) (ho_fcp ob) (ho_vb ob) (ho_vreg ob) (ho_sb ob) (ho_sreg ob) eb
    (ho_so ob) (ho_soreg ob) (ho_se ob) (ho_sereg ob)
    (img_a "exit_failure") (img_gd "exit_failure") 1 (img_a "closeout#ignore_EPIPE") (img_gd "closeout#ignore_EPIPE") 0
    (img_a "closeout#file_name") (img_gd "closeout#file_name") fmt text (hello_sym "closeout#str.52") Unit_misc_error_os.fn___error
    (fun k => error_frame 0 k fmt [WPtr text]) (wconv_ro ∗ wlocale (DfracOwn 1))%I R Q E Φ
    with "Hvt Hwv Hsg Htcb Hol Hop Hsl Hsp Hxl Hxc Hil Hib Hnl Hnp Hout Hse He HL Hmb Hwf Hwr Hlk Hio [Hin]
      [Hinx Hcro Wg Hnames Hcl Hcnt] [HK]").
  41: { intros fb freg wd. apply Hwrite.
    - iIntros "[#H _]". iModIntro. iExact "H".
    - iIntros "[#H Hl]". iFrame "Hl". iIntros "Hl". iFrame "H Hl". }
  24: { intros k Hk. iIntros "He (#Hro2 & Hcro & #Hel2 & HM)".
    iEval (rewrite pts_ptsq) in "Hcro". iMod (ptsq_persist with "Hcro") as "#Hcro".
    iDestruct "HM" as (fb freg lb lr wd (Hout & Hfa & Hfe & Hfr)) "HM".
    pose proof (wp_close_write_error_wide w Herr Hfd2 tb fb freg (ho_vb ob) lb lr cb creg Hout eq_refl Hfa Hfe Hfr
      Hn Hne Hnr tw tm wd k n Hk) as W.
    iApply (wp_wand with "[He HM]").
    { iApply (W with "He").
      iSplitR "HM"; [iSplit; [iExact "Hro2" | iSplit; [iExact "Hcro" | iExact "Hel2"]] | iExact "HM"]. }
    iIntros (r) "(-> & He & HM)". iSplit; [done|]. iSplitL "He"; [iExact "He"|].
    iExists fb, freg, lb, lr, wd. iExact "HM". }
  1-41: try first [exact Herr | exact Hfd1 | exact Hfd2 | (intros; reflexivity) | (vm_compute; reflexivity) |
    (vm_compute; lia) | (cbn; lia)].
  1-2: vm_compute; repeat split; (reflexivity || discriminate).
  - iDestruct "Hin" as (gb greg Hg) "Hl". iExists gb, greg. iSplit; [done | iExact "Hl"].
  - unfold E. iFrame "Hinx Hcro Wg Hnames Hcl Hcnt".
  - assert (Hfs : file_size = 224) by (vm_compute; reflexivity).
    iSplit.
    + iIntros "(%fb & %freg & %lb & %lbreg & %wd & %Hfb & Hc) Hse Htcb HL _ (Hinx & Hcro & Wg & Hnames & Hcl & Hcnt)".
      iEval (rewrite /wlocale /mbr_locale) in "HL". iDestruct "HL" as "[_ (Hlt & Hlp & Hlg & _)]".
      iDestruct ("Wg" with "[$Hlt $Hlp $Hlg]") as "Hg".
      unfold R. iSplitR; [iExact "Hro"|]. iSplitL "Hcro"; [iExact "Hcro"|]. iSplitR; [iExact "Hel"|].
      iExists fb, freg, lb, lbreg, wd. destruct Hfb as (Ho & Ha & Hfe & Hr). rewrite Hfs in Hfe.
      iSplit; [iPureIntro; exact (conj Ho (conj Ha (conj Hfe Hr)))|].
      iEval (rewrite /closed_wide) in "Hc".
      rewrite /M /report_state_for. iFrame "Hc Hse Htcb Hg Hnames Hcl Hcnt".
    + iIntros "Htcb Hio Hin _ _ (Hinx & _)". iApply "HK". iSplit; [done|]. rewrite /exit_io.
      iSplitR; [iExact "Hsg"|]. iSplitL "Htcb"; [iExact "Htcb"|]. iSplitL "Hio"; [iExact "Hio"|]. cbn [big_opL].
      iSplitL; [|done]. iSplitR "Hinx"; [|iExact "Hinx"].
      iDestruct "Hin" as (gb greg Hg) "Hl". iExists gb, greg. iSplit; [done | iExact "Hl"].
Qed.

End call.
