(** When closing stdout fails, Hello reports “write error” with the
    error number that close left behind. Stdout is already closed when
    glibc flushes it at the start of the report. The rest of the
    report uses stderr and the C locale before returning to its caller. *)

From Glibc Require Import Unit_libio_iofflush_os Unit_libio_wfileops_os Unit_misc_error_os Unit_stdioZ2dcommon_fxprintf_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  Pieces Heap Language Logic MemLogic VariadicLogic HelloLeaf.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv FileIdle LibioLogic LibioCloseSteps SysWrappers
  WordString NarrowArgs PrintfSpec LibioFputsSpec LibioCleanupExit FxprintfNormalCall
  ErrorEntry ErrorCall HelloErrorOperand HelloVersionLits HelloEmitBug HelloGlibcDebts HelloGlibcLibsT
  HelloImageLayout HelloImageModule HelloImageLoad StartImageEarly HelloStartFacts HelloGetoptDiagTcb HelloGetoptDiagImage
  HelloStartHdGetopt HelloErrorOperandCall HelloClosedStdout HelloWClosedStdout HelloImageCloseObjs HelloGetoptTable
  HelloCloseReportImage HelloCloseReportText HelloCloseReportLocale HelloCloseReportBody HelloCloseReportPrint HelloCloseReportFinish Fix.
Import ListNotations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps SysWrappers.
Open Scope Z_scope.

Section report.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance report_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation fe := (img_a "_IO_2_1_stderr_").
Local Abbreviation St := (file_idle (ho_vb ob) (ow_self w) (ho_err ob) 2).
Local Abbreviation fmt := (hello_sym "closeout#str.55").
Local Abbreviation text := (hello_sym "closeout#str.53").
Local Abbreviation pre := (sym_ptr hge "glibc_error#str.255").
Local Abbreviation gexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Local Notation dq := DfracDiscarded.
Context (Herr : ow_errno w = Some (mkPtr eb (Obj eb))) (Hfd : In 2 (ow_fds w)).
Context `{Hvf : !HasSpec glibc_os_registry (os_wi w) hge (TAtom "__vfprintf_internal")
  (vfprintf_spec (glibc_program := report_program))}.

(** The report uses the FILE lifetime to load stdout, then lends that same
    lifetime and the retained fields to fflush. The caller gets both back
    along with the updated count, even when the counter wraps. *)
Definition report_state_for tb fb freg (fields : iProp Σ) nb nr count : iProp Σ :=
  (live fb freg ∗ fields) ∗ St ∗ tcb_cleanup_inv (ow_self w) ∗ hello_hd_getopt w R.free tb ∗
  names ob ∗ live nb nr ∗ int_cell nb 0 count.

Definition report_state tb fb freg vb lb lr :=
  report_state_for tb fb freg (closed_stdout_fields fb vb lb lr).

Local Lemma close_literals : ptsq dq hello_close_ro_ps ⊢ word_string dq fmt [37;115] ∗ str_arg (WPtr text).
Proof using Type*.
  rewrite /hello_close_ro_ps ptsq_app. iIntros "[#Ht #Hf]". iSplit.
  - iApply (HelloCloseReportText.report_literal with "Hf"); apply str_shape_b_sound; vm_compute; reflexivity.
  - iApply (ws_arg (glibc_program := report_program) text hello_write_error_text).
    iApply (HelloCloseReportText.report_literal with "Ht"); apply str_shape_b_sound; vm_compute; reflexivity.
Qed.

Context (tb fb : Z) (freg : region) (vb lb : Z) (lr : region) (nb : Z) (nr : region).
Context (Hout : ho_out ob = mkPtr fb (Obj fb)) (Hvb : vb = ho_vb ob)
  (Hfa : fb mod 8 = 0) (Hfe : fb+224 <= r_end freg) (Hfr : r_end freg <= 2^63)
  (Hn : lookup (TAtom "error_message_count") img_globals = Some (mkPtr nb (Obj nb)))
  (Hne : nb+4 <= r_end nr) (Hnr : r_end nr <= 2^63).
Local Abbreviation Ro := (hello_ro hge ob ∗ ptsq dq hello_close_ro_ps ∗ ptsq dq hello_errlist_ps)%I.

Section with_flush.
Context (fields : iProp Σ).
Local Abbreviation M := (report_state_for tb fb freg fields nb nr).
Context (Hflush : forall fr (D : iProp Σ),
  call_frame Unit_libio_iofflush_os.fn___GI__IO_fflush [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> ptr_addr (ow_self w) <> 0 ->
  ⊢ hello_ro hge ob -∗ live fb freg -∗ (fields ∗ D) -∗
  WP (ERun fr : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live fb freg ∗ (fields ∗ D) }}).

Local Lemma wp_report_internal k count ap : 0 <= k < 2^32 ->
  error_va ap [WInt 0; WInt k; WPtr fmt; WPtr text] -∗ errno_any eb -∗ Ro -∗ M count -∗
  WP (ERun (error_internal_frame 0 k fmt ap 0) : gexpr) {{ r, ⌜r = RetVoid⌝ ∗ errno_any eb ∗ M ((count+1) mod 2^32) }}.
Proof using Herr Hfd Hvf Hout Hfa Hfe Hfr Hflush Hn Hne Hnr.
  intros Hk. pose proof (hello_error_link_image R.free) as El. pose proof (hello_link_all R.free R.free_succeeds) as L.
  assert (Hfb : 0 < fb) by (change (mkPtr (img_a "_IO_2_1_stdout_") (Obj (img_a "_IO_2_1_stdout_")) = mkPtr fb (Obj fb)) in Hout;
    injection Hout as <-; vm_compute; reflexivity).
  iIntros "Hva He (#Hro & #Hcro & #Hel) ((Hout & Hfields) & Herr & Htcb & (%x & %Hx & Loan) & Hnames & Hcl & Hcnt)".
  iDestruct ("Loan" with "[$Htcb $He $Herr]") as "HG".
  iDestruct (report_locale_open with "HG") as (tr jb Htr) "(Hclean & Hj & Hflag & HG)".
  iDestruct (report_locale_lend with "HG") as "(Ht & He & Herr & W)".
  pose proof Htr as (Hself & Htb & Hta & Hte & Htrlim). change (ow_self w = mkPtr tb (Obj tb)) in Hself.
  unfold off_cancelhandling in Hte. assert (Hsr : 0 < ptr_addr (ow_self w) < 2^64) by (rewrite Hself; cbn [ptr_addr]; lia).
  iPoseProof "Hro" as "(#Hvt & #Hsg & #Hol & #Hop & #Hsl & #Hsp & _ & _ & _ & _ & _ & _ & #Hp & #Hpg & _)".
  iDestruct "Hpg" as (pb preg (Hpb & Hpa & Hpe & Hpr)) "[#Hpl #Hpp]".
  iDestruct "Hnames" as (a name z) "((Hal & Hap & Hnl & Hnp & Hzl & Hzp) & Has & (%bs & #Hname) & Hzs)".
  iDestruct (ws_life (glibc_program := report_program) with "Hname") as (name_r) "[#Hcap %Haddr]".
  iEval (rewrite Hout) in "Hop". iDestruct (error_va_at (glibc_program := report_program) with "Hva") as "Hva"; [cbn; lia|].
  set (D := (St ∗ errno_any eb ∗ hello_ro hge ob ∗ word_string dq name bs)%I).
  set (S := (fields ∗ D)%I).
  iApply (wp_error_internal_entry_lend (glibc_program := report_program) holds_os_glibc (hk_sys _ _ L)
    (dqs := dq) (dqp := dq) 0 k fmt ap 0 tb tr 0 (ho_so ob) (ho_soreg ob) (mkPtr fb (Obj fb)) (live fb freg)
    pb preg null dq preg (ho_nb ob) (ho_nreg ob) name dq name_r pre Unit_libio_iofflush_os.fn___GI__IO_fflush
    (mkFrame Unit_libio_iofflush_os.fn___GI__IO_fflush [(TAtom "v0", WPtr (mkPtr fb (Obj fb)))] [] None (Enter (TAtom "start") None))
    Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf (fxprintf_normal_frame null pre [WPtr name]) (TAtom "error") Unit_misc_error_os.fn___error (error_frame 0 k fmt [WPtr text])
    S S (fields ∗ St ∗ errno_any eb)%I True%I
    with "Ht Hflag Hol Hop Hout Hpl Hpp [] Hnl Hnp Hcap [$Hfields $Herr $He $Hro $Hname] [//]");
    [exact Hself|exact Htb|exact Hta|lia|exact Htrlim|left; reflexivity|exact (erl_cancel _ _ El)|
     vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; discriminate|vm_compute; discriminate|
     cbn [ptr_addr]; lia|exact Hpb|exact (erl_progname _ _ El _ Hpb)|exact Hpa|exact Hpe|exact Hpr|split; vm_compute; congruence|
     exact (hk_nb _ _ L)|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; discriminate|vm_compute; discriminate|
     exact Haddr|exact (erl_prefix _ _ El)|vm_compute; reflexivity|reflexivity| | |exact (erl_fx _ _ El)|apply fxprintf_normal_call_frame| |
     intros H; contradiction H; reflexivity..| |].
  - iIntros "Hl". iExists (DfracOwn 1),freg. iFrame "Hl". iIntros "$".
  - iIntros "Hl [Hfields HD]". iDestruct "HD" as "(Herr & He & #Hro' & #Hname')".
    iApply (Hflush _ D with "Hro' Hl [$Hfields $Herr $He $Hro' $Hname']"); [reflexivity|exact Hfb|lia].
  - iIntros "Hcap [Hfields (Herr & He & #Hro' & #Hname')]".
    iDestruct (version_lit hge ob ("glibc_error#str.255", [37;115;58;32]) with "Hro'") as "#Hpre";
      [cbn [version_lits]; repeat first [left; reflexivity|right]|].
    iApply (wp_report_fx w Herr Hfd pre [37;115;58;32] _ [WPtr name] with "Hro' Hpre [] Herr He");
      [exact Hsr|reflexivity|reflexivity| | |].
    + apply narrow_fits_all. eapply args_conversion; [constructor|]. do 2 (apply args_literal; [reflexivity|]). constructor.
    + iSplit; [iApply (ws_arg (glibc_program := report_program) with "Hname'")|done].
    + iNext. iIntros (n) "Herr He". iExists _. iSplit; [done|]. iFrame "Hcap Hfields Herr He".
  - done.
  - iIntros (e from cb Hin) "Ht Hflag Hcbl Hsave _ _ Hout _ _ _ Hnl Hnp _ (Hfields & Herr & He) _".
    iDestruct (close_literals with "Hcro") as "[#Hfmt Htext]".
    iApply (wp_report_body (glibc_program := report_program) eb Herr (hk_errno_at _ _ L) holds_os_glibc (hk_sys _ _ L)
      (ho_vb ob) (ho_se ob) (ho_sereg ob) fe e from k fmt text ap cb with "Hsl Hsp Hfmt Htext Hp [] [] Hva Herr He");
      [exact (erl_vfx _ _ El)|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; discriminate|
       vm_compute; discriminate|exact Hsr|exact Hfd|exact Hin|iExists _,_,_; iFrame "Hvt Hsg"|iApply (malloc_ro_of_hello_ro w hge ob L with "Hro")|].
    iIntros (e' pred Hin') "Herr He". iDestruct ("W" with "Ht He Herr") as "HG".
    iApply (wp_report_count_text w Herr Hfd tb tr x.1.1 x.1.2 x.2 e' pred k fmt ap cb nb nr count with "Hro Hel Hcl Hcnt HG");
      [exact Htr|exact (proj1 Hx)|exact Hk|exact Hin'|exact Hn|exact (erl_count _ _ El _ Hn)|exact Hne|exact Hnr|].
    iIntros (e2 pred2 Hin2) "Hcl Hcnt HG".
    iApply (wp_report_finish w Herr Hfd tb tr x.1.1 x.1.2 x.2 e2 pred2 k fmt ap cb with "Hro HG Hflag Hcbl Hsave");
      [exact Htr|exact Hin2|]. iIntros "HG Hflag".
    iAssert (hello_dgx w R.free tb x.1.1 x.1.2 x.2) with "[HG Hflag Hj Hclean]" as "HG".
    { iApply report_locale_open. iExists tr,jb. iFrame. done. }
    iDestruct (hello_dgx_lend w R.free tb Hfd with "HG") as "(Htcb & He & Herr & W)".
    iSplit; [done|]. iFrame "He". rewrite /report_state_for. iSplitL "Hout Hfields"; [iFrame|].
    iFrame "Herr Htcb". iSplitL "W"; [iExists x; by iFrame|]. iSplitR "Hcl Hcnt"; last iFrame.
    iExists a,name,z. rewrite /ncells. iFrame. iExists bs. iExact "Hname".
Qed.

(** The public error wrapper supplies the variadic cursor. The caller
    keeps errno separate from the remaining state so close_stdout can
    use this rule immediately after it reads errno. *)
Lemma wp_close_write_error_with k count : 0 <= k < 2^32 ->
  errno_any eb -∗ (Ro ∗ M count) -∗
  WP (ERun (error_frame 0 k fmt [WPtr text]) : gexpr) {{ r, ⌜r = RetVoid⌝ ∗ errno_any eb ∗ M ((count+1) mod 2^32) }}.
Proof using Herr Hfd Hvf Hout Hfa Hfe Hfr Hflush Hn Hne Hnr.
  intros Hk. iIntros "He [Hro HM]".
  iApply (wp_error_wrapper (glibc_program := report_program) 0 k fmt [WPtr text] (fun ap => error_internal_frame 0 k fmt ap 0)
    (errno_any eb ∗ Ro ∗ M count)%I (errno_any eb ∗ M ((count+1) mod 2^32))%I True%I
    with "[$He $Hro $HM] [//] []"); [reflexivity|lia|exact Hk|exact (erl_internal _ _ (hello_error_link_image R.free))|
      intros; apply error_internal_call_frame| |].
  - intros ap. iIntros "Hva (He & Hro & HM)". iApply (wp_report_internal with "Hva He Hro HM"). exact Hk.
  - iNext. iIntros "$ _". done.
Qed.
End with_flush.

Local Abbreviation M := (report_state tb fb freg vb lb lr nb nr).

(** After a narrow close, fflush calls the narrow sync slot. *)
Corollary wp_close_write_error k count : 0 <= k < 2^32 ->
  errno_any eb -∗ (Ro ∗ M count) -∗
  WP (ERun (error_frame 0 k fmt [WPtr text]) : gexpr) {{ r, ⌜r = RetVoid⌝ ∗ errno_any eb ∗ M ((count+1) mod 2^32) }}.
Proof using Herr Hfd Hvf Hout Hvb Hfa Hfe Hfr Hn Hne Hnr.
  refine (wp_close_write_error_with (closed_stdout_fields fb vb lb lr) _ k count).
  intros fr D Hcall Hfb Hself. subst vb.
  iIntros "#Hro Hl HD". iPoseProof "Hro" as "(#Hvt & #Hsg & _)".
  iDestruct (vtables_slot hge (ho_vb ob) (ho_vreg ob) 96 "_IO_new_file_sync" with "Hvt") as "#Hslot";
    [cbn [file_jumps]; repeat first [left; reflexivity|right]|].
  iApply (wp_closed_stdout_fflush (glibc_program := report_program) holds_os_glibc
    (hk_sys _ _ (hello_link_all _ R.free_succeeds)) report_sync_link
    fr fb freg (ho_vb ob) lb lr (ho_sb ob) (ho_sreg ob) (ho_vreg ob) D with "Hvt Hslot Hsg Hl HD"); assumption.
Qed.

(** The void call resumes at the next instruction with the updated
    counter and errno. Its continuation can take the exit path without
    opening the private state again. *)
Corollary wp_close_write_error_call f e ls lab v fmtv txtv rest j k count Φ :
  arg_x hge e (Arg W v) = Some (WInt k) -> arg_x hge e (Arg P fmtv) = Some (WPtr fmt) ->
  arg_x hge e (Arg P txtv) = Some (WPtr text) -> 0 <= k < 2^32 ->
  errno_any eb -∗ (Ro ∗ M count) -∗
  ▷ (errno_any eb -∗ M ((count+1) mod 2^32) -∗ WP (ERun (mkFrame f e ls None (Exec lab rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Call CVoid (Global (TAtom "error")) [Arg W (Const 0); Arg W v; Arg P fmtv; Arg P txtv] :: rest) j)) : gexpr) {{ Φ }}.
Proof using Herr Hfd Hvf Hout Hvb Hfa Hfe Hfr Hn Hne Hnr.
  intros Hv Hfmt Htext Hk. iIntros "He HR HK".
  iApply wp_call_bind; [cbn [map_option]; rewrite Hv Hfmt Htext; reflexivity|
    exact (erl_error _ _ (hello_error_link_image R.free))|apply error_call_frame|]. iNext.
  iApply (wp_wand with "[He HR]"); [iApply (wp_close_write_error with "He HR"); exact Hk|].
  iIntros (r) "(-> & He & HM)". resume. iApply ("HK" with "He HM").
Qed.

Local Lemma report_wsync_link : ge_fn hge "__GI__IO_wfile_sync" Unit_libio_wfileops_os.fn___GI__IO_wfile_sync.
Proof. exists (img_addr "__GI__IO_wfile_sync"). split; [vm_compute; reflexivity|split; [vm_compute; reflexivity|split; vm_compute; congruence]]. Qed.

Local Abbreviation WM tw tm wd := (report_state_for tb fb freg (closed_wide_fields fb vb lb lr tw tm wd) nb nr).

(** A wide close leaves stdout with its wide jump table and no buffer.
    The report flushes that stream through the wide sync slot. *)
Corollary wp_close_write_error_wide tw tm wd k count : 0 <= k < 2^32 ->
  errno_any eb -∗ (Ro ∗ WM tw tm wd count) -∗
  WP (ERun (error_frame 0 k fmt [WPtr text]) : gexpr)
    {{ r, ⌜r = RetVoid⌝ ∗ errno_any eb ∗ WM tw tm wd ((count+1) mod 2^32) }}.
Proof using Herr Hfd Hvf Hout Hvb Hfa Hfe Hfr Hn Hne Hnr.
  refine (wp_close_write_error_with (closed_wide_fields fb vb lb lr tw tm wd) _ k count).
  intros fr D Hcall Hfb Hself. subst vb.
  iIntros "#Hro Hl HD". iPoseProof "Hro" as "(#Hvt & #Hsg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hwv & _)".
  iApply (wp_closed_wide_fflush (glibc_program := report_program) holds_os_glibc
    (hk_sys _ _ (hello_link_all _ R.free_succeeds)) report_wsync_link
    fr fb freg (ho_vb ob) lb lr tw tm wd (ho_sb ob) (ho_sreg ob) (ho_vreg ob) D with "Hvt Hwv Hsg Hl HD"); assumption.
Qed.
End report.
