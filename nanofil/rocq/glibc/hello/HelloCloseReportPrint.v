(** Glibc counts every write-error report. If close left errno at zero,
    error skips straight to the newline. Otherwise it allocates space
    for strerror and prints the returned string to stderr. Neither
    path needs stdout or restores the cancellation flag yet. *)

From Glibc Require Import Unit_misc_error_os Unit_stdioZ2dcommon_fxprintf_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv FileIdle LibioLogic LibioCloseSteps SysWrappers
  WordString NarrowArgs NarrowFormat PrintfSpec AllocRo LibioFputsSpec FxprintfStream FxprintfNormalCall
  ErrorEntry ErrorText
  HelloGlibcDebts HelloGlibcLibsT HelloImageModule HelloImageLoad HelloImageLayout HelloStartFacts
  HelloEmitBug HelloErrorOperand HelloVfxprintfIdle HelloGetoptDiagImage HelloGetoptDiagTcb
  StartImageEarly HelloCloseReportImage HelloCloseReportLocale HelloCloseReportStrerror HelloCloseReportText LibioCleanupExit Fix.
Import ListNotations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps SysWrappers.
Open Scope Z_scope.

Section print.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance print_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation fe := (img_a "_IO_2_1_stderr_").
Local Abbreviation err_idle := (file_idle (ho_vb ob) (ow_self w) (ho_err ob) 2).
Local Abbreviation gexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Context (Herr : ow_errno w = Some (mkPtr eb (Obj eb))) (Hfd : In 2 (ow_fds w)).
Context `{Hvf : !HasSpec glibc_os_registry (os_wi w) hge (TAtom "__vfprintf_internal")
  (vfprintf_spec (glibc_program := print_program))}.

(** Error uses the null-stream wrapper for the program name, errno
    text and newline. The wrapper selects stderr, so none of these
    calls requires an open descriptor for stdout. *)
Lemma wp_report_fx fmt s ds ys Φ :
  0 < ptr_addr (ow_self w) < 2^64 -> forallb snapshot_word ys = true ->
  parse_narrow s = Some ds -> narrow_fits ds ys [] ->
  hello_ro hge ob -∗ word_string DfracDiscarded fmt s -∗ ([∗ list] y ∈ ys, str_arg y) -∗
  err_idle -∗ errno_any eb -∗
  ▷ (∀ n, err_idle -∗ errno_any eb -∗ Φ (Ret (WInt (n mod 2^32)))) -∗
  WP (ERun (fxprintf_normal_frame null fmt ys) : gexpr) {{ Φ }}.
Proof using Herr Hfd Hvf.
  intros Hself Hsnap Hparse Hfit. iIntros "#Hro #Hfmt Hy Herr He HK".
  iPoseProof "Hro" as "(#Hvt & #Hsg & _ & _ & #Hsl & #Hsp & _ & _ & _ & _ & _ & _ & #Hp & _)".
  iDestruct (ws_life (glibc_program := print_program) with "Hfmt") as (r) "[#Hcap %Haddr]".
  pose proof (hello_link_all R.free R.free_succeeds) as Hk.
  assert (Hs0 : ptr_addr (ow_self w) <> 0) by lia. assert (Hsr : 0 <= ptr_addr (ow_self w) < 2^64) by lia.
  iApply (wp_fxprintf_idle_null (glibc_program := print_program) eb Herr (hk_errno_at _ _ Hk) holds_os_glibc
    (hk_sys _ _ Hk) Hs0 Hsr (ho_vb ob) 2 fe (ho_se ob) (ho_sereg ob) fmt r s ds ys
    with "Hsl Hsp Herr Hcap Hfmt Hy He Hp [] []");
    [vm_compute; reflexivity|exact Hsnap|exact Hparse|exact Hfit|exact Hfd|exact Haddr|
     vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|vm_compute; discriminate|vm_compute; discriminate| | |].
  - iExists _,_,_. iFrame "Hvt Hsg".
  - iApply (malloc_ro_of_hello_ro w hge ob Hk with "Hro").
  - iNext. iIntros (n) "Herr He _". iApply ("HK" with "Herr He").
Qed.

(** Strerror needs the alignment of its scratch array when it calls
    snprintf. The allocation supplies that alignment here. The known
    table entry and the newly written array both satisfy the argument
    check for the following print. *)
Lemma wp_report_count_text tb tr v tid treg e from k fmt ap cb nb nreg count Φ :
  dtx_tcb_at (glibc_program := print_program) tb tr -> 0 <= v < 2^32 -> 0 <= k < 2^32 ->
  error_inputs e 0 k fmt ap 0 cb ->
  lookup (TAtom "error_message_count") img_globals = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb + 4 <= r_end nreg -> r_end nreg <= 2^63 ->
  let G := report_locale w R.free tb tr v tid treg in
  hello_ro hge ob -∗ ptsq DfracDiscarded hello_errlist_ps -∗ live nb nreg -∗ int_cell nb 0 count -∗ G -∗
  (∀ e' pred, ⌜error_inputs e' 0 k fmt ap 0 cb⌝ -∗ live nb nreg -∗ int_cell nb 0 ((count+1) mod 2^32) -∗ G -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e' [] None (Enter (TAtom "iw_2.L92") (Some pred))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Herr Hfd Hvf.
  intros Htr Hv Hk Hin Hglobal Hnb Hne Hnr G. iIntros "#Hro #Hel Hl Hcnt HG HK".
  destruct (Z.eq_dec k 0) as [->|Hnz].
  { iApply (wp_error_count_zero (glibc_program := print_program) e from 0 fmt ap 0 cb nb nreg count G
      with "Hl Hcnt HG HK"); assumption. }
  iDestruct "Hcnt" as "[%Hcount Hbytes]". destruct Hin as (Hstatus & Herrnum & Hfmt & Hap & Hmode & Hsave & Hchk).
  assert (Htext : lookup (TAtom "glibc_error#str.252") img_globals = Some (hello_sym "glibc_error#str.252")) by (vm_compute; reflexivity).
  destruct report_strerror_links as (_ & _ & Hstr).
  assert (Hfx : find_fn hge (TAtom "__fxprintf") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf)) by (vm_compute; reflexivity).
  iApply (wp_live_fit1 (glibc_program := print_program) nb nreg with "Hl"). iIntros ([Hnb0 Hnb48]) "Hl".
  step. step_global Hglobal. check "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hbytes");
    [reflexivity|vx|reflexivity|apply error_count_unsigned; assumption|left; reflexivity|a2|].
  iNext. iIntros "Hl Hbytes". step. check "Hl". store_int "Hl" "Hbytes".
  iEval (rewrite Z.mod_mod; [|lia]) in "Hbytes".
  iEval (rewrite (Z.mod_small count (2^32)); [|exact Hcount]) in "Hbytes". change (1 mod 2^32) with 1.
  branch_as false. step.
  iApply wp_alloc; [reflexivity|vm_compute; discriminate|vm_compute; discriminate|
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w _ _ _ _ _ Hf Hw)|].
  iNext. iIntros (db [Hd [Ha Hspace]]) "Hobj".
  iPoseProof "Hro" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hp & _)".
  iApply wp_call_bind; [vx|exact Hstr|reflexivity|]. iNext. rewrite (Z.mod_small k (2^32) Hk).
  iApply (wp_report_message_string w Herr tb tr v tid treg _ k db with "Hel Hp Hobj HG"); try assumption; first reflexivity.
  iNext. iIntros (p s) "#Hs HG". resume. step_global Htext.
  iApply wp_call_bind; [vx|exact Hfx|apply fxprintf_normal_call_frame|]. iNext.
  iDestruct (report_locale_lend with "HG") as "(Ht & He & Herr & W)".
  iDestruct (report_text_literals with "Hel") as "(_ & _ & #Htf)".
  iApply (wp_report_fx _ _ _ [WPtr p] with "Hro Htf [] Herr He").
  - destruct Htr as (Ht & Htb & Ha2 & Hb2 & He2). change (ow_self w = mkPtr tb (Obj tb)) in Ht.
    rewrite Ht. cbn [ptr_addr]. unfold off_cancelhandling in Hb2. lia.
  - reflexivity.
  - reflexivity.
  - apply narrow_fits_all. do 2 (apply args_literal; [reflexivity|]). eapply args_conversion; constructor.
  - iSplit; [iApply (ws_arg (glibc_program := print_program) with "Hs")|done].
  - iNext. iIntros (n) "Herr He". resume. step.
    iApply ("HK" with "[%] Hl [Hbytes] [W Ht He Herr]").
    + unfold error_inputs. repeat split; lk_prove.
    + iSplit; [iPureIntro; apply Z.mod_pos_bound; lia|iExact "Hbytes"].
    + iApply ("W" with "Ht He Herr").
Qed.
End print.
