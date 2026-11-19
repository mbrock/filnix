(** When strerror cannot find an errno in its table, it passes a
    1024-byte array, a prefix and the number to snprintf. The wrapper
    builds an argument cursor, then initializes, fills and terminates
    the array. The result is a string that error can pass to its next
    print, even if the formatter returned a negative count. *)

From Glibc Require Import PrintfTables Unit_libio_vsnprintf_os Unit_stdioZ2dcommon_printf_buffer_done_os
  GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  ExternalMachine Pieces Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import IRFrames.
From Glibc Require Import Fix FileInv OsWorld OsBlocks OsRegistry LibioLogic WordString NarrowFormat NarrowArgs
  FxprintfStream PrintfLayout PrintfOut PrintfSpec PrintfWrap CodePrelude StartImageEarly HelloImageLoad HelloImageModule
  HelloCloseReportStrerror HelloCloseReportFormat HelloCloseReportFlush HelloCloseReportInit HelloCloseReportDone.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Definition report_vsnprintf := Unit_libio_vsnprintf_os.fn___vsnprintf_internal.

Section snprintf.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance sn_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Context (Herr : ow_errno w = Some (mkPtr eb (Obj eb))).

(** The internal function gives its local printf buffer to the three
    callees in order. Only the last one transfers the caller's array
    back as a terminated string. *)
Local Lemma wp_report_vsnprintf db dr k fmt prefix ap cf Φ :
  0 < db -> db mod 16 = 0 -> db+1024 <= r_end dr -> r_end dr <= 2^48 -> 0 <= k < 2^32 ->
  let dp := mkPtr db (Obj db) in
  call_frame report_vsnprintf [WPtr dp; WInt 1024; WPtr fmt; WPtr ap; WInt 0] = Some cf ->
  printf_ro -∗ word_string DfracDiscarded fmt [37;115;37;100] -∗ str_arg (WPtr prefix) -∗
  va_at ap 24 [WPtr dp; WInt 1024; WPtr fmt; WPtr prefix; WInt k] -∗
  live db dr -∗ win_own db db (db+1024) -∗ errno_any eb -∗
  ▷ (∀ n s, ⌜0 <= n < 2^32⌝ -∗ errno_any eb -∗ word_string (DfracOwn 1) dp s -∗ Φ (Ret (WInt n))) -∗
  WP (ERun cf : sexpr) {{ Φ }}.
Proof using Herr.
  intros Hd Hal Hfit Hspace Hk dp Hcf. injection Hcf as <-.
  assert (Hi : Defines hge "__printf_buffer_snprintf_init" report_init) by (vm_compute; reflexivity).
  assert (Hdone : Defines hge "__printf_buffer_snprintf_done" report_done) by (vm_compute; reflexivity).
  assert (Hcnt : Defines hge "__printf_buffer_done" Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done) by (vm_compute; reflexivity).
  assert (Hg : lookup (TAtom "__libc_errno") img_globals = Some (mkPtr eb (Obj eb))) by (vm_compute; reflexivity).
  iIntros "#Hro #Hfmt Hprefix Hva Hd Hwin He HK". step.
  iApply wp_alloc; [vm_compute; reflexivity|vm_compute; discriminate|vm_compute; discriminate|
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w _ _ _ _ _ Hf Hw)|].
  iNext. iIntros (bb [Hb [Hb16 Hbe]]) "HB".
  iApply wp_call_bind; [vx|exact Hi|reflexivity|]. iNext.
  iApply (wp_report_init _ bb db dr eb with "HB Hd Hwin He"); try assumption; try reflexivity.
  iNext. iIntros "Hout". iExists _. iSplit; [done|]. iNext.
  set (pb := PbIn bb fmt DfracDiscarded [37;115;37;100] [FmtStr;FmtInt] ap 24
    [WPtr dp; WInt 1024; WPtr fmt; WPtr prefix; WInt k] [] eb).
  pose proof (report_format_has_spec w db dr eb) as Hformat.
  iApply (wp_call_spec glibc_os_registry (os_wi w) hge _ (printf_buffer_spec 2 (snprintf_R db dr eb)) pb
    with "[Hout Hva Hprefix]"); [vx| |].
  { iPoseProof (snprintf_lends_errno db dr eb bb) as "#Hlend".
    cbn [pb fs_pre printf_buffer_spec pb_buf pb_fmt pb_dq pb_bytes pb_ds pb_ap pb_skip pb_xs pb_rest pb_eb].
    change (skipn (Z.to_nat (24/8)) _) with [WPtr prefix;WInt k]. iSplit.
    { iPureIntro. split_and!; [reflexivity| |lia|reflexivity|exact Herr|exact Hg].
      apply narrow_fits_all. econstructor; [constructor|]. econstructor; [constructor; exact Hk|constructor]. }
    iSplitL "Hout"; [iExact "Hout"|]. iSplit; [iExact "Hfmt"|]. iSplitL "Hva"; [iExact "Hva"|]. iSplitL "Hprefix".
    { iSplitL "Hprefix"; [iExact "Hprefix"|]. iSplit; [iPureIntro; exact I|iEmpIntro]. }
    iSplit; [iModIntro; iExact "Hlend"|iExact "Hro"]. }
  iIntros (v) "(-> & Hout & _)". iExists _. iSplit; [done|]. iNext.
  iApply wp_call_bind; [vx|exact Hdone|reflexivity|]. iNext.
  iApply (wp_report_done (glibc_program := sn_program) eb Herr Hg db dr _ bb with "Hout"); first reflexivity.
  iNext. iIntros (n s Hn) "He Hs". iExists _. iSplit; [done|]. iNext.
  iApply wp_ret; [reflexivity|vx|]. iNext. rewrite !(Z.mod_small n (2^32) Hn). iApply ("HK" with "[%] He Hs"). exact Hn.
Qed.

(** The public function snapshots all five arguments and skips the
    three named ones. The formatter therefore sees the prefix first
    and the signed integer second. *)
Lemma wp_report_snprintf db dr k fmt prefix Φ :
  0 < db -> db mod 16 = 0 -> db+1024 <= r_end dr -> r_end dr <= 2^48 -> 0 <= k < 2^32 ->
  let dp := mkPtr db (Obj db) in
  printf_ro -∗ word_string DfracDiscarded fmt [37;115;37;100] -∗ str_arg (WPtr prefix) -∗
  live db dr -∗ win_own db db (db+1024) -∗ errno_any eb -∗
  ▷ (∀ n s, ⌜0 <= n < 2^32⌝ -∗ errno_any eb -∗ word_string (DfracOwn 1) dp s -∗ Φ (Ret (WInt n))) -∗
  WP (ERun (invocation report_snprintf [WPtr dp; WInt 1024; WPtr fmt; WPtr prefix; WInt k]) : sexpr) {{ Φ }}.
Proof using Herr.
  intros Hd Hal Hfit Hspace Hk dp. iIntros "#Hro #Hfmt Harg Hd Hwin He HK".
  assert (Hvs : Defines hge "__vsnprintf_internal" report_vsnprintf) by (vm_compute; reflexivity).
  iApply WrapVL.wp_snapshot; [discriminate|reflexivity|
    intros ? ? ? ? Hf Hw; exact (os_wi_snapshot _ _ _ _ _ _ _ Hf Hw)|].
  iNext. iIntros (sb Hsb) "Hsnap". step.
  iApply wp_alloc; [vm_compute; reflexivity|vm_compute; discriminate|vm_compute; discriminate|
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w _ _ _ _ _ Hf Hw)|].
  iNext. iIntros (cb Hcb) "Hobj". change (0 < cb /\ cb mod 16 = 0 /\ cb+32 <= 2^48) in Hcb.
  iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hx & Ha)"; [compute; discriminate|].
  iAssert (live cb (mkRegion cb (cb+32) Heap Live)) with "Hcl" as "Hcl".
  iDestruct (WrapVL.zero_cell_prefix cb 0 24 with "Hx Ha") as "(Hcc & _ & _)".
  iApply WrapVL.wp_va_args; [reflexivity|]. iNext. check "Hcl". store "Hcl" "Hcc".
  iDestruct (va_at_intro (glibc_program := sn_program) cb sb 24 [WPtr dp;WInt 1024;WPtr fmt;WPtr prefix;WInt k]
    with "Hcl Hcc Hsnap") as "Hva";
    [split_and!; Z.div_mod_to_equations; lia|exact Hsb|lia|cbn [length]; lia|].
  iApply wp_call_bind; [vx|exact Hvs|reflexivity|]. iNext.
  iApply (wp_report_vsnprintf db dr k fmt prefix _ _ with "Hro Hfmt Harg Hva Hd Hwin He"); try assumption; first reflexivity.
  iNext. iIntros (n s Hn) "He Hs". iExists _. iSplit; [done|]. iNext.
  iApply wp_ret; [reflexivity|vx|]. iNext. rewrite !(Z.mod_small n (2^32) Hn). iApply ("HK" with "[%] He Hs"). exact Hn.
Qed.
End snprintf.
