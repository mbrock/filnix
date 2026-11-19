(** When glibc finds errno in its error table, strerror returns the
    translated message and leaves its caller's buffer alone. When it
    finds no message, it translates the prefix “Unknown error ” and
    passes it and the original errno to snprintf. This proof runs both
    translations. Only the second path needs a proof of the print. *)

From Glibc Require Import Unit_stdioZ2dcommon_errlist_os Unit_stdioZ2dcommon_snprintf_os Unit_string__strerror_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import IRFrames.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv WordString CodePrelude HelloGlibcProgCells
  StartImageEarly HelloImageModule HelloImageLoad HelloGetoptDiagImage HelloGetoptDiagTcb
  HelloCloseReportImage HelloCloseReportMessages HelloCloseReportLocale Fix.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Definition report_snprintf : func := Unit_stdioZ2dcommon_snprintf_os.fn___GI___snprintf.
Definition unknown_fmt := Eval vm_compute in hello_sym "glibc__strerror#str.136".
Definition unknown_prefix := Eval vm_compute in hello_sym "glibc__strerror#str.137".

Section strerror.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world).
Local Abbreviation hge := (mkGenv hello_image_module img_globals R.free).
#[local] Instance strerror_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Local Abbreviation eb := (img_a "__libc_errno").

(** The image links the two callees that strerror selects. The caller
    of strerror uses the third link to enter the wrapper itself. *)
Lemma report_strerror_links :
  find_fn hge (TAtom "__get_errlist") = Some (Defined Unit_stdioZ2dcommon_errlist_os.fn___get_errlist) /\
  find_fn hge (TAtom "__GI___snprintf") = Some (Defined report_snprintf) /\
  find_fn hge (TAtom "__GI___strerror_r") = Some (Defined Unit_string__strerror_os.fn___GI___strerror_r).
Proof using Type. split_and!; vm_compute; reflexivity. Qed.

(** A table message remains readable after translation. A missing
    entry requires the caller to run the linked snprintf on its own
    buffer; strerror ignores the integer result and returns that buffer. *)
Lemma wp_report_strerror (Herr : ow_errno w = Some (mkPtr eb (Obj eb)))
    tb tr v tid treg cf k buf len Φ :
  dtx_tcb_at tb tr -> 0 <= v < 2^32 -> 0 <= k < 2^32 -> 0 <= len < 2^64 ->
  call_frame Unit_string__strerror_os.fn___GI___strerror_r [WInt k; WPtr buf; WInt len] = Some cf ->
  let G := report_locale w R.free tb tr v tid treg in
  ptsq DfracDiscarded hello_errlist_ps -∗ G -∗
  ▷ (match err_at k with
    | Some (b, _, s) => word_string DfracDiscarded (mkPtr b (Ro b)) s -∗ G -∗ Φ (Ret (WPtr (mkPtr b (Ro b))))
    | None => G -∗ WP (ERun (invocation report_snprintf [WPtr buf; WInt len; WPtr unknown_fmt;
                    WPtr unknown_prefix; WInt k]) : gexpr)
                  {{ result, ∃ n, ⌜result = Ret (WInt n)⌝ ∗ Φ (Ret (WPtr buf)) }}
    end)%I -∗ WP (ERun cf : gexpr) {{ Φ }}.
Proof using Type.
  intros Htr Hv Hk Hlen Hcf G. destruct report_strerror_links as (Hget & Hprint & _).
  assert (Hdom : lookup (TAtom "__GI__libc_intl_domainname") img_globals = Some hello_dom) by (vm_compute; reflexivity).
  assert (Hfmt : lookup (TAtom "glibc__strerror#str.136") img_globals = Some unknown_fmt) by (vm_compute; reflexivity).
  assert (Hprefix : lookup (TAtom "glibc__strerror#str.137") img_globals = Some unknown_prefix) by (vm_compute; reflexivity).
  injection Hcf as <-. iIntros "#Htab HG HK". step.
  iApply wp_call_bind; [vx | exact Hget | reflexivity |]. iNext.
  iApply (wp_hello_get_errlist (glibc_program := strerror_program) with "Htab");
    [reflexivity|reflexivity|apply Z.mod_pos_bound; lia|].
  iNext. rewrite (Z.mod_small k (2^32) Hk).
  destruct (err_at k) as [[[b r] s]|] eqn:Hm.
  - iIntros "#Hs". iPoseProof "Hs" as "(%base & %reg & %ws & %Hsh & _)".
    destruct (str_shape_addr _ _ _ _ _ Hsh) as (Hp & He).
    cbn [ptr_addr] in Hp, He. iExists _. iSplit; [done|]. iNext.
    step. step. step. branch_as true. step. step_global Hdom.
    iApply (wp_report_translate w R.free R.free_succeeds Herr with "HG"). 4: vx.
    exact Htr. exact Hv. cbn; lia. iNext. iIntros "HG".
    iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" with "Hs HG").
  - iIntros "_". iExists _. iSplit; [done|]. iNext.
    step. step. step. branch. step. step_global Hfmt. step_global Hdom. step_global Hprefix.
    iApply (wp_report_translate w R.free R.free_succeeds Herr with "HG"). 4: vx.
    exact Htr. exact Hv. change (0 < ptr_addr unknown_prefix < 2^64); vm_compute; intuition congruence.
    iNext. iIntros "HG". iApply wp_call_bind; [vx|exact Hprint|reflexivity|]. iNext.
    iApply (wp_wand with "[HK HG]").
    { rewrite (Z.mod_small k (2^32) Hk) (Z.mod_small len (2^64) Hlen). iApply ("HK" with "HG"). }
    iIntros (result) "(%n & -> & HK)". iExists _. iSplit; [done|]. iNext.
    iApply wp_ret; [reflexivity|vx|]. by iNext.
Qed.

End strerror.
