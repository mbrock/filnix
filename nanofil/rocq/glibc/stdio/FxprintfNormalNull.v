(** Error prints its prefix, errno text and newline through the same
    function, __fxprintf. This proof connects that function's argument copy,
    stderr selection and locking to its call to the byte-oriented formatter.
    The caller must still prove what the formatter does with the supplied
    format and arguments; its result may indicate failure.

    Printing a newline requires access to stderr, just like printing any
    other text. The existing proof of error does not yet give its newline
    call that access. It must lend the stderr pointer and stream to the
    call and recover them afterward. The stream's lock is initially free;
    earlier calls must preserve that state. Error itself takes no outer lock. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode FxprintfNormalCall VfxprintfNarrow VfxprintfSelect VfxprintfCall.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section wrapper.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hregistry : holds_os registry) (Hext : sys_external ge).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Lemma wp_fxprintf_normal_null fb freg fl lb lbreg fmt ys md dqf fmtreg sb sreg gb greg
    (R E : iProp Σ) (Q : Z -> iProp Σ) Φ :
  forallb snapshot_word ys = true ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= ptr_addr fmt < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  (forall ap, vfxprintf_formatter fb freg fl lb lbreg fmt ap 0 md dqf fmtreg
    (fun p => fx_va p (WPtr null :: WPtr fmt :: ys)) R Q) ->
  single_ro ge sb sreg -∗ live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗
  live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ R -∗ E -∗
  ▷ (∀ r, live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗
    live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
    lock_state lb lbreg 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗
    (∃ ap, fx_va ap (WPtr null :: WPtr fmt :: ys)) -∗ Q r -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (fxprintf_normal_frame null fmt ys) : gexpr) {{ Φ }}.
Proof.
  intros Hys Hfn Hg Hgb Hga Hge Hgr Hfb Hal Hend Hreg Huser Hfmtr Hmd Hself Hselfr Hcall.
  iIntros "#Hs Hgl Hgp Hl Hfl Hlp Hlk Hmd Hfmt HR HE HK".
  set (P := (single_ro ge sb sreg ∗ live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗ live fb freg ∗ int_cell fb 0 fl ∗
    pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
    int_cell fb 192 md ∗ live_capq dqf (ptr_cap fmt) fmtreg ∗ R)%I).
  set (S := fun k => (∃ r, ⌜k = r mod 2 ^ 32⌝ ∗ live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗
    live fb freg ∗ int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
    live_capq dqf (ptr_cap fmt) fmtreg ∗ (∃ ap, fx_va ap (WPtr null :: WPtr fmt :: ys)) ∗ Q r)%I).
  assert (Hcallee : forall ap, ⊢ fx_va ap (WPtr null :: WPtr fmt :: ys) -∗ P -∗
    WP (ERun (vfxprintf_frame null fmt ap 0) : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ S r }}).
  { intros ap. iIntros "HV (#Hs & Hgl & Hgp & Hl & Hfl & Hlp & Hlk & Hmd & Hfmt & HR)".
    iApply (wp_vfxprintf_null Hregistry Hext fb freg fl lb lbreg fmt ap 0 md dqf fmtreg sb sreg
      (fun p => fx_va p (WPtr null :: WPtr fmt :: ys)) R emp Q _
      with "Hs Hgl Hgp Hl Hfl Hlp Hlk Hmd Hfmt HV HR [] []"); try assumption; try apply Hcall.
    { done. }
    iNext. iIntros (r) "Hgl Hgp Hl Hfl Hlp Hlk Hfmt HV HQ _".
    iExists (r mod 2 ^ 32). iSplit; [done |]. unfold S. iExists r.
    iFrame "Hgl Hgp Hl Hfl Hlp Hlk Hfmt HQ". iSplit; [done |].
    iExists ap. iExact "HV". }
  iApply (wp_fxprintf_normal null fmt ys glibc_vfxprintf (fun ap => vfxprintf_frame null fmt ap 0)
    P E S with "[$Hs $Hgl $Hgp $Hl $Hfl $Hlp $Hlk $Hmd $Hfmt $HR] HE [HK]");
    try assumption; [intro; apply vfxprintf_call_frame |].
  iNext. iIntros (k) "HS HE". unfold S.
  iDestruct "HS" as (r ->) "(Hgl & Hgp & Hl & Hfl & Hlp & Hlk & Hfmt & HV & HQ)".
  rewrite Z.mod_mod; [|lia]. iApply ("HK" with "Hgl Hgp Hl Hfl Hlp Hlk Hfmt HV HQ HE").
Qed.
End wrapper.
