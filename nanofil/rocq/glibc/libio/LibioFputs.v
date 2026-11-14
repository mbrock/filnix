From Glibc Require Import GlibcProgram.
(** The triple of `c: fputs(s, fp)` (LibioPutsCode.v,
    libio/iofputs.c) over a string at any share and a stream as
    LibioPutsInv.v's [file_at] has it ([wp_glibc__IO_fputs]):

    ```c
    size_t len = strlen (str);
    int result = EOF;
    _IO_acquire_lock (fp);
    if ((_IO_vtable_offset (fp) != 0 || _IO_fwide (fp, -1) == -1)
        && _IO_sputn (fp, str, len) == len)
      result = 1;
    _IO_release_lock (fp);
    return result;
    ```

    Each part of the function is proved in its own file, and this
    file adds the branch on whether the whole string was written and
    puts the parts together. The write through the jump table stays a
    hypothesis of LibioPutsInv.v.

    | Part | Blocks | File |
    |---|---|---|
    | the length and the lock | start to `c: L29` | LibioFputsLock.v |
    | the orientation and the write | `c: L113` to `c: iw_1.join` | LibioFputsCall.v, over [xsputn_spec] |
    | the result, 1 or `c: EOF` | `c: L162`, `c: L106` | here |
    | the release | `c: L107` | LibioFputsUnlock.v | *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString StrlenLogic LibioXsputnCode LibioPutsCode LibioPutsInv LibioPutsMode LibioFputsLock
  LibioFputsUnlock LibioFputsCall.
From Glibc Require FileInv LibioCloseSteps LibioFputsCall LibioFputsLock LibioFputsUnlock LibioLogic LibioPutsInv OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioFputsCall LibioFputsUnlock LibioFputsLock LibioPutsInv LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context (vb : Z)
  (vreg : region)
  (Rx : iProp Σ).
Context (Hxs_fn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hxs : xsputn_spec w0 registry ge vb Rx).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L107` of `c: fputs` over a [file_at] stream whose lock is
    held once: LibioFputsUnlock.v's [wp_fputs_unlock], the lock free
    again after it. *)
Lemma wp_fputs_L107 e r fb m sb sreg Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v2") e = Some (WPtr fp) -> lookup (TAtom "chk0") e = Some (WPtr fp) ->
  lookup (TAtom "pr.1") e = Some (WInt r) -> 0 <= r < 2 ^ 32 ->
  single_ro ge sb sreg -∗ file_at vb (ow_self w0) fp m (Some 0) -∗
  ▷ (file_at vb (ow_self w0) fp m None -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_fputs e [] None (Exec (TAtom "L107") (b_insts fp_L107) (b_jump fp_L107)))
        : sexpr) {{ Φ }}.
Proof.
  intros fp Hv2 Hc0 Hr Hrr. subst fp. iIntros "#Hs Hf HK".
  iDestruct (file_at_open with "Hf") as (fb' freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (Hfp & Hfb & Hfal & Hfend & Hfreg & Hflr & Hul & Hmv). injection Hfp as <-.
  iDestruct "Hlk" as (lb' lreg Hlb) "Hlk". injection Hlb as <-.
  pose proof Hul as Hul'. unfold has, io_user_lock in Hul'. apply negb_false_iff, Z.eqb_eq in Hul'.
  iApply (wp_fputs_unlock with "Hs Hl [$Hfl //] Hlp Hlk"); try eassumption.
  iNext. iIntros "Hl Hfl Hlp Hlk". iApply "HK".
  iApply ("Hcl" with "[//] Hl Hfl Hlp [Hlk] Hmd Hvtp"). iExists lb, lreg. iSplit; done.
Qed.

(** `c: fputs(s, fp)`, s at p the string at the share dq and fp a
    [file_at] stream at any mode with its lock free: the string and the
    stream come back, the stream oriented ([oriented]) and its lock
    free, and the result is 1 when the whole string was written, else
    `c: EOF`. *)
Lemma wp_glibc__IO_fputs fr p dq s fp mode sb sreg Φ :
  call_frame glibc__IO_fputs [WPtr p; WPtr fp] = Some fr ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  ptr_addr (ow_self w0) <> 0 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ word_string dq p s -∗
  file_at vb (ow_self w0) fp mode None -∗ Rx -∗
  ▷ (∀ r, ⌜r = 1 \/ r = 2 ^ 32 - 1⌝ -∗ word_string dq p s -∗
     file_at vb (ow_self w0) fp (oriented mode) None -∗ Rx -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hstr Hsz. iIntros "#Hvt #Hs Hstr Hf HRx HK".
  iDestruct (file_at_open with "Hf") as (fb freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (-> & Hfb & Hfal & Hfend & Hfreg & Hflr & Hul & Hmv).
  iDestruct "Hlk" as (lb' lreg Hlb) "Hlk". injection Hlb as <-.
  pose proof Hul as Hul'. unfold has, io_user_lock in Hul'. apply negb_false_iff, Z.eqb_eq in Hul'.
  (* The string measured and the lock taken. *)
  iApply (wp_fputs_start Hreg Hext with "Hs Hstr Hl Hfl Hlp Hlk"); try eassumption.
  iNext. iIntros (e (Hv0 & Hv6 & Hv2 & Hc0)) "Hstr Hl Hfl Hlp Hlk".
  iDestruct ("Hcl" $! mode (Some 0) with "[//] Hl Hfl Hlp [Hlk] Hmd Hvtp") as "Hf";
    [iExists lb, lreg; iSplit; done|].
  (* The orientation and the write. *)
  iApply (wp_fputs_L113 vb vreg Rx Hxs_fn Hxs with "Hvt Hf Hstr HRx"); try eassumption.
  iNext. iIntros (e1 c (Hsame & Hc)) "Hf Hstr HRx". rewrite keeps_forall in Hsame; cbn [atoms List.map List.In] in Hsame.
  assert (Hv2' : lookup (TAtom "v2") e1 = Some (WPtr (mkPtr fb (Obj fb)))) by (rewrite Hsame; auto).
  assert (Hc0' : lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr fb (Obj fb)))) by (rewrite Hsame; auto).
  clear Hsame. unfold fp_j162.
  iApply wp_branch; [vx | iNext].
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] => destruct (n =? 0) end;
    cbn [edge_label].
  - (* The write fell short: L106, then L107 with `c: EOF`. *)
    step. step. iApply wp_enter; [reflexivity | vx | iNext].
    iApply (wp_fputs_L107 _ (2 ^ 32 - 1) with "Hs Hf"); [lk_prove | lk_prove | lookups; reflexivity | lia |].
    iNext. iIntros "Hf". iApply ("HK" with "[%] Hstr Hf HRx"). right. reflexivity.
  - (* The whole string written: L107 with 1. *)
    iApply wp_enter; [reflexivity | vx | iNext].
    iApply (wp_fputs_L107 _ 1 with "Hs Hf"); [lk_prove | lk_prove | lookups; reflexivity | lia |].
    iNext. iIntros "Hf". iApply ("HK" with "[%] Hstr Hf HRx"). left. reflexivity.
Qed.

End rules.
