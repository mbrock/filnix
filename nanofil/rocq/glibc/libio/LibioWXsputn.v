(** The wide file writer returns the number of characters it accepted.
    A newline can make it flush the stream before returning. Even if
    that flush fails, the writer returns the count it had already
    accepted and gives the formatter its entire stage back. *)

From Glibc Require Import Unit_string_memcpy_os Unit_string_mempcpy_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioWOverflowDispatch LibioWOverflowWrite LibioWXsputnWords LibioWXsputnRoom LibioWXsputnWindow
  LibioWXsputnSelect LibioWXsputnTail LibioWXsputnRemainder LibioWXsputnCopy WideWriteSpec WideBytes CBlocks.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Section writer.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation at_block e l := (ERun (mkFrame wprintf_xsputn_fn e [] None (body_at wprintf_xsputn_fn l)) : sexpr).
Context (vb : Z) (self : ptr) (E : iProp Σ).
Context `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn} (Hwrite : wdo_pending_spec vb self 1 E).

Local Lemma wf_return e fp dq s sr so cs Φ left :
  size cs <= 128 -> 0 <= left <= size cs -> reg e "v4" (WInt (size cs)) -> reg e "pr.5" (WInt left) ->
  file_wide ge vb self fp 1 -∗ E -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wcount_post vb self E fp dq s sr so cs Φ -∗ WP (at_block e "L183") {{ Φ }}.
Proof using Type.
  intros N R Hn Hleft. iIntros "HF HE Hs Hcs HK". body_start wprintf_xsputn_fn "L183"%string. step.
  iApply wp_ret; [reflexivity|vx|]. iNext. norm. unwrap2. iApply ("HK" with "[%] HF HE Hs Hcs"). lia.
Qed.

Local Ltac open_window := iDestruct "Hwin" as "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)".
Local Ltac close_window := rewrite /write_window; iFrame "Hf Hfl Hwd Hl Hbase Hcur Hend Hstop Hshort Hb".
Local Ltac read_cursor field := load "Hf" "Hwd" "Hl"; step; check "Hl"; load_wpos "Hl" field "Hb".

Local Lemma wf_flush e fb dq s sr so cs Φ left flush :
  size cs <= 128 -> 0 <= left <= size cs -> wf_finish_regs e fb (size cs) flush -> reg e "pr.5" (WInt left) ->
  file_wide ge vb self (obj fb) 1 -∗ E -∗ liveq dq s sr -∗ bytesq dq s so (stage_bytes cs) -∗
  wcount_post vb self E (obj fb) dq s sr so cs Φ -∗ WP (at_block e "L181") {{ Φ }}.
Proof using Type*.
  intros N R (Hfp & Hn & Hck & H6) Hleft. iIntros "HF HE Hs Hcs HK".
  iDestruct (wide_pending with "HF") as (wd w i) "HP".
  iDestruct (pending_write_window with "HP") as (fb' fr wr fl j (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & F & B & Hi & Hj)) "[Hwin Hclose]".
  injection Eq as <-. open_window. iEval (rewrite <-(wpos_zero wd w)) in "Hbase".
  body_start wprintf_xsputn_fn "L181"%string. step. check "Hf". read_cursor "Hbase". read_cursor "Hcur". read_cursor "Hbase".
  do 3 step. step_named. pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hi) as (Hb & Ai & C).
  cbn [wpos ptr_addr] in Ai. rewrite Z.add_0_r wflush_count in E0; [|lia..]. subst x.
  iEval (rewrite wpos_zero) in "Hbase". iDestruct ("Hclose" $! i with "[%] [-HE Hs Hcs HK]") as "HP"; [done|close_window|].
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext. norm. rewrite wpos_zero. unwrap2.
  iApply (Hwrite _ (obj fb) wd w i with "HP HE"); [reflexivity|]. iNext. iIntros (ok) "HP HE".
  destruct ok; [iDestruct (pending_wide with "HP") as "HF"|iRename "HP" into "HF"]; resume; step; step;
    iApply (wf_return _ _ dq s sr so cs Φ left with "HF HE Hs Hcs HK"); try assumption; lookups; done.
Qed.

Local Lemma wf_finish fb dq s sr so cs Φ : size cs <= 128 ->
  wcount_post vb self E (obj fb) dq s sr so cs Φ -∗ wf_after_copy vb self E fb dq s sr so cs Φ.
Proof using Type*.
  intros N. iIntros "HK". iIntros (e left flush (G & Hleft & R & Hflush)) "HF HE Hs Hcs".
  destruct G as (Hfp & Hn & Hck & H6). body_start wprintf_xsputn_fn "L172"%string.
  destruct Hflush as [Z0 | Z1]; subst flush; branch; step.
  - branch. step. iApply (wf_return _ _ dq s sr so cs Φ left with "HF HE Hs Hcs HK"); try assumption; lookups; done.
  - iDestruct (wide_write_window with "HF") as (fb' fr wd wr fl w i j (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & F & B & Hi & Hj)) "[Hwin Hclose]".
    injection Eq as <-. open_window. iEval (rewrite <-(wpos_zero wd w)) in "Hbase".
    step. check "Hf". read_cursor "Hcur". read_cursor "Hbase". do 5 step. iEval (rewrite wpos_zero) in "Hbase".
    iDestruct ("Hclose" $! i with "[%] [-HE Hs Hcs HK]") as "HF"; [done|close_window|].
    branch_cases; step.
    + iApply (wf_return _ _ dq s sr so cs Φ left with "HF HE Hs Hcs HK"); try assumption; lookups; done.
    + iApply (wf_flush _ fb dq s sr so cs Φ left 1 with "HF HE Hs Hcs HK"); try assumption; try unfold wf_finish_regs; repeat split; lookups; done.
Qed.

Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hfn : find_fn ge (TAtom "zmemmove") = None) (Hsym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Context `{!Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
  !Defines ge "__wmempcpy" wmempcpy_fn, !Defines ge "__GI___woverflow" woverflow_fn,
  !Defines ge "__GI__IO_wdefault_xsputn" wdefault_xsputn_fn} (Hov : woverflow_spec vb self E woverflow_fn).

(** The formatter calls the file writer on one staging buffer at a
    time. A zero count returns immediately, without touching the stream.
    Longer greetings use the same rule once for each flush. *)
Lemma wfile_xsputn_has_spec : wprintf_xsputn_call_spec vb self E.
Proof using Type*.
  intros fr fp s sr dq cs Φ Hs Hsa Hse Hsr N V C. injection C as <-. iIntros "HF HE Hs Hcs HK". step. step.
  destruct (Z.eq_dec (size cs) 0) as [Hz|Hnz].
  - branch_as false. step. iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" $! 0 with "[%] HF HE Hs Hcs"). lia.
  - branch_as true. step. iDestruct (wide_write_window with "HF") as (fb frr wd wr fl w i j (Eq & _ & _ & _ & _ & _ & _ & _ & _ & _ & B & Hi & Hj)) "[Hwin Hclose]".
    iDestruct ("Hclose" $! i with "[%] Hwin") as "HF"; [done|]. subst fp.
    iApply (wp_wfile_copy_input Hmove Hfn Hsym vb self E Hov _ fb dq s sr 48 cs with "HF HE Hs Hcs [-]"); try assumption; try lia.
    + unfold wf_input. repeat split; lookups; unwrap2; reflexivity.
    + by iApply wf_finish.
Qed.
End writer.
