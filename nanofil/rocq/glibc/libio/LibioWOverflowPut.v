(** With the stream ready to write, overflow either flushes on request
    or appends one character. A full buffer must flush successfully
    before it can accept that character. A failed flush after the
    store also returns WEOF, but does not undo the store. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioCloseSteps LibioWIdle LibioOverflowBase
  LibioWOverflowDispatch LibioWXsputnWindow LibioWXsputnRoom LibioWOverflowWrite LibioWOverflowFlush LibioWOverflowStore CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Section put.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ).
Context `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn} (Hwrite : wdo_pending_spec vb self 1 E).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e at_ := (ERun (mkFrame wfile_overflow_fn e [] None at_) : sexpr).
Local Abbreviation at_block e l := (run e (body_at wfile_overflow_fn l)).

Definition wo_post fb ch (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ := ∀ r,
  ⌜ovf_ret ch r⌝ -∗ file_wide ge vb self (obj fb) 1 -∗ E -∗ Φ (Ret (WInt r)).

Local Lemma wo_return e fb ch Φ : ch <> 2^32-1 -> 0 <= ch < 2^32 -> reg e "v2" (WInt ch) ->
  file_wide ge vb self (obj fb) 1 -∗ E -∗ wo_post fb ch Φ -∗ WP (at_block e "L334") {{ Φ }}.
Proof using Type.
  intros Ne C Hch. iIntros "HF HE HK". body_start wfile_overflow_fn "L334"%string. iApply wp_ret; [reflexivity|vx|].
  iNext. unwrap2. iApply ("HK" with "[%] HF HE"). right. by rewrite (proj2 (Z.eqb_neq _ _) Ne).
Qed.

Local Lemma wo_after_flush e fb ch wd w i Φ : 0 <= ch < 2^32 -> ch <> 2^32-1 -> wo_regs AfterStore e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗ wo_post fb ch Φ -∗ WP (at_block e "L332") {{ Φ }}.
Proof using Type*.
  intros C Ne G. iIntros "HP HE HK". iApply (wp_wo_flush vb self E Hwrite AfterStore with "HP HE [-]"); [done|].
  iIntros (ee ok ((Hfp & Hch & Hck & H85) & Hv)) "HP HE". destruct ok; cbn [wo_flush_result] in Hv;
    cbn [wo_flush_end]; body_start wfile_overflow_fn "L356"%string; step; branch; step.
  - iDestruct (pending_wide with "HP") as "HF". iApply (wo_return with "HF HE HK"); try assumption; lookups; done.
  - iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" with "[%] HP HE"). by left.
Qed.

Local Lemma wo_after e fb ch wd w i Φ : 0 <= ch < 2^32 -> ch <> 2^32-1 -> wo_regs AfterStore e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗ wo_post fb ch Φ -∗ WP (run e wo_test_flags) {{ Φ }}.
Proof using Type*.
  intros Ch Ne (Hfp & Hch & Hck & H85). iIntros "HP HE HK".
  iDestruct (pending_write_window with "HP") as (fb' fr wr fl j (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & F & B & Hi & Hj)) "[Hwin Hclose]".
  injection Eq as <-. iDestruct "Hwin" as "(Hf & [%V Hfl] & Hrest)".
  iAssert (∀ ee (flush : bool), ⌜wo_regs AfterStore ee fb ch⌝ -∗ live fb fr -∗ bytes fb off_flags (le_bytes fl 4) -∗
    WP (at_block ee (if flush then "L332" else "L334")) {{ Φ }})%I with "[-Hf Hfl]" as "Hend".
  { iIntros (ee flush G) "Hf Hfl". iDestruct ("Hclose" $! i with "[%] [-HE HK]") as "HP"; [done| |].
    { rewrite /write_window. iFrame "Hf Hrest". by iSplit. }
    destruct flush; [by iApply (wo_after_flush with "HP HE HK")|]. iDestruct (pending_wide with "HP") as "HF".
    iApply (wo_return with "HF HE HK"); [done|done|apply G]. }
  unfold wo_test_flags. check "Hf". load_s32 "Hf" "Hfl". step. branch_cases; step.
  - load_s32 "Hf" "Hfl". step. branch_cases; step.
    + branch. step. iApply ("Hend" $! _ false with "[%] Hf Hfl"). unfold wo_regs. split_and!; lookups; done.
    + do 3 step. branch_cases; step; [iApply ("Hend" $! _ false with "[%] Hf Hfl")|iApply ("Hend" $! _ true with "[%] Hf Hfl")]; unfold wo_regs; split_and!; lookups; done.
  - branch. step. iApply ("Hend" $! _ true with "[%] Hf Hfl"). unfold wo_regs. split_and!; lookups; done.
Qed.

Local Lemma wo_append e fb ch wd w i Φ : 0 <= ch < 2^32 -> ch <> 2^32-1 -> i < window_size w -> wo_regs BeforeStore e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗ wo_post fb ch Φ -∗ WP (at_block e "L262") {{ Φ }}.
Proof using Type*.
  intros C Ne Room G. iIntros "HP HE HK". iApply (wp_wo_store vb self e fb ch wd w i with "HP [-]"); try assumption.
  iIntros (ee G') "HP". by iApply (wo_after with "HP HE HK").
Qed.

Local Lemma wo_full e fb ch wd w i Φ : 0 <= ch < 2^32 -> ch <> 2^32-1 -> 0 < window_size w -> wo_regs BeforeStore e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗ wo_post fb ch Φ -∗ WP (at_block e "L260") {{ Φ }}.
Proof using Type*.
  intros C Ne Room G. iIntros "HP HE HK". iApply (wp_wo_flush vb self E Hwrite BeforeStore with "HP HE [-]"); [done|].
  iIntros (ee ok ((Hfp & Hch & Hck & H85) & Hv)) "HP HE". destruct ok; cbn [wo_flush_result] in Hv;
    cbn [wo_flush_end]; body_start wfile_overflow_fn "L281"%string; step; branch; step.
  - iApply (wo_append with "HP HE HK"); try assumption. unfold wo_regs. split_and!; lookups; done.
  - iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" with "[%] HP HE"). by left.
Qed.

(** The setup code gives the writer a nonempty allocation. Even if
    its last slot is already full, a successful flush puts the cursor
    back at index zero in that same allocation. *)
Lemma wp_wo_put e fb ch wd w i Φ : 0 <= ch < 2^32 -> 0 < window_size w -> wo_regs FlushRequest e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗ wo_post fb ch Φ -∗ WP (at_block e "L17") {{ Φ }}.
Proof using Type*.
  intros C Room (Hfp & Hch & Hck & _). iIntros "HP HE HK". body_start wfile_overflow_fn "L17"%string. step.
  destruct (Z.eq_dec ch (2^32-1)) as [->|Ne].
  - branch. step. iApply (wp_wo_flush vb self E Hwrite FlushRequest with "HP HE [-]"); [unfold wo_regs; split_and!; lookups; done|].
    iIntros (ee ok (G & Hv)) "HP HE". cbn [wo_flush_result] in Hv. cbn [wo_flush_end]. body_start wfile_overflow_fn "L218"%string.
    destruct ok; [iDestruct (pending_wide with "HP") as "HF"|iRename "HP" into "HF"]; iApply wp_ret; [reflexivity|vx| |reflexivity|vx|];
      iNext; iApply ("HK" with "[%] HF HE"); [by right|by left].
  - branch_as true. step. iDestruct (pending_write_window with "HP") as (fb' fr wr fl j (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & F & B & Hi & Hj)) "[Hwin Hclose]".
    injection Eq as <-. iDestruct "Hwin" as "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)".
    step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hcur" "Hb".
    load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hstop" "Hb". do 3 step.
    iDestruct ("Hclose" $! i with "[%] [-HE HK]") as "HP"; [done|rewrite /write_window; by iFrame|].
    pose proof (wpos_bounds _ _ _ Hwd ltac:(lia) B Hi) as (Ba & Ai & Cap).
    pose proof (wpos_bounds _ _ (window_size w) Hwd ltac:(lia) B ltac:(lia)) as (_ & Ae & _).
    cbn [ptr_addr wpos] in Ai, Ae. destruct (Z.eq_dec i (window_size w)) as [->|N].
    + branch_as false. step. iApply (wo_full with "HP HE HK"); try assumption. unfold wo_regs. split_and!; lookups; unwrap2; done.
    + branch_as true. step. iApply (wo_append with "HP HE HK"); try assumption; try lia. unfold wo_regs. split_and!; lookups; unwrap2; done.
Qed.
End put.
