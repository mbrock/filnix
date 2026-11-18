(** A wide stream can already be putting when overflow finds that it
    has no wide buffer. The entry checks both the flag and the wide
    write base before it skips setup. If it has to switch a stream
    with an existing buffer, the wide read pointer is at the base,
    not at the end of that allocation. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioWOverflowDispatch LibioWXsputnWindow LibioWXsputnRoom LibioWOverflowWrite LibioWOverflowFlush
  LibioWOverflowPut LibioWOverflowSetp CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Lemma window_cases wd w : 0 < wd -> window_bound w -> w = WbNone \/
  (0 < ptr_addr (window_base wd w) /\ 0 < window_size w).
Proof. intros H B. destruct w as [| |b sz]; [by left|right; cbn; lia|]. destruct B as (? & ? & ? & ?).
  pose proof (Z.div_mod sz 4 ltac:(lia)). right. cbn. lia. Qed.

Section entry.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ).
Context `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn} (Hwrite : wdo_pending_spec vb self 1 E).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e l := (ERun (mkFrame wfile_overflow_fn e [] None (body_at wfile_overflow_fn l)) : sexpr).

(** The two setup paths meet after they have installed a nonempty
    buffer. The allocation path carries the null address it compared
    against, since it uses that address a second time. *)
Definition wo_prepare existing : Prop := forall e fb ch wd w i Φ,
  0 <= ch < 2^32 -> wo_setup_regs e fb ch ->
  (if existing : bool then 0 < window_size w else w = WbNone /\ reg e "v43" (WInt 0)) ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗ wo_post vb self E fb ch Φ -∗
  WP (run e (if existing then "L36" else "L34")) {{ Φ }}.
Context (Hexisting : wo_prepare true) (Hfresh : wo_prepare false).

Local Lemma wo_select_buffer e fb ch wd w i Φ : 0 <= ch < 2^32 -> wo_regs FlushRequest e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗ wo_post vb self E fb ch Φ -∗ WP (run e "L15") {{ Φ }}.
Proof using Type*.
  intros Ch (Hfp & Hch & Hck & _). iIntros "HP HE HK".
  iDestruct (pending_write_window with "HP") as (fb' fr wr fl j (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & F & B & Hi & Hj)) "[Hwin Hclose]".
  injection Eq as <-. iDestruct "Hwin" as "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)".
  iEval (rewrite <-(wpos_zero wd w)) in "Hbase". body_start wfile_overflow_fn "L15"%string.
  step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hbase" "Hb". do 3 step.
  iEval (rewrite wpos_zero) in "Hbase". iDestruct ("Hclose" $! i with "[%] [-HE HK]") as "HP"; [done|rewrite /write_window; by iFrame|].
  pose proof (wpos_bounds wd w 0 Hwd ltac:(lia) B ltac:(lia)) as (_ & R & _). cbn [wpos ptr_addr] in R.
  destruct (window_cases wd w Hwd B) as [->|(Base & Room)].
  - branch. step. iApply (Hfresh _ fb ch wd WbNone i with "HP HE HK"); try assumption; try unfold wo_setup_regs; split_and!; lookups; unwrap2; done.
  - branch_as true. step.
    iDestruct "HP" as (fbb rr st nb tw tm wr' j' P G) "(Hf & Hfields & Hlk & Hnb & Hd)". pose proof G as (Eq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & _). injection Eq as <-.
    iDestruct "Hfields" as "(%Len & Hfl & Hps & Hfd & Hf2 & Hof & %C & Hcol & Hlock & Hoff & Hcv & Hwd & Hfr & Hbuf & Hm & Htot & Hvt)".
    iDestruct "Hd" as (ib ie ob oe ifl icnt ofl ocnt sb scs U) "(Hl & Hw & Hst & Ha & Hin & Hout & Hsb & Hpad & Haux & Hwvt & Hb)".
    pose proof U as (Wd & Wa & We & Wr & _). iEval (rewrite /window_slots /=) in "Hw".
    iDestruct "Hw" as "(Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hstop & Htail)". rewrite W.
    iEval (rewrite <-(wpos_zero wd w)) in "Hrp". step. load "Hf" "Hwd" "Hl". check "Hl". load_wpos "Hl" "Hrp" "Hb".
    change (woff_ptr 7) with 56.
    load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hstop" "Hb". do 3 step.
    pose proof (wpos_bounds _ _ (window_size w) Hwd ltac:(lia) B ltac:(lia)) as (_ & Re & _). cbn [wpos ptr_addr] in Re.
    branch_as true. step. iApply (Hexisting _ fb ch wd w i with "[-HE HK] HE HK"); try assumption; [unfold wo_setup_regs; split_and!; lookups; unwrap2; done|].
    iExists fb, rr, st, nb, tw, tm, wr', j'. iSplit; [done|]. rewrite /file_wide_at. iFrame "Hf Hlk Hnb". iSplit; [done|].
    iSplitL "Hfl Hps Hfd Hf2 Hof Hcol Hlock Hoff Hcv Hwd Hfr Hbuf Hm Htot Hvt"; [rewrite /file_fields W; by iFrame|].
    iExists ib, ie, ob, oe, ifl, icnt, ofl, ocnt, sb, scs. iSplit; [done|]. rewrite /window_slots /=. iEval (rewrite wpos_zero) in "Hrp". by iFrame.
Qed.

Local Lemma wo_already e fb ch wd w i Φ : 0 <= ch < 2^32 -> wo_regs FlushRequest e fb ch ->
  file_pending ge vb self (obj fb) 1 wd w i -∗ E -∗ wo_post vb self E fb ch Φ -∗ WP (run e "L22") {{ Φ }}.
Proof using Type*.
  intros Ch (Hfp & Hch & Hck & _). iIntros "HP HE HK".
  iDestruct (pending_write_window with "HP") as (fb' fr wr fl j (Eq & Hfb & Hfa & Hfe & Hfr & Hwd & Hwa & Hwe & Hwr & F & B & Hi & Hj)) "[Hwin Hclose]".
  injection Eq as <-. iDestruct "Hwin" as "(Hf & Hfl & Hwd & Hl & Hbase & Hcur & Hend & Hstop & Hshort & Hb)".
  iEval (rewrite <-(wpos_zero wd w)) in "Hbase". body_start wfile_overflow_fn "L22"%string.
  step. check "Hf". load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hbase" "Hb". do 5 step.
  iEval (rewrite wpos_zero) in "Hbase". iDestruct ("Hclose" $! i with "[%] [-HE HK]") as "HP"; [done|rewrite /write_window; by iFrame|].
  pose proof (wpos_bounds wd w 0 Hwd ltac:(lia) B ltac:(lia)) as (_ & R & _). cbn [wpos ptr_addr] in R.
  destruct (window_cases wd w Hwd B) as [->|(Base & Room)].
  - branch. step. iApply (wo_select_buffer _ fb ch with "HP HE HK"); [done|unfold wo_regs; split_and!; lookups; done].
  - branch_as true. step. iApply (wp_wo_put vb self E Hwrite _ fb ch with "HP HE HK"); [done|done|unfold wo_regs; split_and!; lookups; done].
Qed.

Lemma wo_entry : woverflow_spec vb self E wfile_overflow_fn.
Proof using Type*.
  intros frame fp ch Φ Ch Call. injection Call as <-. iIntros "HF HE HK".
  iDestruct "HF" as (fb fr st nb wd w tw tm P) "(Hf & Hfields & Hlk & Hnb & Hd)".
  pose proof P as (-> & Hfa & Hfb & Hfe & Hfr & (F & _) & I & _).
  destruct I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N & _).
  specialize (N ltac:(lia)). change (has (fs_flags st) io_no_writes = false) in N. rename N into Nw.
  apply Bool.negb_false_iff, Z.eqb_eq in Nw. unfold io_no_writes in Nw.
  iDestruct "Hfields" as "(%Len & [%Fl Hfl] & Hp & Hfd & Hf2 & Ho & %Col & Hc & Hlock & Hof & Hcv & Hwd & Hfr & Hbuf & Hm & Htot & Hvt)".
  unfold file_size in Hfe. step. norm. check "Hf". load_s32 "Hf" "Hfl". step. norm. rewrite Nw. branch. step. load_s32 "Hf" "Hfl". do 2 step.
  iAssert (file_wide ge vb self (obj fb) 1) with "[-HE HK]" as "HF".
  { iExists fb, fr, st, nb, wd, w, tw, tm. rewrite /file_wide_at. iFrame "Hf Hlk Hnb Hd". iSplit; [done|]. rewrite /file_fields /int_cell. by iFrame. }
  iDestruct (wide_pending with "HF") as (wd' w' i) "HP". branch_cases; step.
  - iApply (wo_already _ fb ch with "HP HE HK"); [done|unfold wo_regs; split_and!; lookups; unwrap2; done].
  - branch. step. iApply (wo_select_buffer _ fb ch with "HP HE HK"); [done|unfold wo_regs; split_and!; lookups; unwrap2; done].
Qed.
End entry.
