(** When overflow sets the putting bit, it rewinds both buffers. The
    stream has no pending narrow bytes or wide characters after the
    switch. Only the wide write end depends on the buffering flags. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv FileIdle LibioLogic LibioPutsInv
  LibioWIdle LibioWOverflowDispatch LibioWXsputnWindow LibioWXsputnRoom
  LibioWOverflowSetp LibioWOverflowSetWide CBlocks.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation obj b := (mkPtr b (Obj b)).

Section setup.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e l := (ERun (mkFrame wfile_overflow_fn e [] None (body_at wfile_overflow_fn l)) : sexpr).

(** A line-buffered or unbuffered stream advertises no room after
    switching to output. Its write end becomes the write pointer,
    although the buffer still has room for its first character. *)
Local Lemma wo_tight e fb fr ch wd wr w Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w -> 0 < window_size w -> wo_setup_regs e fb ch ->
  wo_lives fb fr wd wr w -∗ pcell wd 32 (wpos wd w 0) -∗ pcell wd 40 (wpos wd w (window_size w)) -∗
  (∀ ee, ⌜wo_setup_regs ee fb ch⌝ -∗ wo_lives fb fr wd wr w -∗ pcell wd 32 (wpos wd w 0) -∗
    pcell wd 40 (wpos wd w 0) -∗ WP (run ee "L17") {{ Φ }}) -∗ WP (run e "L195") {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Size (Hfp & Hch & Hck & H7).
  iIntros "(Hf & Hwd & Hl & Hb) Hcur Hend HK". body_start wfile_overflow_fn "L195"%string.
  step. check "Hf". load "Hf" "Hwd" "Hl". step. load "Hf" "Hwd" "Hl". step. check "Hl".
  load_wpos "Hl" "Hcur" "Hb". check "Hl". store "Hl" "Hend". do 2 step.
  iApply ("HK" with "[%] [$] Hcur Hend"). unfold wo_setup_regs. split_and!; lookups; done.
Qed.

(** Both the allocation path and the path with a buffer already in
    place start the switch with the same read cursors. They need not
    agree on the old write cursors: all three are overwritten. *)
Lemma wp_wo_switch e fb fr ch wd wr w nb fl b rb wb wp we stop wwb wwp wwe Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w -> 0 < window_size w ->
  in_buf fb nb b -> in_buf fb nb stop -> wo_setup_regs e fb ch ->
  wo_lives fb fr wd wr w -∗ wo_wide_cursors wd w (window_base wd w) (window_base wd w) (window_base wd w) wwb wwp wwe -∗
  int_cell fb off_flags fl -∗ buf_idle nb -∗ pcell fb 8 b -∗ pcell fb 16 b -∗ pcell fb 24 rb -∗
  pcell fb 32 wb -∗ pcell fb 40 wp -∗ pcell fb 48 we -∗ pcell fb 64 stop -∗
  (∀ ee j, ⌜wo_setup_regs ee fb ch /\ 0 <= j <= window_size w⌝ -∗ wo_lives fb fr wd wr w -∗
    wo_wide_cursors wd w (window_base wd w) (window_base wd w) (window_base wd w) (window_base wd w) (wpos wd w 0) (wpos wd w j) -∗
    int_cell fb off_flags (Z.lor fl 2048) -∗ buf_idle nb -∗ pcell fb 8 b -∗ pcell fb 16 b -∗ pcell fb 24 b -∗
    pcell fb 32 b -∗ pcell fb 40 b -∗ pcell fb 48 stop -∗ pcell fb 64 stop -∗ WP (run ee "L17") {{ Φ }}) -∗ WP (run e "L36") {{ Φ }}.
Proof using Type.
  intros Fb Fa Fe Fr Wd Wa We Wr B Size R S G. iIntros "Hl Hwc Hfl Hb Hrp Hre Hrb Hwb Hwp Hwe Hstop HK".
  iApply (wp_wo_wide_switch with "Hl Hwc [-]"); try eassumption. iIntros (e' G') "(Hf & Hwd & Hl & Hbuf) Hwc".
  iApply (wp_wo_narrow_switch _ fb fr fl ch nb b rb wb wp we stop with "[Hf Hfl Hb Hrp Hre Hrb Hwb Hwp Hwe Hstop] [-]"); try eassumption; [rewrite /wo_narrow_cells; by iFrame|].
  iIntros (ee tight Ge) "(Hf & Hfl & Hb & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hstop)". destruct tight.
  - iDestruct "Hwc" as "(W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7)".
    iApply (wo_tight ee fb fr ch wd wr w with "[Hf Hwd Hl Hbuf] W4 W5 [-]"); try eassumption; [by iFrame|].
    iIntros (ef Gf) "Hl W4 W5". iApply ("HK" $! ef 0 with "[%] Hl [W0 W1 W2 W3 W4 W5 W6 W7] Hfl Hb Hrp Hre Hrb Hwb Hwp Hwe Hstop");
      [split; [done|lia]|rewrite /wo_wide_cursors; by iFrame].
  - iApply ("HK" $! ee (window_size w) with "[%] [$] Hwc Hfl Hb Hrp Hre Hrb Hwb Hwp Hwe Hstop"). split; [done|lia].
Qed.
End setup.
