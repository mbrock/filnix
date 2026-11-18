(** When overflow switches to writing it resets both sets of cursors.
    The wide write pointer starts at the wide read pointer. Glibc then
    sets the wide write end to the physical end, or pulls it back to
    the cursor if the stream is line-buffered or unbuffered. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioWOverflowDispatch LibioWXsputnWindow LibioWXsputnRoom LibioWOverflowWrite LibioWOverflowSetp CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation obj b := (mkPtr b (Obj b)).

Section cursors.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e at_ := (ERun (mkFrame wfile_overflow_fn e [] None at_) : sexpr).

Definition wo_lives fb fr wd wr w : iProp Σ := live fb fr ∗ pcell fb off_wide (obj wd) ∗ live wd wr ∗ wbuf_idle w.
Definition wo_wide_cursors wd w rp re rb wb wp we : iProp Σ :=
  pcell wd 0 rp ∗ pcell wd 8 re ∗ pcell wd 16 rb ∗ pcell wd 24 wb ∗ pcell wd 32 wp ∗ pcell wd 40 we ∗
  pcell wd 48 (window_base wd w) ∗ pcell wd 56 (wpos wd w (window_size w)).

(** A new allocation has its base and end installed, but the other
    pointers do not yet describe the new buffer. Glibc writes its
    base into all three read pointers before it sets the write side. *)
Lemma wp_wo_setg e fb fr ch wd wr w rp re rb wb wp we Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w -> 0 < window_size w -> wo_setup_regs e fb ch ->
  wo_lives fb fr wd wr w -∗ wo_wide_cursors wd w rp re rb wb wp we -∗
  (∀ ee, ⌜wo_setup_regs ee fb ch⌝ -∗ wo_lives fb fr wd wr w -∗
    wo_wide_cursors wd w (window_base wd w) (window_base wd w) (window_base wd w) wb wp we -∗
    WP (run ee (body_at wfile_overflow_fn "L36")) {{ Φ }}) -∗ WP (run e (body_at wfile_overflow_fn "L49")) {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Size (Hfp & Hch & Hck & H7).
  iIntros "(Hf & Hwd & Hl & Hb) (Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hstop) HK".
  iEval (rewrite <-(wpos_zero wd w)) in "Hbase". body_start wfile_overflow_fn "L49"%string.
  step. check "Hf". load "Hf" "Hwd" "Hl". step. load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hbase" "Hb". check "Hl". store "Hl" "Hrb".
  check "Hf". load "Hf" "Hwd" "Hl". load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hbase" "Hb". check "Hl". store "Hl" "Hrp".
  check "Hf". load "Hf" "Hwd" "Hl". step. load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hbase" "Hb". check "Hl". store "Hl" "Hre".
  do 2 step. iEval (rewrite wpos_zero) in "Hrp Hre Hrb Hbase". iApply ("HK" with "[%] [$] [-]"); [unfold wo_setup_regs; split_and!; lookups; done|rewrite /wo_wide_cursors; by iFrame].
Qed.

Lemma wp_wo_wide_switch e fb fr ch wd wr w wb wp we Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w -> 0 < window_size w -> wo_setup_regs e fb ch ->
  wo_lives fb fr wd wr w -∗ wo_wide_cursors wd w (window_base wd w) (window_base wd w) (window_base wd w) wb wp we -∗
  (∀ ee, ⌜wo_setup_regs ee fb ch⌝ -∗ wo_lives fb fr wd wr w -∗
    wo_wide_cursors wd w (window_base wd w) (window_base wd w) (window_base wd w) (window_base wd w)
      (wpos wd w 0) (wpos wd w (window_size w)) -∗ WP (run ee wo_narrow_switch) {{ Φ }}) -∗ WP (run e (body_at wfile_overflow_fn "L36")) {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Size (Hfp & Hch & Hck & H7).
  iIntros "(Hf & Hwd & Hl & Hb) (Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hstop) HK".
  iEval (rewrite <-(wpos_zero wd w)) in "Hrp Hre". body_start wfile_overflow_fn "L36"%string.
  step. check "Hf". load "Hf" "Hwd" "Hl". step. load "Hf" "Hwd" "Hl". check "Hl". load_wpos "Hl" "Hrp" "Hb". check "Hl". store "Hl" "Hwp".
  check "Hf". load "Hf" "Hwd" "Hl". step. load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hwp" "Hb". check "Hl". store "Hl" "Hwb".
  check "Hf". load "Hf" "Hwd" "Hl". step. load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hstop" "Hb". check "Hl". store "Hl" "Hwe".
  check "Hf". load "Hf" "Hwd" "Hl". step. load "Hf" "Hwd" "Hl". load "Hf" "Hwd" "Hl". step. check "Hl". load_wpos "Hl" "Hre" "Hb".
  check "Hl". store "Hl" "Hrp". check "Hl". store "Hl" "Hrb".
  iEval (rewrite wpos_zero) in "Hrp Hre Hrb Hwb". iApply ("HK" with "[%] [$] [-]"); [unfold wo_setup_regs; split_and!; lookups; done|rewrite /wo_wide_cursors; by iFrame].
Qed.
End cursors.
