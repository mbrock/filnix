(** Switching a wide stream to writing also resets its narrow buffer.
    The write pointer starts at the read pointer, and the write end
    becomes the physical buffer end. The short buffer follows the same
    rule as the heap buffer, even on an unbuffered stream. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv FileIdle LibioLogic LibioFflushIdle
  LibioPutsInv LibioWOverflowDispatch CBlocks.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Definition wo_setup_regs e fb ch := reg e "v0" (WPtr (obj fb)) /\ reg e "v2" (WInt ch) /\
  reg e "chk0" (WPtr (obj fb)) /\ reg e "chk7" (WPtr (mkPtr (fb+160) (Obj fb))).

(** The first part of the switch sets the wide pointers. Its last
    store precedes the first access to the narrow read pointer. *)
Definition wo_narrow_switch := Eval vm_compute in
  match body_at wfile_overflow_fn "L36" with Exec l code j => Exec l (skipn 39 code) j | x => x end.

Section setp.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e at_ := (ERun (mkFrame wfile_overflow_fn e [] None at_) : sexpr).

Definition wo_narrow_cells fb fr fl nb b rb wb wp we stop : iProp Σ :=
  live fb fr ∗ int_cell fb off_flags fl ∗ buf_idle nb ∗
  pcell fb 8 b ∗ pcell fb 16 b ∗ pcell fb 24 rb ∗ pcell fb 32 wb ∗ pcell fb 40 wp ∗ pcell fb 48 we ∗ pcell fb 64 stop.

Local Ltac load_buf field := rule3 "Hf" field "Hb" ltac:(eapply wp_load_buf_ptr; inst;
  [reflexivity|vx|reflexivity|a2|a2|lia|lia|assumption]).

Lemma wp_wo_narrow_switch e fb fr fl ch nb b rb wb wp we stop Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  in_buf fb nb b -> in_buf fb nb stop -> wo_setup_regs e fb ch ->
  wo_narrow_cells fb fr fl nb b rb wb wp we stop -∗
  (∀ ee (tight : bool), ⌜wo_setup_regs ee fb ch⌝ -∗
    wo_narrow_cells fb fr (Z.lor fl 2048) nb b b b b stop stop -∗
    WP (run ee (body_at wfile_overflow_fn (if tight then "L195" else "L17"))) {{ Φ }}) -∗ WP (run e wo_narrow_switch) {{ Φ }}.
Proof using Type.
  intros Hfb Hfa Hfe Hfr B S (Hfp & Hch & H0 & H7).
  iIntros "(Hf & [%F Hfl] & Hb & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hstop) HK". unfold wo_narrow_switch.
  do 2 step. check "Hf". load_buf "Hrp". check "Hf". store "Hf" "Hwp".
  step. check "Hf". load_buf "Hwp". check "Hf". store "Hf" "Hwb".
  do 2 step. check "Hf". load_buf "Hstop". check "Hf". store "Hf" "Hwe".
  do 2 step. check "Hf". load_buf "Hre". check "Hf". store "Hf" "Hrp". check "Hf". store "Hf" "Hrb".
  check "Hf". load_s32 "Hf" "Hfl". step. check "Hf". store_int "Hf" "Hfl".
  assert (F' : 0 <= Z.lor fl 2048 < 2^32) by (apply lor_lt32; lia).
  iEval (rewrite (Z.mod_small fl (2^32) F) /= (Z.mod_small _ _ F')) in "Hfl".
  load_s32 "Hf" "Hfl". step. branch_cases; step;
    [iApply ("HK" $! _ false with "[%] [-]")|iApply ("HK" $! _ true with "[%] [-]")];
    try (unfold wo_setup_regs; repeat split; lookups; done); rewrite /wo_narrow_cells /int_cell; by iFrame.
Qed.
End setp.
