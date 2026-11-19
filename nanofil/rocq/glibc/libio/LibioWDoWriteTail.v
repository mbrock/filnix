(** The wide flush `c: _IO_wdo_write` ends by emptying the wide buffer,
    whether or not it converted every character:

    ```
    _IO_wsetg (fp, fp->_wide_data->_IO_buf_base,
               fp->_wide_data->_IO_buf_base, fp->_wide_data->_IO_buf_base);
    _IO_wsetp (fp, fp->_wide_data->_IO_buf_base,
               fp->_flags & (_IO_LINE_BUF | _IO_UNBUFFERED)
               ? fp->_wide_data->_IO_buf_base : fp->_wide_data->_IO_buf_end);
    return to_do == 0 ? 0 : WEOF;
    ```

    A fully buffered stream can accept more characters after the flush,
    so its write end points to the end of the buffer. A line-buffered
    or unbuffered stream puts the write end at the start instead. The
    next character will then go through the overflow handler. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioPutsInv LibioWIdle
  LibioWXsputnWindow LibioWXsputnRoom LibioWOverflowWrite CBlocks.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation objp b := (mkPtr b (Obj b)).

Local Typeclasses Opaque pcell.

Section tail.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The tail reads the narrow flags and the wide data pointer from the
    stream and rewrites six of the wide pointers. It leaves the wide
    buffer empty: every read pointer, the write base and the write
    pointer at the base, and the write end either at the base or at the
    end. The result is 0 when no characters remain and `c: WEOF`
    otherwise. *)
Lemma wp_wdo_tail e fb freg wd wr w k j r fl Ψ :
  reg e "v0" (WPtr (objp fb)) -> reg e "chk0" (WPtr (mkPtr (fb + 152) (Obj fb))) -> reg e "pr.2" (WInt r) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wr -> r_end wr <= 2 ^ 63 -> window_bound w ->
  0 <= k <= window_size w -> 0 <= j <= window_size w -> 0 <= fl < 2 ^ 32 -> 0 <= r < 2 ^ 64 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_wide (objp wd) -∗ live wd wr -∗
  ([∗ list] i ↦ p ∈ window_slots wd w k j, pcell wd (woff_ptr i) p) -∗ wbuf_idle w -∗
  ▷ (∀ j', ⌜0 <= j' <= window_size w⌝ -∗ live fb freg -∗ int_cell fb off_flags fl -∗
     pcell fb off_wide (objp wd) -∗ live wd wr -∗
     ([∗ list] i ↦ p ∈ window_slots wd w 0 j', pcell wd (woff_ptr i) p) -∗ wbuf_idle w -∗
     Ψ (Ret (WInt (if r =? 0 then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame wdo_write_fn e [] None (body_at wdo_write_fn "L12")) : sexpr) {{ Ψ }}.
Proof using Type.
  intros Hv0 Hc0 Hr Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr B Hk Hj Hfl Rr.
  iIntros "Hf Hflags Hwp Hl Hps Hb HK".
  unfold window_slots. cbn [big_opL]. iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _)".
  body_start wdo_write_fn "L12"%string. step. check "Hf". load "Hf" "Hwp" "Hl".
  iEval (rewrite -(wpos_zero wd w)) in "P0 P1 P2 P3 P6". iEval (rewrite /woff_ptr /=) in "P0 P1 P2 P3 P4 P5 P6 P7".
  step. load "Hf" "Hwp" "Hl". step. check "Hl". load_wpos "Hl" "P6" "Hb". check "Hl". store "Hl" "P2".
  check "Hf". load "Hf" "Hwp" "Hl". load "Hf" "Hwp" "Hl". step. check "Hl". load_wpos "Hl" "P6" "Hb". check "Hl". store "Hl" "P0".
  check "Hf". load "Hf" "Hwp" "Hl". step. load "Hf" "Hwp" "Hl". step. check "Hl". load_wpos "Hl" "P6" "Hb". check "Hl". store "Hl" "P1".
  check "Hf". load "Hf" "Hwp" "Hl". step. load "Hf" "Hwp" "Hl". step. load "Hf" "Hwp" "Hl". step. check "Hl". load_wpos "Hl" "P6" "Hb".
  check "Hl". store "Hl" "P4". check "Hl". store "Hl" "P3".
  check "Hf". load "Hf" "Hwp" "Hl". step. iDestruct "Hflags" as "[%Hfl' Hflags]". check "Hf". load_s32 "Hf" "Hflags". step.
  destruct (Z.eq_dec (Z.land fl 514) 0) as [Hz | Hz].
  - branch_as true. step. step. load "Hf" "Hwp" "Hl". step. check "Hl". load_wpos "Hl" "P7" "Hb". step. step. check "Hl". store "Hl" "P5". step.
    destruct (Z.eq_dec r 0) as [-> | Hr0]; [branch_as false | branch_as true]; repeat step.
    all: iApply wp_ret; [reflexivity | vx |]; iNext.
    all: lazymatch goal with |- environments.envs_entails _ (_ (Ret (WInt ?x))) => let y := eval vm_compute in x in change x with y end.
    + iApply ("HK" $! (window_size w) with "[%] Hf [$Hflags //] Hwp Hl [-Hb] Hb"); [lia|].
      rewrite /woff_ptr -(wpos_zero wd w) /=. iFrame.
    + rewrite (proj2 (Z.eqb_neq r 0) Hr0). change (WInt 4294967295) with (WInt (2 ^ 32 - 1)).
      iApply ("HK" $! (window_size w) with "[%] Hf [$Hflags //] Hwp Hl [-Hb] Hb"); [lia|].
      rewrite /woff_ptr -(wpos_zero wd w) /=. iFrame.
  - assert (E : (Z.land (fl mod 2 ^ 32) (514 mod 2 ^ 32) mod 2 ^ 32 =? 0) = false).
    { assert (0 <= Z.land fl 514 < 2 ^ 32) by (apply land_lt32; lia).
      rewrite (Z.mod_small fl) // (Z.mod_small 514) // Z.mod_small //. apply Z.eqb_neq, Hz. }
    branch_symbolic. rewrite E. cbn [edge_label]. step. step. load "Hf" "Hwp" "Hl". step. check "Hl". load_wpos "Hl" "P6" "Hb".
    step. step. check "Hl". store "Hl" "P5". step.
    destruct (Z.eq_dec r 0) as [-> | Hr0]; [branch_as false | branch_as true]; repeat step.
    all: iApply wp_ret; [reflexivity | vx |]; iNext.
    all: lazymatch goal with |- environments.envs_entails _ (_ (Ret (WInt ?x))) => let y := eval vm_compute in x in change x with y end.
    + iApply ("HK" $! 0 with "[%] Hf [$Hflags //] Hwp Hl [-Hb] Hb"); [lia|].
      rewrite /woff_ptr -(wpos_zero wd w) /=. iFrame.
    + rewrite (proj2 (Z.eqb_neq r 0) Hr0). change (WInt 4294967295) with (WInt (2 ^ 32 - 1)).
      iApply ("HK" $! 0 with "[%] Hf [$Hflags //] Hwp Hl [-Hb] Hb"); [lia|].
      rewrite /woff_ptr -(wpos_zero wd w) /=. iFrame.
Qed.

End tail.
