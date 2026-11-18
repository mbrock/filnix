(** A stream with two allocated buffers can finish switching to
    output. Both a fresh allocation and an existing idle stream reach
    this point. Their read pointers agree, but the old write pointers
    can still refer to the state before allocation. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic.
From Glibc Require Import Fix FileInv FileIdle LibioLogic LibioCloseSteps LibioPutsInv LibioWIdle LibioWXsputnWindow
  LibioWOverflowDispatch LibioWOverflowFlush LibioWOverflowPut LibioWOverflowWrite LibioWOverflowSetp LibioWOverflowSetWide
  LibioWOverflowEntry LibioWOverflowSetup LibioWOverflowState LibioWOverflowLoan CBlocks.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation obj b := (mkPtr b (Obj b)).

Definition wo_ptrs_before (b rb wb wp we stop : ptr) := [b;b;rb;wb;wp;we;b;stop].
Definition wo_wide_before wd w wb wp we := let p := window_base wd w in
  [p;p;p;wb;wp;we;p;wpos wd w (window_size w);null;null;null].

Section setup.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ).
Context `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn} (Hwrite : wdo_pending_spec vb self 1 E).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e l := (ERun (mkFrame wfile_overflow_fn e [] None (body_at wfile_overflow_fn l)) : sexpr).

(** A stream without a narrow buffer has null cursors. Every other
    idle wide stream has its narrow read pointer and write base at the
    base of the same short or heap buffer that it owns. *)
Lemma wo_old_storage fp fd fb fr st nb wd w tw tm : wide_file_ok ge vb fp fd fb fr st nb wd w tw tm ->
  buf_idle nb -∗ ⌜(nb = NbNone /\ wo_ptrs st = replicate 8 null) \/
    (wo_storage fb nb (fs_flags st) (fs_ptr st 6) (fs_ptr st 7) /\
     wo_ptrs st = wo_ptrs_before (fs_ptr st 6) (fs_ptr st 2) (fs_ptr st 6) (fs_ptr st 4) (fs_ptr st 5) (fs_ptr st 7))⌝.
Proof using Type.
  intros (_ & _ & _ & _ & _ & _ & I & _ & _ & Buf & (_ & Short) & _).
  destruct I as (_ & _ & _ & _ & _ & _ & R0 & R1 & _).
  change (fs_ptr st 0 = fs_ptr st 1) in R0. change (fs_ptr st 1 = fs_ptr st 3) in R1.
  destruct nb as [| |bb sz|bb].
  - iIntros "_". iPureIntro. left. split; [done|]. unfold wo_ptrs, fs_ptr. rewrite -(take_drop 8 (fs_ptrs st)) Buf. done.
  - iIntros "_". iPureIntro. right. destruct Buf as (Base & Stop & _). destruct Short as (User & _ & Eq).
    split; [unfold wo_storage, fs_ptr; tauto|unfold wo_ptrs, wo_ptrs_before; by rewrite R0 R1 Eq].
  - iIntros "(%br & %xs & %cs & %P & _)". iPureIntro. right. destruct Buf as (Base & Stop & _). destruct Short as (User & _ & Eq).
    split; [unfold wo_storage, fs_ptr; split_and!; try assumption; lia|unfold wo_ptrs, wo_ptrs_before; by rewrite R0 R1 Eq].
  - by iIntros "[]".
Qed.

Lemma wp_wo_ready e fb fr ch st nb fl f2 wd wr w b rb wb wp we stop wwb wwp wwe Φ :
  0 <= ch < 2^32 -> wo_setup_regs e fb ch ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> window_bound w -> 0 < window_size w ->
  wo_storage fb nb fl b stop -> 0 <= fl < 2^32 ->
  (forall m, Z.land 513 m = 0 -> Z.land fl m = Z.land (fs_flags st) m) ->
  (forall m, (m = 2 \/ m = 32 \/ m = io_need_lock) -> Z.land f2 m = Z.land (fs_flags2 st) m) -> wbuf_user_ok w f2 ->
  wo_cells vb fb fr fl f2 nb wd wr w (wo_ptrs_before b rb wb wp we stop) (wo_wide_before wd w wwb wwp wwe) -∗
  wo_close ge vb self fb fr st wd wr -∗ E -∗ wo_post vb self E fb ch Φ -∗ WP (run e "L36") {{ Φ }}.
Proof using Type*.
  intros Ch G Fb Fa Fe Fr Wd Wa We Wr B Room S F Bits B2 User.
  assert (In : in_buf fb nb b /\ in_buf fb nb stop).
  { destruct nb; cbn [wo_storage] in S; try contradiction; destruct S as (-> & -> & Rest); cbn; intuition lia. }
  iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb) Hclose HE HK".
  iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & _)".
  iDestruct "Hw" as "(W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _)".
  iApply (wp_wo_switch e fb fr ch wd wr w nb fl b rb wb wp we stop wwb wwp wwe with
    "[Hf Hwd Hl Hb] [W0 W1 W2 W3 W4 W5 W6 W7] Hfl Hnb P0 P1 P2 P3 P4 P5 P7 [-]"); try assumption; try apply In;
    [rewrite /wo_lives; by iFrame|rewrite /wo_wide_cursors; by iFrame|].
  iIntros (ee j (Ge & R)) "(Hf & Hwd & Hl & Hb) (W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7) Hfl Hnb P0 P1 P2 P3 P4 P5 P7".
  iApply (wp_wo_put vb self E Hwrite ee fb ch wd w 0 with "[-HE HK] HE HK"); [done|done|unfold wo_regs, wo_setup_regs in *; tauto|].
  iApply ("Hclose" $! fl f2 nb w b stop j with "[%] [-]"); [tauto|]. rewrite /wo_cells /wo_reset_ptrs /window_slots /=. by iFrame.
Qed.

(** If overflow finds a wide allocation before setup, it skips both
    allocator calls. The narrow buffer must exist as well, since an
    idle stream without one has no wide allocation. *)
Lemma wo_prepare_existing : wo_prepare vb self E true.
Proof using Type*.
  intros e fb ch wd w i Φ Ch G Room. iIntros "HP HE HK".
  iDestruct (wo_open with "HP") as (fr st nb tw tm wr j (P & Wd & Wa & We & Wr & B & Hi & Hj)) "[HC Hclose]".
  pose proof P as (_ & Fa & Fb & Fe & Fr & (F & _) & _ & _ & _ & _ & _ & User & _ & _ & _ & _ & None).
  iDestruct "HC" as "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb)".
  iDestruct (wo_old_storage _ _ _ _ _ _ _ _ _ _ P with "Hnb") as %[(Eq & _)|(S & Ps)].
  { specialize (None Eq). subst w. done. }
  iApply (wp_wo_ready e fb fr ch st nb (fs_flags st) (fs_flags2 st) wd wr w (fs_ptr st 6) (fs_ptr st 2)
    (fs_ptr st 6) (fs_ptr st 4) (fs_ptr st 5) (fs_ptr st 7) (window_base wd w) (wpos wd w i) (wpos wd w j) with "[-Hclose HE HK] Hclose HE HK");
    try assumption; try reflexivity. rewrite /wo_cells -Ps. by iFrame.
Qed.
End setup.
