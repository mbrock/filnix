From Glibc Require Import Unit_string_stpcpy_os.
From Glibc Require Import GlibcProgram.
(** After glibc's `c: stpcpy` has aligned the destination, it copies the
    string a word at a time. If the source is aligned too, it loads and
    stores whole words. Otherwise it starts the shifting loop of
    StpcpyShift.v with the first aligned source word, whose bytes before
    the string it replaces with 255s so that they cannot look like a
    terminator. This module proves both starts.

    In both cases the loads stay inside the string's window, and the
    stores stay inside the copied string, because a word is stored only
    when the loop knows that none of its bytes is the terminator. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsMemLogic StrlenBits WordString StrcmpBits StrcmpLoop.
From Glibc Require Import StpcpyBytes StpcpyTail StpcpyShift.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld OsMemLogic.

(** These definitions name the loop head of the aligned word loop and
    the block that starts the unaligned one. *)
Definition blk_a : block := Eval vm_compute in sblk "iw_1.L5".
Definition blk_37 : block := Eval vm_compute in sblk "L37".

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance stp_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The aligned word loop

    The loop holds a source address at string index k that is a
    multiple of 8. It loads that word and stores it into the destination
    when none of its bytes is zero. Otherwise it hands the word to the
    byte tail. *)

Lemma stp_align e bd rd xs o q b reg ws dq s k Q Φ :
  str_shape q b reg ws s ->
  lookup (TAtom "iw_1.pr.2") e = Some (WPtr (mkPtr (ptr_addr q + k) (ptr_cap q))) ->
  lookup (TAtom "iw_1.pr.1") e = Some (WPtr (mkPtr (bd + o + k) (Obj bd))) ->
  ptr_addr q mod 8 + k = 8 * Q -> 0 <= k <= Z.of_nat (length s) ->
  0 <= o -> o + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> 0 <= bd -> bd + Z.of_nat (length xs) <= r_end rd ->
  r_end rd <= 2 ^ 48 ->
  live bd rd -∗ bytes bd 0 (stp_dst xs o k (s ++ [0])) -∗ wwin dq b reg (wstart q - b) ws -∗
  (live bd rd -∗ bytes bd 0 (stp_dst xs o (Z.of_nat (length s) + 1) (s ++ [0])) -∗ wwin dq b reg (wstart q - b) ws -∗
     Φ (Ret (WPtr (mkPtr (bd + o + Z.of_nat (length s)) (Obj bd))))) -∗
  WP (ERun (mkFrame Unit_string_stpcpy_os.fn___GI___stpcpy e [] None (Exec (TAtom "iw_1.L5") (b_insts blk_a) (b_jump blk_a))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hs. destruct (shape_facts _ _ _ _ _ Hs) as (B & S1 & M & P & K & E & R & N & C).
  pose proof (ss_words _ _ _ _ _ Hs) as F. pose proof (ss_chars _ _ _ _ _ Hs) as Hch. pose proof (sbyte_agree _ _ _ _ _ Hs) as A.
  set (n := Z.of_nat (length s)) in *. set (S := (s ++ [0])%list) in *.
  assert (HS : Z.of_nat (length S) = n + 1) by (unfold S, n; rewrite length_app; cbn; lia).
  assert (HSn : forall j, 0 <= j < n -> 0 < nth (Z.to_nat j) S 0 < 256).
  { intros j Hj. unfold S. rewrite app_nth1; [|lia]. apply (Forall_nth (fun c => 0 < c < 256)); [exact Hch | lia]. }
  intros Hp2 Hp1 HQ Hk Ho Hox Hbd Hend Hreg.
  remember (Z.to_nat (n - k)) as r eqn:Hr.
  revert k Q e Hp2 Hp1 HQ Hk Hr. induction r as [r IH] using lt_wf_ind.
  intros k Q e Hp2 Hp1 HQ Hk Hr. iIntros "Hl Hb Hw HK". cbn [blk_a b_insts b_jump].
  step.
  iApply (wp_win_word registry (os_wi w0) ge _ _ _ _ _ _ _ _ _ _ dq b reg (wstart q - b) ws Q with "Hw");
    [vx | exact C | cbn; unfold wstart in *; lia | lia | lia | lia | unfold wstart in *; lia | lia | exact F |]. iIntros "Hw".
  set (w := wrd ws Q). pose proof (wrd_range ws Q F) as X.
  assert (Hby : forall t, 0 <= t < 8 -> k + t <= n -> byte_of w t = nth (Z.to_nat (k + t)) S 0).
  { intros t Ht Htn. unfold w. rewrite -(bt_at ws (ptr_addr q mod 8) k Q t); [|lia|lia|lia]. apply (A (k + t)). lia. }
  do 4 step_symbolic. normt (loop_mask w) ltac:(reflexivity). step_symbolic. branch_symbolic.
  rewrite (Z.mod_small (loop_mask w)); [|apply loop_mask_range]. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eq_dec (loop_mask w) 0) as [Hz|Hz].
  - rewrite Hz. close_edge.
    assert (Hk8 : k + 8 <= n).
    { destruct (Z_le_gt_dec (k + 8) n) as [|Hlt]; [assumption|]. exfalso.
      pose proof (proj1 (loop_mask_zero w X) Hz (n - k) ltac:(lia)) as Hne. apply Hne.
      rewrite Hby; [|lia|lia]. replace (k + (n - k)) with n by lia. unfold S, n. rewrite app_nth2; [|lia].
      rewrite Nat2Z.id Nat.sub_diag. reflexivity. }
    step. step. check "Hl".
    pose proof (length_stp_dst xs o k S Ho ltac:(lia) ltac:(lia)) as Hlen.
    iDestruct (bytes_splice bd _ (Z.to_nat (o + k)) 8 with "Hb") as "[Hx Hb]"; [lia|].
    rewrite Z2Nat.id; [|lia].
    iApply (wp_raw_store_l_bytes with "Hl Hx"); [vx | vx | reflexivity | a2 | rewrite length_take length_drop; lia | wi_store |].
    iNext. iIntros "Hl Hx". rewrite (Z.mod_small w); [|lia].
    rewrite (le_bytes_word w S (Z.to_nat k)); [|lia|].
    2:{ intros t Ht. rewrite Hby; [|lia|lia]. f_equal. lia. }
    iDestruct ("Hb" with "[%] Hx") as "Hb"; [rewrite length_take length_drop; lia|].
    replace (Z.to_nat (o + k)) with (Z.to_nat (o + k)) by reflexivity.
    iEval (rewrite stp_dst_word; [|lia|lia|lia|lia]) in "Hb".
    step. step. cbn [ptr_addr ptr_cap].
    normp "iw_1.pr.2" (ptr_addr q + (k + 8)). normp "iw_1.pr.1" (bd + o + (k + 8)).
    iApply (IH (Z.to_nat (n - (k + 8))) ltac:(lia) (k + 8) (Q + 1) _ with "Hl Hb Hw HK"); try lk_prove; lia.
  - replace (loop_mask w =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_edge. step.
    assert (Hn8 : n < k + 8).
    { destruct (loop_mask_has_zero w X Hz) as (j & Hj & Hwj).
      destruct (Z_le_gt_dec (k + j) n) as [Hle|]; [|lia].
      rewrite Hby in Hwj; [|lia|lia]. destruct (Z.eq_dec (k + j) n); [lia|]. pose proof (HSn (k + j) ltac:(lia)). lia. }
    change (0 mod 2 ^ 64) with 0.
    iApply (stp_tail1 _ bd rd xs o s k 0 w with "Hl [Hb] [HK Hw]"); try lk_prove; try lia.
    + rewrite Z.add_0_r. lk_prove.
    + rewrite Z.add_0_r. iExact "Hb".
    + iIntros "Hl Hb". iApply ("HK" with "Hl Hb Hw").
Qed.

(** ## The start of the unaligned loop

    The source address at index c is v bytes past a multiple of 8. The
    code loads the aligned word that holds it, shifts its first v bytes
    out and fills the top v bytes with 255. When the result has no zero
    byte, the loop of StpcpyShift.v takes over with that aligned word.
    Otherwise the string ends in it, and the byte tail copies it. *)

Lemma stp_shift e bd rd xs o q b reg ws dq s c v Q Φ :
  str_shape q b reg ws s ->
  lookup (TAtom "pr.2") e = Some (WPtr (mkPtr (ptr_addr q + c) (ptr_cap q))) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (bd + o + c) (Obj bd))) ->
  lookup (TAtom "v35") e = Some (WInt v) ->
  ptr_addr q mod 8 + c = 8 * Q + v -> 0 < v < 8 -> 0 <= c <= Z.of_nat (length s) ->
  0 <= o -> o + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> 0 <= bd -> bd + Z.of_nat (length xs) <= r_end rd ->
  r_end rd <= 2 ^ 48 ->
  live bd rd -∗ bytes bd 0 (stp_dst xs o c (s ++ [0])) -∗ wwin dq b reg (wstart q - b) ws -∗
  (live bd rd -∗ bytes bd 0 (stp_dst xs o (Z.of_nat (length s) + 1) (s ++ [0])) -∗ wwin dq b reg (wstart q - b) ws -∗
     Φ (Ret (WPtr (mkPtr (bd + o + Z.of_nat (length s)) (Obj bd))))) -∗
  WP (ERun (mkFrame Unit_string_stpcpy_os.fn___GI___stpcpy e [] None (Exec (TAtom "L37") (b_insts blk_37) (b_jump blk_37))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hs. destruct (shape_facts _ _ _ _ _ Hs) as (B & S1 & M & P & K & E & R & N & C).
  pose proof (ss_words _ _ _ _ _ Hs) as F. pose proof (ss_chars _ _ _ _ _ Hs) as Hch. pose proof (sbyte_agree _ _ _ _ _ Hs) as A.
  set (n := Z.of_nat (length s)) in *. set (S := (s ++ [0])%list) in *.
  assert (HSn : forall j, 0 <= j < n -> 0 < nth (Z.to_nat j) S 0 < 256).
  { intros j Hj. unfold S. rewrite app_nth1; [|lia]. apply (Forall_nth (fun c => 0 < c < 256)); [exact Hch | lia]. }
  assert (HSz : forall j, 0 <= j < n -> nth (Z.to_nat j) S 0 <> 0) by (intros j Hj; pose proof (HSn j Hj); lia).
  assert (HS0 : nth (Z.to_nat n) S 0 = 0) by (unfold S, n; rewrite app_nth2; [|lia]; rewrite Nat2Z.id Nat.sub_diag; reflexivity).
  intros Hp2 Hp1 Hv HQ Hv8 Hc Ho Hox Hbd Hend Hreg.
  iIntros "Hl Hb Hw HK". cbn [blk_37 b_insts b_jump].
  step. step. cbn [ptr_addr ptr_cap].
  normp "v47" (wstart q + 8 * Q).
  iApply (wp_win_word registry (os_wi w0) ge _ _ _ _ _ _ _ _ _ _ dq b reg (wstart q - b) ws Q with "Hw");
    [vx | exact C | cbn; lia | lia | lia | lia | lia | lia | exact F |]. iIntros "Hw".
  set (w := wrd ws Q). pose proof (wrd_range ws Q F) as X.
  step_symbolic. normz "iw_2.v12" (8 * v) ltac:(symmetry; apply sh_amt; lia).
  step_symbolic. normz "iw_2.v16" (64 - 8 * v)
    ltac:(change (64 mod 2 ^ 64) with 64; rewrite (Z.mod_small (8 * v)); [rewrite Z.mod_small; lia | lia]).
  step_symbolic. normz "iw_2.v20" (shd w v) ltac:(symmetry; apply sh_down).
  step_symbolic. normz "iw_2.v24" (shu 18446744073709551615 v) ltac:(symmetry; apply sh_up).
  step_symbolic. normz "iw_2.v25" (merge w 18446744073709551615 v) ltac:(rewrite shd_mod shu_mod; reflexivity).
  set (z := merge w 18446744073709551615 v). pose proof (merge_range w 18446744073709551615 v) as Z0.
  assert (Hz : forall t, 0 <= t < 8 - v -> c + t <= n -> byte_of z t = nth (Z.to_nat (c + t)) S 0).
  { intros t Ht Htn. unfold z. rewrite merge_byte; [|lia|lia]. replace (t + v <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold w. rewrite -(bt_at ws (ptr_addr q mod 8) (c - v) Q (t + v)); [|lia|lia|lia].
    replace (ptr_addr q mod 8 + (c - v + (t + v))) with (ptr_addr q mod 8 + (c + t)) by lia. apply (A (c + t)). lia. }
  assert (Hhi : forall t, 8 - v <= t < 8 -> byte_of z t <> 0).
  { intros t Ht. unfold z. rewrite merge_byte; [|lia|lia]. replace (t + v <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite byte_ones; lia. }
  destruct (mask_len z S n c (8 - v) Z0 ltac:(lia) ltac:(lia) Hz Hhi HSz HS0) as [Mz Mnz].
  do 4 step_symbolic. normt (loop_mask z) ltac:(reflexivity). step_symbolic. branch_symbolic.
  rewrite (Z.mod_small (loop_mask z)); [|apply loop_mask_range]. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eq_dec (loop_mask z) 0) as [Ez|Ez].
  - rewrite Ez. close_edge. pose proof (Mz Ez) as Hc8.
    step. cbn [ptr_addr ptr_cap].
    normp "iw_2.pr.5" (wstart q + 8 * (Q + 1)). normz "iw_2.pr.6" (wrd ws Q) ltac:(rewrite Z.mod_small; lia).
    iApply (stp_shift_loop _ bd rd xs o q b reg ws dq s c v Q with "Hl Hb Hw HK"); try lk_prove; lia.
  - replace (loop_mask z =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ez). close_edge.
    pose proof (Mnz Ez) as Hn8.
    step. step. step. change (0 mod 2 ^ 64) with 0.
    normp "iw_2.iw_4.pr.1" (bd + o + c + 0). normz "iw_2.pr.8" z ltac:(rewrite Z.mod_small; lia).
    iApply (stp_tail2 _ bd rd xs o s c 0 z with "Hl [Hb] [HK Hw]"); try lk_prove; try lia.
    + intros t Ht Htn. apply Hz; lia.
    + rewrite Z.add_0_r. iExact "Hb".
    + iIntros "Hl Hb". iApply ("HK" with "Hl Hb Hw").
Qed.
End rules.
