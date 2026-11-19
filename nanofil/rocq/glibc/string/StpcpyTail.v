From Glibc Require Import Unit_string_stpcpy_os.
From Glibc Require Import GlibcProgram.
(** glibc's `c: stpcpy` ends every copy by writing the last word's bytes
    one at a time until it has written the terminator. The source calls
    this step `c: write_byte_from_word`, and the compiler inlined it twice,
    once after the aligned word loop and once after the unaligned one.
    This module proves both copies.

    Each copy starts with a word w whose bytes from position u on agree
    with the string, at least up to its terminator. It stores those bytes
    into the destination buffer and stops after the terminator, so it
    never writes past the end of the copied string. It returns the address
    of the terminator in the destination. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld FileInv LibioLogic StrlenBits GetoptBytes StpcpyBytes.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** This definition finds the block named l in the captured function. *)
Definition sblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks Unit_string_stpcpy_os.fn___GI___stpcpy) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** These definitions name the loop heads of the two copies of the byte loop. *)
Definition blk_t1 : block := Eval vm_compute in sblk "iw_1.iw_2.L7".
Definition blk_t2 : block := Eval vm_compute in sblk "iw_2.iw_4.L7".

(** The low byte of a sign-extended byte is the byte itself. *)
Lemma chr_w_byte x : 0 <= x < 256 -> chr_w x mod 256 = x.
Proof.
  intros Hx. destruct (Z.ltb_spec x 128).
  - rewrite chr_w_small; [apply Z.mod_small; lia | lia].
  - rewrite chr_w_large; [|lia]. replace (x - 256 + 2 ^ 32) with (x + (2 ^ 24 - 1) * 256) by (cbn; lia).
    rewrite Z.mod_add; [apply Z.mod_small; lia | lia].
Qed.

(** The tail extracts byte u of w by a shift and two byte extensions. *)
Lemma stp_extract w u : 0 <= w < 2 ^ 64 -> 0 <= u < 8 ->
  sign_extension 256 128 (((((w mod 2 ^ 64 / 2 ^ (((((u mod 2 ^ 32) mod 2 ^ 32 * 2 ^ ((3 mod 2 ^ 32) mod 32))
    mod 2 ^ 32) mod 2 ^ 32) mod 64)) mod 2 ^ 32) mod 256) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32 = chr_w (byte_of w u).
Proof.
  intros Hw Hu. unfold chr_w. f_equal. f_equal.
  change ((3 mod 2 ^ 32) mod 32) with 3. change (2 ^ 3) with 8.
  rewrite !(Z.mod_small u (2 ^ 32)); try lia. rewrite !(Z.mod_small (u * 8) (2 ^ 32)); try lia.
  rewrite (Z.mod_small (u * 8) 64); [|lia]. rewrite (Z.mod_small w); [|lia].
  unfold byte_of. replace (8 * u) with (u * 8) by lia.
  rewrite (Z.mod_small (((w / 2 ^ (u * 8)) mod 2 ^ 32) mod 256) (2 ^ 32)); [|pose proof (Z.mod_pos_bound ((w / 2 ^ (u * 8)) mod 2 ^ 32) 256); lia].
  rewrite (Z.mod_small (((w / 2 ^ (u * 8)) mod 2 ^ 32) mod 256) (2 ^ 32)); [|pose proof (Z.mod_pos_bound ((w / 2 ^ (u * 8)) mod 2 ^ 32) 256); lia].
  apply Z.mod_mod_divide. exists (2 ^ 24). reflexivity.
Qed.

(** This tactic follows a branch whose condition has become closed. *)
Ltac close_edge := lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
  let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** These tactics rewrite the value that the newest update gives a temporary. *)
Ltac norm name v := match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by a2 end.
Ltac normp name v := match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by a2 end.
(** These tactics rewrite an integer temporary, the newest one or the one
    named, using a supplied proof. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
Ltac normz name v tac := match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance stp_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The byte loop after the aligned loop *)

(** The loop stores byte u of w at offset k + u of the copy. When that
    byte is the terminator, the loop returns the address it wrote it to.
    Otherwise it goes on with the next byte. The bytes of w from u on must
    agree with the string as far as its terminator, which lies within w. *)

Lemma stp_tail1 e bd rd xs o s k u w Φ :
  lookup (TAtom "iw_1.iw_2.pr.2") e = Some (WInt u) ->
  lookup (TAtom "iw_1.iw_2.pr.1") e = Some (WPtr (mkPtr (bd + o + k + u) (Obj bd))) ->
  lookup (TAtom "iw_1.v10") e = Some (WInt w) -> 0 <= w < 2 ^ 64 ->
  0 <= k -> 0 <= u -> k + u <= Z.of_nat (length s) < k + 8 ->
  (forall t, u <= t < 8 -> k + t <= Z.of_nat (length s) -> byte_of w t = nth (Z.to_nat (k + t)) (s ++ [0]) 0) ->
  Forall (fun c => 0 < c < 256) s ->
  0 <= o -> o + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> 0 <= bd -> bd + Z.of_nat (length xs) <= r_end rd ->
  r_end rd <= 2 ^ 48 ->
  live bd rd -∗ bytes bd 0 (stp_dst xs o (k + u) (s ++ [0])) -∗
  (live bd rd -∗ bytes bd 0 (stp_dst xs o (Z.of_nat (length s) + 1) (s ++ [0])) -∗
     Φ (Ret (WPtr (mkPtr (bd + o + Z.of_nat (length s)) (Obj bd))))) -∗
  WP (ERun (mkFrame Unit_string_stpcpy_os.fn___GI___stpcpy e [] None (Exec (TAtom "iw_1.iw_2.L7") (b_insts blk_t1) (b_jump blk_t1))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hu Ha Hw Hw64 Hk Hu0 Hn Hbyte Hs Ho Hox Hbd Hend Hreg.
  set (n := Z.of_nat (length s)) in *. set (S := (s ++ [0])%list) in *.
  assert (HS : Z.of_nat (length S) = n + 1) by (unfold S, n; rewrite length_app; cbn; lia).
  assert (HSn : forall j, 0 <= j < n -> 0 < nth (Z.to_nat j) S 0 < 256).
  { intros j Hj. unfold S. rewrite app_nth1; [|lia]. apply (Forall_nth (fun c => 0 < c < 256)); [exact Hs | lia]. }
  assert (HS0 : nth (Z.to_nat n) S 0 = 0) by (unfold S, n; rewrite app_nth2; [|lia]; rewrite Nat2Z.id Nat.sub_diag; reflexivity).
  remember (Z.to_nat (n - (k + u))) as r eqn:Hr.
  revert u e Hu Ha Hw Hu0 Hn Hbyte Hr. induction r as [r IH] using lt_wf_ind.
  intros u e Hu Ha Hw Hu0 Hn Hbyte Hr. iIntros "Hl Hb HK". cbn [blk_t1 b_insts b_jump].
  step. branch_symbolic. rewrite (Z.mod_small u); [|lia].
  assert (E : (u <? 8) = true) by (apply Z.ltb_lt; lia). rewrite E. cbn [edge_label].
  step. step. step. step. step. step.
  rewrite (stp_extract w u Hw64); [|lia].
  set (c := byte_of w u). assert (Hc : c = nth (Z.to_nat (k + u)) S 0) by (apply Hbyte; lia).
  assert (Hc8 : 0 <= c < 256) by apply byte_of_range.
  pose proof (length_stp_dst xs o (k + u) S Ho ltac:(lia) ltac:(lia)) as Hlen.
  iDestruct (bytes_store1 bd _ (Z.to_nat (o + k + u)) with "Hb") as (x) "[Hx Hb]"; [lia|].
  rewrite Z2Nat.id; [|lia].
  check "Hl".
  iApply (wp_raw_store_byte with "Hl Hx"); [vx | vx | reflexivity | a2 | wi_store |].
  iNext. iIntros "Hl Hx". rewrite (Z.mod_small (chr_w c)); [|apply chr_w_range]. rewrite (chr_w_byte c Hc8). iDestruct ("Hb" with "Hx") as "Hb".
  replace (Z.to_nat (o + k + u)) with (Z.to_nat (o + (k + u))) by lia.
  iEval (rewrite Hc stp_dst_byte; [|lia|lia|lia]) in "Hb".
  step. branch_symbolic. rewrite (Z.mod_small (chr_w c)); [|apply chr_w_range]. change (0 mod 2 ^ 32) with 0.
  rewrite chr_w_eqb; [|exact Hc8|lia].
  destruct (Z.eqb_spec c 0) as [Hz|Hz].
  - assert (Hkn : k + u = n).
    { destruct (Z.eq_dec (k + u) n) as [|Hne]; [assumption|]. exfalso. pose proof (HSn (k + u) ltac:(lia)). lia. }
    rewrite Hz. close_edge. step.
    iApply wp_ret; [reflexivity | vx |]. iNext.
    replace (k + u + 1) with (n + 1) by lia. replace (bd + o + k + u) with (bd + o + n) by lia.
    iApply ("HK" with "Hl Hb").
  - assert (Hkn : k + u < n) by (destruct (Z.eq_dec (k + u) n); [subst c; rewrite e0 HS0 in Hc; lia | lia]).
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_edge. step. step. step. step. step. cbn [ptr_addr ptr_cap].
    normp "iw_1.iw_2.pr.1" (bd + o + k + (u + 1)). norm "iw_1.iw_2.pr.2" (u + 1).
    replace (k + u + 1) with (k + (u + 1)) by lia.
    iApply (IH (Z.to_nat (n - (k + (u + 1)))) ltac:(lia) (u + 1) _ with "Hl Hb HK"); try lk_prove; try lia.
    intros t Ht Htn. apply Hbyte; lia.
Qed.

(** ## The byte loop after the unaligned loop

    The second copy is the same loop with other names, and its word is the
    merged word of the unaligned loop. *)

(** This lemma is the previous one for the second copy of the loop. *)
Lemma stp_tail2 e bd rd xs o s k u w Φ :
  lookup (TAtom "iw_2.iw_4.pr.2") e = Some (WInt u) ->
  lookup (TAtom "iw_2.iw_4.pr.1") e = Some (WPtr (mkPtr (bd + o + k + u) (Obj bd))) ->
  lookup (TAtom "iw_2.pr.8") e = Some (WInt w) -> 0 <= w < 2 ^ 64 ->
  0 <= k -> 0 <= u -> k + u <= Z.of_nat (length s) < k + 8 ->
  (forall t, u <= t < 8 -> k + t <= Z.of_nat (length s) -> byte_of w t = nth (Z.to_nat (k + t)) (s ++ [0]) 0) ->
  Forall (fun c => 0 < c < 256) s ->
  0 <= o -> o + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> 0 <= bd -> bd + Z.of_nat (length xs) <= r_end rd ->
  r_end rd <= 2 ^ 48 ->
  live bd rd -∗ bytes bd 0 (stp_dst xs o (k + u) (s ++ [0])) -∗
  (live bd rd -∗ bytes bd 0 (stp_dst xs o (Z.of_nat (length s) + 1) (s ++ [0])) -∗
     Φ (Ret (WPtr (mkPtr (bd + o + Z.of_nat (length s)) (Obj bd))))) -∗
  WP (ERun (mkFrame Unit_string_stpcpy_os.fn___GI___stpcpy e [] None (Exec (TAtom "iw_2.iw_4.L7") (b_insts blk_t2) (b_jump blk_t2))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hu Ha Hw Hw64 Hk Hu0 Hn Hbyte Hs Ho Hox Hbd Hend Hreg.
  set (n := Z.of_nat (length s)) in *. set (S := (s ++ [0])%list) in *.
  assert (HS : Z.of_nat (length S) = n + 1) by (unfold S, n; rewrite length_app; cbn; lia).
  assert (HSn : forall j, 0 <= j < n -> 0 < nth (Z.to_nat j) S 0 < 256).
  { intros j Hj. unfold S. rewrite app_nth1; [|lia]. apply (Forall_nth (fun c => 0 < c < 256)); [exact Hs | lia]. }
  assert (HS0 : nth (Z.to_nat n) S 0 = 0) by (unfold S, n; rewrite app_nth2; [|lia]; rewrite Nat2Z.id Nat.sub_diag; reflexivity).
  remember (Z.to_nat (n - (k + u))) as r eqn:Hr.
  revert u e Hu Ha Hw Hu0 Hn Hbyte Hr. induction r as [r IH] using lt_wf_ind.
  intros u e Hu Ha Hw Hu0 Hn Hbyte Hr. iIntros "Hl Hb HK". cbn [blk_t2 b_insts b_jump].
  step. branch_symbolic. rewrite (Z.mod_small u); [|lia].
  assert (E : (u <? 8) = true) by (apply Z.ltb_lt; lia). rewrite E. cbn [edge_label].
  step. step. step. step. step. step.
  rewrite (stp_extract w u Hw64); [|lia].
  set (c := byte_of w u). assert (Hc : c = nth (Z.to_nat (k + u)) S 0) by (apply Hbyte; lia).
  assert (Hc8 : 0 <= c < 256) by apply byte_of_range.
  pose proof (length_stp_dst xs o (k + u) S Ho ltac:(lia) ltac:(lia)) as Hlen.
  iDestruct (bytes_store1 bd _ (Z.to_nat (o + k + u)) with "Hb") as (x) "[Hx Hb]"; [lia|].
  rewrite Z2Nat.id; [|lia].
  check "Hl".
  iApply (wp_raw_store_byte with "Hl Hx"); [vx | vx | reflexivity | a2 | wi_store |].
  iNext. iIntros "Hl Hx". rewrite (Z.mod_small (chr_w c)); [|apply chr_w_range]. rewrite (chr_w_byte c Hc8). iDestruct ("Hb" with "Hx") as "Hb".
  replace (Z.to_nat (o + k + u)) with (Z.to_nat (o + (k + u))) by lia.
  iEval (rewrite Hc stp_dst_byte; [|lia|lia|lia]) in "Hb".
  step. branch_symbolic. rewrite (Z.mod_small (chr_w c)); [|apply chr_w_range]. change (0 mod 2 ^ 32) with 0.
  rewrite chr_w_eqb; [|exact Hc8|lia].
  destruct (Z.eqb_spec c 0) as [Hz|Hz].
  - assert (Hkn : k + u = n).
    { destruct (Z.eq_dec (k + u) n) as [|Hne]; [assumption|]. exfalso. pose proof (HSn (k + u) ltac:(lia)). lia. }
    rewrite Hz. close_edge. step.
    iApply wp_ret; [reflexivity | vx |]. iNext.
    replace (k + u + 1) with (n + 1) by lia. replace (bd + o + k + u) with (bd + o + n) by lia.
    iApply ("HK" with "Hl Hb").
  - assert (Hkn : k + u < n) by (destruct (Z.eq_dec (k + u) n); [subst c; rewrite e0 HS0 in Hc; lia | lia]).
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_edge. step. step. step. step. step. cbn [ptr_addr ptr_cap].
    normp "iw_2.iw_4.pr.1" (bd + o + k + (u + 1)). norm "iw_2.iw_4.pr.2" (u + 1).
    replace (k + u + 1) with (k + (u + 1)) by lia.
    iApply (IH (Z.to_nat (n - (k + (u + 1)))) ltac:(lia) (u + 1) _ with "Hl Hb HK"); try lk_prove; try lia.
    intros t Ht Htn. apply Hbyte; lia.
Qed.
End rules.
