(** When snprintf finishes writing an unknown error message, it stores a
    NUL in its output window. The next print reads that message a word
    at a time. The last word may contain bytes after the first NUL;
    the reader gets those bytes as they are, not as zero padding. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv StrlenBits StrlenLogic WordString StartJoin PrintfOut.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** A byte before the terminator that snprintf writes might already
    be zero. Splitting at the first zero gives the string that a
    subsequent reader sees. *)
Local Lemma first_nul xs : In 0 xs -> Forall (fun c => 0 <= c < 256) xs ->
  exists s rest, xs = s ++ 0 :: rest /\ Forall (fun c => 0 < c < 256) s.
Proof.
  induction xs as [|c xs IH]; [inversion 1|]. intros [->|Hin] Hbytes.
  - exists [], xs. split; constructor.
  - inversion Hbytes as [|? ? Hc Hxs]; subst. destruct (Z.eq_dec c 0) as [->|Hnz].
    + exists [], xs. split; constructor.
    + destruct (IH Hin Hxs) as (s & rest & -> & Hs).
      exists (c :: s), rest. split; [reflexivity|constructor; [lia|assumption]].
Qed.

Section window.
Context `{!gen_heapGS piece pval Σ}.

(** A NUL anywhere in the 1024-byte scratch buffer suffices. Only the
    words through the terminator belong to the returned string. *)
Lemma report_buffer_string b reg xs :
  0 < b -> b mod 8 = 0 -> b+1024 <= r_end reg -> r_end reg <= 2^48 ->
  length xs = 1024%nat -> Forall (fun c => 0 <= c < 256) xs -> In 0 xs ->
  live b reg -∗ bytes b 0 xs -∗ ∃ s, word_string (DfracOwn 1) (mkPtr b (Obj b)) s.
Proof using Type.
  intros Hb Hal Hfit Hspace Hlen Hbytes Hin.
  destruct (first_nul xs Hin Hbytes) as (s & rest & Hxs & Hs).
  assert (Ls : (length s < length xs)%nat) by (rewrite Hxs length_app; cbn; lia).
  set (n := Z.to_nat ((Z.of_nat (length s) + 8) / 8)).
  assert (Hn : Z.of_nat n = (Z.of_nat (length s) + 8) / 8)
    by (unfold n; rewrite Z2Nat.id; [reflexivity|apply Z.div_pos; lia]).
  assert (Hwindow : (S (length s) <= 8*n <= length xs)%nat) by (Z.div_mod_to_equations; lia).
  destruct (words_of_ok n (take (8*n) xs) ltac:(rewrite length_take; lia) (Forall_take _ _ _ Hbytes))
    as (Ew & Hw & Lw).
  iIntros "Hl Hxs". iDestruct (bytes_take_drop with "Hxs") as "[Hpre _]"; [exact (proj2 Hwindow)|].
  iExists s, b, reg, (words_of n (take (8*n) xs)). iSplit.
  - iPureIntro. constructor; unfold wstart; cbn [ptr_cap ptr_addr]; rewrite ?Hal ?Lw.
    all: try (by left). all: try assumption. all: try lia.
    rewrite Ew. cbn [Z.to_nat drop]. rewrite firstn_firstn Nat.min_l; [|lia].
    rewrite Hxs firstn_app firstn_all2; [|lia]. replace (S (length s) - length s)%nat with 1%nat by lia. reflexivity.
  - rewrite /wwin /wstart /= Hal Z.sub_0_r Z.sub_diag start_words_ps_bytes Ew. iFrame.
Qed.

(** The flush and finish routines choose different positions for the
    terminator. Either can take the byte at its chosen offset and,
    after storing zero there, turn the window into a readable string. *)
Lemma report_terminate b reg o :
  0 < b -> b mod 8 = 0 -> b+1024 <= r_end reg -> r_end reg <= 2^48 -> 0 <= o < 1024 ->
  win_own b b (b+1024) -∗ ∃ x, ibyte b o x ∗
    (ibyte b o 0 -∗ live b reg -∗ ∃ s, word_string (DfracOwn 1) (mkPtr b (Obj b)) s).
Proof using Type.
  intros Hb Hal Hfit Hspace Ho. iIntros "(%xs & %cs & (%L & _ & %Hbytes) & Hxs & _)".
  rewrite Z.sub_diag. set (i := Z.to_nat o). assert (Hi : (i < length xs)%nat) by (unfold i; lia).
  destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hx].
  set (pre := take i xs). set (post := drop (S i) xs).
  pose proof (take_drop_middle xs i x Hx) as E. fold pre post in E.
  assert (Lo : 0 + Z.of_nat (length pre) = o) by (unfold pre, i; rewrite length_take; lia).
  iEval (rewrite -E bytes_app Lo /bytes byte_ps_cons) in "Hxs".
  iDestruct "Hxs" as "[Hpre [Hx Hpost]]". iExists x. iSplitL "Hx"; [by iFrame|].
  iIntros "Hz Hl". iApply (report_buffer_string _ _ (pre ++ 0 :: post) with "Hl [Hpre Hz Hpost]"); try assumption.
  - rewrite length_app. cbn [length]. rewrite -E length_app in L. cbn [length] in L. lia.
  - apply Forall_app. split; [apply Forall_take; assumption|]. constructor; [lia|apply Forall_drop; assumption].
  - apply in_or_app. right. now left.
  - rewrite bytes_app Lo /bytes byte_ps_cons. iFrame. iEval (rewrite /ibyte /pts big_sepL_singleton) in "Hz". iExact "Hz".
Qed.

End window.
