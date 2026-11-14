From Glibc Require Import GlibcProgram.
(** When a call of glibc's getopt looks for the next argument, it may
    return before it parses any option: no argument is left, or the
    argument is a nonoption that the ordering mode returns. A caller
    that calls getopt again relies on the session that each such return
    leaves behind. This file proves that the three early returns of the
    scanner leave a session at the new index over the permuted argument
    vector. The scanner does not touch the saved position, so the proof
    reuses the fact, known when the scan started, that the position is
    null or at the end of a string. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptArgv GetoptExchange GetoptReturn.
From Glibc Require FileInv GetoptArgv GetoptExchange GetoptInitialize GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## Indices after an early return

    Each early return leaves the public index somewhere the next call
    accepts. The controls below pick asymmetric pending blocks, so that
    an index taken from the wrong end of the block, or one word too far,
    would fail. *)

(** When the scan has used up all five words and two nonoptions wait
    at positions 1 and 2, the scanner sets the index back to 1, so that
    the caller finds them next. *)
Lemma scan_ctl_pending :
  (if 1 =? 3 then 5 else 1) = 1 /\ getopt_bounds 5 1 (mkGetoptState 1 1 0 null 1 null 1 1 3).
Proof. unfold getopt_bounds. cbn. split; [reflexivity | lia]. Qed.

(** When no nonoption waits, because the block starts and ends at 2,
    the scanner leaves the index at the count, 5. *)
Lemma scan_ctl_empty :
  (if 2 =? 2 then 5 else 2) = 5 /\ getopt_bounds 5 5 (mkGetoptState 5 1 0 null 1 null 1 2 2).
Proof. unfold getopt_bounds. cbn. split; [reflexivity | lia]. Qed.

(** The waiting block ends at index 3, and that index also meets the
    bounds. A caller that resumed at 3 would skip both nonoptions, so
    the proof must take the exact index from the code. *)
Lemma scan_ctl_last_index :
  getopt_bounds 5 3 (mkGetoptState 3 1 0 null 1 null 1 1 3) /\ (if 1 =? 3 then 5 else 1) <> 3.
Proof. unfold getopt_bounds. cbn. split; [lia | discriminate]. Qed.

(** When the scanner returns a nonoption as an argument, it moves the
    index forward by one word. From word 2 of three, the index reaches
    the count, which the bounds allow. From the count itself, the index
    would pass the count, which the bounds forbid. *)
Lemma scan_ctl_inorder : getopt_bounds 3 3 (mkGetoptState 3 1 0 null 1 null 1 0 0) /\
  ~ getopt_bounds 3 4 (mkGetoptState 4 1 0 null 1 null 1 0 0).
Proof. unfold getopt_bounds. cbn. lia. Qed.

(** A cursor inside a word needs an index below the count, so it could
    not survive the return at the count. That is why the proof needs the
    scan's start fact that the cursor is null or at a terminator. *)
Lemma scan_ctl_active_end : ~ (0 <= 3 < Z.of_nat (List.length [null; null; null])).
Proof. cbn. lia. Qed.


(** The return module supplies the argument vector, the private object and its rules. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L GetoptArgv.

(** This tactic enters a block that has no phi assignments. *)


Import ProgramAbbreviations.
Section scan_session_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}.
Existing Instance gen_heapGS0.
Lemma scan_session b r av ar ps i err oo a c o f l :
  1 <= Z.of_nat (List.length ps) < 2 ^ 31 -> 0 <= f <= l -> l <= Z.of_nat (List.length ps) ->
  f <= i <= Z.of_nat (List.length ps) -> 0 <= o <= 2 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (List.length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  (⌜c = null⌝ ∨ word_string DfracDiscarded c []) -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 4 err -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
  int_cell b 24 1 -∗ pcell b 32 c -∗ int_cell b 40 o -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  getopt_session b r av ar ps i.
Proof.
  intros Hn Hfl Hln Hfi Ho Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hc Hl Hi He Hoo Ha Hin Hcur Ho Hf Hla".
  iSplit; [iPureIntro; lia|]. iExists (mkGetoptState i err oo a 1 c o f l).
  iSplitL "Hl Hi He Hoo Ha Hin Hcur Ho Hf Hla"; [iFrame; iPureIntro; lia|].
  iSplit; [iPureIntro; unfold getopt_bounds; cbn; lia|]. iRight.
  iSplit; [iPureIntro; cbn; lia|].
  iDestruct "Hc" as "[%Hc | Hc]"; [iLeft; done | iRight; iLeft; done].
Qed.
End scan_session_values.
Section scan_session.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance ss_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The session after an early return

    An early return leaves the nine fields of the private object in the
    caller's hands. The next call needs them packed as a session at the
    new index. These lemmas pack them and then run the return itself. *)

(** The next call can resume after any early return because the
    scanner leaves the object in a known shape. The object is set up,
    its limits hold at the new index, and its saved position is null or
    points at a terminator. Such a position names no word, so the nine
    fields form a session over any argument vector of that length. *)

(** The scanner's early returns must leave a session. The caller keeps
    the five fields that the scanner does not touch: the error flag, the
    option character, the set-up flag, the saved position and nothing
    else of the cursor. It also keeps the fact that the position is null
    or at a terminator. Then each of the scanner's three early exits
    returns, either -1 or, for a nonoption in the returning order, 1.
    The caller learns that the argument vector was permuted and gets a
    session at the new index together with the vector. *)
Lemma scan_exits_session ks e n i o err oo c a b r av ar ps Φ :
  1 <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n -> 0 <= o <= 2 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  int_cell b 4 err -∗ int_cell b 8 oo -∗ int_cell b 24 1 -∗ pcell b 32 c -∗
  (⌜c = null⌝ ∨ word_string DfracDiscarded c []) -∗
  (∀ x ps' i', ⌜Permutation ps ps' /\ (x = 4294967295 \/ x = 1 /\ o <> 0)⌝ -∗
     getopt_session b r av ar ps' i' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     Φ (Ret (WInt x))) -∗
  ((∀ e' fr ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' /\ i' = n⌝ -∗
      live b r -∗ int_cell b 0 (if f' =? l' then i' else f') -∗ pcell b 16 a -∗ int_cell b 40 o -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L275") (Some fr))) : gexpr) {{ Φ }}) ∧
   (∀ e' ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' /\
        i <= i' < n /\ o = 0⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ pcell b 16 a -∗ int_cell b 40 o -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L316") (Some (TAtom "L289")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' /\
        i <= i' < n /\ o <> 0⌝ -∗
      live b r -∗ int_cell b 0 (i' + 1) -∗ pcell b 16 (nth (Z.to_nat i') ps' null) -∗ int_cell b 40 o -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L318") [] (b_jump getopt_blk318))) : gexpr)
        {{ Φ }})).
Proof.
  intros Hn Hlen Ho Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "He Hoo Hin Hcur #Hc HK".
  iSplit; [|iSplit].
  - iIntros (e' fr ps' i' f' l' (Hp & _ & Hfl & Hli & ->)) "Hl Hi Ha Ho Hf Hla Hva Hvc Hvs".
    assert (Hlen' : Z.of_nat (List.length ps') = n) by (rewrite -(Permutation_length Hp); exact Hlen).
    step. iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt 4294967295)); [reflexivity | reflexivity |].
    iNext. iApply ("HK" with "[%] [-Hva Hvc Hvs] Hva Hvc Hvs"); [split; [exact Hp | left; reflexivity] |].
    iApply (scan_session with "Hc Hl Hi He Hoo Ha Hin Hcur Ho Hf Hla");
      rewrite ?Hlen'; try lia; destruct (Z.eqb_spec f' l'); lia.
  - iIntros (e' ps' i' f' l' (Hp & _ & Hfl & Hli & Hii & Ho0)) "Hl Hi Ha Ho Hf Hla Hva Hvc Hvs".
    assert (Hlen' : Z.of_nat (List.length ps') = n) by (rewrite -(Permutation_length Hp); exact Hlen).
    step. iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt 4294967295)); [reflexivity | reflexivity |].
    iNext. iApply ("HK" with "[%] [-Hva Hvc Hvs] Hva Hvc Hvs"); [split; [exact Hp | left; reflexivity] |].
    iApply (scan_session with "Hc Hl Hi He Hoo Ha Hin Hcur Ho Hf Hla"); rewrite ?Hlen'; lia.
  - iIntros (e' ps' i' f' l' (Hp & _ & Hfl & Hli & Hii & Ho0)) "Hl Hi Ha Ho Hf Hla Hva Hvc Hvs".
    assert (Hlen' : Z.of_nat (List.length ps') = n) by (rewrite -(Permutation_length Hp); exact Hlen).
    unfold getopt_blk318; cbn [b_jump].
    iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt 1)); [reflexivity | reflexivity |].
    iNext. iApply ("HK" with "[%] [-Hva Hvc Hvs] Hva Hvc Hvs"); [split; [exact Hp | right; split; [reflexivity | exact Ho0]] |].
    iApply (scan_session with "Hc Hl Hi He Hoo Ha Hin Hcur Ho Hf Hla"); rewrite ?Hlen'; lia.
Qed.

End scan_session.
