(** Once glibc's `__memchr` computes the match mask for the first aligned
    word and shifts away any bytes before `p`, control branches on
    whether a candidate byte matched. This module proves [memchr_hit]
    for a match in the first word, which still checks whether the match
    lies within the `n`-byte bound, and [memchr_next] for the no-match
    path, which either returns null or loads the next word and enters
    [MemchrLoop]'s loop. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrchrCode MemchrLast MemchrLoop.
From Glibc Require MemchrLast MemchrLoop WordString.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** Shifting the match mask of the first word down by `a mod 8` bytes
    places 128 in lane i whenever lane `i + a mod 8` of w matches
    `c mod 256`, and zero in lanes past the word boundary. *)
Lemma first_hit_byte w c a i : 0 <= a -> 0 <= i ->
  byte_of (first_shift (Z.lxor w (rep c)) a) i =
  if i + a mod 8 <? 8 then (if byte_of w (i + a mod 8) =? c mod 256 then 128 else 0) else 0.
Proof.
  intros Ha Hi. rewrite first_shift_byte; [|lia|lia]. destruct (Z.ltb_spec (i + a mod 8) 8); [|reflexivity].
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  destruct (Z.eqb_spec (byte_of (Z.lxor w (rep c)) (i + a mod 8)) 0) as [E|E];
    destruct (Z.eqb_spec (byte_of w (i + a mod 8)) (c mod 256)) as [E'|E']; try reflexivity.
  - exfalso. apply E'. apply xor_zero; [lia | exact E].
  - exfalso. apply E. apply xor_zero; [lia | exact E'].
Qed.

(** Tactic [ar] unfolds pointer and address projections, strips
    64-bit wraps that fit in range, and solves linear or division goals. *)
Ltac ar := cbn [ptr_addr ptr_cap extension]; unfold raw_address;
  change (2 ^ 64) with 18446744073709551616 in *; change (2 ^ 48) with 281474976710656 in *;
  change (2 ^ 32) with 4294967296 in *;
  repeat match goal with |- context [?x mod 18446744073709551616] =>
    rewrite (Z.mod_small x 18446744073709551616); [|lia] end;
  first [lia | Z.div_mod_to_equations; lia].

(** To keep integer expressions in the environment readable, [si]
    rewrites the integer stored in temporary `name` to `v`. *)
Ltac si name v :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by first [reflexivity | ar] end.
(** Tactic [lk] resolves a lookup in the environment by skipping over
    newer `put` bindings until it reaches hypothesis H. *)
Ltac lk H := repeat (rewrite lookup_after_put_other; [|reflexivity]);
  first [rewrite lookup_after_put_same; reflexivity | exact H].
(** Tactic [sp] normalizes the address stored in pointer temporary
    `name` to `v` by computation or [ar]. *)
Ltac sp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by first [reflexivity | ar] end.


Module LG := LG0.
Module L := LG.L.
Import L LG WordString MemchrLast MemchrLoop.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** To step through IR instructions in [[separation-logic|separation logic]],
    [rules_irisGS] connects the contract registry and world invariant `wi`
    to the Iris program logic. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** This shorthand names the expression type of the instantiated
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** To step past pure instructions without manual boilerplate, [st]
    advances one pure `let`, [[flight]], block entry, or `goto` step
    whose premises reduce. *)


(** When the first word contains a matching byte, `__memchr` counts
    trailing bits in the shifted mask to locate the matching byte index
    and checks whether it falls within the search bound. Lemma
    [memchr_hit] verifies that path, returning the matching pointer when
    in bounds and null otherwise. *)
Lemma memchr_hit e from m j a c0 E Φ :
  0 <= m < 2 ^ 64 -> (forall i, 0 <= i < 8 -> byte_of m i = 0 \/ byte_of m i = 128) ->
  0 <= j < 8 -> byte_of m j = 128 -> (forall i, 0 <= i < j -> byte_of m i = 0) ->
  0 <= a <= 2 ^ 48 -> 0 <= E < 2 ^ 64 ->
  lookup (TAtom "iw_5.v12") e = Some (WInt m) -> lookup (TAtom "v0") e = Some (WPtr (mkPtr a c0)) ->
  lookup (TAtom "v40") e = Some (WInt E) ->
  Φ (Ret (WPtr (hit_ptr (mkPtr a c0) (if a + j <=? E then Some (Z.to_nat j) else None)))) -∗
  WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "iw_6.start") from)) : gexpr) {{ Φ }}.
Proof.
  intros Hmr H01 Hj Hb Hlow Ha HE H12 H0 H40. iIntros "HK".
  assert (Hm0 : (m =? 0) = false).
  { apply Z.eqb_neq. intros E'. rewrite E' in Hb. unfold byte_of in Hb. rewrite Z.div_0_l in Hb; [discriminate|].
    apply Z.pow_nonzero; lia. }
  iApply wp_enter; [reflexivity | by destruct from |]. iNext. cbn [b_insts b_jump].
  step. iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small m (2 ^ 64) Hmr) Zmod_0_l Hm0. close_if.
  do 16 (step; gen_top). set_tail "iw_6.iw_1.iw_1.v22" m.
  rewrite (tail_first m j Hmr H01 ltac:(lia) Hb Hlow).
  step. step. si "iw_6.iw_1.iw_1.v23" (8 * j + 7).
  step. change (2 ^ ((3 mod 2 ^ 32) mod 32)) with 8. si "iw_6.iw_1.v27" j. step. si "v59" j. step. sp "v60" (a + j).
  step. si "v66" (a + j).
  step. iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (a + j) (2 ^ 64)); [|zl]. rewrite (Z.mod_small E (2 ^ 64)); [|zl].
  destruct (Z.leb_spec (a + j) E) as [Hle|Hle].
  - replace ((if a + j <=? E then 1 else 0) mod 2 ^ 32 =? 0) with false
      by (rewrite (proj2 (Z.leb_le _ _) Hle); reflexivity).
    cbn [edge_label]. step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    cbn [hit_ptr ptr_addr ptr_cap].
    rewrite Z2Nat.id; [|lia]. iExact "HK".
  - replace ((if a + j <=? E then 1 else 0) mod 2 ^ 32 =? 0) with true
      by (rewrite (proj2 (Z.leb_gt _ _) Hle); reflexivity).
    cbn [edge_label]. step. step. step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    iExact "HK".
Qed.

(** When the first word holds no match, `__memchr` checks whether the
    first word is also the last; if so it returns null, and otherwise it
    loads the next word and enters the word loop. Lemma [memchr_next]
    proves this transition from block `L52` into [memchr_loop], restoring
    all memory pieces at the end. *)
Lemma memchr_next dq b reg w ws A c0 c1 e from c E r Φ :
  (c0 = Obj b \/ c0 = Ro b) -> 0 < b -> b <= A -> A mod 8 = 0 ->
  A + 8 * Z.of_nat (List.length (w :: ws)) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws -> A <= E < 2 ^ 64 ->
  lookup (TAtom "v19") e = Some (WPtr (mkPtr A c0)) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr A c0)) ->
  lookup (TAtom "v43") e = Some (WPtr (mkPtr (E - E mod 8) c1)) ->
  lookup (TAtom "iw_1.v7") e = Some (WInt (rep c)) -> lookup (TAtom "v40") e = Some (WInt E) ->
  (E < A + 8 -> r = None) -> (A + 8 <= E -> ws <> [] /\ loop_hit (wbytes ws) (c mod 256) (A + 8) E r) ->
  liveq dq b reg -∗ ptsq dq (words_ps b (A - b) (w :: ws)) -∗
  (liveq dq b reg -∗ ptsq dq (words_ps b (A - b) (w :: ws)) -∗ Φ (Ret (WPtr (hit_ptr (mkPtr (A + 8) c0) r)))) -∗
  WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "L52") from)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hb0 HbA Hal Hend Hreg Hr HE H19 Hchk H43 H7 H40 Hlast Hnext. iIntros "Hl Hps HK".
  cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  pose proof (Nat2Z.is_nonneg (List.length ws)) as Hws.
  pose proof (Z.mod_pos_bound E 8 ltac:(lia)) as HE8.
  iApply wp_enter; [reflexivity | by destruct from |]. iNext. cbn [b_insts b_jump].
  step. step. step. iApply wp_branch; [reflexivity|]. iNext. cbn [ptr_addr].
  rewrite (Z.mod_small A (2 ^ 64)); [|zl]. rewrite (Z.mod_small (E - E mod 8) (2 ^ 64)); [|zl].
  destruct (Z.eqb_spec A (E - E mod 8)) as [HA|HA].
  - (* The word is the last. *)
    rewrite Hlast; [|lia]. change ((if true then 1 else 0) mod 2 ^ 32 =? 0) with false. cbn [edge_label].
    step. iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "Hl Hps").
  - change ((if false then 1 else 0) mod 2 ^ 32 =? 0) with true. cbn [edge_label].
    assert (Hnx : A + 8 <= E) by (clear -Hal HA HE HE8; zl).
    destruct (Hnext Hnx) as (Hws' & Hhit'). destruct ws as [|w1 ws]; [done|].
    apply Forall_cons_1 in Hr as [Hw1 Hr'].
    step. step. sp "v82" (A + 8).
    cbn [words_ps]. rewrite !ptsq_app. iDestruct "Hps" as "(Hw & Hw1 & Hps)".
    iApply (wp_half_check_read_dq with "Hl").
    { reflexivity. } { vx. } { reflexivity. } { exact Hc. } { ar. } { cbn [List.length] in Hend; ar. }
    { lia. } { zl. } { apply Z.mod_1_r. }
    iNext. iIntros "Hl".
    iApply (wp_raw_load_read_dq with "Hl Hw1"); [reflexivity | reflexivity | exact Hc | ar |].
    iNext. iIntros "Hl Hw1". rewrite (Z.mod_small w1 (2 ^ 64) Hw1). step.
    iApply (memchr_loop _ _ _ dq b reg w1 ws (A - b + 8) _ (Some (TAtom "L74")) (mkPtr (A + 8) c0) c E r
              with "Hl [Hw1 Hps] [Hw HK]").
    * exact Hc.
    * lia.
    * exact Hb0.
    * replace (b + (A - b + 8)) with (A + 1 * 8) by ring. rewrite Z_mod_plus_full. exact Hal.
    * cbn. lia.
    * cbn [List.length] in Hend |- *. lia.
    * exact Hreg.
    * constructor; [exact Hw1 | exact Hr'].
    * zl.
    * reflexivity.
    * lk H43.
    * lk H7.
    * lk H40.
    * replace (b + (A - b + 8)) with (A + 8) by ring. exact Hhit'.
    * cbn [words_ps]. rewrite ptsq_app. replace (A - b + 8 + 8) with (A - b + 8 + 8) by ring. iFrame.
    * iIntros "Hl Hps". iApply ("HK" with "Hl"). cbn [words_ps]. rewrite !ptsq_app. iFrame.
Qed.

End rules.
