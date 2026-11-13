(** After testing the first aligned word, glibc's `__memchr` steps
    through subsequent 8-byte [[word|words]] one at a time until it
    finds a matching byte or reaches the word containing the end of the
    search range. This module proves the loop invariant [memchr_loop] at
    any ownership share, handing off the final word to [MemchrLast]'s
    [memchr_last] so that [MemchrFirst] and [MemchrLogic] can verify the
    whole function. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrchrCode MemchrLast.
Open Scope Z_scope.
Open Scope list_scope.

(** To keep the loop proof independent of a specific runtime
    implementation, [MemchrLoopOn] parameterizes it over a [[runtime]] R
    and program logic instance LG0. *)
Module MemchrLoopOn (R : Runtime) (LG0 : LogicSig R).
Module ML := MemchrLastOn R LG0.
Module WS := ML.WS.
Module LG := LG0.
Module L := LG.L.
Import L LG WS ML.

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
Ltac st :=
  first
    [ iApply wp_let; [reflexivity | reflexivity | vx | intros ?; reflexivity | iNext]
    | iApply wp_flight; [vx | reflexivity | vx | iNext]
    | iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]
    | iApply wp_goto; iNext ].

(** To verify the main search loop over any number of words,
    [memchr_loop_ind] proves by Löb induction that starting at 8-aligned
    word pointer q in block `L84`, `__memchr` either finds a match in q,
    advances to the next word, or delegates the final word to
    [memchr_last]. It returns [hit_ptr] and restores the live [[region]]
    and word pieces. *)
Lemma memchr_loop_ind (dq : dfrac) (b : Z) (reg : region) (c E : Z) (Φ : outcome -> iProp Σ) :
  0 < b -> r_end reg <= 2 ^ 48 ->
  ⊢ ∀ (w : Z) (ws : list Z) (o : Z) (e : list (name * word)) (from : option name) (q : ptr) (r : option nat),
    ⌜(ptr_cap q = Obj b \/ ptr_cap q = Ro b)%Z⌝ -∗ ⌜(0 <= o)%Z⌝ -∗ ⌜((b + o) mod 8 = 0)%Z⌝ -∗ ⌜(ptr_addr q = b + o)%Z⌝ -∗
    ⌜(b + o + 8 * Z.of_nat (List.length (w :: ws)) <= r_end reg)%Z⌝ -∗
    ⌜(Forall (fun w => 0 <= w < 2 ^ 64) (w :: ws))%Z⌝ -∗ ⌜(b + o <= E < 2 ^ 64)%Z⌝ -∗
    ⌜(phis_env ge (b_phis memchr_blk84) from e =
       Some (put (TAtom "pr.1") (WPtr q) (put (TAtom "pr.2") (WInt (w mod 2 ^ 64)) e)))%Z⌝ -∗
    ⌜(lookup (TAtom "v78") e = Some (WInt (E - E mod 8)))%Z⌝ -∗ ⌜(lookup (TAtom "iw_1.v7") e = Some (WInt (rep c)))%Z⌝ -∗
    ⌜(lookup (TAtom "v40") e = Some (WInt E))%Z⌝ -∗
    ⌜(loop_hit (wbytes (w :: ws)) (c mod 256) (b + o) E r)%Z⌝ -∗
    liveq dq b reg -∗ ptsq dq (words_ps b o (w :: ws)) -∗
    (liveq dq b reg -∗ ptsq dq (words_ps b o (w :: ws)) -∗ Φ (Ret (WPtr (hit_ptr q r)))) -∗
    WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "L84") from)) : gexpr) {{ Φ }}.
Proof.
  intros Hb0 Hreg. iLöb as "IH".
  iIntros (w ws o e from q r Hc Ho Hal Hq Hend Hr HE Hphi H78 H7 H40 Hhit) "Hl Hps HK".
  destruct (Z.eq_dec (b + o) (E - E mod 8)) as [HA|HA].
  { iApply (memchr_last with "Hl Hps HK"); eauto. }
  iApply wp_enter; [reflexivity | exact Hphi |]. iNext. cbn [b_insts b_jump memchr_blk84].
  pose proof (Z.mod_pos_bound E 8 ltac:(lia)) as HE8.
  apply Forall_cons_1 in Hr as [Hw0 Hr]. cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  pose proof (Nat2Z.is_nonneg (List.length ws)) as Hws.
  st. st. rewrite Hq (Z.mod_small (b + o)); [|zl]. rewrite (Z.mod_small (E - E mod 8)); [|zl].
  iApply wp_branch; [reflexivity|]. iNext.
  rewrite (proj2 (Z.eqb_neq _ _) HA). cbn [negb].
  change (1 mod 2 ^ 32 =? 0) with false. cbn [edge_label].
  st. do 6 st. rewrite !(Z.mod_small w (2 ^ 64) Hw0) rep_mod.
  set_int "iw_7.iw_1.iw_1.v13" (loop_mask (Z.lxor w (rep c))).
  iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l.
  destruct (hit_word w ws (c mod 256) (b + o) E r ltac:(zl) Hhit)
    as [(j & Hj & -> & Hcj & Hlj) | (Hn & Hws' & H8 & Hhit')].
  + destruct (mask_first w c j Hj Hcj Hlj) as [Hm Ht]. rewrite (proj2 (Z.eqb_neq _ _) Hm). close_if.
    st. st. iApply wp_branch; [reflexivity|]. iNext.
    rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l (proj2 (Z.eqb_neq _ _) Hm).
    close_if. do 16 (st; gen_top).
    set_tail "iw_8.iw_3.iw_1.iw_1.v22" (loop_mask (Z.lxor w (rep c))). rewrite Ht.
    st. st. set_int "iw_8.iw_3.iw_1.iw_1.v23" (8 * j + 7).
    st. set_int "iw_8.iw_3.iw_1.v27" j. st. set_int "v103" j. st. set_ptr "v104" (b + o + j).
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    cbn [hit_ptr]. rewrite Z2Nat.id; [|lia]. rewrite Hq. iApply ("HK" with "Hl Hps").
  + rewrite (mask_none w c Hn). close_if.
    destruct ws as [|w1 ws]; [done|]. apply Forall_cons_1 in Hr as [Hw1 Hr'].
    st. st. set_ptr "v107" (b + o + 8).
    cbn [words_ps]. rewrite !ptsq_app. iDestruct "Hps" as "(Hw & Hw1 & Hps)".
    iApply (wp_check_read_dq with "Hl").
    { reflexivity. } { reflexivity. } { exact Hc. } { arith. } { cbn [List.length] in Hend; arith. } { apply Z.mod_1_r. }
    iNext. iIntros "Hl".
    iApply (wp_raw_load_read_dq with "Hl Hw1"); [reflexivity | reflexivity | exact Hc | arith |].
    iNext. iIntros "Hl Hw1". rewrite (Z.mod_small w1 (2 ^ 64) Hw1).
    st. iApply ("IH" $! w1 ws (o + 8) _ (Some (TAtom "L94")) (mkPtr (b + o + 8) (ptr_cap q))
                  (option_map (fun t => t - 8)%nat r) with "[] [] [] [] [] [] [] [] [] [] [] [] Hl [Hw1 Hps] [Hw HK]").
    all: try iPureIntro.
    * exact Hc.
    * lia.
    * replace (b + (o + 8)) with (b + o + 1 * 8) by ring. rewrite Z_mod_plus_full. exact Hal.
    * cbn. lia.
    * cbn [List.length] in Hend |- *. lia.
    * constructor; [exact Hw1 | exact Hr'].
    * zl.
    * reflexivity.
    * look H78.
    * look H7.
    * look H40.
    * replace (b + (o + 8)) with (b + o + 8) by ring. exact Hhit'.
    * cbn [words_ps]. rewrite ptsq_app. iFrame.
    * iIntros "Hl Hps". cbn [words_ps]. rewrite ptsq_app. iDestruct "Hps" as "[Hw1 Hps]".
      replace (hit_ptr (mkPtr (b + o + 8) (ptr_cap q)) (option_map (fun t => t - 8)%nat r)) with (hit_ptr q r).
      { iApply ("HK" with "Hl"). iFrame. }
      destruct r as [t|]; [|reflexivity]. specialize (H8 t eq_refl). cbn [hit_ptr option_map].
      rewrite Hq Nat2Z.inj_sub; [|exact H8]. f_equal. cbn [ptr_addr]. lia.
Qed.

(** Lemma [memchr_loop] wraps [memchr_loop_ind] with ordinary Rocq
    premises so callers can apply the loop rule directly without Iris
    magic-wand currying. *)
Lemma memchr_loop dq b reg w ws o e from q c E r Φ :
  (ptr_cap q = Obj b \/ ptr_cap q = Ro b) -> 0 <= o -> 0 < b -> (b + o) mod 8 = 0 -> ptr_addr q = b + o ->
  b + o + 8 * Z.of_nat (List.length (w :: ws)) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) (w :: ws) -> b + o <= E < 2 ^ 64 ->
  phis_env ge (b_phis memchr_blk84) from e =
    Some (put (TAtom "pr.1") (WPtr q) (put (TAtom "pr.2") (WInt (w mod 2 ^ 64)) e)) ->
  lookup (TAtom "v78") e = Some (WInt (E - E mod 8)) -> lookup (TAtom "iw_1.v7") e = Some (WInt (rep c)) ->
  lookup (TAtom "v40") e = Some (WInt E) ->
  loop_hit (wbytes (w :: ws)) (c mod 256) (b + o) E r ->
  liveq dq b reg -∗ ptsq dq (words_ps b o (w :: ws)) -∗
  (liveq dq b reg -∗ ptsq dq (words_ps b o (w :: ws)) -∗ Φ (Ret (WPtr (hit_ptr q r)))) -∗
  WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "L84") from)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Ho Hb0 Hal Hq Hend Hreg Hr HE Hphi H78 H7 H40 Hhit. iIntros "Hl Hps HK".
  iApply (memchr_loop_ind dq b reg c E Φ Hb0 Hreg $! w ws o e from q r
            with "[//] [//] [//] [//] [//] [//] [//] [//] [//] [//] [//] [//] Hl Hps HK").
Qed.

End rules.
End MemchrLoopOn.
