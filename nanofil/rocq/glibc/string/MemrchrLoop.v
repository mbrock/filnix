(** After checking the word holding the last of the `n` bytes, glibc's
    `__memrchr` steps backwards through earlier 8-byte [[word|words]]
    until it finds a match or reaches the word containing `p`. In each
    word it tests for a matching byte, counts leading zeros in the match
    mask to locate the highest matching lane, and checks the start
    boundary `p` when it reaches the first word.

    To verify that backward scan at any ownership share, [rloop] proves
    the loop invariant by induction on the word index, assuming no byte
    after the current word matches. [MemrchrMask] enters this loop
    whenever the final word holds no matching byte. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpBits StrcmpLoop StrrchrLogic
  MemchrLast MemrchrCode MemrchrBits.
From Glibc Require StrcmpLoop WordString.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** Function [rblk] looks up a basic block by label in
    [glibc_memrchr]. *)
Definition rblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks glibc_memrchr) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.

(** Block `L83` is the backward word-loop header of [glibc_memrchr]. *)
Definition rblk83 : block := Eval vm_compute in rblk "L83".


(** Module [SL] supplies the step rules for symbolic execution. *)
(** Module [WS] provides word-window and fractional read helpers. *)
(** Module [LG] re-exports the program logic instance. *)
Module LG := LG0.
(** Module [L] re-exports the core logic definitions. *)
Module L := LG.L.
Import L LG WordString StrcmpLoop.

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

(** Tactic [sl] advances one pure `let` instruction while keeping its
    result expression symbolic. *)

(** Tactic [sn] advances one `let` instruction and names its integer
    result in the context. *)

(** Tactic [sf] advances one [[flight]] instruction in the proof mode. *)

(** Tactic [en] steps into the target block and exposes its instructions
    and terminator. *)

(** Tactic [sg] follows an unconditional `goto` and immediately enters the
    destination block. *)

(** Tactic [sb] advances one conditional `branch` while keeping its
    condition expression symbolic. *)

(** To resolve IR temporary arguments during symbolic execution, [vx]
    looks up each temporary in the environment hypotheses and evaluates
    the remaining argument expressions. *)

(** Tactic [sl'] advances one `let` instruction whose arguments are
    resolved via [vx]. *)

(** Tactic [norm] rewrites the integer stored in temporary `name` to `v`
    using tactic `tac`. *)
Ltac norm name v tac :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.
(** To keep intermediate integers readable, [normt] rewrites the
    integer in the newest temporary to `v` using tactic `tac`. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Tactic [normp] rewrites the address of the pointer stored in
    temporary `name` to `v` by arithmetic. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** Once a word tests positive for a matching byte at lane j,
    `__memrchr` computes its exact match mask and runs the 25-step
    leading-zero count to recover j. Tactic [idx_steps] steps through
    that sequence and reduces the resulting index to j. *)
Ltac idx_steps w c j Hj Hcj Hlj :=
  step_symbolic; step_symbolic; step_symbolic; step_symbolic; step_symbolic; normt (first_mask (Z.lxor w (rep c))) ltac:(reflexivity); step_symbolic; branch_symbolic;
  let Hmr := fresh in let Hh := fresh in let Hm0 := fresh in
  pose proof (marks_range w c) as Hmr; pose proof (head_marks w c j Hj Hcj Hlj) as Hh;
  assert (Hm0 : first_mask (Z.lxor w (rep c)) <> 0) by
    (let E := fresh in let B := fresh in intros E; pose proof (marks_byte w c j Hj) as B;
     rewrite E Hcj Z.eqb_refl in B; unfold byte_of in B;
     rewrite Z.div_0_l in B; [discriminate | apply Z.pow_nonzero; lia]);
  rewrite (Z.mod_small _ (2 ^ 64) Hmr) Zmod_0_l (proj2 (Z.eqb_neq _ _) Hm0); close_if; step;
  do 26 step_named;
  match goal with |- context [mkFrame _ (put _ (WInt ?t) _) _ _ _] =>
    let H := fresh in assert (H : t = head (first_mask (Z.lxor w (rep c)))) by (eapply head_chain; eassumption);
    rewrite H Hh; clear H end;
  repeat match goal with H : ?v = _ |- _ => is_var v; clear H end;
  (step; step); step_symbolic; step_symbolic; step_symbolic; normt j ltac:(arith); (step; step); step_symbolic; normt j ltac:(arith).

(** This lemma verifies the backward loop in `L83` by induction on word
    index i: assuming no byte after word i in the n-byte window matches
    c, `__memrchr` scans down to word zero, returns [hit_ptr] for
    [last_hit], and restores the window [wwin]. *)
Lemma rloop dq b reg wo ws cp c (k n i : nat) e r Φ :
  0 < b -> (cp = Obj b \/ cp = Ro b) -> 0 <= wo -> (b + wo) mod 8 = 0 ->
  b + wo + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 -> Forall (fun w => 0 <= w < 2 ^ 64) ws ->
  (k < 8)%nat -> (k + n <= 8 * List.length ws)%nat -> (8 * S i <= k + n)%nat ->
  none_in (wbytes ws) (c mod 256) (8 * S i) (k + n) ->
  last_hit (take n (drop k (wbytes ws))) (c mod 256) r ->
  lookup (TAtom "v77") e = Some (WInt (b + wo)) -> lookup (TAtom "v26") e = Some (WInt (b + wo + Z.of_nat k)) ->
  lookup (TAtom "iw_1.v7") e = Some (WInt (rep c)) ->
  wwin dq b reg wo ws -∗
  (wwin dq b reg wo ws -∗ Φ (Ret (WPtr (hit_ptr (mkPtr (b + wo + Z.of_nat k) cp) r)))) -∗
  WP (ERun (mkFrame glibc_memrchr (put (TAtom "pr.1") (WPtr (mkPtr (b + wo + 8 * Z.of_nat i) cp))
         (put (TAtom "pr.2") (WInt (wrd ws (Z.of_nat i))) e)) [] None
       (Exec (TAtom "L83") (b_insts rblk83) (b_jump rblk83))) : gexpr) {{ Φ }}.
Proof.
  intros Hb0 Hc Hwo Hal Hend Hreg Hr Hk Hkn.
  assert (HB : (k + n <= List.length (wbytes ws))%nat) by (rewrite wbytes_length; lia).
  revert e. induction i as [|i IH]; intros e Hi Hnone Hhit H77 H26 H7; iIntros "Hw HK"; cbn [rblk83 b_insts b_jump];
    step_symbolic; step_symbolic; branch_symbolic; cbn [ptr_addr].
  - (* The first word. *)
    replace (b + wo + 8 * Z.of_nat 0) with (b + wo) by lia. rewrite Z.eqb_refl. close_if. step.
    pose proof (wrd_range ws 0 Hr) as Hw0. set (w := wrd ws (Z.of_nat 0)) in *.
    step_symbolic. step_symbolic. step_symbolic. step_symbolic. step_symbolic. rewrite !(Z.mod_small w (2 ^ 64) Hw0) rep_mod.
    normt (loop_mask (Z.lxor w (rep c))) ltac:(reflexivity). step_symbolic. branch_symbolic.
    rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l.
    destruct (word_last w (c mod 256)) as [(j & Hj & Hcj & Hlj) | Hn].
    + assert (Hm : loop_mask (Z.lxor w (rep c)) <> 0).
      { intros E. apply (proj1 (has_eq_zero w c Hw0) E j Hj Hcj). }
      rewrite (proj2 (Z.eqb_neq _ _) Hm). close_if. step.
      idx_steps w c j Hj Hcj Hlj.
      step. normp "v121" (b + wo + j). step_symbolic. step_symbolic. branch_symbolic. cbn [ptr_addr ptr_cap].
      rewrite (Z.mod_small (b + wo + Z.of_nat k)); [|arith]. rewrite (Z.mod_small (b + wo + j)); [|arith].
      assert (Hv : wbytes ws !! (8 * 0 + Z.to_nat j)%nat = Some (c mod 256)) by (rewrite wbytes_at; [change (wrd ws (Z.of_nat 0)) with w; congruence | lia | exact Hj]).
      pose proof (none_after ws (c mod 256) 0 j (k + n) ltac:(lia) Hj Hlj Hnone) as Hna.
      destruct (Z.leb_spec (b + wo + Z.of_nat k) (b + wo + j)) as [Hge|Hlt].
      * (* At or after the first byte: the match. *)
        close_if. step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
        rewrite (last_hit_unique _ _ _ _ Hhit (hit_at _ _ k n (8 * 0 + Z.to_nat j) HB
                   ltac:(lia) Hv Hna)).
        cbn [hit_ptr ptr_addr ptr_cap]. replace (b + wo + Z.of_nat k + Z.of_nat (8 * 0 + Z.to_nat j - k)) with (b + wo + j)
          by lia. iApply ("HK" with "Hw").
      * (* Before it: none. *)
        close_if. step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
        rewrite (last_hit_unique _ _ _ _ Hhit (hit_none _ _ k n HB
                   ltac:(intros u Hu; apply Hna; lia))).
        iApply ("HK" with "Hw").
    + (* No c in the first word: none. *)
      rewrite (proj2 (has_eq_zero w c Hw0) Hn). close_if. step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      pose proof (none_word ws (c mod 256) 0 (k + n) ltac:(lia) Hn Hnone) as Hnw.
      rewrite (last_hit_unique _ _ _ _ Hhit (hit_none _ _ k n HB
                 ltac:(intros u Hu; apply Hnw; lia))).
      iApply ("HK" with "Hw").
  - (* A word after the first. *)
    rewrite (Z.mod_small (b + wo + 8 * Z.of_nat (S i))); [|arith]. rewrite (Z.mod_small (b + wo)); [|arith].
    rewrite (proj2 (Z.eqb_neq _ _)); [|lia]. close_if. step.
    pose proof (wrd_range ws (Z.of_nat (S i)) Hr) as Hw0. set (w := wrd ws (Z.of_nat (S i))) in *.
    step_symbolic. step_symbolic. step_symbolic. step_symbolic. step_symbolic. rewrite !(Z.mod_small w (2 ^ 64) Hw0) rep_mod.
    normt (loop_mask (Z.lxor w (rep c))) ltac:(reflexivity). step_symbolic. branch_symbolic.
    rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l.
    destruct (word_last w (c mod 256)) as [(j & Hj & Hcj & Hlj) | Hn].
    + (* Its last c. *)
      assert (Hm : loop_mask (Z.lxor w (rep c)) <> 0).
      { intros E. apply (proj1 (has_eq_zero w c Hw0) E j Hj Hcj). }
      rewrite (proj2 (Z.eqb_neq _ _) Hm). close_if. step.
      idx_steps w c j Hj Hcj Hlj.
      step. normp "v103" (b + wo + 8 * Z.of_nat (S i) + j).
      iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      assert (Hv : wbytes ws !! (8 * S i + Z.to_nat j)%nat = Some (c mod 256))
        by (rewrite wbytes_at; [change (wrd ws (Z.of_nat (S i))) with w; congruence | lia | exact Hj]).
      pose proof (none_after ws (c mod 256) (S i) j (k + n) ltac:(lia) Hj Hlj Hnone) as Hna.
      rewrite (last_hit_unique _ _ _ _ Hhit (hit_at _ _ k n (8 * S i + Z.to_nat j) HB ltac:(lia) Hv Hna)).
      cbn [hit_ptr ptr_addr ptr_cap].
      replace (b + wo + Z.of_nat k + Z.of_nat (8 * S i + Z.to_nat j - k)) with (b + wo + 8 * Z.of_nat (S i) + j)
        by lia. iApply ("HK" with "Hw").
    + (* No c: the word before. *)
      rewrite (proj2 (has_eq_zero w c Hw0) Hn). close_if. step.
      pose proof (none_word ws (c mod 256) (S i) (k + n) ltac:(lia) Hn Hnone) as Hnw.
      step. normp "v106" (b + wo + 8 * Z.of_nat i). cbn [ptr_cap].
      iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ (mkPtr (b + wo + 8 * Z.of_nat i) cp) dq b reg wo ws
                (Z.of_nat i) with "Hw"); [reflexivity | exact Hc | reflexivity | lia | exact Hb0 | exact Hwo
                | exact Hend | exact Hreg | exact Hr |].
      iIntros "Hw". (step; step). rewrite (Z.mod_small _ _ (wrd_range ws (Z.of_nat i) Hr)).
      iApply (IH with "Hw HK"); [lia | intros u Hu; apply Hnw; lia | exact Hhit | look H77 | look H26 | look H7].
Qed.

End rules.
