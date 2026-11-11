(** The word loop of glibc's own `__memrchr` (MemrchrCode.v's
    [glibc_memrchr]) over a window of words (WordString.v's [wwin]) at
    any share, for MemrchrMask.v's last word.

    After the word that holds the last of the n bytes, glibc's memrchr
    reads the words before it one by one, down to the one that holds
    the first byte. It tests each for c's byte with `has_eq`
    ([loop_mask] of the word xor'd with [rep] c, [has_eq_zero]), and in
    a word that has one takes the index of the last from the count of
    leading zeros of its marks ([idx_steps], MemrchrBits.v's
    [head_marks]). A match in a word above the first is the answer; in
    the first word it is the answer only at or after the first byte.
    [rloop] proves the loop by induction on the word's index, with no
    byte c after it among the n ([none_in]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpBits StrcmpLoop StrrchrLogic
  MemchrLast MemrchrCode MemrchrBits.
Open Scope Z_scope.
Open Scope list_scope.

(** A block of glibc's memrchr. *)
Definition rblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks glibc_memrchr) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.

(** The loop's block, L83. *)
Definition rblk83 : block := Eval vm_compute in rblk "L83".

(** The loop over the [[runtime]] R and the Logic instance LG0. *)
Module MemrchrLoopOn (R : Runtime) (LG0 : LogicSig R).
(** The step rules of the proof mode. *)
Module SL := StrcmpLoopOn R LG0.
(** Strings' windows. *)
Module WS := SL.WS.
(** The Logic instance. *)
Module LG := LG0.
(** The language of the Logic instance. *)
Module L := LG.L.
Import L LG WS SL.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A let, its value left whole. *)
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** A let, its integer named. *)
Ltac sn := eapply (s_letn registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.
(** A flight. *)
Ltac sf := eapply (s_flight registry wi ge); [reflexivity | reflexivity | reflexivity |].
(** Entering a block. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** A goto and the block it enters. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** A branch, its condition left whole. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** Read the temporaries of the frame's environment below its puts by
    the hypotheses about them there, then compute the rest. *)
Ltac vx :=
  cbn [map2_option map_option flight_arg_x flight_cap arg_x];
  repeat match goal with |- context [value_x ?g ?E ?k (Tmp ?n)] =>
    match goal with H : lookup n _ = Some ?x |- _ =>
      rewrite (value_x_tmp g E k n x); [|look H] end end;
  reflexivity.
(** A let that may read the environment below the puts. *)
Ltac sl' := eapply (s_let registry wi ge); [reflexivity | reflexivity | vx | intros ?; reflexivity |].
(** Replace the integer the temporary name holds by v, proved by tac. *)
Ltac norm name v tac :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.
(** Replace the integer the newest temporary holds by v, proved by tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Replace the address of the pointer the temporary name holds by v. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** From the test of a word w in range whose last c is at byte j, Hj,
    Hcj and Hlj saying so: its marks, their count of leading zeros by
    [head_chain] and [head_marks], and the index j, glibc's
    `index_last_eq`. *)
Ltac idx_steps w c j Hj Hcj Hlj :=
  sl; sl; sl; sl; sl; normt (first_mask (Z.lxor w (rep c))) ltac:(reflexivity); sl; sb;
  let Hmr := fresh in let Hh := fresh in let Hm0 := fresh in
  pose proof (marks_range w c) as Hmr; pose proof (head_marks w c j Hj Hcj Hlj) as Hh;
  assert (Hm0 : first_mask (Z.lxor w (rep c)) <> 0) by
    (let E := fresh in let B := fresh in intros E; pose proof (marks_byte w c j Hj) as B;
     rewrite E Hcj Z.eqb_refl in B; unfold byte_of in B;
     rewrite Z.div_0_l in B; [discriminate | apply Z.pow_nonzero; lia]);
  rewrite (Z.mod_small _ (2 ^ 64) Hmr) Zmod_0_l (proj2 (Z.eqb_neq _ _) Hm0); close_if; en;
  do 26 sn;
  match goal with |- context [mkFrame _ (put _ (WInt ?t) _) _ _ _] =>
    let H := fresh in assert (H : t = head (first_mask (Z.lxor w (rep c)))) by (eapply head_chain; eassumption);
    rewrite H Hh; clear H end;
  repeat match goal with H : ?v = _ |- _ => is_var v; clear H end;
  sg; sl; sl; sl; normt j ltac:(arith); sg; sl; normt j ltac:(arith).

(** The loop at word i of the window ws at the 8-aligned W, b + wo,
    below the one that holds the last of the n bytes from a, W + k: no
    byte after word i in them is c's. It returns what [last_hit] finds
    and hands the window back. *)
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
    sl; sl'; sb; cbn [ptr_addr].
  - (* The first word. *)
    replace (b + wo + 8 * Z.of_nat 0) with (b + wo) by lia. rewrite Z.eqb_refl. close_if. en.
    pose proof (wrd_range ws 0 Hr) as Hw0. set (w := wrd ws (Z.of_nat 0)) in *.
    sl'. sl. sl. sl. sl. rewrite !(Z.mod_small w (2 ^ 64) Hw0) rep_mod.
    normt (loop_mask (Z.lxor w (rep c))) ltac:(reflexivity). sl. sb.
    rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l.
    destruct (word_last w (c mod 256)) as [(j & Hj & Hcj & Hlj) | Hn].
    + assert (Hm : loop_mask (Z.lxor w (rep c)) <> 0).
      { intros E. apply (proj1 (has_eq_zero w c Hw0) E j Hj Hcj). }
      rewrite (proj2 (Z.eqb_neq _ _) Hm). close_if. en.
      idx_steps w c j Hj Hcj Hlj.
      sf. normp "v121" (b + wo + j). sl. sl'. sb. cbn [ptr_addr ptr_cap].
      rewrite (Z.mod_small (b + wo + Z.of_nat k)); [|arith]. rewrite (Z.mod_small (b + wo + j)); [|arith].
      assert (Hv : wbytes ws !! (8 * 0 + Z.to_nat j)%nat = Some (c mod 256)) by (rewrite wbytes_at; [change (wrd ws (Z.of_nat 0)) with w; congruence | lia | exact Hj]).
      pose proof (none_after ws (c mod 256) 0 j (k + n) ltac:(lia) Hj Hlj Hnone) as Hna.
      destruct (Z.leb_spec (b + wo + Z.of_nat k) (b + wo + j)) as [Hge|Hlt].
      * (* At or after the first byte: the match. *)
        close_if. en. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
        rewrite (last_hit_unique _ _ _ _ Hhit (hit_at _ _ k n (8 * 0 + Z.to_nat j) HB
                   ltac:(lia) Hv Hna)).
        cbn [hit_ptr ptr_addr ptr_cap]. replace (b + wo + Z.of_nat k + Z.of_nat (8 * 0 + Z.to_nat j - k)) with (b + wo + j)
          by lia. iApply ("HK" with "Hw").
      * (* Before it: none. *)
        close_if. en. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
        rewrite (last_hit_unique _ _ _ _ Hhit (hit_none _ _ k n HB
                   ltac:(intros u Hu; apply Hna; lia))).
        iApply ("HK" with "Hw").
    + (* No c in the first word: none. *)
      rewrite (proj2 (has_eq_zero w c Hw0) Hn). close_if. en. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      pose proof (none_word ws (c mod 256) 0 (k + n) ltac:(lia) Hn Hnone) as Hnw.
      rewrite (last_hit_unique _ _ _ _ Hhit (hit_none _ _ k n HB
                 ltac:(intros u Hu; apply Hnw; lia))).
      iApply ("HK" with "Hw").
  - (* A word after the first. *)
    rewrite (Z.mod_small (b + wo + 8 * Z.of_nat (S i))); [|arith]. rewrite (Z.mod_small (b + wo)); [|arith].
    rewrite (proj2 (Z.eqb_neq _ _)); [|lia]. close_if. en.
    pose proof (wrd_range ws (Z.of_nat (S i)) Hr) as Hw0. set (w := wrd ws (Z.of_nat (S i))) in *.
    sl'. sl. sl. sl. sl. rewrite !(Z.mod_small w (2 ^ 64) Hw0) rep_mod.
    normt (loop_mask (Z.lxor w (rep c))) ltac:(reflexivity). sl. sb.
    rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l.
    destruct (word_last w (c mod 256)) as [(j & Hj & Hcj & Hlj) | Hn].
    + (* Its last c. *)
      assert (Hm : loop_mask (Z.lxor w (rep c)) <> 0).
      { intros E. apply (proj1 (has_eq_zero w c Hw0) E j Hj Hcj). }
      rewrite (proj2 (Z.eqb_neq _ _) Hm). close_if. en.
      idx_steps w c j Hj Hcj Hlj.
      sf. normp "v103" (b + wo + 8 * Z.of_nat (S i) + j).
      iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      assert (Hv : wbytes ws !! (8 * S i + Z.to_nat j)%nat = Some (c mod 256))
        by (rewrite wbytes_at; [change (wrd ws (Z.of_nat (S i))) with w; congruence | lia | exact Hj]).
      pose proof (none_after ws (c mod 256) (S i) j (k + n) ltac:(lia) Hj Hlj Hnone) as Hna.
      rewrite (last_hit_unique _ _ _ _ Hhit (hit_at _ _ k n (8 * S i + Z.to_nat j) HB ltac:(lia) Hv Hna)).
      cbn [hit_ptr ptr_addr ptr_cap].
      replace (b + wo + Z.of_nat k + Z.of_nat (8 * S i + Z.to_nat j - k)) with (b + wo + 8 * Z.of_nat (S i) + j)
        by lia. iApply ("HK" with "Hw").
    + (* No c: the word before. *)
      rewrite (proj2 (has_eq_zero w c Hw0) Hn). close_if. en.
      pose proof (none_word ws (c mod 256) (S i) (k + n) ltac:(lia) Hn Hnone) as Hnw.
      sf. normp "v106" (b + wo + 8 * Z.of_nat i). cbn [ptr_cap].
      iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ (mkPtr (b + wo + 8 * Z.of_nat i) cp) dq b reg wo ws
                (Z.of_nat i) with "Hw"); [reflexivity | exact Hc | reflexivity | lia | exact Hb0 | exact Hwo
                | exact Hend | exact Hreg | exact Hr |].
      iIntros "Hw". sg. rewrite (Z.mod_small _ _ (wrd_range ws (Z.of_nat i) Hr)).
      iApply (IH with "Hw HK"); [lia | intros u Hu; apply Hnw; lia | exact Hhit | look H77 | look H26 | look H7].
Qed.

End rules.
End MemrchrLoopOn.
