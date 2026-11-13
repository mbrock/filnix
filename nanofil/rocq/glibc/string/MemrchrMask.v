(** After glibc's `__memrchr` loads the word holding the last of the `n`
    bytes and masks off any lanes at or past the end, it tests whether
    any matching byte remains. This module proves [memrchr_mask] from the
    join block `iw_3.join` onward for [MemrchrLogic].

    When the masked word contains a match, `__memrchr` counts leading
    zero bits to find the highest matching byte and checks that its
    address is at least `p`. If the match lies before `p`, it returns
    null. When the masked word has no match, it either returns null or
    loads the previous word using a [[half_check]] and enters the
    backward loop. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpBits StrcmpLoop StrrchrLogic
  MemchrLast MemchrLogic MemrchrCode MemrchrBits MemrchrLoop.
Open Scope Z_scope.
Open Scope list_scope.

(** This functor packages the final-word mask and half-check rules for
    `__memrchr` over a [[runtime]] R and a program logic instance LG0. *)
Module MemrchrMaskOn (R : Runtime) (LG0 : LogicSig R).
(** Module [RL] supplies the backward word-loop proof. *)
Module RL := MemrchrLoopOn R LG0.
(** Module [SL] supplies the step rules for symbolic execution. *)
Module SL := RL.SL.
(** Module [WS] provides word-window and fractional read helpers. *)
Module WS := SL.WS.
(** Module [ML] provides the fractional half-check rule for reading the
    previous word. *)
Module ML := MemchrLastOn R LG0.
(** Module [LG] re-exports the program logic instance. *)
Module LG := LG0.
(** Module [L] re-exports the core logic definitions. *)
Module L := LG.L.
Import L LG WS SL.

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
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** Tactic [sn] advances one `let` instruction and names its integer
    result in the context. *)
Ltac sn := eapply (s_letn registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.
(** Tactic [sf] advances one [[flight]] instruction in the proof mode. *)
Ltac sf := eapply (s_flight registry wi ge); [reflexivity | reflexivity | reflexivity |].
(** Tactic [en] steps into the target block and exposes its instructions
    and terminator. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** Tactic [sg] follows an unconditional `goto` and immediately enters the
    destination block. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** Tactic [sb] advances one conditional `branch` while keeping its
    condition expression symbolic. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** To resolve IR temporary arguments during symbolic execution, [vx]
    looks up each temporary in the environment hypotheses and evaluates
    the remaining argument expressions. *)
Ltac vx :=
  cbn [map2_option map_option flight_arg_x flight_cap arg_x];
  repeat match goal with |- context [value_x ?g ?E ?k (Tmp ?n)] =>
    match goal with H : lookup n _ = Some ?x |- _ =>
      rewrite (value_x_tmp g E k n x); [|look H] end end;
  reflexivity.
(** Tactic [sl'] advances one `let` instruction whose arguments are
    resolved via [vx]. *)
Ltac sl' := eapply (s_let registry wi ge); [reflexivity | reflexivity | vx | intros ?; reflexivity |].
(** Tactic [sf'] advances one [[flight]] instruction whose arguments are
    resolved via [vx]. *)
Ltac sf' := eapply (s_flight registry wi ge); [vx | reflexivity | vx |].
(** Tactic [sb'] advances one `branch` instruction whose arguments are
    resolved via [vx]. *)
Ltac sb' := eapply (s_branch registry wi ge); [vx|].
(** To keep intermediate integers readable, [normt] rewrites the
    integer in the newest temporary to `v` using tactic `tac`. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Tactic [normp] rewrites the address of the pointer stored in
    temporary `name` to `v` by arithmetic. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** Block `iw_3.join` merges the aligned and unaligned final-word mask
    paths of [glibc_memrchr]. *)
Definition rblk_join : block := Eval vm_compute in rblk "iw_3.join".

(** To step backwards from the final word without repeating a full
    bounds check, [wp_win_half] verifies the 8-byte [[half_check]]
    against the existing capability proof and loads the preceding
    word. *)
Lemma wp_win_half f e ls l c d bd p1n pr rest j p1 p dq b reg wo ws q Φ :
  map2_option (value_x ge e) [A; P] [Tmp p1n; Tmp pr] = Some [WPtr p1; WPtr p] -> ptr_cap p1 = ptr_cap p ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  ptr_addr p = b + wo + 8 * q -> 0 <= q < Z.of_nat (List.length ws) -> 0 < b -> 0 <= wo ->
  b + wo + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 -> Forall (fun w => 0 <= w < 2 ^ 64) ws ->
  wwin dq b reg wo ws -∗
  (wwin dq b reg wo ws -∗ WP (ERun (mkFrame f (put d (WInt (wrd ws q)) (put c (WPtr p) e)) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let c A (HalfCheck bd 0 8 Read 1) [Tmp p1n; Tmp pr] ::
                                         Let d L (RawLoad LdL 0) [Tmp c] :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hp1 Hc Ha Hq Hb Hwo Hend Hreg Hr. iIntros "[Hl Hw] HK".
  iApply (ML.wp_half_check_read_dq registry wi ge with "Hl"); [reflexivity | exact Hx | exact Hp1 | exact Hc
    | arith | arith | lia | arith | apply Z.mod_1_r |].
  iNext. iIntros "Hl".
  iApply (wp_read_with registry wi ge (liveq dq b reg ∗ ptsq dq (words_ps b wo ws))%I
            (fun m => live_at m b reg /\ all_agree m (words_ps b wo ws)) _ _ [] with "[$Hl $Hw] [HK]").
  - iIntros (σ) "Hσ [Hl Hw]". iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hw") as %(Hag & _). iPureIntro. auto.
  - intros m fuel [Hlv Hag]. pose proof (win_cell _ _ _ _ _ Hag Hq) as Hcl.
    apply rule_let with (classes := [A]) (xs := [WPtr p]); [reflexivity | reflexivity | |].
    { cbn [map2_option value_x]. rewrite lookup_after_put_same. reflexivity. }
    assert (Er : raw_address (ptr_addr p) 0 = b + (wo + 8 * q)) by arith.
    rewrite (op_raw_load m L p 0).
    + rewrite Er (cell_load m b reg _ _ _ Hlv Hcl eq_refl) (Z.mod_small _ _ (wrd_range ws q Hr)). reflexivity.
    + rewrite Er. apply (access_read _ b reg); [exact Hc | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hw]". iApply ("HK" with "[$Hl $Hw]").
Qed.

(** From the join block `iw_3.join` onward, [memrchr_mask] either
    extracts the highest matching byte from the final-word mask or steps
    back into [rloop], returning [hit_ptr] and restoring the memory
    window. *)
Lemma memrchr_mask dq b reg ws a cp c (k n : nat) (Lz e' fm : Z) e r Φ :
  0 < b -> (cp = Obj b \/ cp = Ro b) -> b <= a - Z.of_nat k -> (a - Z.of_nat k) mod 8 = 0 -> (k < 8)%nat ->
  a - Z.of_nat k + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws -> 0 <= Lz -> Lz + 1 = Z.of_nat (List.length ws) ->
  e' = Z.of_nat k + Z.of_nat n - 8 * Lz -> 0 < e' <= 8 -> 0 <= fm < 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> byte_of fm i = if (i <? e') && (byte_of (wrd ws Lz) i =? c mod 256) then 128 else 0) ->
  last_hit (take n (drop k (wbytes ws))) (c mod 256) r ->
  lookup (TAtom "v31") e = Some (WPtr (mkPtr (a - Z.of_nat k + 8 * Lz) cp)) -> lookup (TAtom "v26") e = Some (WInt a) ->
  lookup (TAtom "v42") e = Some (WPtr (mkPtr (a - Z.of_nat k) cp)) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (a - Z.of_nat k + 8 * Lz) cp)) ->
  lookup (TAtom "iw_1.v7") e = Some (WInt (rep c)) ->
  wwin dq b reg (a - Z.of_nat k - b) ws -∗
  (wwin dq b reg (a - Z.of_nat k - b) ws -∗ Φ (Ret (WPtr (hit_ptr (mkPtr a cp) r)))) -∗
  WP (ERun (mkFrame glibc_memrchr (put (TAtom "v48") (WInt fm) e) [] None
       (Exec (TAtom "iw_3.join") (b_insts rblk_join) (b_jump rblk_join))) : gexpr) {{ Φ }}.
Proof.
  intros Hb0 Hc Hba HW8 Hk Hend Hreg Hr HL0 HLw He' He Hfm Hbyte Hhit H31 H26 H42 Hchk H7. iIntros "Hw HK".
  set (W := a - Z.of_nat k) in *. set (w := wrd ws Lz) in *. assert (EW : W + Z.of_nat k = a) by (unfold W; lia).
  assert (He'' : Z.of_nat k + Z.of_nat n = 8 * Lz + e') by lia. clear He'.
  assert (HB : (k + n <= List.length (wbytes ws))%nat) by (rewrite wbytes_length; lia).
  assert (Hlast : forall u, (8 * Z.to_nat Lz <= u < k + n)%nat ->
            wbytes ws !! u = Some (byte_of w (Z.of_nat u - 8 * Lz))).
  { intros u Hu. replace u with (8 * Z.to_nat Lz + Z.to_nat (Z.of_nat u - 8 * Lz))%nat by lia.
    rewrite wbytes_at; [|lia | lia]. rewrite Z2Nat.id; [|lia]. do 3 f_equal; lia. }
  cbn [rblk_join b_insts b_jump]. sl. sb. rewrite (Z.mod_small fm); [|exact Hfm]. change (0 mod 2 ^ 64) with 0.
  destruct (greatest_below (fun i => byte_of w (Z.of_nat i) = c mod 256) (fun i => Z.eq_dec _ _) (Z.to_nat e'))
    as [(j & Hj & Hcj & Hlj) | Hn].
  - assert (Hj8 : Z.of_nat j < e') by lia. assert (Hj8' : Z.of_nat j < 8) by lia.
    (* The last c of the word below its end, at j. *)
    assert (Hhead : head fm = 56 - 8 * Z.of_nat j).
    { apply head_last; [exact Hfm | | lia | | ].
      - intros i Hi. rewrite Hbyte; [|exact Hi]. destruct (_ && _); auto.
      - rewrite Hbyte; [|lia]. rewrite Hcj Z.eqb_refl andb_true_r. rewrite (proj2 (Z.ltb_lt _ _)); [reflexivity | lia].
      - intros i Hi. rewrite Hbyte; [|lia]. destruct (Z.ltb_spec i e'); [|reflexivity].
        destruct (Z.eqb_spec (byte_of w i) (c mod 256)) as [E|E]; [|reflexivity].
        exfalso. apply (Hlj (Z.to_nat i)); [lia|]. rewrite Z2Nat.id; [exact E | lia]. }
    assert (Hm0 : fm <> 0).
    { intros E. pose proof (Hbyte (Z.of_nat j) ltac:(lia)) as B. rewrite E Hcj Z.eqb_refl andb_true_r in B.
      rewrite (proj2 (Z.ltb_lt _ _)) in B; [|lia]. unfold byte_of in B.
      rewrite Z.div_0_l in B; [discriminate | apply Z.pow_nonzero; lia]. }
    rewrite (proj2 (Z.eqb_neq _ _) Hm0). close_if. en. sl. sb. rewrite (Z.mod_small fm); [|exact Hfm].
    rewrite (proj2 (Z.eqb_neq _ _) Hm0). close_if. en.
    do 26 sn.
    match goal with |- context [mkFrame _ (put _ (WInt ?t) _) _ _ _] =>
      let H := fresh in assert (H : t = head fm) by (eapply head_chain; eassumption); rewrite H Hhead; clear H end.
    repeat match goal with H : ?v = _ |- _ => is_var v; clear H end.
    sg. sl. sl. sl. normt (Z.of_nat j) ltac:(arith). sg. sl. normt (Z.of_nat j) ltac:(arith).
    sf'. normp "v59" (W + 8 * Lz + Z.of_nat j). sl. sl'. sb. cbn [ptr_addr ptr_cap].
    rewrite (Z.mod_small a); [|arith]. rewrite (Z.mod_small (W + 8 * Lz + Z.of_nat j)); [|arith].
    assert (Hna : none_in (wbytes ws) (c mod 256) (S (8 * Z.to_nat Lz + j)) (k + n)).
    { intros u Hu. rewrite Hlast; [|lia]. intros [= E]. apply (Hlj (u - 8 * Z.to_nat Lz)%nat); [lia|].
      rewrite <- E. f_equal. lia. }
    destruct (Z.leb_spec a (W + 8 * Lz + Z.of_nat j)) as [Hge|Hlt].
    + (* At or after the first byte: the match. *)
      close_if. en. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      assert (Hv : wbytes ws !! (8 * Z.to_nat Lz + j)%nat = Some (c mod 256)).
      { rewrite Hlast; [|lia]. rewrite <- Hcj. do 2 f_equal. lia. }
      rewrite (last_hit_unique _ _ _ _ Hhit (hit_at _ _ k n (8 * Z.to_nat Lz + j) HB ltac:(lia) Hv Hna)).
      cbn [hit_ptr ptr_addr ptr_cap].
      replace (a + Z.of_nat (8 * Z.to_nat Lz + j - k)) with (W + 8 * Lz + Z.of_nat j) by lia.
      iApply ("HK" with "Hw").
    + (* Before it: none. *)
      close_if. en. sg. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      rewrite (last_hit_unique _ _ _ _ Hhit (hit_none _ _ k n HB ltac:(intros u Hu; apply Hna; lia))).
      iApply ("HK" with "Hw").
  - (* No c in the word below its end. *)
    assert (Hnl : none_in (wbytes ws) (c mod 256) (8 * Z.to_nat Lz) (k + n)).
    { intros u Hu. rewrite Hlast; [|lia]. intros [= E]. apply (Hn (u - 8 * Z.to_nat Lz)%nat); [lia|].
      rewrite <- E. f_equal. lia. }
    assert (Hz : fm = 0).
    { apply zero_word; [exact Hfm|]. intros i Hi. rewrite Hbyte; [|exact Hi].
      destruct (Z.ltb_spec i e'); [|reflexivity]. destruct (Z.eqb_spec (byte_of w i) (c mod 256)) as [E|E]; [|reflexivity].
      exfalso. apply (Hn (Z.to_nat i)); [lia|]. rewrite Z2Nat.id; [exact E | lia]. }
    subst fm. close_if. en. sl'. sl'. sl. sb. cbn [ptr_addr ptr_cap].
    rewrite (Z.mod_small W); [|arith]. rewrite (Z.mod_small (W + 8 * Lz)); [|arith].
    destruct (Z.eq_dec Lz 0) as [HL|HL].
    + (* The first word was the last: none. *)
      rewrite HL Z.add_0_r Z.eqb_refl. close_if. en. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      rewrite (last_hit_unique _ _ _ _ Hhit (hit_none _ _ k n HB ltac:(intros u Hu; apply Hnl; lia))).
      iApply ("HK" with "Hw").
    + rewrite (proj2 (Z.eqb_neq _ _)); [|lia]. close_if. en.
      sf'. normp "v81" (W + 8 * (Lz - 1)). cbn [ptr_cap].
      iApply (wp_win_half _ _ _ _ _ _ _ _ _ _ _ (mkPtr (W + 8 * Lz) cp) (mkPtr (W + 8 * (Lz - 1)) cp) dq b reg (W - b) ws
                (Lz - 1) with "Hw"); [vx | reflexivity | exact Hc | cbn; lia | lia | exact Hb0 | lia | lia | exact Hreg
                | exact Hr |].
      iIntros "Hw". sg. rewrite (Z.mod_small _ _ (wrd_range ws (Lz - 1) Hr)).
      replace (W + 8 * (Lz - 1)) with (b + (W - b) + 8 * Z.of_nat (Z.to_nat (Lz - 1))) by lia.
      replace (wrd ws (Lz - 1)) with (wrd ws (Z.of_nat (Z.to_nat (Lz - 1)))) by (rewrite Z2Nat.id; [reflexivity | lia]).
      iApply (RL.rloop registry wi ge dq b reg (W - b) ws cp c k n (Z.to_nat (Lz - 1)) with "Hw [HK]");
        [exact Hb0 | exact Hc | lia | replace (b + (W - b)) with W by lia; exact HW8 | lia | exact Hreg | exact Hr
        | exact Hk | rewrite <- wbytes_length; exact HB | lia | intros u Hu; apply Hnl; lia | exact Hhit | | | | ].
      * repeat (rewrite lookup_after_put_other; [|reflexivity]). rewrite lookup_after_put_same. do 2 f_equal. lia.
      * repeat (rewrite lookup_after_put_other; [|reflexivity]). rewrite H26. do 2 f_equal. lia.
      * look H7.
      * iIntros "Hw". replace (b + (W - b) + Z.of_nat k) with a by lia. iApply ("HK" with "Hw").
Qed.

End rules.
End MemrchrMaskOn.
