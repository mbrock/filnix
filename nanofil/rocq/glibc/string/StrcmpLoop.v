(** The word loops of glibc's own `strcmp` (`__GI_strcmp`,
    StrcmpCode.v) over two strings' windows (WordString.v) at any
    shares, for StrcmpLogic.v's triple over [word_string]s.

    Once the first string's pointer is 8-aligned, glibc compares whole
    words: of both strings at once when the second is aligned too
    ([aligned_loop]), else of the first against [merge]s of the
    second's words ([unaligned_loop]). A word pair with a zero ends the
    search with 0, and one with a difference ends it at the first
    stop, which the comparison mask's population count finds and whose
    bytes glibc subtracts ([fin_a], [fin_b], [fin_c], one per copy its
    inlining makes). The answer is StrcmpBits.v's [strcmp_res] in each
    case ([word_stop], [word_zero]). Every read is of a word or byte of a
    window ([wp_win_word], [wp_win_byte]), which each step shows lies
    inside the string's window.

    The steps are taken by rules stated over the proof mode's
    entailment ([s_let], [s_enter]), which take no later and keep the
    goal small, and each value glibc computes that later steps read is
    named ([s_letn]) or rewritten to its meaning as it is made. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpCode StrcmpBits.
Open Scope Z_scope.
Open Scope list_scope.

(** The loops over the [[runtime]] R and the Logic instance LG0. *)
Module StrcmpLoopOn (R : Runtime) (LG0 : LogicSig R).
(** Strings' windows over R and LG0. *)
Module WS := WordStringOn R LG0.
(** The Logic instance. *)
Module LG := LG0.
(** The language of the Logic instance. *)
Module L := LG.L.
Import L LG WS.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** The proof mode's entailment. *)
Local Notation ent Δ P := (environments.envs_entails Δ P).

(** ## Steps in the proof mode *)

(** A step whose rule ends in a later: the goal before it from the
    goal after it, with no later to strip. *)
Lemma next_to Δ (P Q : iProp Σ) : (⊢ ▷ P -∗ Q) -> ent Δ P -> ent Δ Q.
Proof. rewrite environments.envs_entails_unseal. intros HPQ HP. iIntros "H". iApply HPQ. iNext. by iApply HP. Qed.

(** Logic.v's [wp_let] in the proof mode. *)
Lemma s_let Δ f e ls l d k o args rest j classes xs w Φ :
  general_op o = true -> op_arg_classes o k = Some classes -> map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal w) m)) ->
  ent Δ (WP (ERun (mkFrame f (put d w e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [eapply (wp_let registry wi ge); eauto | done]. Qed.

(** [s_let] of an integer, named: the rest is proved for any x equal to
    it, so its later readers see x, not the term. *)
Lemma s_letn Δ f e ls l d k o args rest j classes xs X Φ :
  general_op o = true -> op_arg_classes o k = Some classes -> map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal (WInt X)) m)) ->
  (forall x, x = X -> ent Δ (WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }})) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros. eapply s_let; eauto. Qed.

(** Logic.v's [wp_flight] in the proof mode. *)
Lemma s_flight Δ f e ls l d o args lw rest j xs n c Φ :
  map_option (flight_arg_x ge e) args = Some xs -> alu o L xs = Some (WInt n) -> flight_cap ge e lw = Some c ->
  ent Δ (WP (ERun (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [eapply (wp_flight registry wi ge); eauto | done]. Qed.

(** Logic.v's [wp_enter] in the proof mode. *)
Lemma s_enter Δ f e ls l from b e' Φ :
  find_block l (fn_blocks f) = Some b -> phis_env ge (b_phis b) from e = Some e' ->
  ent Δ (WP (ERun (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Enter l from)) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [eapply (wp_enter registry wi ge); eauto | done]. Qed.

(** Logic.v's [wp_goto] in the proof mode. *)
Lemma s_goto Δ f e ls l t Φ :
  ent Δ (WP (ERun (mkFrame f e ls None (Enter (edge_label t) (Some l))) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l [] (JGoto t))) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [apply (wp_goto registry wi ge) | done]. Qed.

(** Logic.v's [wp_branch] in the proof mode. *)
Lemma s_branch Δ f e ls l v t1 t2 n Φ :
  value_x ge e W v = Some (WInt n) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [eapply (wp_branch registry wi ge); eauto | done]. Qed.

(** Logic.v's [wp_ret] in the proof mode, the returned word any word
    equal to it. *)
Lemma s_ret Δ f e l v x x' Φ :
  fn_ret f = RClass W -> value_x ge e W v = Some (WInt x) -> x = x' -> ent Δ (Φ (Ret (WInt x'))) ->
  ent Δ (WP (ERun (mkFrame f e [] None (Exec l [] (JRet v))) : gexpr) {{ Φ }}).
Proof. intros Hk Hv -> H. eapply next_to; [eapply (wp_ret registry wi ge); eauto | done]. Qed.

(** A let, its value left whole. *)
Ltac sl := eapply s_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** A let, its integer named. *)
Ltac sn := eapply s_letn; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.
(** A flight. *)
Ltac sf := eapply s_flight; [reflexivity | reflexivity | reflexivity |].
(** A goto, and entering its block. *)
Ltac en := eapply s_enter; [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** A goto and the block it enters. *)
Ltac sg := eapply s_goto; en.
(** A let that reads the temporary n of the frame's environment below
    its puts, which H says holds a value. *)
Ltac slk n H := eapply s_let; [reflexivity | reflexivity |
  cbn [map2_option value_x]; repeat (rewrite (lookup_after_put_other _ (TAtom n)); [|reflexivity]);
  rewrite H; reflexivity | intros ?; reflexivity |].
(** A branch, its condition left whole. *)
Ltac sb := eapply s_branch; [reflexivity|].
(** Replace the integer the temporary name holds by v, proved by tac. *)
Ltac norm name v tac :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.
(** Replace the integer the newest temporary holds by v, proved by tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Replace the address of the pointer the temporary name holds by v. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** ## Reads of a window *)

(** A window's word q is its pieces' cell at offset wo + 8q. *)
Lemma win_cell m b wo ws q : all_agree m (words_ps b wo ws) -> 0 <= q < Z.of_nat (List.length ws) ->
  all_agree m (cell b (wo + 8 * q) (wrd ws q)).
Proof.
  intros Ha Hq. apply all_agree_cell. intros i Hi.
  pose proof (words_ps_elem b wo ws (Z.to_nat (8 * q + i)) _ (wbytes_bt ws (8 * q + i) ltac:(lia))) as Hin.
  rewrite Z2Nat.id in Hin; [|lia]. rewrite (bt_word ws q i); [|lia|lia].
  replace (wo + 8 * q + i) with (wo + (8 * q + i)) by lia. exact (all_agree_elem _ _ _ _ Ha Hin).
Qed.

(** A [[check]] of 8 bytes for reading of the pointer pr holds, p, and
    a load of the long there, where p addresses word q of a window at a
    share: the load gives the word. *)
Lemma wp_win_word f e ls l c d pr rest j p dq b reg wo ws q Φ :
  map2_option (value_x ge e) [P] [Tmp pr] = Some [WPtr p] -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  ptr_addr p = b + wo + 8 * q -> 0 <= q < Z.of_nat (List.length ws) -> 0 < b -> 0 <= wo ->
  b + wo + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 -> Forall (fun w => 0 <= w < 2 ^ 64) ws ->
  wwin dq b reg wo ws -∗
  (wwin dq b reg wo ws -∗ WP (ERun (mkFrame f (put d (WInt (wrd ws q)) (put c (WPtr p) e)) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let c A (Check 0 8 Read 1) [Tmp pr] :: Let d L (RawLoad LdL 0) [Tmp c] :: rest) j))
        : gexpr) {{ Φ }}.
Proof.
  intros Hx Hc Ha Hq Hb Hwo Hend Hreg Hr. iIntros "[Hl Hw] HK".
  iApply (wp_check_read_dq with "Hl"); [reflexivity | exact Hx | exact Hc | arith | arith | apply Z.mod_1_r |].
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

(** A [[check]] of one byte for reading of the pointer pr holds, p, and
    a load of the signed byte there, where p addresses byte i of a
    window at a share: the load gives the byte, extended. *)
Lemma wp_win_byte f e ls l c d pr rest j p dq b reg wo ws i Φ :
  map2_option (value_x ge e) [P] [Tmp pr] = Some [WPtr p] -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  ptr_addr p = b + wo + i -> 0 <= i < 8 * Z.of_nat (List.length ws) -> 0 < b -> 0 <= wo ->
  b + wo + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  wwin dq b reg wo ws -∗
  (wwin dq b reg wo ws -∗
   WP (ERun (mkFrame f (put d (WInt (extension Sb (bt ws i) mod 2 ^ 32)) (put c (WPtr p) e)) ls None (Exec l rest j))
         : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let c A (Check 0 1 Read 1) [Tmp pr] ::
                                         Let d W (RawLoad (LdNarrow Sb) 0) [Tmp c] :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hc Ha Hi Hb Hwo Hend Hreg. iIntros "[Hl Hw] HK".
  iApply (wp_check_read_dq with "Hl"); [reflexivity | exact Hx | exact Hc | arith | arith | apply Z.mod_1_r |].
  iNext. iIntros "Hl".
  iApply (wp_read_with registry wi ge (liveq dq b reg ∗ ptsq dq (words_ps b wo ws))%I
            (fun m => live_at m b reg /\ all_agree m (words_ps b wo ws)) _ _ [] with "[$Hl $Hw] [HK]").
  - iIntros (σ) "Hσ [Hl Hw]". iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hw") as %(Hag & _). iPureIntro. auto.
  - intros m fuel [Hlv Hag].
    pose proof (words_ps_elem b wo ws (Z.to_nat i) _ (wbytes_bt ws i Hi)) as Hin.
    apply (all_agree_elem _ _ _ _ Hag) in Hin as [_ Hin]. rewrite Z2Nat.id in Hin; [|lia].
    destruct Hlv as [E Lv]. destruct (Hin reg E Lv) as (_ & _ & Hv).
    apply rule_let with (classes := [A]) (xs := [WPtr p]); [reflexivity | reflexivity | |].
    { cbn [map2_option value_x]. rewrite lookup_after_put_same. reflexivity. }
    assert (Er : raw_address (ptr_addr p) 0 = b + (wo + i)) by arith.
    rewrite (op_raw_load_byte m W Sb p 0 eq_refl).
    + rewrite Er Hv. reflexivity.
    + rewrite Er. apply (access_read _ b reg); [exact Hc | exact E | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hw]". iApply ("HK" with "[$Hl $Hw]").
Qed.

(** ## The returns of a difference *)

(** glibc's last steps on the words x and y whose first stop is byte j,
    from its comparison mask: the mask, its population count, the two
    bytes at j and their difference, returned. *)
Ltac fin_tac x y j :=
  pose proof (cmp_mask_range x y); pose proof (byte_of_range x j); pose proof (byte_of_range y j);
  let Ht := fresh "Ht" in let Hn := fresh "Hn" in
  match goal with H1 : stop_at _ _ j, H2 : same_upto _ _ j |- _ =>
    destruct (cmp_mask_first x y j ltac:(lia) H1 H2) as [Ht Hn] end;
  do 10 sl; normt (cmp_mask x y) ltac:(reflexivity); sl; sb;
  replace (cmp_mask x y mod 2 ^ 64 =? 0 mod 2 ^ 64) with false
    by (symmetry; apply Z.eqb_neq; rewrite Z.mod_small; [exact Hn | lia]);
  close_if; en;
  do 15 sn;
  match goal with |- context [mkFrame _ (put _ (WInt ?t) _) _ _ _] =>
    let H := fresh in assert (H : t = tail (cmp_mask x y)) by (eapply tail_chain; eassumption);
    rewrite H Ht; clear H end;
  repeat match goal with H : ?v = _ |- _ => is_var v; clear H end;
  sg; sl; normt j ltac:(arith); sl; normt (8 * j) ltac:(arith);
  sl; sl; normt (byte_of x j) ltac:(symmetry; apply ub_shift; lia);
  sl; sl; normt (byte_of y j) ltac:(symmetry; apply ub_shift; lia);
  sl; normt ((byte_of x j - byte_of y j) mod 2 ^ 32) ltac:(arith);
  sg; eapply s_ret; [reflexivity | reflexivity | rewrite !Zmod_mod; reflexivity |].

(** The words x and y differ, the second string aligned: glibc returns
    the difference of their bytes at their first stop j. *)
Lemma fin_a Δ e z a b x y j Φ :
  0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  ent Δ (Φ (Ret (WInt ((byte_of x j - byte_of y j) mod 2 ^ 32)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strcmp (put (TAtom "iw_1.v15") z (put (TAtom "iw_1.pr.1") a (put (TAtom "iw_1.pr.2") b
         (put (TAtom "iw_1.pr.3") (WInt x) (put (TAtom "iw_1.pr.4") (WInt y) e))))) [] None
         (Enter (TAtom "iw_1.iw_2.start") (Some (TAtom "iw_1.L10")))) : gexpr) {{ Φ }}).
Proof. intros Hj Hst Hs HK. en. fin_tac x y j. exact HK. Qed.

(** The words x and y differ, y the second string's [merge]: glibc
    returns the difference of their bytes at their first stop j. *)
Lemma fin_b Δ e z1 z2 z3 z4 z5 z6 z7 z8 x y j Φ :
  0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  ent Δ (Φ (Ret (WInt ((byte_of x j - byte_of y j) mod 2 ^ 32)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strcmp (put (TAtom "iw_2.v54") z1 (put (TAtom "iw_2.v48") (WInt y)
         (put (TAtom "iw_2.v47") z2 (put (TAtom "iw_2.v44") z3 (put (TAtom "iw_2.v41") z4 (put (TAtom "chk7") z5
         (put (TAtom "iw_2.v40") z6 (put (TAtom "iw_2.pr.1") z7 (put (TAtom "iw_2.pr.2") z8
         (put (TAtom "iw_2.pr.4") (WInt x) e)))))))))) [] None
         (Enter (TAtom "iw_2.iw_2.start") (Some (TAtom "iw_2.L36")))) : gexpr) {{ Φ }}).
Proof. intros Hj Hst Hs HK. en. fin_tac x y j. exact HK. Qed.

(** The block of glibc's strcmp labelled l. *)
Definition blk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks glibc_strcmp) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** The last word pair's block of an unaligned second string. *)
Definition blk30 : block := Eval vm_compute in blk "iw_2.L30".

(** The words x and y, y the second string's last bytes, at the last
    word pair of an unaligned second string: glibc returns the
    difference of their bytes at their first stop j. *)
Lemma fin_c Δ e x y j Φ :
  0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  ent Δ (Φ (Ret (WInt ((byte_of x j - byte_of y j) mod 2 ^ 32)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strcmp (put (TAtom "iw_2.pr.3") (WInt x) (put (TAtom "iw_2.pr.6") (WInt y) e)) [] None
         (Exec (TAtom "iw_2.L30") (b_insts blk30) (b_jump blk30))) : gexpr) {{ Φ }}).
Proof. intros Hj Hst Hs HK. cbn [blk30 b_insts b_jump]. fin_tac x y j. exact HK. Qed.

(** The arithmetic of the shapes Hs1 and Hs2 of the two strings, and
    the agreement of their bytes. *)
Ltac facts Hs1 Hs2 :=
  destruct (shape_facts _ _ _ _ _ Hs1) as (B1 & S1 & M1 & P1 & K1 & E1 & R1 & N1 & C1);
  destruct (shape_facts _ _ _ _ _ Hs2) as (B2 & S2 & M2 & P2 & K2 & E2 & R2 & N2 & C2);
  pose proof (ss_words _ _ _ _ _ Hs1) as F1; pose proof (ss_words _ _ _ _ _ Hs2) as F2;
  pose proof (ss_chars _ _ _ _ _ Hs1) as H1; pose proof (sbyte_agree _ _ _ _ _ Hs1) as A1;
  pose proof (sbyte_agree _ _ _ _ _ Hs2) as A2.

(** The aligned loop's block. *)
Definition blk10a : block := Eval vm_compute in blk "iw_1.L10".

(** The aligned loop: both strings' bytes from c start words, Q1 and
    Q2 of their windows, read as pr.3 and pr.4, and pr.1 and pr.2 point
    past them; their bytes before c agree and are not 0. strcmp
    returns [strcmp_res] and hands both windows back. *)
Lemma aligned_loop dq1 dq2 p1 p2 b1 b2 reg1 reg2 ws1 ws2 s1 s2 c Q1 Q2 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> 0 <= c ->
  ptr_addr p1 mod 8 + c = 8 * Q1 -> ptr_addr p2 mod 8 + c = 8 * Q2 -> same_upto (sbyte p1 ws1) (sbyte p2 ws2) c ->
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗ Φ (Ret (WInt (strcmp_res s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strcmp (put (TAtom "iw_1.pr.1") (WPtr (mkPtr (ptr_addr p1 + c + 8) (ptr_cap p1)))
       (put (TAtom "iw_1.pr.2") (WPtr (mkPtr (ptr_addr p2 + c + 8) (ptr_cap p2)))
       (put (TAtom "iw_1.pr.3") (WInt (wrd ws1 Q1)) (put (TAtom "iw_1.pr.4") (WInt (wrd ws2 Q2)) e)))) [] None
       (Exec (TAtom "iw_1.L10") (b_insts blk10a) (b_jump blk10a))) : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Hs2. facts Hs1 Hs2.
  remember (Z.to_nat (Z.of_nat (List.length ws1) - Q1)) as n eqn:Hn.
  revert c Q1 Q2 e Hn. induction n as [|n IH]; intros c Q1 Q2 e Hn Hc HQ1 HQ2 Hsame;
    destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame) as [L1 L2]; [exfalso; lia|].
  iIntros "W1 W2 HK". cbn [blk10a b_insts b_jump].
  pose proof (wrd_range ws1 Q1 F1) as X1. pose proof (wrd_range ws2 Q2 F2) as X2.
  assert (Hb : forall u, 0 <= u < 8 -> sbyte p1 ws1 (c + u) = byte_of (wrd ws1 Q1) u /\
                                     sbyte p2 ws2 (c + u) = byte_of (wrd ws2 Q2) u)
    by (intros u Hu; unfold sbyte; split; apply bt_at; lia).
  sl. sb. rewrite (Z.mod_small (wrd ws1 Q1)); [|lia]. rewrite (Z.mod_small (wrd ws2 Q2)); [|lia].
  destruct (Z.eqb_spec (wrd ws1 Q1) (wrd ws2 Q2)) as [Exy|Nxy]; close_if.
  - en. do 4 sl. normt (loop_mask (wrd ws1 Q1)) ltac:(reflexivity). sl. sb.
    destruct (Z.eq_dec (loop_mask (wrd ws1 Q1)) 0) as [Hz|Hz].
    + rewrite Hz. close_if. en.
      assert (Hsame' : same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
      { apply (word_same _ _ c (wrd ws1 Q1) (wrd ws2 Q2) Hc Hsame Hb). intros u Hu. rewrite -Exy. split; [done|].
        apply (loop_mask_zero _ X1); [exact Hz | exact Hu]. }
      destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2'].
      sf. normp "iw_1.v24" (ptr_addr p1 + c + 16).
      iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
        [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
      sf. normp "iw_1.v27" (ptr_addr p2 + c + 16).
      iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (Q2 + 1) with "W2");
        [reflexivity | exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
      sg. normp "iw_1.pr.1" (ptr_addr p1 + (c + 8) + 8). normp "iw_1.pr.2" (ptr_addr p2 + (c + 8) + 8).
      norm "iw_1.pr.3" (wrd ws1 (Q1 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F1).
      norm "iw_1.pr.4" (wrd ws2 (Q2 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
      iApply (IH (c + 8) (Q1 + 1) (Q2 + 1) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsame' with "W1 W2 HK").
    + rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      replace (loop_mask (wrd ws1 Q1) =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_if. en.
      assert (Hres : strcmp_res s1 s2 = 0).
      { apply (word_zero s1 s2 _ _ c (wrd ws1 Q1) H1 A1 A2 Hc Hsame X1); [|exact Hz]. rewrite {2}Exy. exact Hb. }
      eapply (s_ret _ _ _ _ _ _ (strcmp_res s1 s2)); [reflexivity | reflexivity | rewrite Hres; reflexivity |].
      iApply ("HK" with "W1 W2").
  - destruct (words_differ _ _ X1 X2 Nxy) as (t & Ht & Hd).
    destruct (word_stop s1 s2 _ _ c _ _ 8 H1 A1 A2 Hc Hsame ltac:(lia) Hb (ex_intro _ t (conj Ht (or_intror Hd))))
      as (jj & Hjj & Hst & Hsj & Hres).
    eapply (fin_a _ _ _ _ _ _ _ jj); [lia | exact Hst | exact Hsj |]. rewrite -Hres. iApply ("HK" with "W1 W2").
Qed.

(** The unaligned loop's block. *)
Definition blk36 : block := Eval vm_compute in blk "iw_2.L36".

(** The unaligned loop: the first string's bytes from c start its word
    Q1, read as pr.4, the second's are at offset o of its word Q2, read
    as pr.5, and are not 0 to that word's end; pr.1 and pr.2 point past
    them, and v14 and v18 hold the shifts of o. Their bytes before c
    agree and are not 0. strcmp returns [strcmp_res]. *)
Lemma unaligned_loop dq1 dq2 p1 p2 b1 b2 reg1 reg2 ws1 ws2 s1 s2 c o Q1 Q2 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 -> 0 <= c -> 0 < o < 8 ->
  ptr_addr p1 mod 8 + c = 8 * Q1 -> ptr_addr p2 mod 8 + c = 8 * Q2 + o -> same_upto (sbyte p1 ws1) (sbyte p2 ws2) c ->
  (forall u, 0 <= u < 8 - o -> sbyte p2 ws2 (c + u) <> 0) ->
  lookup (TAtom "iw_2.v14") e = Some (WInt (8 * o)) -> lookup (TAtom "iw_2.v18") e = Some (WInt (64 - 8 * o)) ->
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗ Φ (Ret (WInt (strcmp_res s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strcmp (put (TAtom "iw_2.pr.1") (WPtr (mkPtr (ptr_addr p1 + c + 8) (ptr_cap p1)))
       (put (TAtom "iw_2.pr.2") (WPtr (mkPtr (wstart p2 + 8 * Q2 + 8) (ptr_cap p2)))
       (put (TAtom "iw_2.pr.4") (WInt (wrd ws1 Q1)) (put (TAtom "iw_2.pr.5") (WInt (wrd ws2 Q2)) e)))) [] None
       (Exec (TAtom "iw_2.L36") (b_insts blk36) (b_jump blk36))) : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Hs2. facts Hs1 Hs2.
  remember (Z.to_nat (Z.of_nat (List.length ws1) - Q1)) as n eqn:Hn.
  revert c Q1 Q2 e Hn. induction n as [|n IH]; intros c Q1 Q2 e Hn Hc [Ho0 Ho8] HQ1 HQ2 Hsame Hlo H14 H18;
    destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame) as [L1 L2]; [exfalso; lia|].
  iIntros "W1 W2 HK". cbn [blk36 b_insts b_jump].
  assert (Hnz2 : forall j, 0 <= j < c + 8 - o -> sbyte p2 ws2 j <> 0).
  { intros j Hj. destruct (Z.lt_ge_cases j c).
    - destruct (Hsame j ltac:(lia)) as [E N]. congruence.
    - replace j with (c + (j - c)) by lia. apply Hlo. lia. }
  pose proof (nonzero_len _ _ _ A2 Hnz2) as L2'.
  sf. normp "iw_2.v40" (wstart p2 + 8 * Q2 + 16).
  iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (Q2 + 1) with "W2");
    [reflexivity | exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
  set (lo := wrd ws2 Q2). set (hi := wrd ws2 (Q2 + 1)). set (x := wrd ws1 Q1).
  pose proof (wrd_range ws1 Q1 F1) as X1. pose proof (wrd_range ws2 Q2 F2) as XL.
  pose proof (wrd_range ws2 (Q2 + 1) F2) as XH. pose proof (merge_range lo hi o) as XM.
  slk "iw_2.v14" H14. slk "iw_2.v18" H18. sl. normt (merge lo hi o) ltac:(reflexivity).
  assert (Hb : forall u, 0 <= u < 8 -> sbyte p1 ws1 (c + u) = byte_of x u /\ sbyte p2 ws2 (c + u) = byte_of (merge lo hi o) u)
    by (intros u Hu; unfold sbyte; split; [apply bt_at | apply bt_merge]; lia).
  sl. sb. rewrite (Z.mod_small x); [|lia]. rewrite (Z.mod_small (merge lo hi o)); [|lia].
  destruct (Z.eqb_spec x (merge lo hi o)) as [Exy|Nxy]; close_if.
  - en. do 4 sl. normt (loop_mask hi) ltac:(reflexivity). sl. sb.
    assert (Hhi : forall u, 0 <= u < o -> byte_of hi u = byte_of x (u + 8 - o)).
    { intros u Hu. rewrite Exy merge_byte; [|lia|lia]. replace (u + 8 - o + o <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
      f_equal. lia. }
    destruct (Z.eq_dec (loop_mask hi) 0) as [Hz|Hz].
    + rewrite Hz. close_if. en.
      assert (Hsame' : same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
      { apply (word_same _ _ c x (merge lo hi o) Hc Hsame Hb). intros u Hu. rewrite -Exy. split; [done|].
        rewrite Exy merge_byte; [|lia|lia]. destruct (Z.ltb_spec (u + o) 8).
        - unfold lo. rewrite (bt_word ws2 Q2 (u + o)); [|lia|lia]. replace (8 * Q2 + (u + o)) with (ptr_addr p2 mod 8 + (c + u)) by lia. apply Hlo. lia.
        - apply (loop_mask_zero _ XH); [exact Hz | lia]. }
      destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2''].
      sf. normp "iw_2.v67" (ptr_addr p1 + c + 16).
      iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
        [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
      sg. normp "iw_2.pr.1" (ptr_addr p1 + (c + 8) + 8). normp "iw_2.pr.2" (wstart p2 + 8 * (Q2 + 1) + 8).
      norm "iw_2.pr.4" (wrd ws1 (Q1 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F1).
      norm "iw_2.pr.5" (wrd ws2 (Q2 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
      iApply (IH (c + 8) (Q1 + 1) (Q2 + 1) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsame'
                with "W1 W2 HK").
      * intros u Hu. unfold sbyte. replace (ptr_addr p2 mod 8 + (c + 8 + u)) with (8 * (Q2 + 1) + (o + u)) by lia.
        rewrite -bt_word; [|lia|lia]. apply (loop_mask_zero _ XH); [exact Hz | lia].
      * look H14.
      * look H18.
    + rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      replace (loop_mask hi =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_if. en.
      do 4 sl. normt (loop_mask x) ltac:(reflexivity). sl. sb.
      destruct (Z.eq_dec (loop_mask x) 0) as [Hx|Hx].
      * rewrite Hx. close_if. en.
        assert (Hsame' : same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
        { apply (word_same _ _ c x (merge lo hi o) Hc Hsame Hb). intros u Hu. rewrite -Exy. split; [done|].
          apply (loop_mask_zero _ X1); [exact Hx | exact Hu]. }
        destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2''].
        iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
          [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
        slk "iw_2.v14" H14. slk "iw_2.v18" H18. sl. sl. normt (shd hi o) ltac:(unfold shd; symmetry; apply Z.lor_0_r).
        sg. norm "iw_2.pr.6" (shd hi o) ltac:(symmetry; apply shd_mod).
        norm "iw_2.pr.3" (wrd ws1 (Q1 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F1).
        destruct (loop_mask_has_zero hi XH Hz) as (z & Hz8 & Hz0).
        assert (Hzo : o <= z).
        { destruct (Z.lt_ge_cases z o) as [Hlt|]; [|lia]. exfalso. rewrite Hhi in Hz0; [|lia].
          apply (proj1 (loop_mask_zero _ X1) Hx (z + 8 - o)); [lia | exact Hz0]. }
        assert (Hb' : forall u, 0 <= u < 8 - o -> sbyte p1 ws1 (c + 8 + u) = byte_of (wrd ws1 (Q1 + 1)) u /\
                                                sbyte p2 ws2 (c + 8 + u) = byte_of (shd hi o) u).
        { intros u Hu. unfold sbyte. split; [apply bt_at; lia|]. rewrite shd_byte; [|lia|lia].
          replace (u + o <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
          replace (ptr_addr p2 mod 8 + (c + 8 + u)) with (8 * (Q2 + 1) + (u + o)) by lia. rewrite -bt_word; [done|lia|lia]. }
        assert (Hst : stop_at (byte_of (wrd ws1 (Q1 + 1))) (byte_of (shd hi o)) (z - o)).
        { unfold stop_at. rewrite shd_byte; [|lia|lia]. replace (z - o + o <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
          replace (z - o + o) with z by lia. rewrite Hz0. lia. }
        assert (Hzr : 0 <= z - o < 8 - o) by lia.
        destruct (word_stop s1 s2 _ _ (c + 8) _ _ (8 - o) H1 A1 A2 ltac:(lia) Hsame' ltac:(lia) Hb'
                    (ex_intro _ (z - o) (conj Hzr Hst))) as (jj & Hjj & Hst' & Hsj & Hres).
        eapply (fin_c _ _ _ _ jj); [lia | exact Hst' | exact Hsj |]. rewrite -Hres. iApply ("HK" with "W1 W2").
      * rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
        replace (loop_mask x =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hx). close_if. en.
        assert (Hres : strcmp_res s1 s2 = 0).
        { apply (word_zero s1 s2 _ _ c x H1 A1 A2 Hc Hsame X1); [|exact Hx]. rewrite {2}Exy. exact Hb. }
        eapply (s_ret _ _ _ _ _ _ (strcmp_res s1 s2)); [reflexivity | reflexivity | rewrite Hres; reflexivity |].
        iApply ("HK" with "W1 W2").
  - destruct (words_differ _ _ X1 XM Nxy) as (t & Ht & Hd).
    destruct (word_stop s1 s2 _ _ c _ _ 8 H1 A1 A2 Hc Hsame ltac:(lia) Hb (ex_intro _ t (conj Ht (or_intror Hd))))
      as (jj & Hjj & Hst & Hsj & Hres).
    eapply (fin_b _ _ _ _ _ _ _ _ _ _ _ _ jj); [lia | exact Hst | exact Hsj |]. rewrite -Hres. iApply ("HK" with "W1 W2").
Qed.

End rules.
End StrcmpLoopOn.
