(** Once `c: strcmp` aligns the first string pointer to an 8-byte
    boundary, it compares 64-bit words in one of two loops. If the
    second pointer is also aligned, [aligned_loop] loads one word from
    each string per iteration; otherwise, [unaligned_loop] shifts and
    combines consecutive words from the second string with [merge].

    When a word pair differs or contains a NUL byte, control jumps to
    one of three inlined epilogues that locate the first stopping byte
    and return the difference. Every load first passes a Fil-C
    capability [[check]] inside the string's [[word]] window.

    To keep symbolic execution fast across long loop bodies, this module
    also wraps the program logic's stepping rules over proof-mode
    entailments. Those wrappers consume the [[later-modality|later
    modality]] at each step so goals stay flat. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpCode StrcmpBits.
From Glibc Require WordString.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.


(** Module [WS] provides the word-window string representation for R and LG0. *)
(** Module [LG] re-exports the program logic instance LG0. *)
Module LG := LG0.
(** Module [L] provides the nanofil language definition for LG. *)
Module L := LG.L.
Import L LG WordString.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** Instance [rules_irisGS] builds the [[iris]] machine semantics from
    the external registry and world invariant. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** Notation [gexpr] abbreviates expressions in the instantiated language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** Notation [ent] abbreviates proof-mode entailment in the Iris context. *)
Local Notation ent Δ P := (environments.envs_entails Δ P).

(** ## Steps in the proof mode

    Each instruction rule in [Logic](Logic.v) wraps its continuation in
    a [[later-modality|later modality]]. When stepping through dozens of
    instructions in a loop body, stripping those laters manually clutters
    the proof state. This section lifts each stepping rule to
    proof-mode entailments via [next_to] and defines short tactics for
    symbolic execution. *)

(** Lemma [next_to] strips a leading later modality from a weakest
    precondition rule when proving a proof-mode entailment. *)
Lemma next_to Δ (P Q : iProp Σ) : (⊢ ▷ P -∗ Q) -> ent Δ P -> ent Δ Q.
Proof. rewrite environments.envs_entails_unseal. intros HPQ HP. iIntros "H". iApply HPQ. iNext. by iApply HP. Qed.

(** Lemma [s_let] steps past a pure `let` instruction inside a
    proof-mode entailment. *)
Lemma s_let Δ f e ls l d k o args rest j classes xs w Φ :
  general_op o = true -> op_arg_classes o k = Some classes -> map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal w) m)) ->
  ent Δ (WP (ERun (mkFrame f (put d w e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [eapply (wp_let registry wi ge); eauto | done]. Qed.

(** Lemma [s_letn] steps past an integer `let` and binds a fresh Rocq
    variable x equal to the result so later steps stay compact. *)
Lemma s_letn Δ f e ls l d k o args rest j classes xs X Φ :
  general_op o = true -> op_arg_classes o k = Some classes -> map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal (WInt X)) m)) ->
  (forall x, x = X -> ent Δ (WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }})) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros. eapply s_let; eauto. Qed.

(** Pointer arithmetic in Fil-C produces a derived pointer through a
    `flight` instruction, which [s_flight] steps past in one rule. *)
Lemma s_flight Δ f e ls l d o args lw rest j xs n c Φ :
  map_option (flight_arg_x ge e) args = Some xs -> alu o L xs = Some (WInt n) -> flight_cap ge e lw = Some c ->
  ent Δ (WP (ERun (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [eapply (wp_flight registry wi ge); eauto | done]. Qed.

(** Entering a basic block resolves its phi bindings from the incoming
    edge, which [s_enter] performs in a single step. *)
Lemma s_enter Δ f e ls l from b e' Φ :
  find_block l (fn_blocks f) = Some b -> phis_env ge (b_phis b) from e = Some e' ->
  ent Δ (WP (ERun (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Enter l from)) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [eapply (wp_enter registry wi ge); eauto | done]. Qed.

(** Lemma [s_goto] steps past an unconditional `goto` jump inside a
    proof-mode entailment. *)
Lemma s_goto Δ f e ls l t Φ :
  ent Δ (WP (ERun (mkFrame f e ls None (Enter (edge_label t) (Some l))) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l [] (JGoto t))) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [apply (wp_goto registry wi ge) | done]. Qed.

(** Lemma [s_branch] steps past a conditional `branch` instruction
    inside a proof-mode entailment. *)
Lemma s_branch Δ f e ls l v t1 t2 n Φ :
  value_x ge e W v = Some (WInt n) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) : gexpr) {{ Φ }}) ->
  ent Δ (WP (ERun (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) : gexpr) {{ Φ }}).
Proof. intros. eapply next_to; [eapply (wp_branch registry wi ge); eauto | done]. Qed.

(** Lemma [s_ret] steps past a `ret` instruction and rewrites the
    returned word to any provably equal integer x'. *)
Lemma s_ret Δ f e l v x x' Φ :
  fn_ret f = RClass W -> value_x ge e W v = Some (WInt x) -> x = x' -> ent Δ (Φ (Ret (WInt x'))) ->
  ent Δ (WP (ERun (mkFrame f e [] None (Exec l [] (JRet v))) : gexpr) {{ Φ }}).
Proof. intros Hk Hv -> H. eapply next_to; [eapply (wp_ret registry wi ge); eauto | done]. Qed.

(** Tactic [sl] steps past a `let` instruction while keeping its bound
    value symbolic. *)

(** Tactic [sn] steps past an integer `let` and names the resulting
    integer in the context. *)

(** Tactic [sf] steps past a capability `flight` check instruction. *)

(** Tactic [en] enters the target basic block of a pending frame jump. *)

(** Tactic [sg] steps through a `goto` terminator and immediately enters
    its destination block. *)

(** Tactic [slk] steps past a `let` instruction that reads an earlier
    variable n whose value is given by H. *)

(** Tactic [sb] steps past a conditional `branch` instruction without
    evaluating its condition. *)

(** Tactic [norm] rewrites the integer held by variable name to v using
    tactic tac. *)
Ltac norm name v tac :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by tac end.
(** Tactic [normt] normalizes the integer in the newest local variable
    to v using tactic tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Tactic [normp] rewrites the address of the pointer held by variable
    name to v using linear arithmetic. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** ## Reads of a window

    Every memory read in `c: strcmp` executes a Fil-C bounds [[check]]
    followed by a raw load from the string's [[word]] window. Rather
    than unfolding the window representation at every load site,
    [wp_win_word] and [wp_win_byte] verify both instructions together
    and return the window permission unchanged. *)

(** Lemma [win_cell] shows that when physical memory agrees with a
    window's pieces, it also agrees with the 8-byte cell for word q. *)
Lemma win_cell m b wo ws q : all_agree m (words_ps b wo ws) -> 0 <= q < Z.of_nat (List.length ws) ->
  all_agree m (cell b (wo + 8 * q) (wrd ws q)).
Proof.
  intros Ha Hq. apply all_agree_cell. intros i Hi.
  pose proof (words_ps_elem b wo ws (Z.to_nat (8 * q + i)) _ (wbytes_bt ws (8 * q + i) ltac:(lia))) as Hin.
  rewrite Z2Nat.id in Hin; [|lia]. rewrite (bt_word ws q i); [|lia|lia].
  replace (wo + 8 * q + i) with (wo + (8 * q + i)) by lia. exact (all_agree_elem _ _ _ _ Ha Hin).
Qed.

(** Lemma [wp_win_word] steps past an 8-byte read [[check]] and a
    64-bit load at word q of a window, returning word q from ws. *)
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

(** Lemma [wp_win_byte] steps past a 1-byte read [[check]] and a
    signed-byte load at byte i of a window, returning its sign-extended
    value. *)
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

(** ## Returning a byte difference

    When a word pair differs or reaches a NUL byte, glibc computes
    `find_zero_ne_all`, counts trailing bits to locate the first stopping
    byte j, and returns the byte difference. Because the compiler inlined
    this epilogue at three sites, [fin_tac] handles the shared instruction
    sequence for [fin_a], [fin_b], and [fin_c]. The section concludes
    with the two main word-loop proofs, [aligned_loop] and
    [unaligned_loop]. *)

(** Tactic [fin_tac] steps through glibc's comparison-mask, bit-count,
    and byte-subtraction epilogue for words x and y stopping at byte j. *)
Ltac fin_tac x y j :=
  pose proof (cmp_mask_range x y); pose proof (byte_of_range x j); pose proof (byte_of_range y j);
  let Ht := fresh "Ht" in let Hn := fresh "Hn" in
  match goal with H1 : stop_at _ _ j, H2 : same_upto _ _ j |- _ =>
    destruct (cmp_mask_first x y j ltac:(lia) H1 H2) as [Ht Hn] end;
  do 10 step_symbolic; normt (cmp_mask x y) ltac:(reflexivity); step_symbolic; branch_symbolic;
  replace (cmp_mask x y mod 2 ^ 64 =? 0 mod 2 ^ 64) with false
    by (symmetry; apply Z.eqb_neq; rewrite Z.mod_small; [exact Hn | lia]);
  close_if; step;
  do 15 step_named;
  match goal with |- context [mkFrame _ (put _ (WInt ?t) _) _ _ _] =>
    let H := fresh in assert (H : t = tail (cmp_mask x y)) by (eapply tail_chain; eassumption);
    rewrite H Ht; clear H end;
  repeat match goal with H : ?v = _ |- _ => is_var v; clear H end;
  (step; step); step_symbolic; normt j ltac:(arith); step_symbolic; normt (8 * j) ltac:(arith);
  step_symbolic; step_symbolic; normt (byte_of x j) ltac:(symmetry; apply ub_shift; lia);
  step_symbolic; step_symbolic; normt (byte_of y j) ltac:(symmetry; apply ub_shift; lia);
  step_symbolic; normt ((byte_of x j - byte_of y j) mod 2 ^ 32) ltac:(arith);
  (step; step); eapply s_ret; [reflexivity | reflexivity | rewrite !Zmod_mod; reflexivity |].

(** Lemma [fin_a] verifies the difference epilogue for the aligned
    word loop. *)
Lemma fin_a Δ e z a b x y j Φ :
  0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  ent Δ (Φ (Ret (WInt ((byte_of x j - byte_of y j) mod 2 ^ 32)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strcmp (put (TAtom "iw_1.v15") z (put (TAtom "iw_1.pr.1") a (put (TAtom "iw_1.pr.2") b
         (put (TAtom "iw_1.pr.3") (WInt x) (put (TAtom "iw_1.pr.4") (WInt y) e))))) [] None
         (Enter (TAtom "iw_1.iw_2.start") (Some (TAtom "iw_1.L10")))) : gexpr) {{ Φ }}).
Proof. intros Hj Hst Hs HK. step. fin_tac x y j. exact HK. Qed.

(** Lemma [fin_b] verifies the difference epilogue when the unaligned
    loop finds a mismatch against the merged word y. *)
Lemma fin_b Δ e z1 z2 z3 z4 z5 z6 z7 z8 x y j Φ :
  0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  ent Δ (Φ (Ret (WInt ((byte_of x j - byte_of y j) mod 2 ^ 32)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strcmp (put (TAtom "iw_2.v54") z1 (put (TAtom "iw_2.v48") (WInt y)
         (put (TAtom "iw_2.v47") z2 (put (TAtom "iw_2.v44") z3 (put (TAtom "iw_2.v41") z4 (put (TAtom "chk7") z5
         (put (TAtom "iw_2.v40") z6 (put (TAtom "iw_2.pr.1") z7 (put (TAtom "iw_2.pr.2") z8
         (put (TAtom "iw_2.pr.4") (WInt x) e)))))))))) [] None
         (Enter (TAtom "iw_2.iw_2.start") (Some (TAtom "iw_2.L36")))) : gexpr) {{ Φ }}).
Proof. intros Hj Hst Hs HK. step. fin_tac x y j. exact HK. Qed.

(** Function [blk] looks up basic block l in `__GI_strcmp`. *)
Definition blk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks glibc_strcmp) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** Constant [blk30] holds the basic block for the trailing-bytes exit
    of an unaligned second string. *)
Definition blk30 : block := Eval vm_compute in blk "iw_2.L30".

(** Lemma [fin_c] verifies the difference epilogue when an unaligned
    second string ends before the next word boundary. *)
Lemma fin_c Δ e x y j Φ :
  0 <= j < 8 -> stop_at (byte_of x) (byte_of y) j -> same_upto (byte_of x) (byte_of y) j ->
  ent Δ (Φ (Ret (WInt ((byte_of x j - byte_of y j) mod 2 ^ 32)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strcmp (put (TAtom "iw_2.pr.3") (WInt x) (put (TAtom "iw_2.pr.6") (WInt y) e)) [] None
         (Exec (TAtom "iw_2.L30") (b_insts blk30) (b_jump blk30))) : gexpr) {{ Φ }}).
Proof. intros Hj Hst Hs HK. cbn [blk30 b_insts b_jump]. fin_tac x y j. exact HK. Qed.

(** To avoid repeating boilerplate at the start of each loop proof,
    tactic [facts] extracts the address bounds and byte-agreement
    hypotheses from both strings. *)
Ltac facts Hs1 Hs2 :=
  destruct (shape_facts _ _ _ _ _ Hs1) as (B1 & S1 & M1 & P1 & K1 & E1 & R1 & N1 & C1);
  destruct (shape_facts _ _ _ _ _ Hs2) as (B2 & S2 & M2 & P2 & K2 & E2 & R2 & N2 & C2);
  pose proof (ss_words _ _ _ _ _ Hs1) as F1; pose proof (ss_words _ _ _ _ _ Hs2) as F2;
  pose proof (ss_chars _ _ _ _ _ Hs1) as H1; pose proof (sbyte_agree _ _ _ _ _ Hs1) as A1;
  pose proof (sbyte_agree _ _ _ _ _ Hs2) as A2.

(** Constant [blk10a] holds the header block of the aligned word loop. *)
Definition blk10a : block := Eval vm_compute in blk "iw_1.L10".

(** Lemma [aligned_loop] proves by induction on the remaining words of
    the first string that comparing aligned 64-bit words returns
    [strcmp_res] and restores both windows. *)
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
  step_symbolic. branch_symbolic. rewrite (Z.mod_small (wrd ws1 Q1)); [|lia]. rewrite (Z.mod_small (wrd ws2 Q2)); [|lia].
  destruct (Z.eqb_spec (wrd ws1 Q1) (wrd ws2 Q2)) as [Exy|Nxy]; close_if.
  - step. do 4 step_symbolic. normt (loop_mask (wrd ws1 Q1)) ltac:(reflexivity). step_symbolic. branch_symbolic.
    destruct (Z.eq_dec (loop_mask (wrd ws1 Q1)) 0) as [Hz|Hz].
    + rewrite Hz. close_if. step.
      assert (Hsame' : same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
      { apply (word_same _ _ c (wrd ws1 Q1) (wrd ws2 Q2) Hc Hsame Hb). intros u Hu. rewrite -Exy. split; [done|].
        apply (loop_mask_zero _ X1); [exact Hz | exact Hu]. }
      destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2'].
      step. normp "iw_1.v24" (ptr_addr p1 + c + 16).
      iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
        [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
      step. normp "iw_1.v27" (ptr_addr p2 + c + 16).
      iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (Q2 + 1) with "W2");
        [reflexivity | exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
      (step; step). normp "iw_1.pr.1" (ptr_addr p1 + (c + 8) + 8). normp "iw_1.pr.2" (ptr_addr p2 + (c + 8) + 8).
      norm "iw_1.pr.3" (wrd ws1 (Q1 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F1).
      norm "iw_1.pr.4" (wrd ws2 (Q2 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
      iApply (IH (c + 8) (Q1 + 1) (Q2 + 1) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsame' with "W1 W2 HK").
    + rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      replace (loop_mask (wrd ws1 Q1) =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_if. step.
      assert (Hres : strcmp_res s1 s2 = 0).
      { apply (word_zero s1 s2 _ _ c (wrd ws1 Q1) H1 A1 A2 Hc Hsame X1); [|exact Hz]. rewrite {2}Exy. exact Hb. }
      eapply (s_ret _ _ _ _ _ _ (strcmp_res s1 s2)); [reflexivity | reflexivity | rewrite Hres; reflexivity |].
      iApply ("HK" with "W1 W2").
  - destruct (words_differ _ _ X1 X2 Nxy) as (t & Ht & Hd).
    destruct (word_stop s1 s2 _ _ c _ _ 8 H1 A1 A2 Hc Hsame ltac:(lia) Hb (ex_intro _ t (conj Ht (or_intror Hd))))
      as (jj & Hjj & Hst & Hsj & Hres).
    eapply (fin_a _ _ _ _ _ _ _ jj); [lia | exact Hst | exact Hsj |]. rewrite -Hres. iApply ("HK" with "W1 W2").
Qed.

(** Constant [blk36] holds the header block of the unaligned word loop. *)
Definition blk36 : block := Eval vm_compute in blk "iw_2.L36".

(** Lemma [unaligned_loop] proves by induction on the remaining words of
    the first string that merging consecutive words of an unaligned
    second string returns [strcmp_res] and restores both windows. *)
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
  step. normp "iw_2.v40" (wstart p2 + 8 * Q2 + 16).
  iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq2 b2 reg2 (wstart p2 - b2) ws2 (Q2 + 1) with "W2");
    [reflexivity | exact C2 | cbn; lia | lia | lia | lia | lia | lia | exact F2 |]. iIntros "W2".
  set (lo := wrd ws2 Q2). set (hi := wrd ws2 (Q2 + 1)). set (x := wrd ws1 Q1).
  pose proof (wrd_range ws1 Q1 F1) as X1. pose proof (wrd_range ws2 Q2 F2) as XL.
  pose proof (wrd_range ws2 (Q2 + 1) F2) as XH. pose proof (merge_range lo hi o) as XM.
  step_lookup "iw_2.v14" H14. step_lookup "iw_2.v18" H18. step_symbolic. normt (merge lo hi o) ltac:(reflexivity).
  assert (Hb : forall u, 0 <= u < 8 -> sbyte p1 ws1 (c + u) = byte_of x u /\ sbyte p2 ws2 (c + u) = byte_of (merge lo hi o) u)
    by (intros u Hu; unfold sbyte; split; [apply bt_at | apply bt_merge]; lia).
  step_symbolic. branch_symbolic. rewrite (Z.mod_small x); [|lia]. rewrite (Z.mod_small (merge lo hi o)); [|lia].
  destruct (Z.eqb_spec x (merge lo hi o)) as [Exy|Nxy]; close_if.
  - step. do 4 step_symbolic. normt (loop_mask hi) ltac:(reflexivity). step_symbolic. branch_symbolic.
    assert (Hhi : forall u, 0 <= u < o -> byte_of hi u = byte_of x (u + 8 - o)).
    { intros u Hu. rewrite Exy merge_byte; [|lia|lia]. replace (u + 8 - o + o <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
      f_equal. lia. }
    destruct (Z.eq_dec (loop_mask hi) 0) as [Hz|Hz].
    + rewrite Hz. close_if. step.
      assert (Hsame' : same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
      { apply (word_same _ _ c x (merge lo hi o) Hc Hsame Hb). intros u Hu. rewrite -Exy. split; [done|].
        rewrite Exy merge_byte; [|lia|lia]. destruct (Z.ltb_spec (u + o) 8).
        - unfold lo. rewrite (bt_word ws2 Q2 (u + o)); [|lia|lia]. replace (8 * Q2 + (u + o)) with (ptr_addr p2 mod 8 + (c + u)) by lia. apply Hlo. lia.
        - apply (loop_mask_zero _ XH); [exact Hz | lia]. }
      destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2''].
      step. normp "iw_2.v67" (ptr_addr p1 + c + 16).
      iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
        [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
      (step; step). normp "iw_2.pr.1" (ptr_addr p1 + (c + 8) + 8). normp "iw_2.pr.2" (wstart p2 + 8 * (Q2 + 1) + 8).
      norm "iw_2.pr.4" (wrd ws1 (Q1 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F1).
      norm "iw_2.pr.5" (wrd ws2 (Q2 + 1)) ltac:(symmetry; apply Z.mod_small, wrd_range, F2).
      iApply (IH (c + 8) (Q1 + 1) (Q2 + 1) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsame'
                with "W1 W2 HK").
      * intros u Hu. unfold sbyte. replace (ptr_addr p2 mod 8 + (c + 8 + u)) with (8 * (Q2 + 1) + (o + u)) by lia.
        rewrite -bt_word; [|lia|lia]. apply (loop_mask_zero _ XH); [exact Hz | lia].
      * look H14.
      * look H18.
    + rewrite (Z.mod_small (loop_mask _) _ (loop_mask_range _)).
      replace (loop_mask hi =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hz). close_if. step.
      do 4 step_symbolic. normt (loop_mask x) ltac:(reflexivity). step_symbolic. branch_symbolic.
      destruct (Z.eq_dec (loop_mask x) 0) as [Hx|Hx].
      * rewrite Hx. close_if. step.
        assert (Hsame' : same_upto (sbyte p1 ws1) (sbyte p2 ws2) (c + 8)).
        { apply (word_same _ _ c x (merge lo hi o) Hc Hsame Hb). intros u Hu. rewrite -Exy. split; [done|].
          apply (loop_mask_zero _ X1); [exact Hx | exact Hu]. }
        destruct (same_upto_len _ _ _ _ _ A1 A2 Hsame') as [L1' L2''].
        iApply (wp_win_word _ _ _ _ _ _ _ _ _ _ dq1 b1 reg1 (wstart p1 - b1) ws1 (Q1 + 1) with "W1");
          [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W1".
        step_lookup "iw_2.v14" H14. step_lookup "iw_2.v18" H18. step_symbolic. step_symbolic. normt (shd hi o) ltac:(unfold shd; symmetry; apply Z.lor_0_r).
        (step; step). norm "iw_2.pr.6" (shd hi o) ltac:(symmetry; apply shd_mod).
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
        replace (loop_mask x =? 0 mod 2 ^ 64) with false by (symmetry; apply Z.eqb_neq; exact Hx). close_if. step.
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
