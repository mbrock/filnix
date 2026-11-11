(** glibc's `__GI_strcmp` (StrcmpCode.v) over [word_string] (WordString.v) at
    any shares dq1 and dq2, with no aliasing restriction between p1 and p2. *)

From Stdlib Require Import String ZArith Lia.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpCode StrcmpBits.
Open Scope Z_scope.
Open Scope list_scope.

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
Module StrcmpLogicOn (R : Runtime) (LG0 : LogicSig R).
Module WS := WordStringOn R LG0.
Module LG := LG0.
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

(** ## Pure and window step rules *)

(** [wp_let] as an entailment implication, avoiding proofmode overhead. *)
Lemma pure_let (P : iProp Σ) f e ls l d k o args rest j classes xs w Φ :
  general_op o = true -> op_arg_classes o k = Some classes -> map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal w) m)) ->
  (P ⊢ WP (ERun (mkFrame f (put d w e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  (P ⊢ WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros Hg Hc Hx Ho H. iIntros "HP". iApply wp_let; [exact Hg | exact Hc | exact Hx | exact Ho |]. iNext. by iApply H. Qed.

(** [pure_let] binding a fresh Coq variable x for an integer result. *)
Lemma pure_let_gen (P : iProp Σ) f e ls l d k o args rest j classes xs w Φ :
  general_op o = true -> op_arg_classes o k = Some classes -> map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal (WInt w)) m)) ->
  (forall x, x = w -> P ⊢ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  (P ⊢ WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros Hg Hc Hx Ho H. exact (pure_let P f e ls l d k o args rest j classes xs (WInt w) Φ Hg Hc Hx Ho (H w eq_refl)). Qed.

(** Replace the integer at the head of the frame's environment. *)
Lemma set_head_int (P : iProp Σ) f d x v e ls dm pt Φ :
  x = v -> (P ⊢ WP (ERun (mkFrame f (put d (WInt v) e) ls dm pt) : gexpr) {{ Φ }}) ->
  (P ⊢ WP (ERun (mkFrame f (put d (WInt x) e) ls dm pt) : gexpr) {{ Φ }}).
Proof. intros -> H. exact H. Qed.

(** Replace the pointer address at the head of the frame's environment. *)
Lemma set_head_ptr (P : iProp Σ) f d a v c e ls dm pt Φ :
  a = v -> (P ⊢ WP (ERun (mkFrame f (put d (WPtr (mkPtr v c)) e) ls dm pt) : gexpr) {{ Φ }}) ->
  (P ⊢ WP (ERun (mkFrame f (put d (WPtr (mkPtr a c)) e) ls dm pt) : gexpr) {{ Φ }}).
Proof. intros -> H. exact H. Qed.

(** [wp_flight] as an entailment implication. *)
Lemma pure_flight (P : iProp Σ) f e ls l d o args lw rest j xs n c Φ :
  map_option (flight_arg_x ge e) args = Some xs -> alu o L xs = Some (WInt n) -> flight_cap ge e lw = Some c ->
  (P ⊢ WP (ERun (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  (P ⊢ WP (ERun (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) : gexpr) {{ Φ }}).
Proof. intros Hx Ha Hc H. iIntros "HP". iApply wp_flight; [exact Hx | exact Ha | exact Hc |]. iNext. by iApply H. Qed.

(** [wp_enter] as an entailment implication. *)
Lemma pure_enter (P : iProp Σ) f e ls l from b e' Φ :
  find_block l (fn_blocks f) = Some b -> phis_env ge (b_phis b) from e = Some e' ->
  (P ⊢ WP (ERun (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) : gexpr) {{ Φ }}) ->
  (P ⊢ WP (ERun (mkFrame f e ls None (Enter l from)) : gexpr) {{ Φ }}).
Proof. intros Hb Hp H. iIntros "HP". iApply wp_enter; [exact Hb | exact Hp |]. iNext. by iApply H. Qed.

(** [wp_goto] as an entailment implication. *)
Lemma pure_goto (P : iProp Σ) f e ls l t Φ :
  (P ⊢ WP (ERun (mkFrame f e ls None (Enter (edge_label t) (Some l))) : gexpr) {{ Φ }}) ->
  (P ⊢ WP (ERun (mkFrame f e ls None (Exec l [] (JGoto t))) : gexpr) {{ Φ }}).
Proof. intros H. iIntros "HP". iApply wp_goto. iNext. by iApply H. Qed.

(** [wp_branch] as an entailment implication. *)
Lemma pure_branch (P : iProp Σ) f e ls l v t1 t2 n Φ :
  value_x ge e W v = Some (WInt n) ->
  (P ⊢ WP (ERun (mkFrame f e ls None (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) : gexpr) {{ Φ }}) ->
  (P ⊢ WP (ERun (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) : gexpr) {{ Φ }}).
Proof. intros Hv H. iIntros "HP". iApply wp_branch; [exact Hv|]. iNext. by iApply H. Qed.

(** [wp_ret] as an entailment implication. *)
Lemma pure_ret (P : iProp Σ) f e l v k x Φ :
  fn_ret f = RClass k -> value_x ge e k v = Some x -> (P ⊢ Φ (Ret x)) ->
  (P ⊢ WP (ERun (mkFrame f e [] None (Exec l [] (JRet v))) : gexpr) {{ Φ }}).
Proof. intros Hk Hv H. iIntros "HP". iApply wp_ret; [exact Hk | exact Hv |]. iNext. by iApply H. Qed.

(** One pure instruction or jump step. *)
Ltac pst :=
  first [ eapply pure_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |]
        | eapply pure_flight; [reflexivity | reflexivity | reflexivity |]
        | eapply pure_enter; [reflexivity | reflexivity | cbn [b_insts b_jump]]
        | eapply pure_goto ].

(** One pure [Let] step reading a temporary from H in the environment. *)
Ltac pst_look H :=
  lazymatch type of H with lookup ?n _ = Some ?v =>
    eapply pure_let; [ reflexivity | reflexivity
                     | cbn [map2_option]; rewrite (value_x_tmp _ _ _ n v); [reflexivity | look H]
                     | intros ?; reflexivity | ]
  end.

(** One pure [Let] step naming its integer result as a fresh variable. *)
Ltac pst_gen :=
  let x := fresh "x" in let E := fresh "E" in
  eapply pure_let_gen; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | intros x E].

(** Replace the newest temporary's integer with v. *)
Ltac top_int v := eapply (set_head_int _ _ _ _ v); [first [reflexivity | arith] |].

(** Replace the newest temporary's pointer address with v. *)
Ltac top_ptr v :=
  eapply (set_head_ptr _ _ _ _ v);
  [unfold wstart, ptr_add, raw_address in *; cbn [ptr_addr ptr_cap length] in *; first [reflexivity | arith] |].

(** Replace the newest temporary's comparison mask with [cmp_mask] x y. *)
Ltac top_cmp_mask x y :=
  eapply (set_head_int _ _ _ _ (cmp_mask x y));
  [ eapply cmp_mask_chain; eassumption | repeat match goal with H : ?v = _ |- _ => is_var v; clear H end ].

(** Replace the newest temporary's popcount with [tail] r. *)
Ltac top_tail r :=
  eapply (set_head_int _ _ _ _ (tail r));
  [ eapply tail_chain; eassumption | repeat match goal with H : ?v = _ |- _ => is_var v; clear H end ].

(** Split the window of ws at word j, keeping a wand to reassemble it. *)
Lemma wwin_drop dq p b reg ws (n j : nat) :
  (j <= length ws)%nat -> wstart (ptr_add p (Z.of_nat n)) - b = wstart p - b + 8 * Z.of_nat j ->
  wwin dq b reg (wstart p - b) ws ⊢
  wwin dq b reg (wstart (ptr_add p (Z.of_nat n)) - b) (drop j ws) ∗
  (wwin dq b reg (wstart (ptr_add p (Z.of_nat n)) - b) (drop j ws) -∗ wwin dq b reg (wstart p - b) ws).
Proof.
  intros Hj Ho.
  assert (Hsp : words_ps b (wstart p - b) ws =
                words_ps b (wstart p - b) (take j ws) ++ words_ps b (wstart p - b + 8 * Z.of_nat j) (drop j ws))
    by (rewrite -{1}(take_drop j ws); rewrite words_ps_app (length_take_le _ _ Hj); reflexivity).
  rewrite /wwin Ho !Hsp !ptsq_app.
  iIntros "[Hl [Ht Hd]]". iSplitL "Hl Hd"; [iFrame|]. iIntros "[Hl Hd]". iFrame.
Qed.

(** The combined window state and return continuation for two strings. *)
Definition strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 (Φ : outcome -> iProp Σ) : iProp Σ :=
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 ∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 ∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗
   Φ (Ret (WInt (strcmp_res s1 s2)))).

(** Finishing a return from [strcmp_ctx]. *)
Lemma strcmp_ctx_done dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ :
  strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ ⊢ Φ (Ret (WInt (strcmp_res s1 s2))).
Proof. iIntros "(H1 & H2 & HK)". iApply ("HK" with "H1 H2"). Qed.

(** Focus the first string's window in [strcmp_ctx]. *)
Lemma ctx_wwin_1 dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ :
  strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ ⊢
  wwin dq1 b1 reg1 (wstart p1 - b1) ws1 ∗
  (wwin dq1 b1 reg1 (wstart p1 - b1) ws1 -∗ strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ).
Proof. iIntros "($ & H2 & HK)". iIntros "$". iFrame. Qed.

(** Focus the second string's window in [strcmp_ctx]. *)
Lemma ctx_wwin_2 dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ :
  strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ ⊢
  wwin dq2 b2 reg2 (wstart p2 - b2) ws2 ∗
  (wwin dq2 b2 reg2 (wstart p2 - b2) ws2 -∗ strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ).
Proof. iIntros "(H1 & $ & HK)". iIntros "$". iFrame. Qed.

(** Advancing both strings in [strcmp_ctx] by n equal nonzero bytes. *)
Lemma pure_advance (n j1 j2 : nat) dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 ex Φ :
  (j1 <= length ws1)%nat -> (j2 <= length ws2)%nat ->
  wstart (ptr_add p1 (Z.of_nat n)) - b1 = wstart p1 - b1 + 8 * Z.of_nat j1 ->
  wstart (ptr_add p2 (Z.of_nat n)) - b2 = wstart p2 - b2 + 8 * Z.of_nat j2 ->
  strcmp_res s1 s2 = strcmp_res (drop n s1) (drop n s2) ->
  (strcmp_ctx dq1 b1 reg1 (ptr_add p1 (Z.of_nat n)) (drop j1 ws1) (drop n s1)
              dq2 b2 reg2 (ptr_add p2 (Z.of_nat n)) (drop j2 ws2) (drop n s2) Φ ⊢ WP ex {{ Φ }}) ->
  strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ ⊢ WP ex {{ Φ }}.
Proof.
  intros Hj1 Hj2 Ho1 Ho2 Hres H. iIntros "(H1 & H2 & HK)". iApply H.
  iDestruct (wwin_drop dq1 p1 b1 reg1 ws1 n j1 Hj1 Ho1 with "H1") as "[H1 Hk1]".
  iDestruct (wwin_drop dq2 p2 b2 reg2 ws2 n j2 Hj2 Ho2 with "H2") as "[H2 Hk2]".
  iFrame "H1 H2". iIntros "H1 H2". rewrite -Hres. iApply ("HK" with "(Hk1 H1) (Hk2 H2)").
Qed.

(** A read check over a string window extracted from P. *)
Lemma pure_check (P : iProp Σ) dq b reg p ws s f e ls l d hi args rest j classes q Φ :
  str_shape p b reg ws s ->
  (P ⊢ wwin dq b reg (wstart p - b) ws ∗ (wwin dq b reg (wstart p - b) ws -∗ P)) ->
  op_arg_classes (Check 0 hi Read 1) A = Some classes -> map2_option (value_x ge e) classes args = Some [WPtr q] ->
  ptr_cap q = ptr_cap p -> 0 <= hi -> b <= ptr_addr q -> ptr_addr q + hi <= wstart p + 8 * Z.of_nat (length ws) ->
  (P ⊢ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  P ⊢ WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check 0 hi Read 1) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hs Hctx Hc Hx Hcap Hhi0 Hlo Hhi H. iIntros "HP". iDestruct (Hctx with "HP") as "([Hl Hw] & HK)".
  pose proof (ss_cap _ _ _ _ _ Hs) as Hcp. pose proof (ss_base _ _ _ _ _ Hs).
  pose proof (ss_fit _ _ _ _ _ Hs). pose proof (ss_space _ _ _ _ _ Hs).
  iApply (wp_check_read_dq with "Hl");
    [exact Hc | exact Hx | rewrite Hcap; exact Hcp | arith | arith | apply Z.mod_1_r |].
  iNext. iIntros "Hl". iApply H. iApply ("HK" with "[$Hl $Hw]").
Qed.

(** A signed-byte load at p, the start of s, over a window extracted from P. *)
Lemma pure_load_byte (P : iProp Σ) dq b reg p ws s f e ls l d args rest j classes y Φ :
  str_shape p b reg ws s ->
  (P ⊢ wwin dq b reg (wstart p - b) ws ∗ (wwin dq b reg (wstart p - b) ws -∗ P)) ->
  op_arg_classes (RawLoad (LdNarrow Sb) 0) W = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] -> extended Sb W (hd 0 s) = Some y ->
  (P ⊢ WP (ERun (mkFrame f (put d y e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  P ⊢ WP (ERun (mkFrame f e ls None (Exec l (Let d W (RawLoad (LdNarrow Sb) 0) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hs Hctx Hc Hx Hy H. iIntros "HP". iDestruct (Hctx with "HP") as "([Hl Hw] & HK)".
  iApply (wp_read_dq registry wi ge dq ([(PLive b, VLive reg)] ++ words_ps b (wstart p - b) ws) _ _ []
            with "[Hl Hw] [HK]").
  - intros m fuel (Hf & _). apply all_agree_app in Hf as [[Hlv _] Hws].
    cbn [agree_piece fst snd] in Hlv. destruct Hlv as [Er Lv].
    pose proof (str_shape_byte p b reg ws s 0 Hs ltac:(lia)) as Eby.
    destruct (str_shape_hd_range p b reg ws s Hs) as [_ Ehd]. rewrite Nat.add_0_r Ehd in Eby.
    pose proof (words_ps_elem b (wstart p - b) ws (Z.to_nat (ptr_addr p mod 8)) (hd 0 s) Eby) as Hin.
    pose proof (proj2 (all_agree_elem _ _ _ _ Hws Hin) reg Er Lv) as (Ho & He & Emb).
    pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
    pose proof (ss_base _ _ _ _ _ Hs). pose proof (ss_start _ _ _ _ _ Hs). pose proof (ss_space _ _ _ _ _ Hs).
    rewrite Z2Nat.id in Ho, He, Emb; [|lia]. unfold wstart in Ho, He, Emb.
    replace (b + (ptr_addr p - ptr_addr p mod 8 - b + ptr_addr p mod 8)) with (ptr_addr p) in Emb by lia.
    assert (Hra : raw_address (ptr_addr p) 0 = ptr_addr p) by (unfold raw_address; rewrite Z.add_0_r; apply Z.mod_small; lia).
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load_byte m W Sb p 0 eq_refl) Hra;
      [rewrite Emb Hy; reflexivity | apply (access_read _ b reg); [exact (ss_cap _ _ _ _ _ Hs) | exact Er | lia | lia | apply Z.mod_1_r]].
  - rewrite ptsq_app. iFrame.
  - iNext. iIntros "H". rewrite ptsq_app. iDestruct "H" as "[Hl Hw]". iApply H. iApply ("HK" with "[$Hl $Hw]").
Qed.

(** A 64-bit word load at word `length ws0` of `ws0 ++ w :: ws` extracted from P. *)
Lemma pure_load_word (P : iProp Σ) ws0 w ws dq b reg p s f e ls l d args rest j classes q Φ :
  str_shape p b reg (ws0 ++ w :: ws) s ->
  (P ⊢ wwin dq b reg (wstart p - b) (ws0 ++ w :: ws) ∗ (wwin dq b reg (wstart p - b) (ws0 ++ w :: ws) -∗ P)) ->
  op_arg_classes (RawLoad LdL 0) L = Some classes -> map2_option (value_x ge e) classes args = Some [WPtr q] ->
  ptr_addr q = wstart p + 8 * Z.of_nat (length ws0) -> ptr_cap q = ptr_cap p ->
  (P ⊢ WP (ERun (mkFrame f (put d (WInt w) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) ->
  P ⊢ WP (ERun (mkFrame f e ls None (Exec l (Let d L (RawLoad LdL 0) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hs Hctx Hc Hx Hqa Hqc H. iIntros "HP". iDestruct (Hctx with "HP") as "([Hl Hw] & HK)".
  pose proof (ss_words _ _ _ _ _ Hs) as Hws. apply Forall_app in Hws as [_ Hws].
  apply Forall_cons_1 in Hws as [Hw0 _]. pose proof (str_shape_addr_bound _ _ _ _ _ Hs) as Hbnd.
  rewrite length_app in Hbnd. cbn [length] in Hbnd. unfold wstart in *.
  rewrite words_ps_app ptsq_app. iDestruct "Hw" as "[Hw0 Hw]".
  cbn [words_ps]. rewrite ptsq_app. iDestruct "Hw" as "[Hc Hw]".
  iApply (wp_raw_load_read_dq with "Hl Hc");
    [exact Hc | exact Hx | rewrite Hqc; exact (ss_cap _ _ _ _ _ Hs) | arith |].
  iNext. iIntros "Hl Hc". rewrite (Z.mod_small w (2 ^ 64) Hw0).
  iApply H. iApply ("HK" with "[Hl Hw0 Hc Hw]"). iFrame "Hl".
  rewrite words_ps_app ptsq_app. iFrame "Hw0". cbn [words_ps]. rewrite ptsq_app. iFrame.
Qed.

(** Check on a string window. *)
Ltac chk ctx_lem Hsh :=
  pose proof (str_shape_addr_bound _ _ _ _ _ Hsh);
  eapply pure_check; [exact Hsh | apply ctx_lem | reflexivity | reflexivity | reflexivity | lia
                     | unfold wstart in *; cbn [ptr_addr ptr_cap length] in *; lia
                     | rewrite ?length_app; unfold wstart in *; cbn [ptr_addr ptr_cap length] in *; rewrite ?Nat2Z.inj_succ; lia |].
(** Load a word from a string window. *)
Ltac ldw ctx_lem ws0 w ws Hsh :=
  eapply (pure_load_word _ ws0 w ws);
    [exact Hsh | apply ctx_lem | reflexivity | reflexivity | unfold wstart in *; cbn [ptr_addr ptr_cap length] in *; lia | reflexivity |].

(** The phi nodes of block l in [glibc_strcmp]. *)
Definition strcmp_phis (l : string) : list phi :=
  match find_block (TAtom l) (fn_blocks glibc_strcmp) with Some b => b_phis b | None => [] end.

(** ## Mismatch exits *)

(** Shared proof script for the three word-mismatch exits (`iw_1.iw_2.start`, `iw_2.iw_2.start`, `iw_2.L30`). *)
Ltac mismatch_steps x y Hx_rng Hy_rng j Hat Hlow Hres :=
  do 10 pst_gen; top_cmp_mask x y; pst; eapply pure_branch; [reflexivity|];
  rewrite (mask_nz (cmp_mask x y) (Z.of_nat j) (cmp_mask_range x y) ltac:(lia) Hat) Z.eqb_refl;
  cbn [edge_label]; pst; do 15 pst_gen; top_tail (cmp_mask x y);
  rewrite (tail_first (cmp_mask x y) (Z.of_nat j) (cmp_mask_range x y) (cmp_mask_01 x y) ltac:(lia) Hat Hlow);
  pst; pst; top_int (8 * Z.of_nat j + 7); pst; top_int (Z.of_nat j); pst; top_int (8 * Z.of_nat j);
  pst; pst; eapply (set_head_int _ _ _ _ (byte_of x (Z.of_nat j)));
  [ rewrite (Z.mod_small x (2 ^ 64) Hx_rng) (Z.mod_small (8 * Z.of_nat j) (2 ^ 32) ltac:(lia))
      (Z.mod_small (8 * Z.of_nat j) 64 ltac:(lia)); exact (shr_ext_ub x (Z.of_nat j) ltac:(lia)) |];
  pst; pst; eapply (set_head_int _ _ _ _ (byte_of y (Z.of_nat j)));
  [ rewrite (Z.mod_small y (2 ^ 64) Hy_rng) (Z.mod_small (8 * Z.of_nat j) (2 ^ 32) ltac:(lia))
      (Z.mod_small (8 * Z.of_nat j) 64 ltac:(lia)); exact (shr_ext_ub y (Z.of_nat j) ltac:(lia)) |];
  pose proof (byte_of_range x (Z.of_nat j)); pose proof (byte_of_range y (Z.of_nat j));
  pst; top_int ((byte_of x (Z.of_nat j) - byte_of y (Z.of_nat j)) mod 2 ^ 32); do 2 pst;
  eapply pure_ret; [reflexivity | reflexivity |]; rewrite !Z.mod_mod; [|lia|lia]; rewrite Hres; done.

(** Block `iw_2.L30`: resolve a word pair (x, y) where x <> y or s2 has fewer than 8 bytes. *)
Lemma l30_spec (P : iProp Σ) p1 b1 reg1 x ws1 s1 p2 b2 reg2 ws2 s2 y e from Φ :
  0 <= y < 2 ^ 64 -> str_shape p1 b1 reg1 (x :: ws1) s1 -> ptr_addr p1 mod 8 = 0 -> str_shape p2 b2 reg2 ws2 s2 ->
  (forall i : nat, (i <= length s2)%nat -> (i < 8)%nat -> (s2 ++ [0]) !! i = Some (byte_of y (Z.of_nat i))) ->
  (x <> y \/ (length s2 < 8)%nat \/ loop_mask x <> 0) ->
  phis_env ge (strcmp_phis "iw_2.L30") from e =
    Some (put (TAtom "iw_2.pr.3") (WInt (x mod 2 ^ 64)) (put (TAtom "iw_2.pr.6") (WInt (y mod 2 ^ 64)) e)) ->
  (P ⊢ Φ (Ret (WInt (strcmp_res s1 s2)))) ->
  (P ⊢ WP (ERun (mkFrame glibc_strcmp e [] None (Enter (TAtom "iw_2.L30") from)) : gexpr) {{ Φ }}).
Proof.
  intros Hy_rng Hs1 Ha1 Hs2 Hy Hdiff Hphi HK.
  pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs1))) as Hx_rng.
  destruct (word_mismatch_strcmp p1 b1 reg1 x ws1 s1 p2 b2 reg2 ws2 s2 y Hy_rng Hs1 Ha1 Hs2 Hy Hdiff)
    as (j & Hj8 & Hat & Hlow & Hres).
  eapply pure_enter; [reflexivity | exact Hphi |]. cbn [b_insts b_jump].
  rewrite (Z.mod_small x (2 ^ 64) Hx_rng) (Z.mod_small y (2 ^ 64) Hy_rng).
  mismatch_steps x y Hx_rng Hy_rng j Hat Hlow Hres.
Qed.

(** Block `iw_1.iw_2.start`: mismatch exit of the aligned word loop. *)
Lemma iw1_iw2_spec (P : iProp Σ) p1 b1 reg1 x ws1 s1 p2 b2 reg2 ws2 s2 y q1 q2 e Φ :
  0 <= y < 2 ^ 64 -> str_shape p1 b1 reg1 (x :: ws1) s1 -> ptr_addr p1 mod 8 = 0 -> str_shape p2 b2 reg2 ws2 s2 ->
  (forall i : nat, (i <= length s2)%nat -> (i < 8)%nat -> (s2 ++ [0]) !! i = Some (byte_of y (Z.of_nat i))) ->
  x <> y -> (P ⊢ Φ (Ret (WInt (strcmp_res s1 s2)))) ->
  (P ⊢ WP (ERun (mkFrame glibc_strcmp
             (put (TAtom "iw_1.v15") (WInt 0) (put (TAtom "iw_1.pr.1") (WPtr q1) (put (TAtom "iw_1.pr.2") (WPtr q2)
               (put (TAtom "iw_1.pr.3") (WInt x) (put (TAtom "iw_1.pr.4") (WInt y) e))))) [] None
             (Enter (TAtom "iw_1.iw_2.start") (Some (TAtom "iw_1.L10")))) : gexpr) {{ Φ }}).
Proof.
  intros Hy_rng Hs1 Ha1 Hs2 Hy Hne HK.
  pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs1))) as Hx_rng.
  destruct (word_mismatch_strcmp p1 b1 reg1 x ws1 s1 p2 b2 reg2 ws2 s2 y Hy_rng Hs1 Ha1 Hs2 Hy (or_introl Hne))
    as (j & Hj8 & Hat & Hlow & Hres).
  pst. mismatch_steps x y Hx_rng Hy_rng j Hat Hlow Hres.
Qed.

(** Block `iw_2.iw_2.start`: mismatch exit of the unaligned word loop. *)
Lemma iw2_iw2_spec (P : iProp Σ) p1 b1 reg1 x ws1 s1 p2 b2 reg2 ws2 s2 y v44 v47 v41 v40 q1 q2 u0 e Φ :
  0 <= y < 2 ^ 64 -> str_shape p1 b1 reg1 (x :: ws1) s1 -> ptr_addr p1 mod 8 = 0 -> str_shape p2 b2 reg2 ws2 s2 ->
  (forall i : nat, (i <= length s2)%nat -> (i < 8)%nat -> (s2 ++ [0]) !! i = Some (byte_of y (Z.of_nat i))) ->
  x <> y -> (P ⊢ Φ (Ret (WInt (strcmp_res s1 s2)))) ->
  (P ⊢ WP (ERun (mkFrame glibc_strcmp
             (put (TAtom "iw_2.v54") (WInt 1) (put (TAtom "iw_2.v48") (WInt y) (put (TAtom "iw_2.v47") (WInt v47)
               (put (TAtom "iw_2.v44") (WInt v44) (put (TAtom "iw_2.v41") (WInt v41) (put (TAtom "chk7") (WPtr q2)
                 (put (TAtom "iw_2.v40") (WPtr v40) (put (TAtom "iw_2.pr.1") (WPtr q1) (put (TAtom "iw_2.pr.2") (WPtr q2)
                   (put (TAtom "iw_2.pr.4") (WInt x) (put (TAtom "iw_2.pr.5") (WInt u0) e))))))))))) [] None
             (Enter (TAtom "iw_2.iw_2.start") (Some (TAtom "iw_2.L36")))) : gexpr) {{ Φ }}).
Proof.
  intros Hy_rng Hs1 Ha1 Hs2 Hy Hne HK.
  pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs1))) as Hx_rng.
  destruct (word_mismatch_strcmp p1 b1 reg1 x ws1 s1 p2 b2 reg2 ws2 s2 y Hy_rng Hs1 Ha1 Hs2 Hy (or_introl Hne))
    as (j & Hj8 & Hat & Hlow & Hres).
  pst. mismatch_steps x y Hx_rng Hy_rng j Hat Hlow Hres.
Qed.

(** ## Word loops *)

(** The aligned word loop `iw_1.L10`, when both pointers are 8-aligned. *)
Lemma aligned_loop_spec dq1 dq2 p1 b1 reg1 w1 ws1 s1 p2 b2 reg2 w2 ws2 s2 q1 q2 e from Φ :
  str_shape p1 b1 reg1 (w1 :: ws1) s1 -> ptr_addr p1 mod 8 = 0 ->
  str_shape p2 b2 reg2 (w2 :: ws2) s2 -> ptr_addr p2 mod 8 = 0 -> q1 = ptr_add p1 8 -> q2 = ptr_add p2 8 ->
  phis_env ge (strcmp_phis "iw_1.L10") from e =
    Some (put (TAtom "iw_1.pr.1") (WPtr q1) (put (TAtom "iw_1.pr.2") (WPtr q2)
           (put (TAtom "iw_1.pr.3") (WInt (w1 mod 2 ^ 64)) (put (TAtom "iw_1.pr.4") (WInt (w2 mod 2 ^ 64)) e)))) ->
  strcmp_ctx dq1 b1 reg1 p1 (w1 :: ws1) s1 dq2 b2 reg2 p2 (w2 :: ws2) s2 Φ ⊢
  WP (ERun (mkFrame glibc_strcmp e [] None (Enter (TAtom "iw_1.L10") from)) : gexpr) {{ Φ }}.
Proof.
  revert p1 w1 s1 p2 w2 ws2 s2 q1 q2 e from.
  induction ws1 as [|w1' ws1 IH]; intros p1 w1 s1 p2 w2 ws2 s2 q1 q2 e from Hs1 Ha1 Hs2 Ha2 -> -> Hphi;
    (pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs1))) as Hw1;
     pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs2))) as Hw2;
     eapply pure_enter; [reflexivity | exact Hphi |]; cbn [b_insts b_jump];
     rewrite (Z.mod_small w1 (2 ^ 64) Hw1) (Z.mod_small w2 (2 ^ 64) Hw2);
     pst; eapply pure_branch; [reflexivity|];
     rewrite (Z.mod_small w1 (2 ^ 64) Hw1) (Z.mod_small w2 (2 ^ 64) Hw2);
     destruct (Z.eqb_spec w1 w2) as [<- | Hne];
     [ close_if; pst; do 4 pst; top_int (loop_mask w1); pst; eapply pure_branch; [reflexivity|];
       rewrite (Z.mod_small (loop_mask w1) (2 ^ 64) (loop_mask_range w1)) Zmod_0_l;
       destruct (Z.eqb_spec (loop_mask w1) 0) as [Hm0 | Hmnz];
       [ close_if;
         destruct (word_eq_advance p1 b1 reg1 w1 _ s1 p2 b2 reg2 w1 ws2 s2 Hs1 Ha1 Hs2 Hm0
                     (fun k Hk => ltac:(rewrite Ha2; exact (wbytes_head w1 ws2 k Hk))))
           as (Hj1 & Hj2 & Hres & Hsh1 & Ho1 & Hsh2 & Ho2 & Ha1' & Ha2')
       | close_if; pst; eapply pure_ret; [reflexivity | reflexivity |];
         change ((0 mod 2 ^ 32) mod 2 ^ 32) with 0;
         rewrite -(word_eq_zero_strcmp p1 b1 reg1 w1 _ s1 p2 b2 reg2 (w1 :: ws2) s2 Hs1 Ha1 Hs2
                     (fun i Hi H8 => str_shape_aligned_byte p2 b2 reg2 w1 ws2 s2 i Hs2 Ha2 Hi H8) Hmnz);
         apply strcmp_ctx_done ]
     | close_if;
       eapply (iw1_iw2_spec _ p1 b1 reg1 w1 _ s1 p2 b2 reg2 (w2 :: ws2) s2 w2);
         [exact Hw2 | exact Hs1 | exact Ha1 | exact Hs2
         | intros i Hi H8; exact (str_shape_aligned_byte p2 b2 reg2 w2 ws2 s2 i Hs2 Ha2 Hi H8)
         | exact Hne | apply strcmp_ctx_done] ]).
  - exfalso. exact (str_shape_nonempty _ _ _ _ _ Hsh1 eq_refl).
  - destruct ws2 as [|w2' ws2]; [exfalso; exact (str_shape_nonempty _ _ _ _ _ Hsh2 eq_refl)|].
    pst. eapply (pure_advance 8 1 1); [exact Hj1 | exact Hj2 | exact Ho1 | exact Ho2 | exact Hres |].
    cbn [drop]. rewrite Ha2 in Ha2'.
    pose proof (str_shape_addr_bound _ _ _ _ _ Hsh1). pose proof (str_shape_addr_bound _ _ _ _ _ Hsh2).
    pst. top_ptr (ptr_addr (ptr_add p1 8) + 8). chk ctx_wwin_1 Hsh1. ldw ctx_wwin_1 ([] : list Z) w1' ws1 Hsh1.
    pst. top_ptr (ptr_addr (ptr_add p2 8) + 8). chk ctx_wwin_2 Hsh2. ldw ctx_wwin_2 ([] : list Z) w2' ws2 Hsh2.
    pst. eapply (IH (ptr_add p1 8) w1' (drop 8 s1) (ptr_add p2 8) w2' ws2 (drop 8 s2));
      [exact Hsh1 | exact Ha1' | exact Hsh2 | exact Ha2' | reflexivity | reflexivity | reflexivity].
Qed.

(** The unaligned word loop `iw_2.L36`, when p1 is 8-aligned and p2 is
    at offset k2 in 1..7 of its word, with u0's high 8 - k2 bytes nonzero. *)
Lemma unaligned_loop_spec dq1 dq2 p1 b1 reg1 w1 ws1 s1 p2 b2 reg2 u0 u1 ws2 s2 q1 q2 e from Φ :
  str_shape p1 b1 reg1 (w1 :: ws1) s1 -> ptr_addr p1 mod 8 = 0 ->
  str_shape p2 b2 reg2 (u0 :: u1 :: ws2) s2 -> 1 <= ptr_addr p2 mod 8 < 8 ->
  (forall i, 0 <= i < 8 - ptr_addr p2 mod 8 -> byte_of u0 (i + ptr_addr p2 mod 8) <> 0) ->
  q1 = ptr_add p1 8 -> q2 = mkPtr (wstart p2 + 8) (ptr_cap p2) ->
  lookup (TAtom "iw_2.v14") e = Some (WInt (8 * (ptr_addr p2 mod 8))) ->
  lookup (TAtom "iw_2.v18") e = Some (WInt (64 - 8 * (ptr_addr p2 mod 8))) ->
  phis_env ge (strcmp_phis "iw_2.L36") from e =
    Some (put (TAtom "iw_2.pr.1") (WPtr q1) (put (TAtom "iw_2.pr.2") (WPtr q2)
           (put (TAtom "iw_2.pr.4") (WInt (w1 mod 2 ^ 64)) (put (TAtom "iw_2.pr.5") (WInt (u0 mod 2 ^ 64)) e)))) ->
  strcmp_ctx dq1 b1 reg1 p1 (w1 :: ws1) s1 dq2 b2 reg2 p2 (u0 :: u1 :: ws2) s2 Φ ⊢
  WP (ERun (mkFrame glibc_strcmp e [] None (Enter (TAtom "iw_2.L36") from)) : gexpr) {{ Φ }}.
Proof.
  revert p1 w1 s1 p2 u0 u1 ws2 s2 q1 q2 e from.
  induction ws1 as [|w1' ws1 IH];
    intros p1 w1 s1 p2 u0 u1 ws2 s2 q1 q2 e from Hs1 Ha1 Hs2 Hk2 Hnz0 -> -> Hv14 Hv18 Hphi;
    (pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs1))) as Hw1;
     pose proof (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs2)) as [Hu0 Hws2];
     pose proof (proj1 (Forall_cons_1 _ _ _ Hws2)) as Hu1;
     pose proof (str_shape_addr_bound _ _ _ _ _ Hs2);
     eapply pure_enter; [reflexivity | exact Hphi |]; cbn [b_insts b_jump];
     rewrite (Z.mod_small w1 (2 ^ 64) Hw1) (Z.mod_small u0 (2 ^ 64) Hu0);
     pst; top_ptr (wstart p2 + 16); chk ctx_wwin_2 Hs2; ldw ctx_wwin_2 [u0] u1 ws2 Hs2;
     pst_look Hv14; pst_look Hv18; pst;
     eapply (set_head_int _ _ _ _ (merge_words u0 u1 (ptr_addr p2 mod 8)));
       [exact (merge_words_ir u0 u1 (ptr_addr p2 mod 8) Hu0 Hu1 Hk2) |];
     pst; eapply pure_branch; [reflexivity|];
     pose proof (merge_words_range u0 u1 (ptr_addr p2 mod 8) Hu0 Hu1 Hk2) as Hmw_rng;
     rewrite (Z.mod_small w1 (2 ^ 64) Hw1) (Z.mod_small (merge_words u0 u1 _) (2 ^ 64) Hmw_rng);
     destruct (Z.eqb_spec w1 (merge_words u0 u1 (ptr_addr p2 mod 8))) as [Heq | Hne];
     [ close_if; pst; do 4 pst; top_int (loop_mask u1); pst; eapply pure_branch; [reflexivity|];
       rewrite (Z.mod_small (loop_mask u1) (2 ^ 64) (loop_mask_range u1)) Zmod_0_l;
       destruct (Z.eqb_spec (loop_mask u1) 0) as [Hm1_0 | Hm1_nz];
       [ close_if;
         assert (Hm0 : loop_mask w1 = 0) by
           (rewrite Heq; exact (merge_words_mask_0 u0 u1 (ptr_addr p2 mod 8) Hu0 Hu1 Hk2 Hnz0 Hm1_0));
         destruct (word_eq_advance p1 b1 reg1 w1 _ s1 p2 b2 reg2 u0 (u1 :: ws2) s2 Hs1 Ha1 Hs2 Hm0
                     (fun k Hk => ltac:(rewrite Heq (wbytes_merge u0 u1 ws2 (Z.to_nat (ptr_addr p2 mod 8)) k Hu0 Hu1 ltac:(lia) Hk)
                                          Z2Nat.id; [reflexivity|lia])))
           as (Hj1 & Hj2 & Hres & Hsh1 & Ho1 & Hsh2 & Ho2 & Ha1' & Hk2')
       | close_if; pst; do 4 pst; top_int (loop_mask w1); pst; eapply pure_branch; [reflexivity|];
         rewrite (Z.mod_small (loop_mask w1) (2 ^ 64) (loop_mask_range w1)) Zmod_0_l;
         destruct (Z.eqb_spec (loop_mask w1) 0) as [Hm0_0 | Hm0_nz];
         [ close_if;
           destruct (word_eq_advance p1 b1 reg1 w1 _ s1 p2 b2 reg2 u0 (u1 :: ws2) s2 Hs1 Ha1 Hs2 Hm0_0
                       (fun k Hk => ltac:(rewrite Heq (wbytes_merge u0 u1 ws2 (Z.to_nat (ptr_addr p2 mod 8)) k Hu0 Hu1 ltac:(lia) Hk)
                                            Z2Nat.id; [reflexivity|lia])))
             as (Hj1 & Hj2 & Hres & Hsh1 & Ho1 & Hsh2 & Ho2 & Ha1' & Hk2')
         | close_if; pst; eapply pure_ret; [reflexivity | reflexivity |];
           change ((0 mod 2 ^ 32) mod 2 ^ 32) with 0;
           rewrite -(word_eq_zero_strcmp p1 b1 reg1 w1 _ s1 p2 b2 reg2 (u0 :: u1 :: ws2) s2 Hs1 Ha1 Hs2
                       (fun i Hi H8 => ltac:(rewrite Heq; exact (str_shape_merge_byte p2 b2 reg2 u0 u1 ws2 s2 i Hs2 Hk2 Hi H8)))
                       Hm0_nz);
           apply strcmp_ctx_done ] ]
     | close_if;
       eapply (iw2_iw2_spec _ p1 b1 reg1 w1 _ s1 p2 b2 reg2 (u0 :: u1 :: ws2) s2 (merge_words u0 u1 _));
         [exact Hmw_rng | exact Hs1 | exact Ha1 | exact Hs2
         | intros i Hi H8; exact (str_shape_merge_byte p2 b2 reg2 u0 u1 ws2 s2 i Hs2 Hk2 Hi H8)
         | exact Hne | apply strcmp_ctx_done] ]).
  - exfalso. exact (str_shape_nonempty _ _ _ _ _ Hsh1 eq_refl).
  - exfalso. exact (str_shape_nonempty _ _ _ _ _ Hsh1 eq_refl).
  - assert (Hnz1 : forall i, 0 <= i < 8 - ptr_addr (ptr_add p2 8) mod 8 -> byte_of u1 (i + ptr_addr (ptr_add p2 8) mod 8) <> 0) by
      (intros i Hi; rewrite Hk2' in Hi |- *; apply (proj1 (loop_mask_eq_0 u1) Hm1_0); lia).
    destruct ws2 as [|u2 ws2]; [exfalso; exact (unaligned_has_next_word _ _ _ _ _ _ Hsh2 Hnz1 eq_refl)|].
    pst. eapply (pure_advance 8 1 1); [exact Hj1 | exact Hj2 | exact Ho1 | exact Ho2 | exact Hres |].
    cbn [drop]. pose proof (str_shape_addr_bound _ _ _ _ _ Hsh1).
    pst. top_ptr (ptr_addr (ptr_add p1 8) + 8). chk ctx_wwin_1 Hsh1. ldw ctx_wwin_1 ([] : list Z) w1' ws1 Hsh1.
    pst. eapply (IH (ptr_add p1 8) w1' (drop 8 s1) (ptr_add p2 8) u1 u2 ws2 (drop 8 s2)
                  (ptr_add (ptr_add p1 8) 8) (mkPtr (wstart p2 + 16) (ptr_cap p2)));
      [exact Hsh1 | exact Ha1' | exact Hsh2 | rewrite Hk2'; exact Hk2 | exact Hnz1 | reflexivity
      | cbn; f_equal; lia | rewrite Hk2'; look Hv14 | rewrite Hk2'; look Hv18 | reflexivity].
  - pst. eapply (pure_advance 8 1 1); [exact Hj1 | exact Hj2 | exact Ho1 | exact Ho2 | exact Hres |].
    cbn [drop]. chk ctx_wwin_1 Hsh1. ldw ctx_wwin_1 ([] : list Z) w1' ws1 Hsh1.
    pst_look Hv14. pst_look Hv18. do 2 pst.
    destruct (tail_shift_ir u1 (ptr_addr p2 mod 8) Hu1 Hk2) as [Etsh Htsh_rng].
    eapply (set_head_int _ _ _ _ (u1 / 2 ^ (8 * (ptr_addr p2 mod 8)))); [exact Etsh |].
    pst. rewrite Heq in Hm0_0.
    destruct (unaligned_tail_zero_str p2 b2 reg2 u0 u1 ws2 s2 Hu0 Hsh2 Hk2 Hm0_0 Hm1_nz) as [Hlt8 Hby].
    eapply (l30_spec _ (ptr_add p1 8) b1 reg1 w1' ws1 (drop 8 s1) (ptr_add p2 8) b2 reg2 (u1 :: ws2) (drop 8 s2)
              (u1 / 2 ^ (8 * (ptr_addr p2 mod 8))));
      [exact Htsh_rng | exact Hsh1 | exact Ha1' | exact Hsh2 | exact Hby | right; left; exact Hlt8
      | reflexivity | apply strcmp_ctx_done].
Qed.

(** ## Entry, byte loop, and top-level triples *)

(** Block `L13`: p1 is 8-aligned; dispatch to the aligned or unaligned word loop. *)
Lemma l13_spec dq1 dq2 p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 v17 v16 e Φ :
  str_shape p1 b1 reg1 ws1 s1 -> ptr_addr p1 mod 8 = 0 -> str_shape p2 b2 reg2 ws2 s2 ->
  strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ ⊢
  WP (ERun (mkFrame glibc_strcmp
             (put (TAtom "v17") (WInt v17) (put (TAtom "v16") (WInt v16)
               (put (TAtom "pr.1") (WPtr p1) (put (TAtom "pr.2") (WPtr p2) e)))) [] None
             (Enter (TAtom "L13") (Some (TAtom "L10")))) : gexpr) {{ Φ }}.
Proof.
  intros Hs1 Ha1 Hs2.
  destruct ws1 as [|w1 ws1]; [exfalso; exact (str_shape_nonempty _ _ _ _ _ Hs1 eq_refl)|].
  destruct ws2 as [|u0 ws2]; [exfalso; exact (str_shape_nonempty _ _ _ _ _ Hs2 eq_refl)|].
  pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs1))) as Hw1.
  pose proof (proj1 (Forall_cons_1 _ _ _ (ss_words _ _ _ _ _ Hs2))) as Hu0.
  pose proof (str_shape_addr_bound _ _ _ _ _ Hs1). pose proof (str_shape_addr_bound _ _ _ _ _ Hs2).
  pose proof (Z.mod_pos_bound (ptr_addr p2) 8 ltac:(lia)) as Hk2.
  pst. pst. top_ptr (ptr_addr p1 + 8). chk ctx_wwin_1 Hs1. ldw ctx_wwin_1 ([] : list Z) w1 ws1 Hs1.
  pst. pst. eapply (set_head_int _ _ _ _ (ptr_addr p2 mod 8)); [apply mod8_land; lia |].
  pst. eapply pure_branch; [reflexivity|].
  rewrite (Z.mod_small (ptr_addr p2 mod 8) (2 ^ 64) ltac:(lia)) Zmod_0_l.
  destruct (Z.eqb_spec (ptr_addr p2 mod 8) 0) as [Ha2 | Hk2_nz].
  - close_if. pst. pst. top_ptr (ptr_addr p2 + 8). chk ctx_wwin_2 Hs2. ldw ctx_wwin_2 ([] : list Z) u0 ws2 Hs2. pst.
    eapply (aligned_loop_spec dq1 dq2 p1 b1 reg1 w1 ws1 s1 p2 b2 reg2 u0 ws2 s2 (ptr_add p1 8) (ptr_add p2 8));
      [exact Hs1 | exact Ha1 | exact Hs2 | exact Ha2 | reflexivity | reflexivity | reflexivity].
  - assert (Hk2_rng : 1 <= ptr_addr p2 mod 8 < 8) by lia.
    assert (Hall : 0 <= all64 < 2 ^ 64) by (vm_compute; split; congruence).
    close_if. pst. pst. top_ptr (wstart p2). pst. top_ptr (wstart p2 + 8).
    chk ctx_wwin_2 Hs2. ldw ctx_wwin_2 ([] : list Z) u0 ws2 Hs2.
    pst. top_int (8 * (ptr_addr p2 mod 8)). pst. top_int (64 - 8 * (ptr_addr p2 mod 8)).
    do 3 pst. eapply (set_head_int _ _ _ _ (merge_words u0 all64 (ptr_addr p2 mod 8)));
      [exact (merge_words_ir u0 all64 (ptr_addr p2 mod 8) Hu0 Hall Hk2_rng) |].
    do 4 pst. top_int (loop_mask (merge_words u0 all64 (ptr_addr p2 mod 8))).
    pst. eapply pure_branch; [reflexivity|].
    rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l.
    destruct (Z.eqb_spec (loop_mask (merge_words u0 all64 (ptr_addr p2 mod 8))) 0) as [Hhp0 | Hhpnz].
    + close_if.
      assert (Hnz0 : forall i, 0 <= i < 8 - ptr_addr p2 mod 8 -> byte_of u0 (i + ptr_addr p2 mod 8) <> 0).
      { intros i Hi. pose proof (proj1 (loop_mask_eq_0 _) Hhp0 i ltac:(lia)) as Hnz.
        rewrite (byte_of_merge_words u0 all64 (ptr_addr p2 mod 8) i Hu0 Hall Hk2_rng ltac:(lia)) in Hnz.
        replace (i <? 8 - ptr_addr p2 mod 8) with true in Hnz by (symmetry; apply Z.ltb_lt; lia). exact Hnz. }
      destruct ws2 as [|u1 ws2]; [exfalso; exact (unaligned_has_next_word _ _ _ _ _ _ Hs2 Hnz0 eq_refl)|].
      eapply (unaligned_loop_spec dq1 dq2 p1 b1 reg1 w1 ws1 s1 p2 b2 reg2 u0 u1 ws2 s2
                (ptr_add p1 8) (mkPtr (wstart p2 + 8) (ptr_cap p2)));
        [exact Hs1 | exact Ha1 | exact Hs2 | exact Hk2_rng | exact Hnz0 | reflexivity | reflexivity
        | reflexivity | reflexivity | reflexivity].
    + close_if. destruct (head_pad_zero_str p2 b2 reg2 u0 ws2 s2 Hs2 Hk2_rng Hhpnz) as [Hlt8 Hby].
      eapply (l30_spec _ p1 b1 reg1 w1 ws1 s1 p2 b2 reg2 (u0 :: ws2) s2 (merge_words u0 all64 (ptr_addr p2 mod 8)));
        [exact (merge_words_range u0 all64 _ Hu0 Hall Hk2_rng) | exact Hs1 | exact Ha1 | exact Hs2 | exact Hby
        | right; left; exact Hlt8 | reflexivity | apply strcmp_ctx_done].
Qed.

(** The byte-alignment loop `L10`, stepping `rem` bytes until `p1` is 8-aligned or a NUL/mismatch byte is reached. *)
Lemma byte_loop_spec (rem : nat) dq1 dq2 p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 i v8 e from Φ :
  str_shape p1 b1 reg1 ws1 s1 -> str_shape p2 b2 reg2 ws2 s2 ->
  0 <= i -> v8 = i + Z.of_nat rem -> v8 < 8 -> (ptr_addr p1 + Z.of_nat rem) mod 8 = 0 ->
  lookup (TAtom "v8") e = Some (WInt v8) ->
  phis_env ge (strcmp_phis "L10") from e =
    Some (put (TAtom "pr.1") (WPtr p1) (put (TAtom "pr.2") (WPtr p2) (put (TAtom "pr.3") (WInt (i mod 2 ^ 32)) e))) ->
  strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ ⊢
  WP (ERun (mkFrame glibc_strcmp e [] None (Enter (TAtom "L10") from)) : gexpr) {{ Φ }}.
Proof.
  revert p1 ws1 s1 p2 ws2 s2 i e from.
  induction rem as [|rem IH]; intros p1 ws1 s1 p2 ws2 s2 i e from Hs1 Hs2 Hi Hv8 Hv8_lt Hal Hlk8 Hphi;
    (eapply pure_enter; [reflexivity | exact Hphi |]; cbn [b_insts b_jump]; pst;
     eapply (set_head_int _ _ _ _ i);
       [unfold extension, sign_extension; rewrite !(Z.mod_small i (2 ^ 32) ltac:(lia));
        replace (2 ^ 31 <=? i) with false by (symmetry; apply Z.leb_gt; lia); apply Z.mod_small; lia |];
     pst_look Hlk8; eapply pure_branch; [reflexivity|];
     rewrite (Z.mod_small i (2 ^ 64) ltac:(lia)) (Z.mod_small v8 (2 ^ 64) ltac:(lia))).
  - replace (i <? v8) with false by (symmetry; apply Z.ltb_ge; lia). close_if. rewrite Z.add_0_r in Hal.
    exact (l13_spec dq1 dq2 p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 _ _ _ Φ Hs1 Hal Hs2).
  - replace (i <? v8) with true by (symmetry; apply Z.ltb_lt; lia). close_if. pst.
    pose proof (str_shape_addr_bound _ _ _ _ _ Hs1). pose proof (str_shape_addr_bound _ _ _ _ _ Hs2).
    destruct (str_shape_hd_range p1 b1 reg1 ws1 s1 Hs1) as [Hc1 Ehd1].
    destruct (str_shape_hd_range p2 b2 reg2 ws2 s2 Hs2) as [Hc2 Ehd2].
    pst. top_ptr (ptr_addr p1 + 1). chk ctx_wwin_1 Hs1.
    eapply pure_load_byte; [exact Hs1 | apply ctx_wwin_1 | reflexivity | reflexivity | reflexivity |].
    pst. eapply (set_head_int _ _ _ _ (hd 0 s1)); [exact (ext_ub_sb (hd 0 s1) Hc1) |].
    pst. top_ptr (ptr_addr p2 + 1). chk ctx_wwin_2 Hs2.
    eapply pure_load_byte; [exact Hs2 | apply ctx_wwin_2 | reflexivity | reflexivity | reflexivity |].
    pst. eapply (set_head_int _ _ _ _ (hd 0 s2)); [exact (ext_ub_sb (hd 0 s2) Hc2) |].
    pst. top_int ((hd 0 s1 - hd 0 s2) mod 2 ^ 32). pst. eapply pure_branch; [reflexivity|].
    rewrite (Z.mod_small (hd 0 s1) (2 ^ 32) ltac:(lia)) Zmod_0_l.
    destruct (Z.eqb_spec (hd 0 s1) 0) as [Hc1_0 | Hc1_nz].
    + close_if. pst. eapply pure_branch; [reflexivity|]. close_if. pst.
      eapply pure_ret; [reflexivity | reflexivity |]. rewrite Z.mod_mod; [|lia].
      rewrite -(strcmp_res_at s1 s2 0 (hd 0 s1) (hd 0 s2)
                  (ss_chars _ _ _ _ _ Hs1) (ss_chars _ _ _ _ _ Hs2) ltac:(intros; lia) Ehd1 Ehd2 (or_introl Hc1_0)).
      apply strcmp_ctx_done.
    + close_if. do 4 pst. eapply pure_branch; [reflexivity|].
      rewrite !Z.mod_mod; [|lia|lia]. rewrite Zmod_0_l.
      destruct (Z.eqb_spec (hd 0 s1) (hd 0 s2)) as [Heq_c | Hne_c].
      * replace ((hd 0 s1 - hd 0 s2) mod 2 ^ 32 =? 0) with true
          by (symmetry; apply Z.eqb_eq; rewrite Heq_c Z.sub_diag; reflexivity).
        close_if. pst. pst. top_int (i + 1). pst.
        destruct (byte_eq_advance p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 Hs1 Hs2 Hc1_nz Heq_c)
          as (Hj1 & Hj2 & Hres & Hsh1 & Ho1 & Hsh2 & Ho2).
        eapply (pure_advance 1 _ _); [exact Hj1 | exact Hj2 | exact Ho1 | exact Ho2 | exact Hres |].
        eapply (IH (ptr_add p1 1) _ (drop 1 s1) (ptr_add p2 1) _ (drop 1 s2) (i + 1));
          [exact Hsh1 | exact Hsh2 | lia | lia | lia
          | cbn [ptr_addr ptr_add]; replace (ptr_addr p1 + 1 + Z.of_nat rem) with (ptr_addr p1 + Z.of_nat (S rem)) by lia; exact Hal
          | look Hlk8 | reflexivity].
      * assert (Hsub_nz : (hd 0 s1 - hd 0 s2) mod 2 ^ 32 <> 0) by
          (intros Hz; apply Hne_c; exact (proj1 (sub32_eq_0 _ _ Hc1 Hc2) Hz)).
        replace ((hd 0 s1 - hd 0 s2) mod 2 ^ 32 =? 0) with false by (symmetry; apply Z.eqb_neq, Hsub_nz).
        close_if. pst. eapply pure_ret; [reflexivity | reflexivity |]. rewrite Z.mod_mod; [|lia].
        rewrite -(strcmp_res_at s1 s2 0 (hd 0 s1) (hd 0 s2)
                    (ss_chars _ _ _ _ _ Hs1) (ss_chars _ _ _ _ _ Hs2) ltac:(intros; lia) Ehd1 Ehd2 (or_intror Hne_c)).
        apply strcmp_ctx_done.
Qed.

(** Step from `Enter (TAtom "start") None` to [byte_loop_spec]. *)
Ltac start_steps dq1 dq2 p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 Hs1 Hs2 :=
  pose proof (str_shape_addr_bound _ _ _ _ _ Hs1); do 4 pst;
  eapply (set_head_int _ _ _ _ ((- ptr_addr p1) mod 8)); [apply align_rem |]; pst;
  pose proof (Z.mod_pos_bound (- ptr_addr p1) 8 ltac:(lia));
  eapply (byte_loop_spec (Z.to_nat ((- ptr_addr p1) mod 8)) dq1 dq2 p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 0
            ((- ptr_addr p1) mod 8));
    [exact Hs1 | exact Hs2 | lia | rewrite Z2Nat.id; lia | lia
    | rewrite Z2Nat.id; [rewrite Zplus_mod_idemp_r Z.add_opp_diag_r; reflexivity | lia]
    | reflexivity | reflexivity].

(** glibc's `__GI_strcmp` on two [word_string]s at any shares dq1 and
    dq2, with no aliasing restriction between p1 and p2: it returns
    [strcmp_res] s1 s2 and hands both strings back. *)
Lemma wp_glibc_strcmp_ws dq1 dq2 p1 p2 s1 s2 Φ :
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ Φ (Ret (WInt (strcmp_res s1 s2)))) -∗
  WP (ERun (mkFrame glibc_strcmp [(TAtom "v0", WPtr p1); (TAtom "v2", WPtr p2)] [] None
             (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  iIntros "(%b1 & %reg1 & %ws1 & %Hs1 & Hw1) (%b2 & %reg2 & %ws2 & %Hs2 & Hw2) HK".
  iAssert (strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2 Φ) with "[Hw1 Hw2 HK]" as "Hctx".
  { iFrame "Hw1 Hw2". iIntros "Hw1 Hw2". iApply ("HK" with "[Hw1] [Hw2]"); iExists _, _, _; by iFrame. }
  iStopProof. start_steps dq1 dq2 p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 Hs1 Hs2.
Qed.

(** A call of glibc's strcmp, in any module whose function at the
    called name g is [glibc_strcmp], on two [word_string]s at any
    shares dq1 and dq2: the caller resumes with [strcmp_res] s1 s2 and
    both strings back. *)
Lemma wp_call_glibc_strcmp f e ls l r g args rest j dq1 dq2 p1 p2 s1 s2 cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p1; WPtr p2] ->
  find_fn ge g = Some (Defined glibc_strcmp) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WInt (strcmp_res s1 s2))) = Some cf' ->
  word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗
  ▷ (word_string dq1 p1 s1 -∗ word_string dq2 p2 s2 -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hg Hr. iIntros "(%b1 & %reg1 & %ws1 & %Hs1 & Hw1) (%b2 & %reg2 & %ws2 & %Hs2 & Hw2) HK".
  iApply (wp_call_bind with "[Hw1 Hw2 HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iAssert (strcmp_ctx dq1 b1 reg1 p1 ws1 s1 dq2 b2 reg2 p2 ws2 s2
             (fun o => ∃ cf', ⌜resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) o = Some cf'⌝ ∗
                              ▷ WP (ERun cf' : gexpr) {{ Φ }}))%I with "[Hw1 Hw2 HK]" as "Hctx".
  { iFrame "Hw1 Hw2". iIntros "Hw1 Hw2". iExists cf'. iSplit; [done|]. iNext.
    iApply ("HK" with "[Hw1] [Hw2]"); iExists _, _, _; by iFrame. }
  iStopProof. start_steps dq1 dq2 p1 b1 reg1 ws1 s1 p2 b2 reg2 ws2 s2 Hs1 Hs2.
Qed.

End rules.
End StrcmpLogicOn.
