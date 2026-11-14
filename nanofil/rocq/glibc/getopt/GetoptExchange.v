(** Glibc's option scanner moves skipped nonoptions behind the options
    that follow them. Its exchange routine swaps two adjacent blocks of
    argument pointers by repeatedly swapping equal-length runs. This file
    proves the captured loops of that routine safe on the caller's
    argument vector: every swap reads and writes two distinct cells inside
    the vector, and the vector stays a permutation of the original. *)

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
  GetoptInitialize GetoptEntry GetoptArgv.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptInitialize GetoptState LibioLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Local Transparent glibc_getopt_internal_r.

(** Sign extension keeps a nonnegative signed 32-bit value. *)
Lemma sx_nonneg x : 0 <= x < 2 ^ 31 -> sign_extension (2 ^ 32) (2 ^ 31) x = x.
Proof. intros H. unfold sign_extension. rewrite Z.mod_small; [|lia]. rewrite (proj2 (Z.leb_gt _ _)); lia. Qed.

(** Glibc's scanner inlines the exchange twice, and the captured blocks
    carry the prefixes iw_2 and iw_3. This definition looks up a block
    of the captured scanner by its label. *)
Definition x_blk (l : string) : block := Eval vm_compute in
  match find_block (TAtom l) (fn_blocks glibc_getopt_internal_r) with
  | Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** The lower swap loop of the first exchange starts here. *)
Definition x2_blk44 : block := Eval vm_compute in x_blk "iw_2.L44".
(** The upper swap loop of the first exchange starts here. *)
Definition x2_blk100 : block := Eval vm_compute in x_blk "iw_2.L100".
(** The lower swap loop of the second exchange starts here. *)
Definition x3_blk44 : block := Eval vm_compute in x_blk "iw_3.L44".
(** The upper swap loop of the second exchange starts here. *)
Definition x3_blk100 : block := Eval vm_compute in x_blk "iw_3.L100".

(** The outer loop of an exchange with prefix x assigns these names. *)
Definition x_loop (x : string) : list name :=
  List.map (fun s => TAtom (x ++ s)%string) [".pr.1"; ".pr.3"; ".v21"; ".v26"; ".v28"; ".v34"; ".v37"; ".v38"]%string.

(** A caller must know which names a swap loop overwrites. This list
    holds them for the exchange with prefix x, with its four checks named
    by cs. *)
Definition x_inner (x : string) (cs : list string) : list name :=
  List.map (fun s => TAtom (x ++ s)%string)
    [".pr.5"; ".v50"; ".v54"; ".v55"; ".v56"; ".v57"; ".v58"; ".v71"; ".v73"; ".v74"; ".v75"; ".v76";
     ".v77"; ".v91"; ".v94"; ".pr.6"; ".v106"; ".v110"; ".v111"; ".v112"; ".v113"; ".v114"; ".v125";
     ".v126"; ".v127"; ".v128"; ".v129"; ".v139"; ".v142"]%string ++ List.map TAtom cs.
(** The swap loops of the first exchange assign these names. *)
Definition x2_inner : list name := Eval vm_compute in
  x_inner "iw_2" ["chk39"; "chk40"; "chk41"; "chk42"; "chk43"; "chk44"; "chk45"; "chk46"]%string.
(** All loops of the first exchange assign these names. *)
Definition x2_outer : list name := x_loop "iw_2" ++ x2_inner.
(** The swap loops of the second exchange assign these names. *)
Definition x3_inner : list name := Eval vm_compute in
  x_inner "iw_3" ["chk80"; "chk81"; "chk82"; "chk83"; "chk84"; "chk85"; "chk86"; "chk87"]%string.
(** All loops of the second exchange assign these names. *)
Definition x3_outer : list name := x_loop "iw_3" ++ x3_inner.
(** The outer loop of the first exchange starts here. *)
Definition x2_blk16 : block := Eval vm_compute in x_blk "iw_2.L16".
(** The outer loop of the second exchange starts here. *)
Definition x3_blk16 : block := Eval vm_compute in x_blk "iw_3.L16".


(** Initialization supplies the private-field and byte modules. *)
(** This module describes the argument vector cells. *)
Import GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section helpers.
Context `{!gen_heapGS piece pval Σ}.

(** Names that avoid two lists avoid their concatenation. *)
Lemma avoids_app ks W1 W2 : avoids ks (W1 ++ W2) = true -> avoids ks W1 = true /\ avoids ks W2 = true.
Proof.
  unfold avoids. rewrite !forallb_forall. intros H. split; intros k Hk; specialize (H k Hk);
    rewrite forallb_app in H; apply andb_prop in H; tauto.
Qed.

(** Names avoid a list exactly when each avoids it. *)
Lemma avoids_cons k ks W : avoids (k :: ks) W = forallb (fun w => negb (name_eqb k w)) W && avoids ks W.
Proof. reflexivity. Qed.

(** A shared string pointer carries the lifetime its loads need. *)
Lemma argv_str_cap q s : word_string DfracDiscarded q s ⊢
  ∃ reg, live_capq DfracDiscarded (ptr_cap q) reg ∗ ⌜0 <= ptr_addr q < 2 ^ 64⌝.
Proof.
  iIntros "#H". iDestruct (ws_shape with "H") as %(_ & Hq0 & Hqe).
  iDestruct (ws_byte q s 0 with "H") as (b reg) "(%Hb & Hl & _)"; [lia|].
  destruct Hb as (Hc & _). iExists reg. iSplit; [|iPureIntro; lia].
  by destruct Hc as [-> | ->].
Qed.

(** Every argument the vector holds is a shared string. *)
Definition argv_strs (ps : list ptr) : iProp Σ := [∗ list] q ∈ ps, ∃ s, word_string DfracDiscarded q s.

(** A vector entry in range has a shared string with a usable lifetime. *)
Lemma argv_strs_cap ps j : (j < List.length ps)%nat -> argv_strs ps ⊢
  ∃ reg, live_capq DfracDiscarded (ptr_cap (nth j ps null)) reg ∗ ⌜0 <= ptr_addr (nth j ps null) < 2 ^ 64⌝.
Proof.
  intros Hj. iIntros "H". destruct (lookup_lt_is_Some_2 ps j Hj) as [x Hx].
  rewrite (nth_lookup_Some _ _ _ _ Hx).
  iDestruct (big_sepL_lookup with "H") as (s) "Hs"; [exact Hx|]. by iApply argv_str_cap.
Qed.

End helpers.

(** This tactic unfolds a precomputed block that the goal executes. *)
Ltac unfold_blk := repeat match goal with |- context [b_insts ?B] => progress unfold B end.

(** Signed comparisons of nonnegative 32-bit values read the values. *)
Ltac sx := repeat match goal with |- context [sign_extension (2 ^ 32) (2 ^ 31) (?x mod 2 ^ 32)] =>
  rewrite (sx_small x); [|lia] end.

(** This tactic decides a branch whose condition arithmetic settles. *)
Ltac brz :=
  iApply wp_branch; [vx | iNext]; sx;
  repeat match goal with
    | |- context [?x <? ?y] =>
        first [rewrite (proj2 (Z.ltb_lt x y)); [|lia] | rewrite (proj2 (Z.ltb_ge x y)); [|lia]]
    | |- context [?x =? ?y] =>
        first [rewrite (proj2 (Z.eqb_eq x y)); [|lia] | rewrite (proj2 (Z.eqb_neq x y)); [|lia]]
    end;
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].


(** This tactic decides a branch whose condition has become closed. *)
Ltac close_br :=
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** This tactic reduces an index computation of the form base plus offset, scaled by eight. *)
Ltac idx x := norm; rewrite (sx_nonneg x); [|lia]; change (2 ^ (3 mod 64)) with 8; norm.

(** A run of assignments to loop names keeps the lookups at names that avoid them. *)
Ltac xkeep := repeat (match goal with H : avoids _ ?Wl = true |- _ => apply keeps_put_avoid with (W := Wl); [vm_compute; reflexivity | exact H |] end);
  first [apply keeps_refl | assumption].

(** This tactic computes a value whose arithmetic needs range facts. *)
Ltac vxn :=
  cbn -[put];
  repeat match goal with
    |- context [lookup ?k ?E] =>
      let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H
    end;
  unwrap; reflexivity.

(** These scripts prove the lower swap loop of either exchange. Each
    iteration swaps the entry at bot plus i with the entry the same
    distance into the top run. *)
Ltac x_lower_step IH bot mid top i av ps :=
  brz; step; step; step; step; step; idx (bot + i);
  set (j := Z.to_nat (bot + i)); set (k := Z.to_nat (top - (mid - bot) + i));
  assert (Hj : Z.of_nat j = bot + i) by (unfold j; lia);
  assert (Hk : Z.of_nat k = top - (mid - bot) + i) by (unfold k; lia);
  iDestruct (argv_cells_two av ps j k with "Hc") as "(Hcj & Hck & Hc)"; [lia | lia | lia |];
  iDestruct (argv_strs_cap ps j with "Hs") as (rj) "[Hcapj %Hqj]"; [lia|];
  iDestruct (argv_strs_cap ps k with "Hs") as (rk) "[Hcapk %Hqk]"; [lia|];
  check "Hl";
  iApply (wp_raw_load_pointer_dq with "Hl Hcj Hcapj"); [reflexivity | vx | left; reflexivity | arith | arith | lia |];
  iNext; iIntros "Hl Hcj _";
  step; step; step; step; step; idx (top - (mid - bot) + i); check "Hl";
  iApply (wp_raw_load_pointer_dq with "Hl Hck Hcapk"); [reflexivity | vx | left; reflexivity | arith | arith | lia |];
  iNext; iIntros "Hl Hck _"; check "Hl";
  iApply (wp_raw_store_pointer with "Hl Hcj"); [vx | vx | reflexivity | arith | arith | wi_store |];
  iNext; iIntros "Hl Hcj"; check "Hl";
  iApply (wp_raw_store_pointer with "Hl Hck"); [vx | vx | reflexivity | arith | arith | wi_store |];
  iNext; iIntros "Hl Hck"; step; step;
  iSpecialize ("Hc" with "Hcj Hck");
  pose proof (swap_at_perm ps j k ltac:(lia) ltac:(lia)) as Hp;
  iApply (IH (Z.to_nat (mid - bot - (i + 1))) ltac:(lia) _ _ (i + 1) (swap_at ps j k) eq_refl
    with "Hl Hc [] [HK]");
  [ vxn | lk_prove | lk_prove | lk_prove | lk_prove | lia | lia | lia | lia
  | by rewrite length_swap_at | lia | lia | lia | lia
  | unfold argv_strs; iEval (rewrite -Hp); iExact "Hs"
  | iIntros (e' ps' (Hp' & Hk' & H94)) "Hl Hc Hs'"; iApply ("HK" with "[%] Hl Hc Hs'");
    split; [by rewrite Hp|]; split; [|assumption]; eapply keeps_trans; [|eassumption]; xkeep ].

Ltac x_lower e fr i ps bot mid top av :=
  intros Hks; remember (Z.to_nat (mid - bot - i)) as m eqn:Hms; revert e fr i ps Hms;
  induction m as [m IH] using (well_founded_induction lt_wf); intros e fr i ps Hms;
  iIntros (Hphi Hb Ht Hm Hv2 Hb0 Hi Hlt Htop Hlen Hav Hal Hend Hr) "Hl Hc #Hs HK";
  iApply wp_enter; [reflexivity | eassumption | iNext]; unfold_blk; cbn [b_insts b_jump];
  step; destruct (Z.eq_dec i (mid - bot)) as [->|Hne];
  [ brz; step; step; step; iApply ("HK" with "[%] Hl Hc Hs"); split; [done|]; split; [xkeep|vxn]
  | x_lower_step IH bot mid top i av ps ].

(** These scripts prove an upper swap loop of either exchange: one
    iteration swaps entry bot + i with entry mid + i. *)
Ltac x_upper_step IH bot mid top i av ps :=
  brz; step; step; step; step; step; idx (bot + i);
  set (j := Z.to_nat (bot + i)); set (k := Z.to_nat (mid + i));
  assert (Hj : Z.of_nat j = bot + i) by (unfold j; lia);
  assert (Hk : Z.of_nat k = mid + i) by (unfold k; lia);
  iDestruct (argv_cells_two av ps j k with "Hc") as "(Hcj & Hck & Hc)"; [lia | lia | lia |];
  iDestruct (argv_strs_cap ps j with "Hs") as (rj) "[Hcapj %Hqj]"; [lia|];
  iDestruct (argv_strs_cap ps k with "Hs") as (rk) "[Hcapk %Hqk]"; [lia|];
  check "Hl";
  iApply (wp_raw_load_pointer_dq with "Hl Hcj Hcapj"); [reflexivity | vx | left; reflexivity | arith | arith | lia |];
  iNext; iIntros "Hl Hcj _";
  step; step; step; step; idx (mid + i); check "Hl";
  iApply (wp_raw_load_pointer_dq with "Hl Hck Hcapk"); [reflexivity | vx | left; reflexivity | arith | arith | lia |];
  iNext; iIntros "Hl Hck _"; check "Hl";
  iApply (wp_raw_store_pointer with "Hl Hcj"); [vx | vx | reflexivity | arith | arith | wi_store |];
  iNext; iIntros "Hl Hcj"; check "Hl";
  iApply (wp_raw_store_pointer with "Hl Hck"); [vx | vx | reflexivity | arith | arith | wi_store |];
  iNext; iIntros "Hl Hck"; step; step;
  iSpecialize ("Hc" with "Hcj Hck");
  pose proof (swap_at_perm ps j k ltac:(lia) ltac:(lia)) as Hp;
  iApply (IH (Z.to_nat (top - mid - (i + 1))) ltac:(lia) _ _ (i + 1) (swap_at ps j k) eq_refl
    with "Hl Hc [] [HK]");
  [ vxn | lk_prove | lk_prove | lk_prove | lk_prove | lia | lia | lia | lia
  | by rewrite length_swap_at | lia | lia | lia | lia
  | unfold argv_strs; iEval (rewrite -Hp); iExact "Hs"
  | iIntros (e' ps' (Hp' & Hk' & H94)) "Hl Hc Hs'"; iApply ("HK" with "[%] Hl Hc Hs'");
    split; [by rewrite Hp|]; split; [|assumption]; eapply keeps_trans; [|eassumption]; xkeep ].

Ltac x_upper e fr i ps bot mid top av :=
  intros Hks; remember (Z.to_nat (top - mid - i)) as m eqn:Hms; revert e fr i ps Hms;
  induction m as [m IH] using (well_founded_induction lt_wf); intros e fr i ps Hms;
  iIntros (Hphi Hb Ht Hm Hv2 Hb0 Hi Hlt Htop Hlen Hav Hal Hend Hr) "Hl Hc #Hs HK";
  iApply wp_enter; [reflexivity | eassumption | iNext]; unfold_blk; cbn [b_insts b_jump];
  step; destruct (Z.eq_dec i (top - mid)) as [->|Hne];
  [ brz; step; step; step; iApply ("HK" with "[%] Hl Hc Hs"); split; [done|]; split; [xkeep|vxn]
  | x_upper_step IH bot mid top i av ps ].

