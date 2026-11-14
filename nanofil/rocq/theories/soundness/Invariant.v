(** When the compiler reuses a pointer check across later instructions,
    the proof of soundness must show that every fact the [[validator]]
    assumes at runtime still holds when the program reaches it. A single
    step of the machine cannot establish that alone, because a check in
    one block may justify a memory access several blocks or instructions
    later.

    This module defines the run-level [[evidence-invariant|evidence invariant]]
    [inv] over machine configurations and proves the structural lemmas
    that connect it to the [[evidence-pass|evidence pass]]. The
    invariant requires the running [[frame]]—unless a failed
    [[check_ahead]] has marked it [[doomed]]—to sit at a program point
    whose live facts hold and whose checked pointers dominate the point,
    while every waiting caller on the stack sits [[parked]] with no live
    facts. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Sites Coverage Evidence Walk Steps.
Import ListNotations.
Open Scope Z_scope.

(** ## The live facts' pointers dominate

    In SSA form, a [[reuse]] instruction can only rely on a previously
    checked pointer if that pointer's [[single definition]] [[dominates]]
    the current program point. Otherwise, control flow could reach the
    reuse without ever defining or checking the pointer along the path.

    Every check inspects an operand already defined in the function, and
    any fact surviving at a block merge must have survived every
    incoming path. The lemmas below prove [live_dom] block by block by
    showing that each checked pointer's defining [[site]] dominates
    every reachable predecessor and thus the block entry. *)

(** Every function in a validated module satisfies the structural
    conditions that the dominance proofs assume. Lemma [func_facts]
    extracts its non-empty block list, its [[dominator intervals]], its
    distinct block labels, and the proof that every use is dominated by
    its definition. *)
Lemma func_facts : forall md f,
  checked_module md -> In (IFunc f) md ->
  exists b0 rest, fn_blocks f = b0 :: rest /\ block_intervals (b0 :: rest) = Some (fn_doms f) /\
    no_dups (map b_label (fn_blocks f)) = true /\ definitions_dominate f (fn_doms f) = true.
Proof.
  unfold checked_module, valid. intros md f [Hv _] Hin.
  destruct (existsb _ md); [discriminate Hv|]. injection Hv as Hv.
  unfold valid_items in Hv. apply andb_true_iff in Hv as [_ Hv]. rewrite forallb_forall in Hv.
  specialize (Hv _ Hin). simpl in Hv. unfold valid_func, fn_doms in *.
  destruct (fn_blocks f) as [|b0 bs] eqn:Eb; [discriminate Hv|].
  destruct (block_intervals (b0 :: bs)) as [doms|] eqn:Ed; [|discriminate Hv].
  repeat match goal with Hb : (_ && _) = true |- _ => apply andb_true_iff in Hb as [? ?] end.
  exists b0, bs. auto.
Qed.

(** Where the labels of the blocks bs are distinct, the block
    [find_block] finds for l is the only block of bs labelled l. *)
Lemma find_block_unique : forall bs l b b',
  no_dups (map b_label bs) = true -> find_block l bs = Some b -> In b' bs -> b_label b' = l -> b' = b.
Proof.
  induction bs as [|b0 bs IH]; simpl; intros l b b' Hnd Hf Hin Hl; [discriminate Hf|].
  apply andb_true_iff in Hnd as [Hn Hnd]. destruct (name_eqb (b_label b0) l) eqn:E.
  - injection Hf as <-. apply name_eqb_true in E. destruct Hin as [-> | Hin]; [reflexivity|].
    exfalso. apply negb_true_iff in Hn. pose proof (mem_false _ _ Hn (b_label b') (in_map _ _ _ Hin)) as Hne.
    rewrite E, Hl in Hne. apply name_eqb_false in Hne. exact (Hne eq_refl).
  - destruct Hin as [-> | Hin]; [rewrite Hl in E; apply name_eqb_false in E; contradiction|].
    exact (IH _ _ _ Hnd Hf Hin Hl).
Qed.

(** Where dropping k elements of l leaves x before rest, x is l's
    element at k, dropping k + 1 leaves rest, and k is below l's
    length. *)
Lemma skipn_cons : forall (A : Type) k (l : list A) x rest,
  skipn k l = x :: rest -> nth_error l k = Some x /\ skipn (S k) l = rest /\ (S k <= length l)%nat.
Proof.
  intros A k. induction k as [|k IH]; intros l x rest H; destruct l as [|y l]; simpl in *; try discriminate H.
  - injection H as -> ->. split; [reflexivity|]. split; [reflexivity | lia].
  - destruct (IH _ _ _ H) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2 | lia].
Qed.

(** A temporary among the values vs is among their temporaries
    ([value_temps]). *)
Lemma value_temps_in : forall vs a, In (Tmp a) vs -> In a (value_temps vs).
Proof. intros vs a H. unfold value_temps. apply in_flat_map. exists (Tmp a). split; [exact H | left; reflexivity]. Qed.

(** Predicate [facts_dominate] checks that every [[live fact]] whose
    pointer has a single definition in function f is defined at a site
    that dominates instruction index k of block l. *)
Definition facts_dominate (f : func) (l : name) (k : Z) (live : list fact) : Prop :=
  forall fa y, In fa live -> f_p fa = Tmp y -> once_has (single_definitions f) y = true ->
    dominating f l k y.

(** Unreachable blocks need no dominance guarantee because execution can
    never enter them. Predicate [live_dom] restricts [facts_dominate] to
    blocks that are reachable in the function's dominator tree. *)
Definition live_dom (f : func) (l : name) (k : nat) (live : list fact) : Prop :=
  is_reachable (fn_doms f) l = true -> facts_dominate f l (Z.of_nat k) live.

(** A site that dominates index k of block l dominates every later index
    k' of l. *)
Lemma site_dominates_mono : forall doms l k k' s,
  k <= k' -> site_dominates doms l k s = true -> site_dominates doms l k' s = true.
Proof.
  intros doms l k k' [|d j] Hk H; simpl in *; [reflexivity|].
  destruct (name_eqb d l); [apply Z.ltb_lt in H; apply Z.ltb_lt; lia | exact H].
Qed.

(** So live facts that dominate index k of a block dominate every later
    index of it. *)
Lemma live_dom_mono : forall f l k k' live, (k <= k')%nat -> live_dom f l k live -> live_dom f l k' live.
Proof.
  intros f l k k' live Hk H Hr fa y Hfa Hy Ho. destruct (H Hr fa y Hfa Hy Ho) as (s & D & H1 & H2 & H3).
  exists s, D. split; [exact H1|]. split; [exact H2|]. eapply site_dominates_mono; [|exact H3]. lia.
Qed.

(** The empty list of facts dominates every point. *)
Lemma live_dom_nil : forall f l k, live_dom f l k [].
Proof. intros f l k _ fa y []. Qed.

(** [kill] d keeps only facts it was given. *)
Lemma kill_incl : forall d fs fa, In fa (kill d fs) -> In fa fs.
Proof. unfold kill. intros d fs fa H. apply filter_In in H. exact (proj1 H). Qed.

(** [evidence_after] keeps only facts it was given. *)
Lemma evidence_after_incl : forall i fs fa, In fa (evidence_after i fs) -> In fa fs.
Proof.
  unfold evidence_after. intros i fs fa H.
  destruct (evidence_preserving i); [|destruct H].
  destruct (inst_def_first i); [exact (kill_incl _ _ _ H) | exact H].
Qed.

(** Every check instruction inspects a pointer temporary that appears
    among its own operands. Lemma [check_fact_uses] records that the
    pointer named by [check_fact] is an operand used by instruction i. *)
Lemma check_fact_uses : forall i fa y, check_fact i = Some fa -> f_p fa = Tmp y -> In y (inst_uses i).
Proof.
  intros i fa y H Hy. destruct i as [q k o args | | | | | | | | ]; try discriminate H.
  destruct k, o; try discriminate H;
    destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; simpl in H; try discriminate H;
    injection H as <-; simpl in Hy; subst; apply value_temps_in; simpl; auto.
Qed.

(** One step of the pass ([checked_inst_rest]) takes one instruction,
    or a check and its access, and keeps only facts it had or the
    check's own. *)
Lemma pass_live_after : forall s i rest live rest' live',
  checked_inst_rest s i rest live = Some (rest', live') ->
  (rest' = rest \/ exists a, rest = a :: rest') /\
  forall fa, In fa live' -> In fa live \/ check_fact i = Some fa.
Proof.
  intros s i rest live rest' live' Hc.
  destruct (check_fact i) as [fa0|] eqn:Hf.
  - destruct (access_fact_some _ _ Hf) as [fb Hg].
    destruct (checked_inst_rest_check _ _ _ _ _ _ _ _ Hf Hg Hc) as (access & -> & _ & ->).
    split; [right; eauto|]. intros fa Hfa. apply evidence_after_incl in Hfa as [<- | Hfa]; [right; reflexivity|].
    left. exact (evidence_after_incl _ _ _ Hfa).
  - destruct (is_check_local i) eqn:Hcl.
    + destruct i as [q k o args | | | | | | | | ]; try discriminate Hcl.
      destruct k; try discriminate Hcl; destruct o; try discriminate Hcl;
        destruct args; try discriminate Hcl.
      destruct (checked_inst_rest_local_cov _ _ _ _ _ _ _ _ _ _ _ Hc) as (access & -> & _ & ->).
      split; [right; eauto|]. intros fa Hfa. left. exact (kill_incl _ _ _ (evidence_after_incl _ _ _ Hfa)).
    + destruct (is_check_function i) eqn:Hcf.
      * destruct i as [q k o args | | | | | | | | ]; try discriminate Hcf.
        destruct k; try discriminate Hcf; destruct o; try discriminate Hcf.
        destruct (checked_inst_rest_function_rest _ _ _ _ _ _ _ Hc) as (-> & r & cargs & ->).
        split; [right; eauto | intros fa []].
      * assert (Hs' : pass_special i = false).
        { destruct (pass_special i) eqn:Hp; [|reflexivity].
          destruct (pass_special_cases _ Hp Hf) as [E | E]; congruence. }
        rewrite (checked_inst_rest_generic _ _ _ _ Hs') in Hc.
        destruct (generic_rest_shape _ _ _ _ _ _ Hc) as (-> & Hlive & _). split; [left; reflexivity|].
        intros fa Hfa. left. destruct Hlive as [-> | (d & g & _ & ->)];
          [exact (evidence_after_incl _ _ _ Hfa) | exact (kill_incl _ _ _ Hfa)].
Qed.

(** A pointer check can only add evidence about a temporary variable that
    was defined before the check runs. Lemma [pass_step_dom] shows that
    each instruction step preserves dominance of all live facts at the
    next instruction index. *)
Lemma pass_step_dom : forall md f b k i rest live rest' live',
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) ->
  nth_error (b_insts b) k = Some i ->
  checked_inst_rest (fn_src md f) i rest live = Some (rest', live') ->
  live_dom f (b_label b) k live -> live_dom f (b_label b) (S k) live'.
Proof.
  intros md f b k i rest live rest' live' Hmd Hin Hb Hk Hc H Hr fa y Hfa Hy Ho.
  destruct (proj2 (pass_live_after _ _ _ _ _ _ Hc) fa Hfa) as [Hl | Hf].
  - exact (live_dom_mono _ _ _ _ _ (le_S _ _ (le_n k)) H Hr fa y Hl Hy Ho).
  - destruct (func_facts _ _ Hmd Hin) as (_ & _ & _ & _ & _ & Hdd).
    unfold once_has in Ho. destruct (lookup y (single_definitions f)) as [D|] eqn:Ey; [|discriminate Ho].
    destruct (use_dominated _ _ _ _ _ _ _ Hdd Hb Hr Hk (check_fact_uses _ _ _ Hf Hy) Ey) as (s & Hs & Hsd).
    exists s, D. split; [exact Ey|]. split; [exact Hs|]. eapply site_dominates_mono; [|exact Hsd]. lia.
Qed.

(** Any pointer check recorded inside a basic block can only be reused
    in a successor block if the pointer's definition dominates the
    outgoing edge. By induction over the remaining instructions in the
    block, [walk_dom] proves that the block's exit facts dominate its
    end. *)
Lemma walk_dom : forall md f b n k instructions live out,
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) ->
  instructions = skipn k (b_insts b) -> (k <= length (b_insts b))%nat ->
  live_dom f (b_label b) k live ->
  checked_insts (fn_src md f) n instructions live = Some out ->
  live_dom f (b_label b) (length (b_insts b)) out.
Proof.
  intros md f b n. induction n as [|n IH]; intros k instructions live out Hmd Hin Hb Hs Hk H Hc;
    (destruct instructions as [|i rest]; cbn [checked_insts] in Hc; [injection Hc as <-; exact (live_dom_mono _ _ _ _ _ Hk H)|]);
    [discriminate Hc|].
  destruct (checked_inst_rest _ i rest live) as [[rest' live']|] eqn:Ec; [|discriminate Hc]. simpl in Hc.
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hs)) as (Hki & Hrest & Hlen).
  pose proof (pass_step_dom _ _ _ _ _ _ _ _ _ Hmd Hin Hb Hki Ec H) as H1.
  destruct (proj1 (pass_live_after _ _ _ _ _ _ Ec)) as [-> | (a & ->)].
  - exact (IH _ _ _ _ Hmd Hin Hb (eq_sym Hrest) Hlen H1 Hc).
  - destruct (skipn_cons _ _ _ _ _ Hrest) as (_ & Hrest' & Hlen').
    exact (IH _ _ _ _ Hmd Hin Hb (eq_sym Hrest') Hlen' (live_dom_mono _ _ _ _ _ (le_S _ _ (le_n _)) H1) Hc).
Qed.

(** Predicate [exits_dom] states that every block's recorded exit facts
    in map ex dominate the end of that block. *)
Definition exits_dom (f : func) (ex : list (name * list fact)) : Prop :=
  forall bp out, In bp (fn_blocks f) -> lookup (b_label bp) ex = Some out ->
    live_dom f (b_label bp) (length (b_insts bp)) out.

(** Each successor label of a jump j is the label of one of its targets
    ([jump_targets]). *)
Lemma jump_succs_target : forall j s, In s (jump_succs j) -> exists t, In t (jump_targets j) /\ edge_label t = s.
Proof.
  intros [t | v t1 t2 | v | vs | | ] s H; simpl in H; try contradiction.
  - destruct H as [<- | []]. exists t. split; [left|]; reflexivity.
  - destruct H as [<- | [<- | []]]; [exists t1 | exists t2]; simpl; auto.
Qed.

(** At a merge point, a fact enters block b only if it survives every
    incoming edge. When every predecessor's exit facts dominate its own
    end, the meet over incoming edges in [entry_live] produces facts
    that dominate the entry of b. *)
Lemma entry_dom : forall md f ex b,
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) -> exits_dom f ex ->
  live_dom f (b_label b) 0 (entry_live f ex b).
Proof.
  intros md f ex b Hmd Hin Hb Hex Hr fa y Hfa Hy Ho.
  destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Eb & Hdoms & Hnd & _).
  destruct (module_func _ _ Hmd Hin) as (_ & (b0' & bs' & Eb' & Hnoin) & _).
  rewrite Eb in Eb'. injection Eb' as <- <-.
  unfold entry_live in Hfa. apply entry_kill_in in Hfa as [Hfa _].
  destruct (name_eqb (b_label b) (b_label b0)) eqn:E0.
  { apply name_eqb_true in E0. rewrite E0, (incoming_nil (fn_blocks f) (b_label b0)) in Hfa; [destruct Hfa|].
    exact Hnoin. }
  apply name_eqb_false in E0.
  unfold once_has in Ho. destruct (lookup y (single_definitions f)) as [D|] eqn:Ey; [|discriminate Ho].
  destruct (once_position _ _ _ Ey) as (s0 & Hs0 & Huniq).
  exists s0, D. split; [exact Ey|]. split; [exact Hs0|].
  destruct s0 as [|d j]; [reflexivity|]. simpl.
  rewrite Eb in Hnd.
  assert (Hpre : forall p, edge (b0 :: rest) p (b_label b) -> is_reachable (fn_doms f) p = true ->
                   dominates (fn_doms f) d p = true).
  { intros p (bp & Hbp & Hpl & Hsj) Hrp. rewrite <- Eb in Hbp.
    destruct (jump_succs_target _ _ Hsj) as (t & Ht & Htl).
    pose proof (incoming_in _ _ _ Hbp Ht) as Hinc. rewrite Htl in Hinc.
    pose proof (evidence_meet_in _ _ _ Hfa (in_map (edge_set ex) _ _ Hinc)) as Hset.
    unfold edge_set in Hset. simpl in Hset. destruct (is_poll t); [destruct Hset|].
    destruct (lookup (b_label bp) ex) as [fs|] eqn:Ex; [|destruct Hset].
    destruct (Hex bp fs Hbp Ex ltac:(rewrite Hpl; exact Hrp) fa y Hset Hy ltac:(unfold once_has; rewrite Ey; reflexivity))
      as (s & D' & Ey' & Hs & Hsd).
    rewrite Ey in Ey'. injection Ey' as <-. destruct (Huniq _ _ Hs) as [-> _].
    rewrite Hpl in Hsd. simpl in Hsd. destruct (name_eqb d p) eqn:Edp; [|exact Hsd].
    apply name_eqb_true in Edp. rewrite Edp. exact (dominates_refl _ _ _ Hdoms _ Hrp). }
  destruct (dom_meet _ _ _ Hdoms _ _ Hnd Hr E0 Hpre) as [Hd Hne].
  rewrite (proj2 (name_eqb_false _ _) Hne). exact Hd.
Qed.

(** By walking each block in order from its entry facts, [pass_exits]
    computes an exit map for function f whose facts dominate every block
    end. *)
Lemma pass_exits_dom : forall md f E,
  checked_module md -> In (IFunc f) md -> pass_exits (fn_src md f) f = Some E -> exits_dom f E.
Proof.
  intros md f E Hmd Hin HE. unfold pass_exits in HE.
  destruct (func_facts _ _ Hmd Hin) as (_ & _ & _ & _ & Hnd & _).
  assert (G : forall bs ex, (forall b, In b bs -> In b (fn_blocks f)) ->
                fold_left (pass_block (fn_src md f) f) bs (Some ex) = Some E -> exits_dom f ex -> exits_dom f E).
  { induction bs as [|b bs IH]; cbn [fold_left]; intros ex Hbs H Hex; [injection H as <-; exact Hex|].
    rewrite pass_block_some in H.
    destruct (checked_insts _ _ _ (entry_live f ex b)) as [out|] eqn:Ec; [|rewrite pass_fold_none in H; discriminate H].
    apply (IH _ (fun b' Hb' => Hbs b' (or_intror Hb')) H).
    pose proof (Hbs b (or_introl eq_refl)) as Hb.
    intros bp out' Hbp Hl. rewrite lookup_put in Hl. destruct (name_eqb (b_label bp) (b_label b)) eqn:El.
    - injection Hl as <-. apply name_eqb_true in El.
      assert (Hf : find_block (b_label b) (fn_blocks f) = Some b).
      { clear -Hnd Hb. induction (fn_blocks f) as [|b1 bs1 IHb]; [destruct Hb|]. simpl in *.
        apply andb_true_iff in Hnd as [Hn Hnd]. destruct (name_eqb (b_label b1) (b_label b)) eqn:E.
        - destruct Hb as [-> | Hb]; [reflexivity|]. exfalso. apply negb_true_iff in Hn.
          pose proof (mem_false _ _ Hn (b_label b) (in_map _ _ _ Hb)) as Hne.
          apply name_eqb_true in E. rewrite E, name_eqb_refl in Hne. discriminate Hne.
        - destruct Hb as [-> | Hb]; [rewrite name_eqb_refl in E; discriminate E | exact (IHb Hnd Hb)]. }
      rewrite (find_block_unique _ _ _ _ Hnd Hf Hbp El).
      exact (walk_dom _ _ _ _ 0 _ _ _ Hmd Hin Hb eq_refl (Nat.le_0_l _) (entry_dom _ _ _ _ Hmd Hin Hb Hex) Ec).
    - exact (Hex _ _ Hbp Hl). }
  apply (G _ _ (fun b Hb => Hb) HE). intros bp out _ Hl. discriminate Hl.
Qed.

(** ## The invariant, frame by frame

    To prove that a whole program run never dereferences an unchecked
    pointer, we track what every call frame on the stack knows at each
    execution point. Functor [Invariant] defines this state invariant
    over [Machine] R: the active frame agrees with the evidence pass,
    and every suspended caller waits immediately after a call with no
    cached facts. *)

(** Functor [Invariant] defines the run-level invariant [inv] and its
    step lemmas for any concrete [[runtime]] R. *)
Module Invariant (R : Runtime).

Module RM := Machine R.
Import RM.

(** The edge a jump j takes ([taken_target]) is one of its targets. *)
Lemma taken_target_in : forall ge fr j t, taken_target ge fr j = Some t -> In t (jump_targets j).
Proof.
  unfold taken_target. intros ge fr j t H. destruct j; try discriminate H.
  - injection H as <-. left. reflexivity.
  - destruct (value_x _ _ _ _) as [[n| |]|]; try discriminate H. injection H as <-.
    destruct (n =? 0); simpl; auto.
Qed.

(** Jumping to another basic block transfers control without changing
    memory or consuming [[fuel]]. Lemma [edge_step_next'] records that
    the frame lands at the target block's entry and either stays
    undoomed or took a non-polling edge. *)
Lemma edge_step_next' : forall c from t c',
  edge_step c from t = Next c' ->
  c' = continue_at c (with_point (c_frame c) (Enter (edge_label t) (Some from))) (c_mem c) (c_fuel c) /\
  (fr_doomed (c_frame c) = None \/ is_poll t = false).
Proof.
  unfold edge_step. intros c from t c' H.
  destruct t, (fr_doomed (c_frame c)); try discriminate H; injection H as <-; auto.
Qed.

(** A jump at the end of block l takes an edge, the one [taken_target]
    names, or returns from a frame that is not doomed. *)
Lemma jump_step_next : forall ge c l j c',
  jump_step ge c l j = Next c' ->
  (exists t, taken_target ge (c_frame c) j = Some t /\
     c' = continue_at c (with_point (c_frame c) (Enter (edge_label t) (Some l))) (c_mem c) (c_fuel c)) \/
  (fr_doomed (c_frame c) = None /\ exists o, return_step c o = Next c').
Proof.
  intros ge c l j c' H. unfold jump_step in H.
  destruct j as [t | v t1 t2 | v | vs | | ].
  - left. exists t. split; [reflexivity|].
    assert (H' : edge_step c l t = Next c') by (destruct (fr_doomed (c_frame c)); exact H).
    exact (proj1 (edge_step_next' _ _ _ _ H')).
  - left.
    assert (H' : or_stuck "branch"
                   (let* x := value_x ge (fr_env (c_frame c)) W v in
                    match x with
                    | WInt n => Some (edge_step c l (if n =? 0 then t2 else t1))
                    | _ => None
                    end) = Next c') by (destruct (fr_doomed (c_frame c)); exact H).
    apply or_stuck_next in H'. unfold taken_target.
    destruct (value_x ge (fr_env (c_frame c)) W v) as [[n| |]|]; try discriminate H'.
    injection H' as H'. eexists. split; [reflexivity|]. exact (proj1 (edge_step_next' _ _ _ _ H')).
  - destruct (fr_doomed (c_frame c)) eqn:Ew; [discriminate H|]. right. split; [reflexivity|].
    apply or_stuck_next in H. destruct (fn_ret _); try discriminate H.
    destruct (value_x _ _ _ _); [injection H as H; eauto | discriminate H].
  - destruct (fr_doomed (c_frame c)) eqn:Ew; [discriminate H|]. right. split; [reflexivity|].
    apply or_stuck_next in H. destruct (fn_ret _); try discriminate H.
    destruct (map2_option _ _ _); [injection H as H; eauto | discriminate H].
  - destruct (fr_doomed (c_frame c)) eqn:Ew; [discriminate H|]. right. eauto.
  - destruct (fr_doomed (c_frame c)); discriminate H.
Qed.

(** ### What holds where

    As execution moves through a basic block, we need to track which
    pointer checks remain valid before each instruction or outgoing
    jump. The definitions below state what holds between two
    instructions and between a paired check and its memory access. *)

(** Before taking a jump at the end of a block, the frame needs its
    outgoing facts to survive into the next block. Predicate
    [jump_claim] requires those facts to hold whenever the taken edge
    does not [[poll]], because a poll edge may trigger the garbage
    collector and invalidate live facts. *)
Definition jump_claim (ge : genv) (m : Memory.mem) (fr : frame) (j : jump) (live : list fact) : Prop :=
  forall t, taken_target ge fr j = Some t -> is_poll t = false -> facts_hold ge m (fr_env fr) live.

(** When a pointer check is paired directly with its memory access, the
    machine steps to a point between the two instructions. Predicate
    [pair_claim] states that the check's fact covers the upcoming
    access, or that a function check just validated a raw call's target. *)
Definition pair_claim (ge : genv) (m : Memory.mem) (fr : frame) (access : inst) (live' : list fact) : Prop :=
  (exists fb pre, (covered_access access (f_q fb) (f_lo fb) (f_hi fb) (f_r fb) (f_al fb) = true \/
                   access = Touch (f_q fb)) /\
     live' = evidence_after access pre /\ facts_hold ge m (fr_env fr) (fb :: pre)) \/
  (live' = [] /\ exists r q args p, access = RawCall r (Tmp q) args /\
     lookup q (fr_env fr) = Some (WPtr p) /\ function_check_res ge p = Some ok).

(** Inside a basic block, execution is either waiting for the next
    instruction or paused between a paired check and its access.
    Predicate [at_pos] captures both cases at instruction index k of
    block l. *)
Definition at_pos (ge : genv) (s : src) (m : Memory.mem) (fr : frame) (instructions : list inst) (j : jump)
    (out : list fact) (f : func) (l : name) (k : nat) : Prop :=
  (exists live, walks s instructions live out /\ live_dom f l k live /\
     match instructions with
     | i :: _ => relies s i = true -> facts_hold ge m (fr_env fr) live
     | [] => jump_claim ge m fr j live
     end) \/
  (exists access rest' live', instructions = access :: rest' /\ walks s rest' live' out /\
     live_dom f l (S k) live' /\ pair_claim ge m fr access live').

(** Predicate [point_ok] ties the frame's current execution point to the
    module's validated evidence. At function entry or [[snapshot]] it
    checks the entry label, at a block entry it checks the incoming edge's
    exit facts unless the edge polls, and inside a block it delegates to
    [at_pos]. *)
Definition point_ok (ge : genv) (md : module) (m : Memory.mem) (fr : frame) : Prop :=
  let f := fr_fn fr in
  exists E, pass_exits (fn_src md f) f = Some E /\
  match fr_at fr with
  | Snapshot _ l => entry_label f = Some l
  | Enter l None => entry_label f = Some l
  | Enter l (Some p) =>
      exists bp t, find_block p (fn_blocks f) = Some bp /\ In t (jump_targets (b_jump bp)) /\
        edge_label t = l /\
        (is_poll t = true \/ exists out, lookup p E = Some out /\ facts_hold ge m (fr_env fr) out)
  | Exec l instructions j =>
      exists b out k, find_block l (fn_blocks f) = Some b /\ lookup l E = Some out /\
        j = b_jump b /\ instructions = skipn k (b_insts b) /\ at_pos ge (fn_src md f) m fr instructions j out f l k
  end.

(** Every named local the frame has allocated lies above address 0: a
    `check_local`'s fact needs its address not to wrap. *)
Definition locals_pos (fr : frame) : Prop :=
  forall x base, lookup x (fr_locals fr) = Some (Some base) -> 0 < base.

(** To stay safe while executing C code, the active call frame must keep
    its stack locals at positive addresses and maintain valid pointer
    evidence unless it is already doomed to trap. Predicate [frame_ok]
    states that the function belongs to md, its locals lie above 0, and
    either it is [[doomed]] or [point_ok] holds. *)
Definition frame_ok (ge : genv) (md : module) (m : Memory.mem) (fr : frame) : Prop :=
  In (IFunc (fr_fn fr)) md /\ locals_pos fr /\ (fr_doomed fr <> None \/ point_ok ge md m fr).

(** A function call can overwrite arbitrary memory and trigger garbage
    collection, so no cached pointer facts survive across it. Predicate
    [parked] describes a waiting caller on the stack: it is undoomed,
    its locals lie above address 0, and execution resumes after the call
    with an empty fact list. *)
Definition parked (md : module) (fr : frame) : Prop :=
  In (IFunc (fr_fn fr)) md /\ locals_pos fr /\ fr_doomed fr = None /\
  exists E l rest j b out k, pass_exits (fn_src md (fr_fn fr)) (fr_fn fr) = Some E /\
    fr_at fr = Exec l rest j /\ find_block l (fn_blocks (fr_fn fr)) = Some b /\
    lookup l E = Some out /\ j = b_jump b /\ rest = skipn k (b_insts b) /\
    walks (fn_src md (fr_fn fr)) rest [] out.

(** The run-level invariant [inv] holds of a machine state when its
    running frame satisfies [frame_ok] and every suspended caller on the
    call stack satisfies [parked]. *)
Definition inv (ge : genv) (md : module) (st : mstate) : Prop :=
  frame_ok ge md (c_mem (fst st)) (c_frame (fst st)) /\
  Forall (fun fp => parked md (fst fp)) (c_callers (fst st)).

(** If the [[runtime]] freed objects at a [[safepoint]] right before an
    instruction that relies on cached evidence, those cached facts could
    become stale. Predicate [spares] requires [R.safepoint] to leave
    all memory regions unchanged before any instruction where [relies]
    is true. *)
Definition spares (ge : genv) (md : module) : Prop :=
  forall c s s' m',
    safepoint_due ge c = true -> R.safepoint s (c_mem c) s' m' ->
    forall l i rest j, fr_at (c_frame c) = Exec l (i :: rest) j ->
    relies (fn_src md (fr_fn (c_frame c))) i = true -> m_regions m' = m_regions (c_mem c).

(** In Fil-C, the garbage collector may move or sweep dead objects at a
    safepoint, but it never frees objects that are still live. By
    [R.collector_live], every runtime satisfies [spares] for every
    module. *)
Lemma spares_any : forall ge md, spares ge md.
Proof. intros ge md c s s' m' _ Hsp _ _ _ _ _ _. exact (R.collector_live _ _ _ _ Hsp). Qed.

(** The empty list of facts holds. *)
Lemma facts_hold_nil : forall ge m e, facts_hold ge m e [].
Proof. intros ge m e fa []. Qed.

(** Where the facts after a step hold, whatever comes next may rely on
    them. *)
Lemma at_pos_between : forall ge s m fr instructions j live out f l k,
  walks s instructions live out -> live_dom f l k live -> facts_hold ge m (fr_env fr) live -> at_pos ge s m fr instructions j out f l k.
Proof.
  intros ge s m fr instructions j live out f l k Hw Hd Hl. left. exists live. split; [exact Hw|]. split; [exact Hd|].
  destruct instructions; [intros t _ _; exact Hl | intros _; exact Hl].
Qed.

(** When a callee returns, the suspended caller resumes with the
    callee's return value bound in a fresh environment and potentially
    updated memory. Because a [parked] caller waits with no live facts,
    it immediately satisfies [frame_ok] in any resulting memory. *)
Lemma parked_resume : forall ge md m fr e,
  parked md fr -> frame_ok ge md m (mkFrame (fr_fn fr) e (fr_locals fr) (fr_doomed fr) (fr_at fr)).
Proof.
  intros ge md m fr e (Hin & Hpos & Hd & E & l & rest & j & b & out & k & HE & Ha & Hb & Hout & Hj & Hk & Hw).
  split; [exact Hin|]. split; [exact Hpos|]. right. exists E. split; [exact HE|]. simpl. rewrite Ha.
  exists b, out, k. split; [exact Hb|]. split; [exact Hout|]. split; [exact Hj|]. split; [exact Hk|].
  eapply at_pos_between; [exact Hw | apply live_dom_nil | apply facts_hold_nil].
Qed.

(** Calling a C function starts execution at the callee's entry block
    before any stack local variables have been allocated. Because a
    freshly built frame has no named locals and starts at the entry
    point, it satisfies [frame_ok]. *)
Lemma call_frame_ok : forall ge md m g xs fr,
  checked_module md -> In (IFunc g) md -> call_frame g xs = Some fr -> frame_ok ge md m fr.
Proof.
  intros ge md m g xs fr Hmd Hin H. unfold call_frame in H.
  destruct (length xs <? length (fn_params g))%nat; [discriminate H|].
  destruct (module_func _ _ Hmd Hin) as (_ & _ & E & HE).
  destruct (fn_blocks g) as [|b bs] eqn:Eb; [discriminate H|]. injection H as <-.
  split; [exact Hin|]. split; [intros x base Hx; exfalso; exact (lookup_unallocated _ _ _ Hx)|].
  right. exists E. split; [exact HE|]. unfold entry_label. simpl. rewrite Eb.
  destruct (variadic_func g); reflexivity.
Qed.

(** Executing an instruction accepted by the evidence pass advances the
    proof state by one step. If the instruction continues without
    stopping, either the updated live facts hold after it or the pass
    paused between a check and its access where [pair_claim] holds. *)
Lemma pass_step : forall ge s fr m i rest live rest' live' e1 l1 m1 fr1,
  objects_fit (m_regions m) -> locals_pos fr ->
  (relies s i = true -> facts_hold ge m (fr_env fr) live) ->
  checked_inst_rest s i rest live = Some (rest', live') ->
  inst_step ge fr m i = Some (IContinue e1 l1 m1) -> fr_env fr1 = e1 ->
  (rest' = rest /\ facts_hold ge m1 e1 live') \/
  (exists access, rest = access :: rest' /\ pair_claim ge m1 fr1 access live').
Proof.
  intros ge s fr m i rest live rest' live' e1 l1 m1 fr1 Hfit Hpos Hl Hc Hs He.
  destruct (check_fact i) as [fa|] eqn:Hf.
  - assert (Hr : relies s i = true)
      by (unfold relies; rewrite (check_fact_preserving _ _ Hf); reflexivity).
    specialize (Hl Hr).
    assert (exists fb, access_fact i = Some fb) as [fb Hg] by (eapply access_fact_some; eauto).
    destruct (checked_inst_rest_check _ _ _ _ _ _ _ _ Hf Hg Hc) as (access & -> & Hu & ->).
    destruct (check_like_holds _ _ _ _ _ _ _ _ _ Hf Hg Hs) as [Ha Hb].
    right. exists access. split; [reflexivity|]. left. exists fb, (fa :: evidence_after i live).
    split; [destruct (proof_use_cases _ _ _ _ _ _ Hu); auto|]. split; [reflexivity|].
    rewrite He. apply facts_hold_cons; [exact Hb|]. apply facts_hold_cons; [exact Ha|].
    eapply evidence_after_holds; eauto.
  - destruct (is_check_local i) eqn:Hcl.
    + destruct i as [q k o args | | | | | | | | ]; try discriminate Hcl.
      destruct k; try discriminate Hcl; destruct o; try discriminate Hcl;
        destruct args; try discriminate Hcl.
      specialize (Hl eq_refl).
      destruct (checked_inst_rest_local_cov _ _ _ _ _ _ _ _ _ _ _ Hc) as (access & -> & Hcov & ->).
      destruct (check_local_fact _ _ _ _ _ _ _ _ _ _ _ _ _ Hfit Hpos Hcov Hs) as (-> & Hag & Hq).
      destruct (let_step _ _ _ _ _ _ _ _ _ _ Hs) as [Hreg _].
      right. exists access. split; [reflexivity|]. left.
      exists (mkFact q (Tmp q) 0 bytes r align), (kill q live). split; [left; exact Hcov|].
      split; [reflexivity|]. rewrite He. apply facts_hold_cons; [exact Hq|].
      eapply facts_hold_kill; [reflexivity | exact Hag | exact Hl].
    + destruct (is_check_function i) eqn:Hcf.
      * destruct i as [q k o args | | | | | | | | ]; try discriminate Hcf.
        destruct k; try discriminate Hcf; destruct o; try discriminate Hcf.
        destruct (checked_inst_rest_function_rest _ _ _ _ _ _ _ Hc) as (-> & r & cargs & ->).
        destruct (check_function_step _ _ _ _ _ _ _ _ Hs) as (p & Hp & ->).
        right. eexists. split; [reflexivity|]. right. split; [reflexivity|].
        exists r, q, cargs, p. split; [reflexivity|]. split; [|exact Hp].
        rewrite He. apply lookup_put_same.
      * assert (Hs' : pass_special i = false).
        { destruct (pass_special i) eqn:Hp; [|reflexivity].
          destruct (pass_special_cases _ Hp Hf) as [E | E]; congruence. }
        left. rewrite (checked_inst_rest_generic _ _ _ _ Hs') in Hc.
        destruct (generic_rest_shape _ _ _ _ _ _ Hc) as (-> & Hlive & _). split; [reflexivity|].
        destruct (relies s i) eqn:Hr.
        -- specialize (Hl eq_refl). destruct Hlive as [-> | (d & g & -> & ->)].
           ++ eapply evidence_after_holds; eauto.
           ++ destruct (let_step _ _ _ _ _ _ _ _ _ _ Hs) as [Hreg Hag]. eapply facts_hold_kill; eauto.
        -- rewrite <- (checked_inst_rest_generic _ _ _ _ Hs') in Hc.
           rewrite (relies_false _ _ _ _ _ _ Hr Hc). apply facts_hold_nil.
Qed.

(** After a pointer check validates an upcoming memory access, the
    access itself runs without invalidating unrelated evidence. Lemma
    [pair_continue] proves that any facts surviving the access still
    hold in the new memory and environment. *)
Lemma pair_continue : forall ge m fr access live' e1 l1 m1,
  pair_claim ge m fr access live' ->
  inst_step ge fr m access = Some (IContinue e1 l1 m1) -> facts_hold ge m1 e1 live'.
Proof.
  intros ge m fr access live' e1 l1 m1 [(fb & pre & _ & -> & Hh) | (-> & _)] Hs; [|apply facts_hold_nil].
  eapply evidence_after_holds; [|exact Hs]. intros fa Hin. apply Hh. right. exact Hin.
Qed.

(** Every non-stopping instruction inside a basic block advances
    execution to the next instruction without losing evidence. Lemma
    [at_pos_continue] preserves [at_pos] at index k + 1 whether the pass
    stepped normally or completed a paired access. *)
Lemma at_pos_continue : forall ge md m fr i rest j out e1 l1 m1 fr1 f l b k,
  checked_module md -> In (IFunc f) md -> find_block l (fn_blocks f) = Some b ->
  i :: rest = skipn k (b_insts b) ->
  objects_fit (m_regions m) -> locals_pos fr ->
  at_pos ge (fn_src md f) m fr (i :: rest) j out f l k ->
  inst_step ge fr m i = Some (IContinue e1 l1 m1) -> fr_env fr1 = e1 ->
  at_pos ge (fn_src md f) m1 fr1 rest j out f l (S k).
Proof.
  intros ge md m fr i rest j out e1 l1 m1 fr1 f l b k Hmd Hin Hb Hk Hfit Hpos Hat Hs He.
  destruct (find_block_in _ _ _ Hb) as [Hbin <-].
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hk)) as (Hki & _ & _).
  destruct Hat as [(live & Hw & Hd & Hl) | (access & rest' & live' & E & Hw & Hd & Hp)].
  - destruct (walks_cons _ _ _ _ _ Hw) as (rest' & live' & Hc & Hw').
    pose proof (pass_step_dom _ _ _ _ _ _ _ _ _ Hmd Hin Hbin Hki Hc Hd) as Hd'.
    destruct (pass_step _ _ _ _ _ _ _ _ _ _ _ _ _ Hfit Hpos Hl Hc Hs He)
      as [(-> & Hh) | (access & -> & Hp)].
    + eapply at_pos_between; [exact Hw' | exact Hd' | rewrite He; exact Hh].
    + right. exists access, rest', live'. split; [reflexivity|]. split; [exact Hw'|].
      split; [exact (live_dom_mono _ _ _ _ _ (le_S _ _ (le_n _)) Hd')|]. exact Hp.
  - injection E as <- <-. eapply at_pos_between; [exact Hw | exact Hd|]. rewrite He.
    eapply pair_continue; eauto.
Qed.

(** Because function calls and allocations can change memory
    arbitrarily, no cached pointer evidence survives across them. After
    any instruction that discards cached facts—except a function
    check—execution continues with an empty fact list. *)
Lemma walks_after : forall ge s m fr i rest j out f l k,
  at_pos ge s m fr (i :: rest) j out f l k -> relies s i = false -> is_check_function i = false ->
  walks s rest [] out.
Proof.
  intros ge s m fr i rest j out f l k Hat Hr Hcf.
  destruct Hat as [(live & Hw & _) | (access & rest' & live' & E & Hw & _ & Hp)].
  - destruct (walks_cons _ _ _ _ _ Hw) as (rest' & live' & Hc & Hw').
    destruct (relies_false_rest _ _ _ _ _ _ Hr Hcf Hc) as [-> ->]. exact Hw'.
  - injection E as <- <-.
    destruct Hp as [(fb & pre & _ & -> & _) | (-> & _)]; [|exact Hw].
    unfold evidence_after in Hw. rewrite (relies_preserving _ _ Hr) in Hw. exact Hw.
Qed.

(** ### Reading and making [point_ok]

    Many step proofs inspect a frame executing inside a block and then
    rebuild [point_ok] at the next position. The two helper lemmas below
    pack and unpack the existential witnesses inside [point_ok] for
    [Exec] points. *)

(** To re-establish the frame invariant after stepping inside a block, a
    proof needs to package the block's exit evidence and the current
    position into [point_ok]. Lemma [point_ok_exec] builds that witness
    at instruction index k. *)
Lemma point_ok_exec : forall ge md m fr l instructions j E b out k,
  pass_exits (fn_src md (fr_fn fr)) (fr_fn fr) = Some E -> fr_at fr = Exec l instructions j ->
  find_block l (fn_blocks (fr_fn fr)) = Some b -> lookup l E = Some out -> j = b_jump b ->
  instructions = skipn k (b_insts b) ->
  at_pos ge (fn_src md (fr_fn fr)) m fr instructions j out (fr_fn fr) l k -> point_ok ge md m fr.
Proof.
  intros ge md m fr l instructions j E b out k HE Ha Hb Ho Hj Hk Hat. unfold point_ok. cbv zeta.
  exists E. split; [exact HE|]. rewrite Ha. eauto 8.
Qed.

(** To analyze an instruction step inside a basic block, a proof needs
    the block's instruction list, its exit facts, and the evidence
    currently live. Lemma [point_ok_exec_inv] extracts all of those
    fields from [point_ok]. *)
Lemma point_ok_exec_inv : forall ge md m fr l instructions j,
  point_ok ge md m fr -> fr_at fr = Exec l instructions j ->
  exists E b out k, pass_exits (fn_src md (fr_fn fr)) (fr_fn fr) = Some E /\
    find_block l (fn_blocks (fr_fn fr)) = Some b /\ lookup l E = Some out /\ j = b_jump b /\
    instructions = skipn k (b_insts b) /\ at_pos ge (fn_src md (fr_fn fr)) m fr instructions j out (fr_fn fr) l k.
Proof.
  intros ge md m fr l instructions j H Ha. unfold point_ok in H. cbv zeta in H.
  destruct H as (E & HE & H). rewrite Ha in H. destruct H as (b & out & k & ?). eauto 10.
Qed.

(** When a function calls another function, any pointer checks cached in
    the caller cannot be assumed after the callee runs. An undoomed
    frame at a call therefore leaves a waiting caller on the stack with
    no live facts. *)
Lemma call_parked : forall ge md m fr l r callee args rest j,
  frame_ok ge md m fr -> fr_doomed fr = None -> fr_at fr = Exec l (Call r callee args :: rest) j ->
  parked md (mkFrame (fr_fn fr) (fr_env fr) (fr_locals fr) None (Exec l rest j)).
Proof.
  intros ge md m fr l r callee args rest j (Hin & Hpos & Hpt) Hd Ha.
  destruct Hpt as [Hd0 | Hp]; [congruence|].
  destruct (point_ok_exec_inv _ _ _ _ _ _ _ Hp Ha) as (E & b & out & k & HE & Hb & Hout & Hj & Hk & Hat).
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hk)) as (_ & Hrest & _).
  split; [exact Hin|]. split; [exact Hpos|]. split; [reflexivity|].
  exists E, l, rest, j, b, out, (S k). simpl. repeat (split; [assumption || reflexivity|]).
  split; [symmetry; exact Hrest|].
  eapply walks_after; [exact Hat | reflexivity | reflexivity].
Qed.

(** A variadic function first takes a [[snapshot]] of its extra
    arguments and then enters its entry block. Lemma [point_ok_entry]
    transfers [point_ok] from the snapshot (or entry) to the entry block
    in any resulting memory. *)
Lemma point_ok_entry : forall ge md m m' fr fr' xs l,
  point_ok ge md m fr -> fr_at fr = Snapshot xs l \/ fr_at fr = Enter l None ->
  fr_fn fr' = fr_fn fr -> fr_at fr' = Enter l None -> point_ok ge md m' fr'.
Proof.
  intros ge md m m' fr fr' xs l H Ha Hf Ha'. unfold point_ok in *. cbv zeta in *. rewrite Hf, Ha'.
  destruct H as (E & HE & H). exists E. split; [exact HE|].
  destruct Ha as [Ha | Ha]; rewrite Ha in H; exact H.
Qed.

(** Nothing is found in an empty map. *)
Lemma lookup_nil_none : forall (A : Type) n, @lookup A n [] = None.
Proof. reflexivity. Qed.

(** Entering a basic block evaluates its phi nodes to bind incoming
    values before running its first instruction. Lemma [enter_point_ok]
    proves that evaluating those phi nodes preserves every fact
    surviving the incoming edge, so the frame remains [point_ok] at the
    block entry. *)
Lemma enter_point_ok : forall ge md c c' l from,
  checked_module md -> In (IFunc (fr_fn (c_frame c))) md ->
  fr_at (c_frame c) = Enter l from -> step ge c = Next c' ->
  point_ok ge md (c_mem c) (c_frame c) -> point_ok ge md (c_mem c') (c_frame c').
Proof.
  intros ge md c c' l from Hmd Hin Ha Hs H.
  destruct (step_enter _ _ _ _ _ Ha Hs) as (b & e & Hb & Hp & ->).
  unfold point_ok in H. cbv zeta in H. destruct H as (E & HE & Hpt). rewrite Ha in Hpt.
  set (f := fr_fn (c_frame c)) in *.
  destruct (module_func _ _ Hmd Hin) as (Hd & (b0 & bs & Eb & Hnoin) & _).
  pose proof (find_block_in _ _ _ Hb) as [Hbin Hbl].
  destruct (pass_fold _ _ _ _ _ HE Hd (fun b _ => lookup_nil_none _ (b_label b)) b Hbin)
    as (exits & out & Hsub & Hout & Hc).
  eapply point_ok_exec with (b := b) (out := out) (k := 0%nat); simpl; [exact HE | reflexivity | exact Hb
                                                         | rewrite <- Hbl; exact Hout | reflexivity | reflexivity |].
  eapply at_pos_between; [exists (S (length (b_insts b))); exact Hc| |].
  { rewrite <- Hbl. apply (entry_dom md); [exact Hmd | exact Hin | exact Hbin|].
    intros bp o Hbp Ho. apply (pass_exits_dom _ _ _ Hmd Hin HE _ _ Hbp). exact (Hsub _ _ Ho). }
  simpl.
  unfold entry_live. destruct from as [p|].
  - eapply phis_facts_hold; [exact Hp|]. intros fa Hfa.
    destruct Hpt as (bp & t & Hbp & Ht & Hl & Hpoll).
    destruct (find_block_in _ _ _ Hbp) as [Hbpin Hbpl].
    assert (Hset : In (edge_set exits (p, is_poll t))
                      (map (edge_set exits) (incoming (fn_blocks f) (b_label b)))).
    { apply in_map. rewrite Hbl, <- Hl, <- Hbpl. apply incoming_in; assumption. }
    pose proof (evidence_meet_in _ _ _ Hfa Hset) as Hfa'. unfold edge_set in Hfa'. simpl in Hfa'.
    destruct (is_poll t) eqn:Ep; [destruct Hfa'|].
    destruct (lookup p exits) as [fs|] eqn:Ex; [|destruct Hfa'].
    destruct Hpoll as [Hpoll | (out' & Ho' & Hh)]; [discriminate Hpoll|].
    rewrite (Hsub _ _ Ex) in Ho'. injection Ho' as <-. exact (Hh fa Hfa').
  - intros fa Hfa. exfalso.
    unfold entry_label in Hpt. rewrite Eb in Hpt. injection Hpt as Hl0.
    rewrite Hbl, (incoming_nil (fn_blocks f) l) in Hfa; [destruct (entry_kill_in _ _ _ Hfa) as [[] _]|].
    rewrite <- Hl0. rewrite Eb in Hnoin |- *. exact Hnoin.
Qed.

End Invariant.
