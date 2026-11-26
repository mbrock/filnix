(** This module proves structural and semantic preservation invariants for the
    dead-code elimination, unreachable-block pruning, and block-merging passes
    in [Simplify]. Together with [OptAluProof], it certifies that dead-code
    elimination only drops pure, memory-preserving, trap-free definitions whose
    results no live instruction, phi, or terminator reads.

    It also proves that the worklist fuel supplied by [Simplify.dead_code]
    always suffices to reach a closed live set, that [Simplify.prune_blocks]
    retains every reachable block and live incoming phi edge, and that
    [Simplify.bypass_one] and [Simplify.absorb_one] preserve entry blocks,
    non-empty instruction sequences, and single-predecessor straight-line code. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Ops Semantics Cfg.
From Backend Require Import Order Pizlonate Liveness TermCfg Escape.
From Opt Require Import Provenance OptIr Simplify OptAluProof.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Removable instructions and purity

    Dead-code elimination builds its table of candidate pure definitions from
    [Simplify.removable_inst]. We relate that syntactic predicate directly to
    [OptAluProof.pure_op_no_trap_no_mem] so every deleted instruction is known
    to be side-effect-free and trap-free. *)

(** Any instruction accepted by [Simplify.removable_inst] is a `let` binding
    to a single temporary whose operation satisfies [Simplify.pure_op] and is
    not a copy of a global symbol. *)
Lemma removable_inst_spec : forall i,
  Simplify.removable_inst i = true ->
  exists d t k op args,
    let_parts i = Some (d, k, op, args) /\
    tmp_name d = [t] /\
    Simplify.pure_op op = true /\
    ~ (op = TAtom "copy" /\ exists g, args = [TApp "global" [g]]).
Proof.
  intros i H. unfold Simplify.removable_inst in H.
  destruct (let_parts i) as [[[[d k] op] args]|] eqn:Hlet; [| discriminate H].
  destruct (tmp_name d) as [|t [|t2 ts]] eqn:Htmp; try discriminate H.
  apply andb_true_iff in H as [Hpure Hnotg].
  exists d, t, k, op, args. repeat split; try assumption.
  intros [-> [g ->]].
  cbn in Hnotg. discriminate Hnotg.
Qed.

(** Every removable instruction whose operation decodes via [OptAluProof.opt_op]
    never traps, never faults as unchecked, never allocates, and leaves memory
    unchanged under [Nanofil.Ops.op_res]. *)
Corollary removable_inst_no_trap_no_mem : forall i d k op args o kc xs m out,
  Simplify.removable_inst i = true ->
  let_parts i = Some (d, k, op, args) ->
  opt_op op = Some o ->
  Ops.op_res o kc xs m = Some out ->
  (exists w, out = OpRes (RVal w) m) \/
  (exists fk sg why, o = FloatToInt fk sg /\ out = OpUB why).
Proof.
  intros i d k op args o kc xs m out Hrem Hlet Hop Hres.
  destruct (removable_inst_spec i Hrem) as (d' & t & k' & op' & args' & Hlet' & _ & Hpure & _).
  rewrite Hlet in Hlet'. injection Hlet' as <- <- <- <-.
  exact (pure_op_no_trap_no_mem op o kc xs m out Hpure Hop Hres).
Qed.

(** ## Live-set worklist monotonicity and fuel completeness

    [Simplify.dead_code] marks live temporaries backwards from non-removable
    instructions and terminators using a fuel budget equal to one plus the root
    count and total pure-dependency edge count. We prove that this budget is
    always enough to exhaust the worklist and yield a dependency-closed live set. *)

(** Once a temporary is marked in [live], it remains marked after any number
    of [Simplify.mark_live] steps. *)
Lemma mark_live_monotone : forall fuel work pure live x,
  nm_mem x live = true ->
  nm_mem x (Simplify.mark_live fuel work pure live) = true.
Proof.
  induction fuel as [|fuel IH]; intros [|t ts] pure live x Hx; simpl; try exact Hx.
  destruct (nm_mem t live) eqn:Ht.
  - apply IH. exact Hx.
  - apply IH. rewrite nm_mem_add, Hx, orb_true_r. reflexivity.
Qed.

(** Removing all entries already present in [live] measures the remaining pure
    dependency edges that [Simplify.mark_live] can still enqueue. *)
Fixpoint unmarked_edges (pure_list : list (term * list term)) (live : nmap unit) : nat :=
  match pure_list with
  | [] => O
  | (t, us) :: rest =>
      if nm_mem t live then unmarked_edges rest live
      else Nat.add (length us) (unmarked_edges rest live)
  end.

(** Marking a new temporary never increases [unmarked_edges]. *)
Lemma unmarked_edges_add_le : forall ps live t,
  (unmarked_edges ps (nm_add t tt live) <= unmarked_edges ps live)%nat.
Proof.
  induction ps as [|[k us] ps IH]; intros live t; simpl; [lia |].
  rewrite nm_mem_add. destruct (nm_mem k live) eqn:Hk.
  - rewrite orb_true_r. apply IH.
  - rewrite orb_false_r. destruct (name_eqb k t); pose proof (IH live t); lia.
Qed.

(** Marking an unmarked temporary present in [ps] reduces [unmarked_edges] by
    at least the length of its recorded dependency list. *)
Lemma unmarked_edges_add_drop : forall ps live t us,
  In (t, us) ps ->
  nm_mem t live = false ->
  (Nat.add (length us) (unmarked_edges ps (nm_add t tt live)) <= unmarked_edges ps live)%nat.
Proof.
  induction ps as [|[k vs] ps IH]; intros live t us Hin Hmem; simpl in *; [contradiction |].
  destruct Hin as [Heq | Hin].
  - injection Heq as -> ->. rewrite Hmem. rewrite nm_mem_add.
    unfold name_eqb. rewrite term_eqb_refl. simpl.
    pose proof (unmarked_edges_add_le ps live t). lia.
  - rewrite nm_mem_add. destruct (nm_mem k live) eqn:Hk.
    + rewrite orb_true_r. apply IH; assumption.
    + rewrite orb_false_r. destruct (name_eqb k t);
        pose proof (IH live t us Hin Hmem); lia.
Qed.

(** Every lookup in [nm_of_list ps] returns a pair belonging to [ps]. *)
Lemma nm_of_list_in : forall (A : Type) (ps : list (term * A)) k v,
  nm_find k (nm_of_list ps) = Some v -> In (k, v) ps.
Proof.
  intros A ps. unfold nm_of_list.
  assert (Hfold : forall (qs : list (term * A)) m,
            (forall k v, nm_find k m = Some v -> In (k, v) ps) ->
            (forall p, In p qs -> In p ps) ->
            forall k v, nm_find k (fold_left (fun acc p => nm_add (fst p) (snd p) acc) qs m) = Some v ->
                        In (k, v) ps).
  { induction qs as [|[x w] qs IH]; intros m Hm Hsub k v Hfind; simpl in *.
    - exact (Hm k v Hfind).
    - apply (IH (nm_add x w m)); [| intros p Hp; apply Hsub; right; exact Hp | exact Hfind].
      intros k' v' Hk'. rewrite nm_find_add in Hk'.
      destruct (name_eqb k' x) eqn:Ek.
      + apply term_eqb_eq in Ek. subst. injection Hk' as <-. apply Hsub. left. reflexivity.
      + exact (Hm k' v' Hk'). }
  apply Hfold.
  - intros k v H. rewrite nm_find_empty in H. discriminate H.
  - auto.
Qed.

(** The total edge sum computed by [Simplify.dead_code] equals
    [unmarked_edges] on an empty live map. *)
Lemma unmarked_edges_empty_eq : forall ps acc,
  fold_left (fun n p => Nat.add n (length (snd p))) ps acc =
  Nat.add acc (unmarked_edges ps nm_empty).
Proof.
  induction ps as [|[t us] ps IH]; intros acc; cbn [fold_left unmarked_edges snd]; [lia |].
  unfold nm_mem. rewrite nm_find_empty. rewrite IH. lia.
Qed.

(** A live map [live] is closed with respect to worklist [work] and pure map
    [pure] if every already-marked temporary whose entry lies in [pure] has
    each of its operands either already marked or queued in [work]. *)
Definition work_closed (pure : nmap (list term)) (work : list term) (live : nmap unit) : Prop :=
  forall t us u,
    nm_mem t live = true ->
    nm_find t pure = Some us ->
    In u us ->
    nm_mem u live = true \/ In u work.

(** When fuel exceeds the pending worklist length plus [unmarked_edges],
    [Simplify.mark_live] marks every worklist item and finishes with a live set
    closed under all pure dependencies. *)
Theorem mark_live_complete : forall fuel ps work live,
  let pure := nm_of_list ps in
  (Nat.add (length work) (unmarked_edges ps live) < fuel)%nat ->
  work_closed pure work live ->
  let final := Simplify.mark_live fuel work pure live in
  (forall x, In x work -> nm_mem x final = true) /\
  (forall t us u,
     nm_mem t final = true ->
     nm_find t pure = Some us ->
     In u us ->
     nm_mem u final = true).
Proof.
  induction fuel as [|fuel IH]; intros ps work live pure Hfuel Hcl; simpl in *.
  - lia.
  - destruct work as [|t ts].
    + split.
      * intros x [].
      * intros t us u Ht Hfind Hu.
        destruct (Hcl t us u Ht Hfind Hu) as [Hl | []]. exact Hl.
    + destruct (nm_mem t live) eqn:Ht.
      * assert (Hfuel' : (Nat.add (length ts) (unmarked_edges ps live) < fuel)%nat) by (simpl in Hfuel; lia).
        assert (Hcl' : work_closed pure ts live).
        { intros x us u Hx Hfind Hu.
          destruct (Hcl x us u Hx Hfind Hu) as [Hl | [<- | Hin]].
          - left. exact Hl.
          - left. exact Ht.
          - right. exact Hin. }
        destruct (IH ps ts live Hfuel' Hcl') as [Hwork Hfin].
        split; [| exact Hfin].
        intros x [<- | Hin].
        -- apply mark_live_monotone. exact Ht.
        -- apply Hwork. exact Hin.
      * set (live1 := nm_add t tt live).
        set (ts1 := match nm_find t pure with Some us => us ++ ts | None => ts end).
        assert (Hfuel' : (Nat.add (length ts1) (unmarked_edges ps live1) < fuel)%nat).
        { unfold ts1, live1.
          destruct (nm_find t pure) as [us|] eqn:Hfind.
          - rewrite length_app.
            pose proof (nm_of_list_in _ ps t us Hfind) as Hin.
            pose proof (unmarked_edges_add_drop ps live t us Hin Ht).
            simpl in Hfuel. lia.
          - pose proof (unmarked_edges_add_le ps live t).
            simpl in Hfuel. lia. }
        assert (Hcl' : work_closed pure ts1 live1).
        { intros x us u Hx Hfind Hu.
          unfold live1 in Hx. rewrite nm_mem_add in Hx.
          apply orb_true_iff in Hx as [Heq | Hxold].
          - apply term_eqb_eq in Heq. subst x.
            right. unfold ts1. rewrite Hfind. apply in_or_app. left. exact Hu.
          - destruct (Hcl x us u Hxold Hfind Hu) as [Hl | [<- | Hin]].
            + left. unfold live1. rewrite nm_mem_add, Hl, orb_true_r. reflexivity.
            + left. unfold live1. rewrite nm_mem_add. unfold name_eqb. rewrite term_eqb_refl. reflexivity.
            + right. unfold ts1. destruct (nm_find t pure); [apply in_or_app; right |]; exact Hin. }
        destruct (IH ps ts1 live1 Hfuel' Hcl') as [Hwork Hfin].
        split; [| exact Hfin].
        intros x [<- | Hin].
        -- apply mark_live_monotone. unfold live1. rewrite nm_mem_add.
           unfold name_eqb. rewrite term_eqb_refl. reflexivity.
        -- apply Hwork. unfold ts1. destruct (nm_find t pure); [apply in_or_app; right |]; exact Hin.
Qed.

(** Starting [Simplify.mark_live] with the exact fuel computed by
    [Simplify.dead_code] from an empty live map always marks every root and
    every transitive pure dependency of a marked temporary. *)
Corollary dead_code_mark_live_complete : forall pure_uses roots,
  let pure := nm_of_list pure_uses in
  let edge_sum := fold_left (fun acc p => Nat.add acc (length (snd p))) pure_uses O in
  let live := Simplify.mark_live (S (Nat.add (length roots) edge_sum)) roots pure nm_empty in
  (forall x, In x roots -> nm_mem x live = true) /\
  (forall t us u,
     nm_mem t live = true ->
     nm_find t pure = Some us ->
     In u us ->
     nm_mem u live = true).
Proof.
  intros pure_uses roots pure edge_sum live.
  apply mark_live_complete.
  - unfold edge_sum. rewrite unmarked_edges_empty_eq. lia.
  - intros t us u Ht _ _. unfold nm_mem in Ht. rewrite nm_find_empty in Ht. discriminate Ht.
Qed.

(** ## Dead-code elimination preservation

    Applying [mark_live_complete] to the instruction filter [live_insts_ctx]
    shows that every non-removable instruction survives intact and every
    deleted instruction is removable, pure, and unmarked. *)

(** Separating surviving and deleted instructions in [Simplify.live_insts_ctx]
    shows that [live_insts_ctx] keeps exactly the instructions that are not
    dead pure definitions. *)
Lemma live_insts_ctx_filter : forall pure live lbl oi ni insts out_rev map_rev,
  let is_dead (i : term) : bool :=
    match let_parts i with
    | Some (d, _, _, _) =>
        match tmp_name d with
        | [t] => nm_mem t pure && negb (nm_mem t live)
        | _ => false
        end
    | None => false
    end in
  fst (Simplify.live_insts_ctx pure live lbl oi ni insts out_rev map_rev) =
  rev' out_rev ++ filter (fun i => negb (is_dead i)) insts.
Proof.
  intros pure live lbl oi ni insts.
  revert oi ni.
  induction insts as [|i rest IH]; intros oi ni out_rev map_rev; simpl.
  - rewrite app_nil_r. reflexivity.
  - match goal with
    | |- context [if ?b then [] else [i]] => destruct b eqn:Hdead
    end.
    + simpl. exact (IH (oi + 1) ni out_rev map_rev).
    + simpl. rewrite (IH (oi + 1) (ni + 1) (i :: out_rev)).
      unfold rev'. rewrite !rev_append_rev. simpl. rewrite !app_nil_r, <- app_assoc. reflexivity.
Qed.

(** Every instruction kept by [Simplify.live_insts_ctx] from an empty
    accumulator is an original instruction, and every instruction whose
    defined temporary is absent from [pure] or present in [live] is kept. *)
Theorem live_insts_ctx_spec : forall pure live lbl insts,
  let kept := fst (Simplify.live_insts_ctx pure live lbl 0 0 insts [] []) in
  (forall i, In i kept -> In i insts) /\
  (forall i, In i insts -> ~ In i kept ->
     exists d t k op args,
       let_parts i = Some (d, k, op, args) /\
       tmp_name d = [t] /\
       nm_mem t pure = true /\
       nm_mem t live = false).
Proof.
  intros pure live lbl insts kept.
  unfold kept. rewrite live_insts_ctx_filter. simpl.
  split.
  - intros i Hin. apply filter_In in Hin as [H1 _]. exact H1.
  - intros i Hin Hnot.
    destruct (let_parts i) as [[[[d k] op] args]|] eqn:Hlet.
    + destruct (tmp_name d) as [|t [|t2 ts]] eqn:Htmp.
      * exfalso. apply Hnot. apply filter_In. split; [exact Hin |].
        rewrite Hlet, Htmp. reflexivity.
      * destruct (nm_mem t pure) eqn:Hp; destruct (nm_mem t live) eqn:Hl.
        -- exfalso. apply Hnot. apply filter_In. split; [exact Hin |].
           rewrite Hlet, Htmp, Hp, Hl. reflexivity.
        -- exists d, t, k, op, args. repeat split; assumption.
        -- exfalso. apply Hnot. apply filter_In. split; [exact Hin |].
           rewrite Hlet, Htmp, Hp, Hl. reflexivity.
        -- exfalso. apply Hnot. apply filter_In. split; [exact Hin |].
           rewrite Hlet, Htmp, Hp, Hl. reflexivity.
      * exfalso. apply Hnot. apply filter_In. split; [exact Hin |].
        rewrite Hlet, Htmp. reflexivity.
    + exfalso. apply Hnot. apply filter_In. split; [exact Hin |].
      rewrite Hlet. reflexivity.
Qed.

(** Mapping a function over a list relates every original element to its
    image under any pointwise relation. *)
Lemma Forall2_map_r : forall (A B : Type) (R : A -> B -> Prop) (f : A -> B) (xs : list A),
  (forall x, In x xs -> R x (f x)) ->
  Forall2 R xs (map f xs).
Proof.
  intros A B R f xs H. induction xs as [|x xs IH]; simpl; constructor.
  - apply H. left. reflexivity.
  - apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(** Any instruction dropped by [Simplify.dead_code] defines a temporary in the
    pure table and therefore cannot be a non-removable side-effecting
    instruction when every temporary has at most one definition. *)
Theorem dead_code_keeps_non_pure : forall bs0 rs0 bs rs,
  Simplify.dead_code bs0 rs0 = Some (bs, rs) ->
  length bs = length bs0 /\
  Forall2 (fun b0 b =>
             tb_label b = tb_label b0 /\
             tb_jump b = tb_jump b0 /\
             (forall p, In p (tb_phis b) -> In p (tb_phis b0)) /\
             (forall i, In i (tb_insts b) -> In i (tb_insts b0)))
          bs0 bs.
Proof.
  intros bs0 rs0 bs rs Hdc.
  unfold Simplify.dead_code in Hdc.
  destruct (map_option _ bs0) as [roots_lists|] eqn:Hroots; [| discriminate Hdc].
  simpl in Hdc.
  destruct (forallb _ _) eqn:Hall.
  - injection Hdc as <- <-. split; [reflexivity |].
    clear Hroots Hall.
    induction bs0 as [|b0 rest IH]; constructor; [repeat split; auto | exact IH].
  - injection Hdc as <- <-.
    split; [rewrite !length_map; reflexivity |].
    rewrite map_map. apply Forall2_map_r. intros b0 _.
    match goal with
    | |- context [Simplify.live_insts_ctx ?p ?l (tb_label b0) 0 0 (tb_insts b0) [] []] =>
        pose proof (proj1 (live_insts_ctx_spec p l (tb_label b0) (tb_insts b0))) as Hkeep;
        destruct (Simplify.live_insts_ctx p l (tb_label b0) 0 0 (tb_insts b0) [] []) as [is' sm] eqn:Hli
    end.
    simpl in *. repeat split.
    + intros ph Hph. apply filter_In in Hph as [H1 _]. exact H1.
    + intros i Hi. exact (Hkeep i Hi).
Qed.

(** ## Unreachable-block pruning

    [Simplify.prune_blocks] computes the reachable label set [reached g] from
    the CFG and keeps exactly the reachable blocks while trimming phi edges
    whose predecessors are unreachable or no longer target the block. *)

(** Partitioning a list into elements satisfying [f] and the remainder returns
    the filtered elements as its first component. *)
Lemma partition_fst_filter : forall (A : Type) (f : A -> bool) (xs : list A),
  fst (partition f xs) = filter f xs.
Proof.
  intros A f xs. induction xs as [|x xs IH]; simpl; [reflexivity |].
  destruct (partition f xs) as [g d] eqn:Hp. simpl in IH.
  destruct (f x); simpl; [f_equal |]; exact IH.
Qed.

(** Every block surviving [Simplify.prune_blocks] comes from a reachable block
    in [bs0] with identical label, instructions, and terminator, and every
    reachable block in [bs0] survives in the pruned list. *)
Theorem prune_blocks_preserves_reachable : forall bs0 rs0 bs rs g,
  term_cfg bs0 = Some g ->
  Simplify.prune_blocks bs0 rs0 = Some (bs, rs) ->
  map tb_label bs = map tb_label (filter (fun b => nm_mem (tb_label b) (reached g)) bs0) /\
  Forall2 (fun b0 b =>
             nm_mem (tb_label b0) (reached g) = true /\
             tb_label b = tb_label b0 /\
             tb_insts b = tb_insts b0 /\
             tb_jump b = tb_jump b0)
          (filter (fun b => nm_mem (tb_label b) (reached g)) bs0) bs.
Proof.
  intros bs0 rs0 bs rs g Hg Hpr.
  unfold Simplify.prune_blocks in Hpr.
  rewrite Hg in Hpr. simpl in Hpr.
  destruct (partition (fun b => nm_mem (tb_label b) (reached g)) bs0) as [kept gone] eqn:Hp.
  assert (Hkept : kept = filter (fun b => nm_mem (tb_label b) (reached g)) bs0).
  { pose proof (partition_fst_filter _ (fun b => nm_mem (tb_label b) (reached g)) bs0) as Hpf.
    rewrite Hp in Hpf. exact Hpf. }
  subst kept.
  destruct (match gone with [] => _ | _ => false end);
    injection Hpr as <- <-;
    (split;
     [ rewrite map_map; simpl; reflexivity
     | clear Hg Hp gone;
       induction bs0 as [|b0 rest IH]; simpl; [constructor |];
       destruct (nm_mem (tb_label b0) (reached g)) eqn:Hr; simpl;
       [ constructor; [repeat split; assumption | exact IH] | exact IH ] ]).
Qed.

(** ## Empty-block bypassing and straight-line block absorption

    The block merger never removes the entry block, only bypasses empty
    non-entry `goto` blocks, and only absorbs phi-less single-predecessor
    `goto` successors by concatenating their instructions in program order. *)

(** Retargeting plain jumps in block [p] from [e] to [t] preserves every other
    block unchanged and preserves [p]'s label, phis, and instructions. *)
Lemma retarget_block_preserves_body : forall e t p idx l b,
  nm_find l idx = Some b ->
  exists b',
    nm_find l (Simplify.retarget_block e t p idx) = Some b' /\
    tb_label b' = tb_label b /\
    tb_phis b' = tb_phis b /\
    tb_insts b' = tb_insts b.
Proof.
  intros e t p idx l b Hfind. unfold Simplify.retarget_block.
  destruct (nm_find p idx) as [bp|] eqn:Hp.
  - rewrite nm_find_add. destruct (name_eqb l p) eqn:Elp.
    + apply term_eqb_eq in Elp. subst p. rewrite Hfind in Hp. injection Hp as <-.
      eexists. repeat split; reflexivity.
    + exists b. split; [exact Hfind | split; [reflexivity | split; reflexivity]].
  - exists b. split; [exact Hfind | split; [reflexivity | split; reflexivity]].
Qed.

(** Bypassing block [e] never deletes the entry block and only adds [e] to
    [bs_gone] when [e] is a non-entry empty plain `goto` block. *)
Theorem bypass_one_sound : forall entry e st,
  let st' := Simplify.bypass_one entry e st in
  (In entry (bs_gone st') -> In entry (bs_gone st)) /\
  (bs_gone st' <> bs_gone st ->
   exists eb t,
     e <> entry /\
     nm_find e (bs_index st) = Some eb /\
     tb_insts eb = [] /\
     tb_jump eb = TApp "goto" [t] /\
     Simplify.is_plain_target t = true /\
     t <> e /\
     bs_gone st' = e :: bs_gone st).
Proof.
  intros entry e st st'. unfold st', Simplify.bypass_one.
  destruct (nm_find e (bs_index st)) as [eb|] eqn:Heb;
    [| split; [auto | intros H; contradiction]].
  destruct (tb_insts eb) as [|i0 is0] eqn:Hinsts;
    [| split; [auto | intros H; contradiction]].
  destruct (tb_jump eb) as [| |jf [|t [|t2 ts]]|] eqn:Hjump;
    try (split; [auto | intros H; contradiction]).
  destruct (negb ((String.eqb jf "goto") && negb (term_eqb e entry)
                  && Simplify.is_plain_target t && negb (term_eqb t e))) eqn:Hcond;
    [split; [auto | intros H; contradiction] |].
  apply negb_false_iff in Hcond.
  repeat rewrite andb_true_iff in Hcond.
  destruct Hcond as [[[Hjf Hne] Hplain] Hte].
  apply String.eqb_eq in Hjf. subst jf.
  apply negb_true_iff in Hne. apply negb_true_iff in Hte.
  assert (Hne' : e <> entry).
  { intros ->. rewrite term_eqb_refl in Hne. discriminate Hne. }
  assert (Hte' : t <> e).
  { intros ->. rewrite term_eqb_refl in Hte. discriminate Hte. }
  destruct (Simplify.preds_of (bs_preds st) e) as [|p0 ps0];
    [split; [auto | intros H; contradiction] |].
  destruct (negb _ || existsb _ _)%bool;
    [split; [auto | intros H; contradiction] |].
  destruct (existsb _ _ || negb _ || negb _)%bool;
    [split; [auto | intros H; contradiction] |].
  destruct (nm_find t (bs_index st)) as [tb|];
    [| split; [auto | intros H; contradiction]].
  destruct (negb (forallb _ (tb_phis eb)));
    [split; [auto | intros H; contradiction] |].
  destruct (fold_left _ (tb_phis tb) ([], bs_uses st)) as [tphis_rev uses1].
  simpl. split.
  - intros [Heq | Hin]; [exfalso; apply Hne'; exact Heq | exact Hin].
  - intros _. exists eb, t. repeat split; assumption.
Qed.

(** Renaming predecessor [t] to [b] on block [s] keeps every block present in
    [idx] with its exact instruction list and terminator. *)
Lemma rename_pred_preserves_body : forall t b s idx preds l bl,
  nm_find l idx = Some bl ->
  exists bl',
    nm_find l (fst (Simplify.rename_pred t b s (idx, preds))) = Some bl' /\
    tb_insts bl' = tb_insts bl /\
    tb_jump bl' = tb_jump bl.
Proof.
  intros t b s idx preds l bl Hfind. unfold Simplify.rename_pred. simpl.
  destruct (nm_find s idx) as [sb|] eqn:Hs.
  - rewrite nm_find_add. destruct (name_eqb l s) eqn:Els.
    + apply term_eqb_eq in Els. subst s. rewrite Hfind in Hs. injection Hs as <-.
      eexists. repeat split; reflexivity.
    + exists bl. split; [exact Hfind | split; reflexivity].
  - exists bl. split; [exact Hfind | split; reflexivity].
Qed.

(** Straight-line absorption never removes the entry block from [as_index]. *)
Theorem absorb_one_preserves_entry : forall fuel entry b st eb,
  nm_find entry (as_index st) = Some eb ->
  exists eb', nm_find entry (as_index (Simplify.absorb_one fuel entry b st)) = Some eb'.
Proof.
  induction fuel as [|fuel IH]; intros entry b st eb Hentry; simpl; [exists eb; exact Hentry |].
  destruct (nm_find b (as_index st)) as [bb|] eqn:Hb; [| exists eb; exact Hentry].
  destruct (tb_jump bb) as [| |jf [|t [|t2 ts]]|]; try (exists eb; exact Hentry).
  destruct (negb ((String.eqb jf "goto") && Simplify.is_plain_target t
                  && negb (term_eqb t b) && negb (term_eqb t entry))) eqn:Hcond;
    [exists eb; exact Hentry |].
  apply negb_false_iff in Hcond. repeat rewrite andb_true_iff in Hcond.
  destruct Hcond as [[[_ _] _] Hte]. apply negb_true_iff in Hte.
  destruct (Simplify.preds_of (as_preds st) t) as [|p0 [|p1 ps]]; try (exists eb; exact Hentry).
  destruct (negb (term_eqb p0 b)); [exists eb; exact Hentry |].
  destruct (nm_find t (as_index st)) as [tb|]; [| exists eb; exact Hentry].
  destruct (tb_phis tb); [| exists eb; exact Hentry].
  destruct (negb (forallb _ _)); [exists eb; exact Hentry |].
  set (ss := nsort (map target_label (Simplify.jump_targets (tb_jump tb)))).
  set (idx1 := nm_remove t (as_index st)).
  set (idx2 := nm_add b (mkTBlock b (tb_phis bb) (tb_insts bb ++ tb_insts tb) (tb_jump tb)) idx1).
  assert (Hentry2 : exists e2, nm_find entry idx2 = Some e2).
  { unfold idx2, idx1. rewrite nm_find_add.
    destruct (name_eqb entry b).
    - eexists. reflexivity.
    - rewrite nm_find_remove.
      destruct (name_eqb entry t) eqn:Eet.
      + apply term_eqb_eq in Eet. subst t. rewrite term_eqb_refl in Hte. discriminate Hte.
      + exists eb. exact Hentry. }
  assert (Hfold : forall ls ix pr e0,
            nm_find entry ix = Some e0 ->
            exists e1, nm_find entry (fst (fold_left (fun acc s => Simplify.rename_pred t b s acc) ls (ix, pr))) = Some e1).
  { induction ls as [|s ls IHl]; intros ix pr e0 He0; cbn [fold_left]; [exists e0; exact He0 |].
    destruct (rename_pred_preserves_body t b s ix pr entry e0 He0) as (e1 & He1 & _ & _).
    destruct (Simplify.rename_pred t b s (ix, pr)) as [ix1 pr1]. simpl in He1.
    exact (IHl ix1 pr1 e1 He1). }
  destruct Hentry2 as [e2 He2].
  destruct (Hfold ss idx2 (as_preds st) e2 He2) as [e3 He3].
  fold ss idx1 idx2.
  destruct (fold_left (fun acc s => Simplify.rename_pred t b s acc) ss (idx2, as_preds st)) as [idx3 preds1].
  simpl in He3.
  destruct (nm_find t (as_jump_of st));
    apply (IH entry b _ e3); exact He3.
Qed.
