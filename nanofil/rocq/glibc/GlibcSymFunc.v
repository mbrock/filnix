(** A function proof can follow several blocks before returning to the
    ordinary step tactics. This executor carries the symbolic environment,
    owned memory and pending conditions across those blocks. Unknown branches
    produce two proof goals, while cut labels and fuel bound the traversal.

    A jump must read all incoming values before changing any temporary.
    The executor preserves this [[phi]] assignment rule when it crosses
    blocks, and its theorem proves the resulting [[weakest-precondition]]. *)

From iris.proofmode Require Import proofmode reduction.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic ExternalCalls StepRules.
From Glibc Require Import Fix GlibcTactics GlibcSym.
Import ListNotations LG0 LG0.L.
Open Scope Z_scope.

(** ## Following control flow

    A block may choose its incoming values according to which block ran
    before it, so the executor records that label. When a branch condition
    remains unknown, the proof must cover both possible paths. *)

(** A leaf names its predecessor, and a split retains both possible paths. *)
Inductive stree : Type :=
  | TLeaf (l : name) (lf : leaf)
  | TSplit (c : zexp) (yes no : stree).

(** All incoming operands are read from the environment before the edge. *)
Fixpoint sphis (ge : genv) (fs : facts) (se : senv) (from : name)
    (ps : list phi) : option (list (name * sword)) :=
  match ps with
  | [] => Some []
  | Phi d k pairs :: rest =>
      match lookup from pairs with
      | None => None
      | Some v =>
          match svalue ge fs se k v, sphis ge fs se from rest with
          | Some w, Some ws => Some ((d, w) :: ws)
          | _, _ => None
          end
      end
  end.

(** Binding already evaluated operands preserves parallel assignment on the edge. *)
Definition sbinds (ws : list (name * sword)) (s : sstate) : sstate :=
  fold_left (fun s nw => sbind (fst nw) (snd nw) s) ws s.

(** A known interval decides a branch only when it excludes zero or contains only zero. *)
Definition branch_choice (fs : facts) (c : zexp) : option bool :=
  match zrange fs c with
  | Some (lo, hi) =>
      if (hi <? 0) || (0 <? lo) then Some true
      else if (lo =? 0) && (hi =? 0) then Some false else None
  | None => None
  end.

(** Boolean conditions give each successor an exact value for later comparisons. *)
Definition branch_facts (fs : facts) (c : zexp) (yes : bool) : facts :=
  match zrange fs c with
  | Some (lo, hi) =>
      if (0 <=? lo) && (hi <=? 1) then
        mkFacts (mkBound c (if yes then 1 else 0) (if yes then 2 else 1) :: f_bounds fs) (f_caps fs)
      else fs
  | None => fs
  end.

(** A failed lookup or phi evaluation leaves the original jump for the caller. *)
Definition sym_follow (ge : genv) (f : func) (cuts : list name)
    (next : facts -> sstate -> name -> list inst -> jump -> stree)
    (fs : facts) (s : sstate) (l : name) (t : target) : stree :=
  if existsb (name_eqb (edge_label t)) cuts then TLeaf l (LGoto t s)
  else match find_block (edge_label t) (fn_blocks f) with
  | None => TLeaf l (LGoto t s)
  | Some b =>
      match sphis ge fs (st_env s) l (b_phis b) with
      | None => TLeaf l (LGoto t s)
      | Some ws => next fs (sbinds ws s) (edge_label t) (b_insts b) (b_jump b)
      end
  end.

(** Fuel counts crossed edges; the current block still executes when fuel is zero. *)
Fixpoint sym_func (ge : genv) (f : func) (cuts : list name) (fuel : nat)
    (fs : facts) (s : sstate) (l : name) (insts : list inst) (j : jump) : stree :=
  let lf := sym_exec ge fs s insts j in
  match fuel with
  | O => TLeaf l lf
  | S fuel' =>
      let follow := sym_follow ge f cuts (sym_func ge f cuts fuel') in
      match lf with
      | LGoto t s' => follow fs s' l t
      | LBranch c t1 t2 s' =>
          match branch_choice fs c with
          | Some true => follow fs s' l t1
          | Some false => follow fs s' l t2
          | None => TSplit c
              (follow (branch_facts fs c true) s' l t1)
              (follow (branch_facts fs c false) s' l t2)
          end
      | _ => TLeaf l lf
      end
  end.

(** ## Parallel assignments and branch facts

    Crossing an edge must preserve the meaning of every known temporary.
    These lemmas connect the symbolic assignments and successor facts to
    the concrete environment used by the machine's entry rule. *)

(** Applying several symbolic bindings produces the same concrete sequence of puts. *)
Lemma apply_ups_sbinds ρ ws s e :
  apply_ups ρ (st_ups (sbinds ws s)) e =
  apply_ups ρ ws (apply_ups ρ (st_ups s) e).
Proof.
  revert s. induction ws as [|[d w] ws IH]; intros s; cbn [sbinds fold_left fst snd].
  - reflexivity.
  - rewrite IH apply_ups_sbind. reflexivity.
Qed.

(** Phi bindings preserve the owned heap and every condition accumulated before entry. *)
Lemma sbinds_resources ws s :
  st_heap (sbinds ws s) = st_heap s /\ st_obs (sbinds ws s) = st_obs s.
Proof.
  revert s. induction ws as [|[d w] ws IH]; intros s; cbn [sbinds fold_left fst snd].
  - auto.
  - exact (IH (sbind d w s)).
Qed.

(** Each bound destination has its computed value in the resulting environment. *)
Lemma sbinds_models ρ ws s e : env_models ρ (st_env s) (apply_ups ρ (st_ups s) e) ->
  env_models ρ (st_env (sbinds ws s)) (apply_ups ρ (st_ups (sbinds ws s)) e).
Proof.
  revert s. induction ws as [|[d w] ws IH]; intros s H; cbn [sbinds fold_left fst snd].
  - exact H.
  - apply IH. rewrite apply_ups_sbind. apply env_models_put. exact H.
Qed.

(** Evaluating phis symbolically agrees with reading every operand before the first put. *)
Lemma sphis_sound ρ ge fs se from ps ws e0 :
  facts_hold ρ fs -> env_models ρ se e0 -> sphis ge fs se from ps = Some ws ->
  forall e, fold_left (fun acc ph =>
    match acc, ph with
    | Some e', Phi d k pairs =>
        match lookup from pairs with
        | Some v => match value_x ge e0 k v with Some w => Some (put d w e') | None => None end
        | None => None end
    | None, _ => None end) ps (Some e) = Some (apply_ups ρ ws e).
Proof.
  intros Hfs Henv. revert ws. induction ps as [|[d k pairs] ps IH]; intros ws H e.
  - injection H as <-. reflexivity.
  - cbn [sphis] in H. destruct (lookup from pairs) as [v|] eqn:Hv; [|discriminate].
    destruct (svalue ge fs se k v) as [w|] eqn:Hw; [|discriminate].
    destruct (sphis ge fs se from ps) as [rest|] eqn:Hr; [|discriminate].
    injection H as <-. cbn [fold_left]. rewrite Hv (svalue_sound _ _ _ _ _ _ _ _ Hfs Henv Hw).
    exact (IH rest eq_refl (put d (wden ρ w) e)).
Qed.

(** A decided branch has the selected truth value under every valuation satisfying the facts. *)
Lemma branch_choice_sound ρ fs c yes : facts_hold ρ fs -> branch_choice fs c = Some yes ->
  if yes then zden ρ c <> 0 else zden ρ c = 0.
Proof.
  intros Hfs. unfold branch_choice.
  destruct (zrange fs c) as [[lo hi]|] eqn:E; [|discriminate].
  pose proof (zrange_sound _ _ _ _ _ Hfs E) as Hrange.
  destruct ((hi <? 0) || (0 <? lo)) eqn:En.
  - intros H. injection H as <-. apply orb_true_iff in En.
    destruct En; apply Z.ltb_lt in H; lia.
  - destruct ((lo =? 0) && (hi =? 0)) eqn:Ez; [|discriminate].
    intros H. injection H as <-. apply andb_true_iff in Ez as [Hlo Hhi].
    apply Z.eqb_eq in Hlo, Hhi. lia.
Qed.

(** A successor's boolean bound follows from its branch assumption and the old facts. *)
Lemma branch_facts_sound ρ fs c (yes : bool) : facts_hold ρ fs ->
  (if yes then zden ρ c <> 0 else zden ρ c = 0) -> facts_hold ρ (branch_facts fs c yes).
Proof.
  intros Hfs Hc. unfold branch_facts.
  destruct (zrange fs c) as [[lo hi]|] eqn:E; [|exact Hfs].
  destruct ((0 <=? lo) && (hi <=? 1)) eqn:Eb; [|exact Hfs].
  pose proof (zrange_sound _ _ _ _ _ Hfs E) as Hrange.
  apply andb_true_iff in Eb as [Hlo Hhi]. apply Z.leb_le in Hlo, Hhi.
  destruct Hfs as [Hb Hcaps]. split; [constructor; [destruct yes; cbn; lia|exact Hb]|exact Hcaps].
Qed.

(** ## Soundness of a run tree

    The caller proves each path under its branch assumptions and receives
    the resources described by its final leaf. The soundness proof links
    these continuations using the block theorem and the machine's entry rule. *)

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance sym_func_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A split asks for both continuations, each under the condition selecting that path. *)
Fixpoint stree_den ρ f e ls Φ (t : stree) : iProp Σ :=
  match t with
  | TLeaf l lf => leaf_den registry wi ge ρ f e ls l Φ lf
  | TSplit c yes no =>
      (⌜zden ρ c <> 0⌝ -∗ stree_den ρ f e ls Φ yes) ∧
      (⌜zden ρ c = 0⌝ -∗ stree_den ρ f e ls Φ no)
  end.

(** A continued path supplies the conditions needed before entry as well as its remaining execution. *)
Definition run_den ρ f e ls l insts j Φ s : iProp Σ :=
  ⌜obs_den wi ρ (st_obs s)⌝ ∗
  (heap_den ρ (st_heap s) -∗
   ⌜env_models ρ (st_env s) (apply_ups ρ (st_ups s) e)⌝ -∗
   WP (ERun (mkFrame f (apply_ups ρ (st_ups s) e) ls None (Exec l insts j)) : gexpr) {{ Φ }}).

(** When a jump reaches another block, its incoming values agree with the machine's entry rule. *)
Lemma sym_follow_rule ρ f e ls cuts next fs s l t Φ :
  facts_hold ρ fs ->
  (forall fs' s' l' insts j, facts_hold ρ fs' ->
    stree_den ρ f e ls Φ (next fs' s' l' insts j) ⊢ run_den ρ f e ls l' insts j Φ s') ->
  stree_den ρ f e ls Φ (sym_follow ge f cuts next fs s l t) ⊢
  leaf_den registry wi ge ρ f e ls l Φ (LGoto t s).
Proof.
  intros Hfs IH. unfold sym_follow.
  destruct (existsb (name_eqb (edge_label t)) cuts); [done|].
  destruct (find_block (edge_label t) (fn_blocks f)) as [b|] eqn:Hb; [|done].
  destruct (sphis ge fs (st_env s) l (b_phis b)) as [ws|] eqn:Hp; [|done].
  destruct (sbinds_resources ws s) as [Hheap Hobs].
  iIntros "H". iDestruct (IH with "H") as "[%Ho HK]"; [exact Hfs|].
  unfold run_den. cbn [leaf_den]. rewrite Hobs in Ho.
  iSplit; [done|]. iNext. iIntros "Hheap %He".
  iApply (wp_enter registry wi ge _ _ _ _ _ b (apply_ups ρ (st_ups (sbinds ws s)) e)); [exact Hb| |].
  - rewrite apply_ups_sbinds. unfold phis_env.
    exact (sphis_sound _ _ _ _ _ _ _ _ Hfs He Hp _).
  - iNext. iApply ("HK" with "[Hheap] []").
    + rewrite Hheap. iFrame.
    + iPureIntro. apply sbinds_models. exact He.
Qed.

(** Proving the final paths also proves the conditions and execution required at the starting block. *)
Lemma sym_func_rule ρ f e ls cuts fuel fs s l insts j Φ :
  facts_hold ρ fs ->
  stree_den ρ f e ls Φ (sym_func ge f cuts fuel fs s l insts j) ⊢
  run_den ρ f e ls l insts j Φ s.
Proof.
  revert fs s l insts j. induction fuel as [|fuel IH]; intros fs s l insts j Hfs.
  all: assert (Hleaf : stree_den ρ f e ls Φ (sym_func ge f cuts
      ltac:(first [exact (S fuel) | exact O]) fs s l insts j) ⊢
      leaf_den registry wi ge ρ f e ls l Φ (sym_exec ge fs s insts j)).
  - done.
  - iIntros "H". iDestruct (Hleaf with "H") as "H".
    iDestruct (leaf_den_obs with "H") as "[%Ho H]".
    destruct (sym_exec_obs ge fs insts j s) as [os E]. rewrite E in Ho.
    apply Forall_app in Ho as [Ho _]. unfold run_den. iSplit; [done|].
    iIntros "Hheap %He". iApply (sym_exec_rule registry wi ge ρ fs insts j s f e ls l Φ Hfs He with "Hheap H").
  - cbn [sym_func]. destruct (sym_exec ge fs s insts j) as [t ss|c t1 t2 ss|why rest jj ss].
    + apply sym_follow_rule; assumption.
    + destruct (branch_choice fs c) as [yes|] eqn:Ec.
      * pose proof (branch_choice_sound _ _ _ _ Hfs Ec) as Hc.
        destruct yes; iIntros "H";
          iDestruct (sym_follow_rule with "H") as "H"; try exact Hfs; try exact IH.
        -- cbn [leaf_den]. rewrite (proj2 (Z.eqb_neq _ _) Hc). done.
        -- cbn [leaf_den]. rewrite Hc Z.eqb_refl. done.
      * cbn [stree_den]. destruct (Z.eq_dec (zden ρ c) 0) as [Hc|Hc].
        -- iIntros "[_ H]". iDestruct ("H" with "[]") as "H"; [done|].
           iDestruct (sym_follow_rule with "H") as "H";
             [apply branch_facts_sound; assumption|exact IH|].
           cbn [leaf_den]. rewrite Hc Z.eqb_refl. done.
        -- iIntros "[H _]". iDestruct ("H" with "[]") as "H"; [done|].
           iDestruct (sym_follow_rule with "H") as "H";
             [apply branch_facts_sound; assumption|exact IH|].
           cbn [leaf_den]. rewrite (proj2 (Z.eqb_neq _ _) Hc). done.
    + done.
  - iIntros "H". iDestruct (Hleaf with "H") as "H".
    iDestruct (leaf_den_obs with "H") as "[%Ho H]".
    destruct (sym_exec_obs ge fs insts j s) as [os E]. rewrite E in Ho.
    apply Forall_app in Ho as [Ho _]. unfold run_den. iSplit; [done|].
    iIntros "Hheap %He". iApply (sym_exec_rule registry wi ge ρ fs insts j s f e ls l Φ Hfs He with "Hheap H").
Qed.

(** One application of this theorem justifies all blocks traversed by the computation. *)
Theorem sym_func_sound fs se h f e ls cuts fuel l insts j ρ Φ :
  facts_hold ρ fs -> env_models ρ se e ->
  heap_den ρ h -∗ stree_den ρ f e ls Φ (sym_func ge f cuts fuel fs (mkSState se [] h []) l insts j) -∗
  WP (ERun (mkFrame f e ls None (Exec l insts j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs He. iIntros "Hheap H".
  iDestruct (sym_func_rule with "H") as "[_ HK]"; [exact Hfs|].
  iApply ("HK" with "Hheap []"). done.
Qed.

End sound.

(** ## Returning named proof contexts

    The executor can return a proof context directly instead of rebuilding it
    with framing tactics. A single relation records which caller hypotheses
    become available after a step, so each path can reuse that relation. *)

Import environments Term.
Open Scope Z_scope.

(** Matching a returned cell consumes its old name, so no path assigns the same name twice. *)
Fixpoint sym_pick_name (fs : facts) (a : atom) (slots : list (ident * atom)) :
    option (ident * list (ident * atom)) :=
  match slots with
  | [] => None
  | (n, b) :: slots =>
      if atom_slot fs a b then Some (n, slots)
      else match sym_pick_name fs a slots with
           | Some (m, rest) => Some (m, (n, b) :: rest)
           | None => None
           end
  end.

(** The output names follow the heap's new order, including the order produced by stores. *)
Fixpoint sym_output_names (fs : facts) (slots : list (ident * atom)) (h : list atom) : option (list ident) :=
  match h with
  | [] => Some []
  | a :: h =>
      match sym_pick_name fs a slots with
      | Some (n, rest) => option_map (cons n) (sym_output_names fs rest h)
      | None => None
      end
  end.

(** A named tree retains the executor's leaves and adds their computed hypothesis names. *)
Inductive named_tree : Type :=
  | NLeaf (l : name) (lf : leaf) (names : option (list ident))
  | NSplit (c : zexp) (yes no : named_tree).

(** Naming is part of the same computation that evaluates the function's blocks. *)
Fixpoint sym_name_tree fs slots (t : stree) : named_tree :=
  match t with
  | TLeaf l lf => NLeaf l lf (sym_output_names fs slots (st_heap (leaf_state lf)))
  | TSplit c yes no => NSplit c (sym_name_tree fs slots yes) (sym_name_tree fs slots no)
  end.

(** Erasing names recovers the execution tree without changing any branch or state. *)
Fixpoint sym_erase_names (t : named_tree) : stree :=
  match t with
  | NLeaf l lf _ => TLeaf l lf
  | NSplit c yes no => TSplit c (sym_erase_names yes) (sym_erase_names no)
  end.

(** Hypothesis naming does not affect the executor's result. *)
Lemma sym_name_tree_sound fs slots t : sym_erase_names (sym_name_tree fs slots t) = t.
Proof. induction t; cbn; congruence. Qed.

(** Advancing each hypothesis advances both the persistent and spatial interpretations of its environment. *)
Lemma sym_env_later {Σ : gFunctors} (Γ Γ' : environments.env (iProp Σ)) :
  env_Forall2 (fun P Q => P ⊢ ▷ Q) Γ Γ' ->
  (env_and_persistently Γ ⊢ ▷ env_and_persistently Γ') /\
  (([∗] Γ) ⊢ ▷ ([∗] Γ')).
Proof.
  intros H. induction H as [|Γ Γ' i P Q HΓ [Hp Hs] HP]; cbn.
  - split; apply bi.later_intro.
  - split.
    + rewrite HP -bi.later_persistently Hp -bi.later_and. done.
    + rewrite HP Hs -bi.later_sep. done.
Qed.

(** The relation preserves hypothesis names and validity while moving the whole context through one later. *)
Lemma sym_envs_later {Σ : gFunctors} (Δ Δ' : envs (iProp Σ)) :
  envs_Forall2 (fun P Q => P ⊢ ▷ Q) Δ Δ' ->
  of_envs Δ ⊢ ▷ of_envs Δ'.
Proof.
  intros [Hp Hs]. rewrite !of_envs_eq !bi.later_and.
  apply bi.and_mono.
  - iIntros "%Hwf". iNext. iPureIntro.
    destruct Hwf as [Hwp Hws Hd]. constructor.
    + eapply env_Forall2_wf; eassumption.
    + eapply env_Forall2_wf; eassumption.
    + intros i. destruct (Hd i) as [H|H]; [left|right]; eapply env_Forall2_fresh; eassumption.
  - apply bi.and_mono; [exact (proj1 (sym_env_later _ _ Hp))|exact (proj2 (sym_env_later _ _ Hs))].
Qed.

(** Resource names have no logical meaning, but their number must match the returned ownership atoms. *)
Fixpoint sym_named_heap `{!gen_heapGS piece pval Σ} (ρ : valuation)
    (names : list ident) (h : list atom) : option (environments.env (iProp Σ)) :=
  match names, h with
  | [], [] => Some Enil
  | n :: names, a :: h =>
      match sym_named_heap ρ names h with
      | Some Γ => Some (Esnoc Γ n (atom_den ρ a))
      | None => None
      end
  | _, _ => None
  end.

(** Naming the returned atoms preserves their separating conjunction. *)
Lemma sym_named_heap_sound `{!gen_heapGS piece pval Σ} ρ names h Γ :
  sym_named_heap ρ names h = Some Γ -> heap_den ρ h ⊣⊢ ([∗] Γ).
Proof.
  revert h Γ. induction names as [|n names IH]; intros [|a h] Γ; cbn [sym_named_heap]; try discriminate.
  - intros H. injection H as <-. done.
  - destruct (sym_named_heap ρ names h) as [Γ'|] eqn:E; [|discriminate].
    intros H. injection H as <-. cbn [heap_den env_to_list]. rewrite (IH _ _ E). done.
Qed.

(** A leaf resumes at a jump target or at the first instruction the executor could not handle. *)
Definition sym_leaf_frame ρ f e ls l lf : frame :=
  let s := leaf_state lf in
  mkFrame f (apply_ups ρ (st_ups s) e) ls None
    (match lf with
     | LGoto t _ => Enter (edge_label t) (Some l)
     | LBranch c t1 t2 _ => Enter (edge_label (if zden ρ c =? 0 then t2 else t1)) (Some l)
     | LStop _ insts j _ => Exec l insts j
     end).

(** Jump leaves provide a step; stopped leaves require their continuation immediately. *)
Definition sym_leaf_later (lf : leaf) : bool :=
  match lf with LStop _ _ _ _ => false | _ => true end.

(** Returning resources appends their computed names to the caller's untouched context. *)
Definition sym_return_env `{!gen_heapGS piece pval Σ} ρ names h (Δ : envs (iProp Σ)) : option (envs (iProp Σ)) :=
  match names with
  | Some ns => match sym_named_heap ρ ns h with Some Γ => envs_app false Γ Δ | None => None end
  | None => None
  end.

Section context_sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance sym_context_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The caller must justify each path's arithmetic conditions before using its returned memory permissions.
    The continuation receives those permissions under their computed names. *)
Fixpoint sym_context_goals ρ f e ls Φ (Δ Δlater : envs (iProp Σ)) (t : named_tree) : Prop :=
  match t with
  | NLeaf l lf names =>
      obs_den wi ρ (st_obs (leaf_state lf)) /\
      match sym_return_env ρ names (st_heap (leaf_state lf)) (if sym_leaf_later lf then Δlater else Δ) with
      | Some Δout => envs_entails Δout (WP (ERun (sym_leaf_frame ρ f e ls l lf) : gexpr) {{ Φ }})
      | None => False
      end
  | NSplit c yes no =>
      (zden ρ c <> 0 -> sym_context_goals ρ f e ls Φ Δ Δlater yes) /\
      (zden ρ c = 0 -> sym_context_goals ρ f e ls Φ Δ Δlater no)
  end.

(** Appending the named heap supplies exactly the resources expected by the continuation. *)
Lemma sym_return_env_sound ρ names h Δ Δout :
  sym_return_env ρ names h Δ = Some Δout ->
  of_envs Δ ∗ heap_den ρ h ⊢ of_envs Δout.
Proof.
  unfold sym_return_env. destruct names as [ns|]; [|discriminate].
  destruct (sym_named_heap ρ ns h) as [Γ|] eqn:E; [|discriminate].
  intros Happ. rewrite (sym_named_heap_sound _ _ _ _ E).
  iIntros "[HΔ Hheap]". iApply (envs_app_sound _ _ _ _ Happ with "HΔ Hheap").
Qed.

(** Crossing a jump lets the caller use permissions guarded by one execution step.
    Each continuation also receives the memory permissions returned by its path. *)
Lemma sym_context_goals_sound ρ f e ls Φ Δ Δlater t :
  envs_Forall2 (fun P Q => P ⊢ ▷ Q) Δ Δlater ->
  sym_context_goals ρ f e ls Φ Δ Δlater t ->
  of_envs Δ ⊢ stree_den registry wi ge ρ f e ls Φ (sym_erase_names t).
Proof.
  intros Hlater. induction t as [l lf names|c yes IHyes no IHno].
  - destruct lf; cbn [sym_context_goals sym_erase_names stree_den leaf_den sym_leaf_later leaf_state sym_leaf_frame];
      intros [Hobs Hgoal].
    all: match type of Hgoal with context [sym_return_env ?ρ ?ns ?h ?Δ] =>
      destruct (sym_return_env ρ ns h Δ) as [Δout|] eqn:E; [|contradiction] end.
    all: rewrite envs_entails_unseal in Hgoal.
    all: iIntros "HΔ"; iSplit; [done|].
    1,2: iDestruct (sym_envs_later _ _ Hlater with "HΔ") as "HΔ"; iNext.
    all: iIntros "Hheap _"; iApply Hgoal; iApply (sym_return_env_sound _ _ _ _ _ E with "[$HΔ $Hheap]").
  - cbn [sym_context_goals sym_erase_names stree_den]. intros [Hy Hn].
    iIntros "HΔ". iSplit.
    + iIntros "%Hc". iApply (IHyes (Hy Hc) with "HΔ").
    + iIntros "%Hc". iApply (IHno (Hn Hc) with "HΔ").
Qed.

(** The caller selects named memory permissions for execution and retains the remaining hypotheses.
    This theorem connects those hypotheses directly to the computed run's continuations. *)
Theorem tac_sym_func_sound Δ Δrest Δlater names p Ps fs se h f e ls cuts fuel l insts j ρ Φ tree :
  envs_lookup_delete_list false names Δ = Some (p, Ps, Δrest) ->
  Ps = map (atom_den ρ) h ->
  envs_Forall2 (fun P Q => P ⊢ ▷ Q) Δrest Δlater ->
  facts_hold ρ fs -> env_models ρ se e ->
  sym_name_tree fs (combine names h) (sym_func ge f cuts fuel fs (mkSState se [] h []) l insts j) = tree ->
  sym_context_goals ρ f e ls Φ Δrest Δlater tree ->
  envs_entails Δ (WP (ERun (mkFrame f e ls None (Exec l insts j)) : gexpr) {{ Φ }}).
Proof.
  intros Htake -> Hlater Hfacts Henv <- Hgoals. rewrite envs_entails_unseal.
  rewrite (envs_lookup_delete_list_sound _ _ _ _ _ _ Htake) bi.intuitionistically_if_elim.
  assert (Hheap : ([∗] map (atom_den ρ) h) ⊣⊢ heap_den ρ h).
  { clear Htake Hlater Hfacts Henv Hgoals.
    induction h; cbn [heap_den List.map]; [done|]. rewrite big_op.big_sepL_cons IHh. done. }
  rewrite Hheap. iIntros "[Hheap Hrest]".
  iApply (sym_func_sound registry wi ge fs se h f e ls cuts fuel l insts j ρ Φ Hfacts Henv with "Hheap").
  rewrite -(sym_name_tree_sound fs (combine names h)
    (sym_func ge f cuts fuel fs (mkSState se [] h []) l insts j)).
  iApply (sym_context_goals_sound _ _ _ _ _ _ _ _ Hlater Hgoals with "Hrest").
Qed.

End context_sound.

(** A list of arithmetic conditions becomes one conjunction, so a solver can normalize shared expressions once. *)
Fixpoint sym_conjunction {A : Type} (P : A -> Prop) (xs : list A) : Prop :=
  match xs with [] => True | x :: xs => P x /\ sym_conjunction P xs end.

(** The solver proves the arithmetic conditions together; this lemma returns them as the list the executor requires. *)
Lemma sym_conjunction_sound {A : Type} (P : A -> Prop) xs :
  sym_conjunction P xs -> Forall P xs.
Proof.
  induction xs as [|x xs IH]; cbn [sym_conjunction]; intros H.
  - constructor.
  - destruct H as [Hx Hxs]. constructor; [exact Hx|apply IH; exact Hxs].
Qed.

(** The caller may use its continuation after one execution step.
    This rule advances that permission without examining the caller's memory. *)
Lemma sym_later_wand {Σ : gFunctors} (P Q : iProp Σ) :
  (P -∗ Q) -∗ ▷ P -∗ ▷ Q.
Proof. iIntros "HK HP". iNext. iApply ("HK" with "HP"). Qed.

(** ## Running the executor from a proof

    The proof author names the memory permissions that the function may use
    and the labels where execution should stop. The tactic collects those
    permissions once, then returns them under their original names on each path. *)

(** The default conversion computes a tree and lets the kernel check its equality. *)
Ltac sym_vm call finish :=
  let tree := eval vm_compute in call in
  let checked := constr:(ltac:(vm_cast_no_check (eq_refl tree)) : call = tree) in
  finish tree checked.

(** Native conversion uses the same interface when a larger computation justifies compilation. *)
Ltac sym_native call finish :=
  let tree := eval native_compute in call in
  let checked := constr:(ltac:(native_cast_no_check (eq_refl tree)) : call = tree) in
  finish tree checked.

(** Arithmetic is solved together when possible; other conditions remain available as individual goals. *)
Ltac sym_solve_obligations solve :=
  apply sym_conjunction_sound;
  cbn [sym_conjunction]; sym_den_simpl;
  first [solve [solve] | repeat split; try solve].

(** Selected hypotheses are removed without reducing the assertions they contain. *)
Ltac sym_take names delta :=
  lazymatch names with
  | [] => constr:(envs_lookup_delete_list_nil delta false)
  | ?n :: ?rest =>
      let entry := pm_eval (envs_lookup_delete false n delta) in
      lazymatch entry with
      | Some (?p, ?P, ?next) =>
          let tail := sym_take rest next in
          lazymatch type of tail with
          | _ = Some (?q, ?Ps, ?out) =>
              constr:(envs_lookup_delete_list_cons delta next out false n rest p q P Ps eq_refl tail)
          end
      end
  end.

(** Explicit guards are stripped while other assertions keep their current form. *)
Ltac sym_guard_env gamma :=
  lazymatch gamma with
  | Enil => lazymatch type of gamma with environments.env ?A =>
      constr:(env_Forall2_nil (fun P Q : A => P ⊢ ▷ Q)) end
  | Esnoc ?rest ?n ?P =>
      let tail := sym_guard_env rest in
      lazymatch type of tail with
      | env_Forall2 _ _ ?out =>
          lazymatch P with
          | (▷ ?Q)%I =>
              let step := constr:(ltac:(reflexivity) : P ⊢ ▷ Q) in
              constr:(env_Forall2_snoc (fun X Y => X ⊢ ▷ Y) rest out n P Q tail step)
          | _ => constr:(env_Forall2_snoc (fun X Y => X ⊢ ▷ Y) rest out n P P tail (bi.later_intro P))
          end
      end
  end.

(** Named leaves expose ordinary proof goals without framing or restoring names through Iris tactics. *)
Ltac sym_context_finish solve tree :=
  lazymatch tree with
  | NSplit ?c ?yes ?no =>
      split; [let H := fresh "Hsym_yes" in intros H; cbn [zden cden vz vp vr nth nth_error] in H; sym_context_finish solve yes |
              let H := fresh "Hsym_no" in intros H; cbn [zden cden vz vp vr nth nth_error] in H; sym_context_finish solve no]
  | NLeaf ?l ?lf ?names =>
      cbn [sym_context_goals leaf_state st_obs st_heap];
      split; [unfold obs_den; sym_solve_obligations solve |
      lazymatch lf with LStop ?why _ _ _ => idtac "sym_frun stopped:" why | _ => idtac end;
      cbn [sym_return_env sym_named_heap leaf_state st_heap sym_leaf_later];
      lazymatch goal with
      | |- match ?app with Some _ => _ | None => _ end =>
          let out := pm_eval app in change app with out
      end;
      unfold sym_leaf_frame;
      cbn [leaf_state st_ups apply_ups fold_left fst snd
        atom_den wden cden zden vz vp vr nth nth_error edge_label];
      rewrite ?sym_ptr_eta]
  end.

(** Execution uses the same memory interpretation as the caller.
    The tactic reads this interpretation from the program instance before constructing its proof. *)
Ltac sym_context_rule instance :=
  lazymatch instance with
  | @nanofil_irisGS ?lc ?sigma ?inv ?heap ?world ?reg ?wi ?ge =>
      constr:(@tac_sym_func_sound lc sigma inv heap world reg wi ltac:(typeclasses eauto) ge)
  | _ => let next := eval red in instance in sym_context_rule next
  end.

(** The soundness theorem connects the single computed tree to the caller's execution goal. *)
Ltac sym_func_finish cs se h rho names cuts solve conv bs :=
  let fs := constr:(mkFacts bs cs) in
  let rule := lazymatch goal with |- @envs_entails _ _ _ (@wp _ _ _ _ ?W _ _ _ _) =>
    lazymatch W with @wp' _ _ _ ?instance => sym_context_rule instance end end in
  lazymatch goal with
  | |- environments.envs_entails ?delta (wp _ _ (_ (mkFrame ?f ?e ?ls None (Exec ?l ?insts ?j))) ?Phi) =>
      let fuel := eval vm_compute in (List.length (fn_blocks f)) in
      let ids := eval vm_compute in (map INamed names) in
      let take := sym_take ids delta in
      lazymatch type of take with
      | _ = Some (?p, ?Ps, ?rest) =>
        lazymatch rest with Envs ?persistent ?spatial ?counter =>
          let hp := sym_guard_env persistent in let hs := sym_guard_env spatial in
          lazymatch type of hp with env_Forall2 _ _ ?pp =>
          lazymatch type of hs with env_Forall2 _ _ ?ss =>
          let later := constr:(Envs pp ss counter) in
          let guard := constr:(@Build_envs_Forall2 _ _ (fun P Q => P ⊢ ▷ Q) rest later hp hs) in
          refine (rule delta rest later ids p Ps fs se h f e ls cuts fuel l insts j rho Phi _ take _ guard _ _ _ _);
          [sym_den_simpl; reflexivity |
           unfold facts_hold; split; sym_forall_side solve |
           unfold env_models; sym_forall_side ltac:(lk_prove) |
           lazymatch goal with |- ?call = _ => conv call ltac:(fun tree checked => exact checked) end |
           lazymatch goal with |- sym_context_goals _ _ _ _ _ _ _ _ _ _ ?tree => sym_context_finish solve tree end]
          end end
        end
      end
  end.

(** The caller chooses cut labels, an obligation solver and a checked conversion method. *)
Ltac sym_frun_with names cuts solve conv :=
  iStartProof; autounfold with offs in *;
  let names := String.words names in
  let props := sym_context constr:(@nil Prop) in
  let props := sym_flatten props in
  let qh := sym_quote_heap constr:(mkVal [] [] []) names in
  lazymatch qh with (?h, ?r1) =>
    lazymatch goal with
    | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ ?e _ None (Exec _ _ _))) _) =>
        let qe := sym_quote_env r1 props e in
        lazymatch qe with (?se, ?r2) => let qc := sym_quote_caps r2 props in
          lazymatch qc with (?cs, ?rho) =>
            let terms := sym_bound_terms rho in
            sym_bounds props terms constr:(@nil bound)
              ltac:(sym_func_finish cs se h rho names cuts solve conv)
          end end
    end
  end.

(** Ordinary calls use virtual-machine conversion and the block executor's arithmetic solver. *)
Ltac sym_frun names cuts := sym_frun_with names cuts ltac:(sym_lia) ltac:(sym_vm).

(** A two-block run swaps two temporaries without reading an overwritten phi destination. *)
Definition sym_swap_function : func :=
  mkFunc (TAtom "swap") (TAtom "local") RVoid []
    [mkBlock (TAtom "swap")
      [Phi (TAtom "x") L [(TAtom "entry", Tmp (TAtom "y"))];
       Phi (TAtom "y") L [(TAtom "entry", Tmp (TAtom "x"))]]
      [] (JGoto (To (TAtom "done")))].

(** Unequal input values distinguish parallel phi evaluation from sequential assignment. *)
Example sym_swap_run `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
    {world : Type} (registry : name -> option (contract world))
    (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} ge e Φ :
  let _ := nanofil_irisGS registry wi ge in
  lookup (TAtom "x") e = Some (WInt 11) -> lookup (TAtom "y") e = Some (WInt 23) ->
  ▷ WP (ERun (mkFrame sym_swap_function (put (TAtom "y") (WInt 11) (put (TAtom "x") (WInt 23) e))
       [] None (Enter (TAtom "done") (Some (TAtom "swap")))) : language.expr (nanofil_lang registry ge)) {{ Φ }} -∗
  WP (ERun (mkFrame sym_swap_function e [] None (Exec (TAtom "entry") [] (JGoto (To (TAtom "swap")))))
      : language.expr (nanofil_lang registry ge)) {{ Φ }}.
Proof.
  intros ? Hx Hy. iIntros "H".
  sym_frun_with "" [TAtom "done"] ltac:(sym_lia) ltac:(sym_native). done.
Qed.

(** A jump makes both guarded permissions available while preserving an unguarded continuation. *)
Example sym_guarded_context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
    {world : Type} (registry : name -> option (contract world))
    (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi}
    ge e (P Q : iProp Σ) Φ :
  let _ := nanofil_irisGS registry wi ge in
  ▷ P -∗ ▷ Q -∗
  (P -∗ Q -∗ WP (ERun (mkFrame sym_swap_function e [] None (Enter (TAtom "done") (Some (TAtom "entry"))))) {{ Φ }}) -∗
  WP (ERun (mkFrame sym_swap_function e [] None (Exec (TAtom "entry") [] (JGoto (To (TAtom "done")))))) {{ Φ }}.
Proof.
  intros ?. iIntros "HP HQ HK". sym_frun "" [TAtom "done"].
  iApply ("HK" with "HP HQ").
Qed.

Print Assumptions sym_func_sound.
Print Assumptions tac_sym_func_sound.
