(** This module proves that the [[dominance|dominator intervals]]
    computed by [Cfg] are sound.
    [formal.md, Campaign 3](../../../docs/formal.md#campaign-3-the-soundness-theorem)
    and [rocq.md, Dominance](../../../docs/rocq.md#dominance) describe
    the surrounding campaign.

    Before the [[validator]] can reuse a pointer check from an earlier
    [[block]], it must know whether that earlier block dominates the
    current block. Block A dominates block B when every path from the
    function entry to B passes through A. To answer that question
    quickly, the validator builds a dominator tree with [cfg_idoms]
    using the Cooper-Harvey-Kennedy algorithm, then numbers the tree in
    preorder with [dom_intervals]. Each block receives a numeric
    interval, and [dominates_by_interval] tests dominance by checking
    whether one interval contains another.

    Campaign 3's [[single-definition]] invariant needs those interval
    answers to hold along every run of the [[machine]]. Theorem
    [dom_closed] shows that every reachable block has an interval, and
    [dom_edge] shows that any dominator of a successor other than the
    successor itself dominates the predecessor block. We prove these
    facts directly for [block_intervals] rather than a simplified copy,
    so the proof covers the exact validator that the compiler runs.

    Soundness does not require proving that the computed tree is the
    smallest fixpoint. Instead, it rests on three structural properties
    of the output. First, [cfg_ok] ensures the reverse postorder starts
    at the entry and stays closed under successors. Second, [idoms_ok]
    ensures each block's parent in the tree is an ancestor of its
    reachable predecessors. Third, [si_ok] ensures each interval matches
    the preorder numbers of its subtree, which places every ancestor on
    every path from the entry. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Validate.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Names and maps

    Block labels and temporary names live in [[name-map|name maps]]
    throughout the validator. These helper lemmas connect boolean name
    equality and map membership to propositional equality so later
    proofs can rewrite directly. *)

(** Comparing names with [name_eqb] answers true exactly when the two names
    are equal. *)
Lemma name_eqb_true : forall a b, name_eqb a b = true <-> a = b.
Proof.
  intros a b. split; [apply term_eqb_eq|]. intros ->. apply term_eqb_refl.
Qed.

(** [name_eqb] answers false exactly when the two names differ. *)
Lemma name_eqb_false : forall a b, name_eqb a b = false <-> a <> b.
Proof.
  intros a b. rewrite <- not_true_iff_false, name_eqb_true. reflexivity.
Qed.

(** A [[name map]] m has the key k ([nm_mem]) exactly when looking k up in m
    finds some value. *)
Lemma nm_mem_find : forall (A : Type) k (m : nmap A), nm_mem k m = true <-> exists v, nm_find k m = Some v.
Proof.
  intros A k m. unfold nm_mem. destruct (nm_find k m); split; intros H; eauto.
  - discriminate H.
  - destruct H as [v H]. discriminate H.
Qed.

(** After adding the key n to a name map m, k is a key exactly when it is n
    or was a key of m. *)
Lemma nm_mem_add_iff : forall (A : Type) k n (v : A) m, nm_mem k (nm_add n v m) = true <-> k = n \/ nm_mem k m = true.
Proof.
  intros A k n v m. rewrite nm_mem_add, orb_true_iff, name_eqb_true. reflexivity.
Qed.

(** The empty name map has no keys. *)
Lemma nm_mem_empty : forall (A : Type) k, nm_mem k (@nm_empty A) = false.
Proof. intros A k. unfold nm_mem. rewrite nm_find_empty. reflexivity. Qed.

(** ## Depth-first search

    To visit blocks in topological order where possible, the validator
    walks the control-flow graph depth first from the function entry.
    It records labels in reverse postorder, placing each block before
    its forward successors while breaking cycles at back edges. The
    lemmas below characterize what one bounded walk marks and emits. *)

(** A bounded depth-first walk from labels ns over successor map succs
    preserves all prior marks in seen and all prior entries in post. It
    marks every label in ns, emits every newly marked label into post'
    along with marks for all its successors, and emits nothing else. *)
Lemma reverse_postorder_spec : forall fuel ns succs seen post seen' post',
  reverse_postorder fuel ns succs seen post = Some (seen', post') ->
  (forall x, nm_mem x seen = true -> nm_mem x seen' = true) /\
  (forall x, In x ns -> nm_mem x seen' = true) /\
  (forall x, nm_mem x seen' = true -> nm_mem x seen = false ->
     In x post' /\ exists ss, nm_find x succs = Some ss /\ forall y, In y ss -> nm_mem y seen' = true) /\
  (forall x, In x post' -> In x post \/ (nm_mem x seen' = true /\ nm_mem x seen = false)) /\
  (forall x, In x post -> In x post').
Proof.
  induction fuel as [|fuel IH]; intros ns succs seen post seen' post' H; simpl in H; [discriminate H|].
  destruct ns as [|l ls].
  - injection H as <- <-. split; [auto|]. split; [intros x Hx; destruct Hx|].
    split; [intros x Hs Hn; congruence|]. split; [intros x Hx; left; exact Hx | auto].
  - destruct (nm_mem l seen) eqn:El.
    + destruct (IH _ _ _ _ _ _ H) as (Ha & Hb & Hc & Hd & He).
      split; [exact Ha|]. split; [intros x [<- | Hx]; [exact (Ha _ El) | exact (Hb _ Hx)]|].
      split; [exact Hc|]. split; [exact Hd | exact He].
    + destruct (nm_find l succs) as [ss|] eqn:Ess; [|discriminate H].
      destruct (reverse_postorder fuel ss succs (nm_add l tt seen) post) as [[seen2 post1]|] eqn:E1;
        [|discriminate H].
      destruct (IH _ _ _ _ _ _ E1) as (Ha1 & Hb1 & Hc1 & Hd1 & He1).
      destruct (IH _ _ _ _ _ _ H) as (Ha2 & Hb2 & Hc2 & Hd2 & He2).
      assert (Hl2 : nm_mem l seen2 = true) by (apply Ha1, nm_mem_add_iff; left; reflexivity).
      assert (Hs2 : forall x, nm_mem x seen = true -> nm_mem x seen2 = true)
        by (intros x Hx; apply Ha1, nm_mem_add_iff; right; exact Hx).
      split; [|split; [|split; [|split]]].
      * intros x Hx. exact (Ha2 _ (Hs2 _ Hx)).
      * intros x [<- | Hx]; [exact (Ha2 _ Hl2) | exact (Hb2 _ Hx)].
      * intros x Hx Hn. destruct (nm_mem x seen2) eqn:Ex2.
        -- destruct (name_eqb x l) eqn:Exl.
           ++ apply name_eqb_true in Exl. subst x. split; [apply He2; left; reflexivity|].
              exists ss. split; [exact Ess|]. intros y Hy. exact (Ha2 _ (Hb1 _ Hy)).
           ++ assert (Hn' : nm_mem x (nm_add l tt seen) = false).
              { rewrite nm_mem_add, Exl, Hn. reflexivity. }
              destruct (Hc1 _ Ex2 Hn') as [Hp (ss' & Hf & Hy)].
              split; [apply He2; right; exact Hp|]. exists ss'. split; [exact Hf|].
              intros y Hyy. exact (Ha2 _ (Hy _ Hyy)).
        -- exact (Hc2 _ Hx Ex2).
      * intros x Hx. destruct (Hd2 _ Hx) as [[<- | Hp] | [Hx2 Hn2]].
        -- right. split; [exact (Ha2 _ Hl2) | exact El].
        -- destruct (Hd1 _ Hp) as [Hp' | [Hx1 Hn1]]; [left; exact Hp'|].
           right. split; [exact (Ha2 _ Hx1)|].
           rewrite nm_mem_add in Hn1. apply orb_false_iff in Hn1. exact (proj2 Hn1).
        -- right. split; [exact Hx2|]. destruct (nm_mem x seen) eqn:Ex; [|reflexivity].
           rewrite (Hs2 _ Ex) in Hn2. discriminate Hn2.
      * intros x Hx. apply He2. right. exact (He1 _ Hx).
Qed.

(** When [[fuel]] remains and the worklist is empty, the walk returns
    the current marks and postorder list unchanged. *)
Lemma reverse_postorder_nil : forall f succs seen post,
  reverse_postorder (S f) [] succs seen post = Some (seen, post).
Proof. reflexivity. Qed.

(** When fuel remains on a nonempty worklist l :: ls, the walk skips l
    if seen already marks it. Otherwise it marks l, visits l's
    successors, prepends l to their output, and continues with ls. This
    one-step unfolding lets later proofs step through the walk from the
    entry. *)
Lemma reverse_postorder_cons : forall f l ls succs seen post,
  reverse_postorder (S f) (l :: ls) succs seen post =
  if nm_mem l seen then reverse_postorder f ls succs seen post
  else match nm_find l succs with
       | Some ss =>
           match reverse_postorder f ss succs (nm_add l tt seen) post with
           | Some (seen2, post1) => reverse_postorder f ls succs seen2 (l :: post1)
           | None => None
           end
       | None => None
       end.
Proof. reflexivity. Qed.

(** ## The graph a function's blocks make

    A function's [[block|blocks]] form a directed control-flow graph
    whose edges follow each block's final jump. This section relates
    that graph to the successor and predecessor maps that [func_cfg]
    builds from the block list. *)

(** A control-flow edge connects block p to block s when some [[block]]
    labelled p ends with a jump that can target s. *)
Definition edge (bs : list block) (p s : name) : Prop :=
  exists b, In b bs /\ b_label b = p /\ In s (jump_succs (b_jump b)).

(** ### The successor map *)

(** If [lookup] finds v for the key k in an association list ps, ps holds a
    pair of v with a key k' that [name_eqb] finds equal to k. *)
Lemma lookup_some_in : forall (A : Type) k (ps : list (name * A)) v,
  lookup k ps = Some v -> exists k', name_eqb k k' = true /\ In (k', v) ps.
Proof.
  intros A k ps v. induction ps as [|[k' v'] ps IH]; simpl; intros H; [discriminate H|].
  destruct (name_eqb k k') eqn:E.
  - injection H as <-. exists k'. split; [exact E | left; reflexivity].
  - destruct (IH H) as (k'' & E' & Hin). exists k''. split; [exact E' | right; exact Hin].
Qed.

(** [lookup] finds nothing for the key k in an association list where no
    pair has the key k. *)
Lemma lookup_none : forall (A : Type) k (ps : list (name * A)),
  (forall k' v, In (k', v) ps -> k' <> k) -> lookup k ps = None.
Proof.
  intros A k ps H. induction ps as [|[k' v'] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb k k') eqn:E.
  - apply name_eqb_true in E. subst k'. exfalso. exact (H k v' (or_introl eq_refl) eq_refl).
  - apply IH. intros k'' v'' Hin. exact (H k'' v'' (or_intror Hin)).
Qed.

(** The validator's list membership test [mem] n ns is true exactly when n
    is in ns. *)
Lemma mem_in : forall n ns, mem n ns = true <-> In n ns.
Proof.
  intros n ns. unfold mem. rewrite existsb_exists. split.
  - intros (n' & Hin & E). apply name_eqb_true in E. subst. exact Hin.
  - intros Hin. exists n. split; [exact Hin | apply term_eqb_refl].
Qed.

(** In an association list ps whose keys are distinct ([no_dups]), looking k
    up in the reversed list finds the value of k's one pair (k, v).
    [nm_of_list] keeps the last pair of a key, so this is how a map built
    from such a list finds a key's only value. *)
Lemma lookup_rev_unique : forall (A : Type) (ps : list (name * A)) k v,
  no_dups (map fst ps) = true -> In (k, v) ps -> lookup k (rev ps) = Some v.
Proof.
  intros A ps. induction ps as [|[k' v'] ps IH]; simpl; intros k v Hd Hin; [destruct Hin|].
  apply andb_true_iff in Hd as [Hn Hd]. apply negb_true_iff in Hn.
  rewrite lookup_app. destruct Hin as [E | Hin].
  - injection E as <- <-.
    rewrite lookup_none; [simpl; rewrite term_eqb_refl; reflexivity|].
    intros k'' v'' Hin E. subst k''. apply in_rev in Hin.
    assert (Hm : mem k' (map fst ps) = true)
      by (apply mem_in, in_map_iff; exists (k', v''); auto).
    congruence.
  - rewrite (IH _ _ Hd Hin). reflexivity.
Qed.

(** The validator builds a successor map [block_succs] from the block
    list bs by mapping each block's label to its jump targets. *)
Definition block_succs (bs : list block) : nmap (list name) :=
  nm_of_list (map (fun b => (b_label b, jump_succs (b_jump b))) bs).

(** Where no two blocks of bs share a label, the successor map gives each
    block b of bs the labels b's jump can go to. *)
Lemma block_succs_find : forall bs b,
  no_dups (map b_label bs) = true -> In b bs ->
  nm_find (b_label b) (block_succs bs) = Some (jump_succs (b_jump b)).
Proof.
  intros bs b Hd Hin. unfold block_succs, nm_of_list. rewrite nm_find_fold_add.
  rewrite (lookup_rev_unique _ _ (b_label b) (jump_succs (b_jump b))); [reflexivity| |].
  - rewrite map_map. exact Hd.
  - apply in_map_iff. exists b. auto.
Qed.

(** Every entry of the successor map comes from a block: if it gives the
    label l the list ss, some block of bs is labelled l and its jump can go
    to exactly ss. *)
Lemma block_succs_some : forall bs l ss,
  nm_find l (block_succs bs) = Some ss -> exists b, In b bs /\ b_label b = l /\ ss = jump_succs (b_jump b).
Proof.
  intros bs l ss H. unfold block_succs, nm_of_list in H. rewrite nm_find_fold_add, nm_find_empty in H.
  destruct (lookup l (rev _)) eqn:E; [|discriminate H]. injection H as <-.
  destruct (lookup_some_in _ _ _ _ E) as (l' & El & Hin). apply name_eqb_true in El. subst l'.
  apply in_rev, in_map_iff in Hin as (b & Eb & Hb). injection Eb as <- <-.
  exists b. auto.
Qed.

(** ### The predecessor map *)

(** To invert the successor edges, [cfg_edges] collects every edge in
    bs as a pair containing the successor label first and the source
    block's label second. *)
Definition cfg_edges (bs : list block) : list (name * name) :=
  flat_map (fun b => map (fun s => (s, b_label b)) (jump_succs (b_jump b))) bs.

(** Adds the edge e, a successor and the label it is reached from, to the
    predecessor map m: the source goes in front of the successor's list.
    `func_cfg/2` folds it over [cfg_edges]. *)
Definition add_pred (m : nmap (list name)) (e : name * name) : nmap (list name) :=
  let ps := match nm_find (fst e) m with Some ps => ps | None => [] end in
  nm_add (fst e) (snd e :: ps) m.

(** Adding more edges keeps every predecessor listed: if s's list in m holds
    p, so does s's list after folding [add_pred] over the edges es. *)
Lemma add_pred_keeps : forall es m s p,
  (exists ps, nm_find s m = Some ps /\ In p ps) ->
  exists ps, nm_find s (fold_left add_pred es m) = Some ps /\ In p ps.
Proof.
  induction es as [|e es IH]; simpl; intros m s p H; [exact H|].
  apply IH. destruct H as (ps & Hf & Hp). unfold add_pred. rewrite nm_find_add.
  destruct (name_eqb s (fst e)) eqn:E.
  - apply name_eqb_true in E. subst s. rewrite Hf. eexists. split; [reflexivity | right; exact Hp].
  - exists ps. auto.
Qed.

(** After folding [add_pred] over the edges es, the successor of each edge
    of es lists that edge's source among its predecessors. *)
Lemma add_pred_in : forall es m e,
  In e es -> exists ps, nm_find (fst e) (fold_left add_pred es m) = Some ps /\ In (snd e) ps.
Proof.
  induction es as [|e0 es IH]; simpl; intros m e Hin; [destruct Hin|].
  destruct Hin as [<- | Hin]; [|exact (IH _ _ Hin)].
  apply add_pred_keeps. unfold add_pred. rewrite nm_find_add, term_eqb_refl.
  eexists. split; [reflexivity | left; reflexivity].
Qed.

(** Folding [add_pred] over edges es preserves any binary relation P
    that already holds on every edge in m and every edge in es. Every
    predecessor in the resulting map therefore comes from either the
    initial map or the added edge list. *)
Lemma add_pred_only : forall (P : name -> name -> Prop) es m,
  (forall s ps p, nm_find s m = Some ps -> In p ps -> P s p) ->
  (forall e, In e es -> P (fst e) (snd e)) ->
  forall s ps p, nm_find s (fold_left add_pred es m) = Some ps -> In p ps -> P s p.
Proof.
  intros P es. induction es as [|e es IH]; simpl; intros m Hm He; [exact Hm|].
  apply IH; [|intros e' He'; exact (He e' (or_intror He'))].
  intros s ps p Hs Hp. unfold add_pred in Hs. rewrite nm_find_add in Hs.
  destruct (name_eqb s (fst e)) eqn:E.
  - apply name_eqb_true in E. subst s. injection Hs as <-. destruct Hp as [<- | Hp].
    + exact (He e (or_introl eq_refl)).
    + destruct (nm_find (fst e) m) as [ps0|] eqn:E0; [exact (Hm _ _ _ E0 Hp) | destruct Hp].
  - exact (Hm _ _ _ Hs Hp).
Qed.

(** ### What `func_cfg/2` builds *)

(** The record [cfg_ok] captures the invariants that [func_cfg]
    establishes on a graph g built from blocks bs. Its successor map
    matches [block_succs], its predecessor map records every [edge] and
    nothing else, and its reverse postorder begins with the entry and is
    closed under successors. *)
Record cfg_ok (bs : list block) (g : cfg) : Prop := {
  cfg_ok_succs : cfg_succs g = block_succs bs;
  cfg_ok_preds : forall p s, edge bs p s -> exists ps, nm_find s (cfg_preds g) = Some ps /\ In p ps;
  cfg_ok_rpo : exists rest, cfg_rpo g = cfg_entry g :: rest /\ ~ In (cfg_entry g) rest;
  cfg_ok_closed : forall x, In x (cfg_rpo g) ->
                  exists ss, nm_find x (cfg_succs g) = Some ss /\ forall y, In y ss -> In y (cfg_rpo g);
  cfg_ok_pred_edge : forall s ps p, nm_find s (cfg_preds g) = Some ps -> In p ps -> edge bs p s
}.

(** Whenever `func_cfg/2` builds a graph g of the blocks bs, g is [cfg_ok],
    bs is not empty, and g's entry is the label of bs's first block. *)
Lemma func_cfg_ok : forall bs g, func_cfg bs = Some g -> cfg_ok bs g /\ exists b0 rest, bs = b0 :: rest /\ cfg_entry g = b_label b0.
Proof.
  intros bs g H. unfold func_cfg in H. destruct bs as [|b0 rest]; [discriminate H|]. cbv zeta in H.
  destruct (negb _) eqn:Ec; [discriminate H|].
  match type of H with context [reverse_postorder ?fu ?ns ?su ?se ?po] =>
    destruct (reverse_postorder fu ns su se po) as [[seen post]|] eqn:Er; [|discriminate H] end.
  injection H as <-. split; [|exists b0, rest; auto].
  (* the first steps of the walk from the entry *)
  rewrite reverse_postorder_cons, nm_mem_empty in Er.
  destruct (nm_find (b_label b0) _) as [ss|] eqn:Ess; [|discriminate Er].
  match type of Er with context [reverse_postorder ?fu ss ?su ?se []] =>
    destruct (reverse_postorder fu ss su se []) as [[seen2 post1]|] eqn:E1; [|discriminate Er] end.
  rewrite reverse_postorder_nil in Er. injection Er as <- <-.
  destruct (reverse_postorder_spec _ _ _ _ _ _ _ E1) as (Ha & Hb & Hc & Hd & _).
  assert (Hent : nm_mem (b_label b0) seen2 = true)
    by (apply Ha, nm_mem_add_iff; left; reflexivity).
  assert (Hsp : forall x, In x (b_label b0 :: post1) <-> nm_mem x seen2 = true).
  { intros x. split.
    - intros [<- | Hx]; [exact Hent|]. destruct (Hd _ Hx) as [[] | [Hx2 _]]. exact Hx2.
    - intros Hx. destruct (name_eqb x (b_label b0)) eqn:E.
      + apply name_eqb_true in E. left. auto.
      + right. refine (proj1 (Hc _ Hx _)). rewrite nm_mem_add, E, nm_mem_empty. reflexivity. }
  constructor; simpl.
  - reflexivity.
  - intros p s (b & Hbin & <- & Hs).
    assert (Hin : In (s, b_label b) (cfg_edges (b0 :: rest))).
    { unfold cfg_edges. apply in_flat_map. exists b. split; [exact Hbin|]. apply in_map_iff. eauto. }
    exact (add_pred_in _ _ _ Hin).
  - exists post1. split; [reflexivity|]. intros Hin.
    destruct (Hd _ Hin) as [[] | [_ Hn]].
    rewrite nm_mem_add, term_eqb_refl in Hn. discriminate Hn.
  - intros x Hx. apply Hsp in Hx. destruct (name_eqb x (b_label b0)) eqn:E.
    + apply name_eqb_true in E. subst x. exists ss. split; [exact Ess|].
      intros y Hy. apply Hsp. exact (Hb _ Hy).
    + assert (Hn : nm_mem x (nm_add (b_label b0) tt nm_empty) = false)
        by (rewrite nm_mem_add, E, nm_mem_empty; reflexivity).
      destruct (Hc _ Hx Hn) as [_ (ss' & Hf & Hy)]. exists ss'. split; [exact Hf|].
      intros y Hyy. apply Hsp. exact (Hy _ Hyy).
  - apply (add_pred_only (fun s p => edge (b0 :: rest) p s)).
    + intros s ps p Hs Hp. unfold nm_of_list in Hs. rewrite nm_find_fold_add, nm_find_empty in Hs.
      destruct (lookup s (rev _)) eqn:E; [|discriminate Hs]. injection Hs as <-.
      destruct (lookup_some_in _ _ _ _ E) as (s' & _ & Hin).
      apply (proj2 (in_rev _ _)) in Hin.
      destruct Hin as [Eb | Hin]; [injection Eb as _ <- | apply in_map_iff in Hin as (b & Eb & _);
        injection Eb as _ <-]; destruct Hp.
    + intros [s p] Hin. change (In (s, p) (cfg_edges (b0 :: rest))) in Hin.
      unfold cfg_edges in Hin. apply in_flat_map in Hin as (b & Hbin & Hin).
      apply in_map_iff in Hin as (s' & Eb & Hs'). injection Eb as <- <-. exists b. auto.
Qed.

(** The walk lists each label at most once: from a list post without repeats
    whose labels are all marked, it leaves a list without repeats whose
    labels are all marked. *)
Lemma reverse_postorder_nodup : forall fuel ns succs seen post seen' post',
  reverse_postorder fuel ns succs seen post = Some (seen', post') ->
  NoDup post -> (forall x, In x post -> nm_mem x seen = true) ->
  NoDup post' /\ forall x, In x post' -> nm_mem x seen' = true.
Proof.
  induction fuel as [|fuel IH]; intros ns succs seen post seen' post' H Hn Hs; simpl in H; [discriminate H|].
  destruct ns as [|l ls].
  - injection H as <- <-. auto.
  - destruct (nm_mem l seen) eqn:El; [exact (IH _ _ _ _ _ _ H Hn Hs)|].
    destruct (nm_find l succs) as [ss|]; [|discriminate H].
    destruct (reverse_postorder fuel ss succs (nm_add l tt seen) post) as [[seen2 post1]|] eqn:E1;
      [|discriminate H].
    destruct (IH _ _ _ _ _ _ E1 Hn) as [Hn1 Hs1].
    { intros x Hx. apply nm_mem_add_iff. right. exact (Hs _ Hx). }
    destruct (reverse_postorder_spec _ _ _ _ _ _ _ E1) as (Ha1 & _ & _ & Hd1 & _).
    apply (IH _ _ _ _ _ _ H).
    + constructor; [|exact Hn1]. intros Hl. destruct (Hd1 _ Hl) as [Hp | [_ Hn']].
      * rewrite (Hs _ Hp) in El. discriminate El.
      * rewrite nm_mem_add, term_eqb_refl in Hn'. discriminate Hn'.
    + intros x [<- | Hx]; [|exact (Hs1 _ Hx)]. apply Ha1, nm_mem_add_iff. left. reflexivity.
Qed.

(** The reverse postorder of a graph `func_cfg/2` builds lists each label
    once. *)
Lemma func_cfg_nodup : forall bs g, func_cfg bs = Some g -> NoDup (cfg_rpo g).
Proof.
  intros bs g H. unfold func_cfg in H. destruct bs as [|b0 rest]; [discriminate H|]. cbv zeta in H.
  destruct (negb _); [discriminate H|].
  match type of H with context [reverse_postorder ?fu ?ns ?su ?se ?po] =>
    destruct (reverse_postorder fu ns su se po) as [[seen post]|] eqn:Er; [|discriminate H] end.
  injection H as <-. simpl.
  refine (proj1 (reverse_postorder_nodup _ _ _ _ _ _ _ Er _ _)); [constructor | intros x []].
Qed.

(** ### Each label after a predecessor

    Depth-first search visits a reachable label from one of its
    predecessors, so every reachable label except the entry appears after
    at least one predecessor in reverse postorder. The nearest common
    ancestor proof later relies on this ordering when it numbers labels. *)

(** Splitting a concatenated list a ++ b at element x places x either
    in the prefix a or in the suffix b. This list helper lets us track a
    newly emitted label across the two recursive halves of the depth-first
    walk. *)
Lemma app_cons_split : forall (A : Type) (a b u v : list A) (x : A),
  a ++ b = u ++ x :: v ->
  (exists v', a = u ++ x :: v') \/ (exists w, u = a ++ w /\ b = w ++ x :: v).
Proof.
  intros A a. induction a as [|y a IH]; simpl; intros b u v x H.
  - right. exists u. auto.
  - destruct u as [|z u]; simpl in H; injection H as <- H.
    + left. exists a. reflexivity.
    + destruct (IH _ _ _ _ H) as [(v' & ->) | (w & -> & ->)];
        [left; exists v' | right; exists w; split]; reflexivity.
Qed.

(** A depth-first walk prepends a sublist new of newly visited labels
    before post, and every label x in new is either one of the starting
    labels ns or a successor of a label listed before x in new. *)
Lemma reverse_postorder_parent : forall fuel ns succs seen post seen' post',
  reverse_postorder fuel ns succs seen post = Some (seen', post') ->
  exists new, post' = new ++ post /\
    forall u x v, new = u ++ x :: v ->
      In x ns \/ exists p ss, In p u /\ nm_find p succs = Some ss /\ In x ss.
Proof.
  induction fuel as [|fuel IH]; intros ns succs seen post seen' post' H; simpl in H; [discriminate H|].
  destruct ns as [|l ls].
  - injection H as <- <-. exists []. split; [reflexivity|]. intros u x v E. destruct u; discriminate E.
  - destruct (nm_mem l seen).
    + destruct (IH _ _ _ _ _ _ H) as (new & -> & Hn). exists new. split; [reflexivity|].
      intros u x v E. destruct (Hn _ _ _ E) as [Hx | Hp]; [left; right; exact Hx | right; exact Hp].
    + destruct (nm_find l succs) as [ss|] eqn:Ess; [|discriminate H].
      destruct (reverse_postorder fuel ss succs (nm_add l tt seen) post) as [[seen2 post1]|] eqn:E1;
        [|discriminate H].
      destruct (IH _ _ _ _ _ _ E1) as (new1 & -> & Hn1).
      destruct (IH _ _ _ _ _ _ H) as (new2 & -> & Hn2).
      exists (new2 ++ l :: new1). split; [rewrite <- app_assoc; reflexivity|].
      intros u x v E.
      destruct (app_cons_split _ _ _ _ _ _ E) as [(v' & E2) | (w & -> & E3)].
      * destruct (Hn2 _ _ _ E2) as [Hx | Hp]; [left; right; exact Hx | right; exact Hp].
      * destruct w as [|y w]; simpl in E3; injection E3 as <- E3.
        -- left. left. reflexivity.
        -- right. destruct (Hn1 _ _ _ E3) as [Hx | (p & ss' & Hp & Hf & Hs)].
           ++ exists l, ss. split; [apply in_or_app; right; left; reflexivity|]. auto.
           ++ exists p, ss'. split; [apply in_or_app; right; right; exact Hp|]. auto.
Qed.

(** In the reverse postorder of a graph g built by [func_cfg], every
    label x other than the entry has a predecessor p listed before it in
    the prefix u. *)
Lemma func_cfg_parent : forall bs g, func_cfg bs = Some g ->
  forall u x v, cfg_rpo g = u ++ x :: v -> x <> cfg_entry g ->
  exists p ps, In p u /\ nm_find x (cfg_preds g) = Some ps /\ In p ps.
Proof.
  intros bs g H u x v E Hx. destruct (func_cfg_ok _ _ H) as [Hok _].
  unfold func_cfg in H. destruct bs as [|b0 rest]; [discriminate H|]. cbv zeta in H.
  destruct (negb _) eqn:Ec; [discriminate H|].
  match type of H with context [reverse_postorder ?fu ?ns ?su ?se ?po] =>
    destruct (reverse_postorder fu ns su se po) as [[seen post]|] eqn:Er; [|discriminate H] end.
  injection H as <-. simpl in E, Hx.
  destruct (reverse_postorder_parent _ _ _ _ _ _ _ Er) as (new & Ep & Hn).
  rewrite app_nil_r in Ep. subst new.
  destruct (Hn _ _ _ E) as [[<- | []] | (p & ss & Hp & Hf & Hs)]; [congruence|].
  destruct (block_succs_some _ _ _ Hf) as (b & Hb & Eb & ->).
  destruct (cfg_ok_preds _ _ Hok p x) as (ps & Hps & Hin); [exists b; auto|].
  exists p, ps. auto.
Qed.

(** ## The tree of immediate dominators

    A label's immediate dominator (idom) is its parent in the
    [[dominance|dominator tree]]. `cfg_idoms/2` computes them as a
    [[name map]] by sweeping the reverse postorder until a sweep changes
    nothing; each label's idom is then the meet, walking up the tree,
    of its predecessors. *)

(** In the tree whose parent map is t, a is an ancestor of b: a is b, or a
    is an ancestor of b's parent. *)
Inductive anc (t : nmap name) (a : name) : name -> Prop :=
| anc_refl : anc t a a
| anc_up : forall b c, nm_find b t = Some c -> anc t a c -> anc t a b.

(** An ancestor of an ancestor of c is an ancestor of c. *)
Lemma anc_trans : forall t a b c, anc t a b -> anc t b c -> anc t a c.
Proof.
  intros t a b c Hab Hbc. induction Hbc as [|c d Hf _ IH]; [exact Hab|].
  exact (anc_up _ _ _ _ Hf IH).
Qed.

(** Walking up the immediate dominator map t from a and b with
    [common_dominator] returns a label c that is an ancestor of both a
    and b in the dominator tree. *)
Lemma common_dominator_anc : forall fuel num t a b c,
  common_dominator fuel num t a b = Some c -> anc t c a /\ anc t c b.
Proof.
  induction fuel as [|fuel IH]; intros num t a b c H; simpl in H; [discriminate H|].
  destruct (name_eqb a b) eqn:E.
  - apply name_eqb_true in E. subst b. injection H as <-. split; constructor.
  - destruct (nm_find a num) as [na|]; [|discriminate H].
    destruct (nm_find b num) as [nb|]; [|discriminate H].
    destruct (nb <? na).
    + destruct (nm_find a t) as [a1|] eqn:Ea; [|discriminate H].
      destruct (IH _ _ _ _ _ H) as [H1 H2]. split; [exact (anc_up _ _ _ _ Ea H1) | exact H2].
    + destruct (nm_find b t) as [b1|] eqn:Eb; [|discriminate H].
      destruct (IH _ _ _ _ _ H) as [H1 H2]. split; [exact H1 | exact (anc_up _ _ _ _ Eb H2)].
Qed.

(** One step of the predecessor fold combines the accumulator so far
    with the next predecessor p by calling [common_dominator]. *)
Definition common_step (fuel : nat) (num : nmap Z) (t : nmap name) (acc : option name) (p : name)
  : option name :=
  let* c := acc in common_dominator fuel num t p c.

(** If finding a common ancestor for two predecessors runs out of fuel,
    the remaining fold over the predecessor list fails immediately. *)
Lemma common_fold_none : forall fuel num t others, fold_left (common_step fuel num t) others None = None.
Proof. intros fuel num t others. induction others as [|p others IH]; [reflexivity | exact IH]. Qed.

(** When a block has several predecessors, we find their common ancestor
    by folding [common_step] over the remaining predecessors starting
    from the first predecessor c0. The resulting label nw is an ancestor
    of c0 and of every other predecessor in the list. *)
Lemma common_fold_anc : forall fuel num t others c0 nw,
  fold_left (common_step fuel num t) others (Some c0) = Some nw ->
  anc t nw c0 /\ forall p, In p others -> anc t nw p.
Proof.
  intros fuel num t others. induction others as [|p others IH]; simpl; intros c0 nw H.
  - injection H as <-. split; [constructor | intros p []].
  - simpl in H.
    destruct (common_dominator fuel num t p c0) as [c1|] eqn:E1;
      [|rewrite common_fold_none in H; discriminate H].
    destruct (IH _ _ H) as [H1 H2]. destruct (common_dominator_anc _ _ _ _ _ _ E1) as [Hp Hc].
    split; [exact (anc_trans _ _ _ _ H1 Hc)|].
    intros p' [<- | Hin]; [exact (anc_trans _ _ _ _ H1 Hp) | exact (H2 _ Hin)].
Qed.

(** ### The sweeps to the fixpoint *)

(** A sweep of `label_idoms/5` over the labels that has failed stays failed. *)
Lemma label_idoms_none : forall preds num cf ls, fold_left (label_idoms preds num cf) ls None = None.
Proof. intros preds num cf ls. induction ls as [|b ls IH]; [reflexivity | exact IH]. Qed.

(** A sweep that has changed some immediate dominator ends with its changed
    flag still set. *)
Lemma label_idoms_changed : forall preds num cf ls t t' c,
  fold_left (label_idoms preds num cf) ls (Some (t, true)) = Some (t', c) -> c = true.
Proof.
  intros preds num cf ls. induction ls as [|b ls IH]; simpl; intros t t' c H.
  - injection H as _ <-. reflexivity.
  - simpl in H.
    destruct (nm_find b preds) as [ps|]; [|rewrite label_idoms_none in H; discriminate H].
    destruct (filter _ ps) as [|first others]; [rewrite label_idoms_none in H; discriminate H|].
    destruct (fold_left _ others (Some first)) as [nw|]; [|rewrite label_idoms_none in H; discriminate H].
    destruct (nm_find b t) as [old|].
    + destruct (name_eqb old nw); exact (IH _ _ _ H).
    + exact (IH _ _ _ H).
Qed.

(** The fixpoint loop stops as soon as a sweep over the blocks makes no
    changes. At that point, the parent map t is unchanged, and every
    block b in ls already maps to the meet of its predecessors that have
    parents. *)
Lemma label_idoms_unchanged : forall preds num cf ls t t',
  fold_left (label_idoms preds num cf) ls (Some (t, false)) = Some (t', false) ->
  t' = t /\ forall b, In b ls -> exists ps first others nw,
    nm_find b preds = Some ps /\ filter (fun p => nm_mem p t) ps = first :: others /\
    fold_left (common_step cf num t) others (Some first) = Some nw /\ nm_find b t = Some nw.
Proof.
  intros preds num cf ls. induction ls as [|b ls IH]; simpl; intros t t' H.
  - injection H as <-. split; [reflexivity | intros b []].
  - simpl in H.
    destruct (nm_find b preds) as [ps|] eqn:Ep; [|rewrite label_idoms_none in H; discriminate H].
    destruct (filter _ ps) as [|first others] eqn:Ef; [rewrite label_idoms_none in H; discriminate H|].
    destruct (fold_left _ others (Some first)) as [nw|] eqn:Ec; [|rewrite label_idoms_none in H; discriminate H].
    destruct (nm_find b t) as [old|] eqn:Eo.
    + destruct (name_eqb old nw) eqn:En.
      * apply name_eqb_true in En. subst old. destruct (IH _ _ H) as [-> Hall]. split; [reflexivity|].
        intros b' [<- | Hin]; [|exact (Hall _ Hin)].
        exists ps, first, others, nw. auto.
      * apply label_idoms_changed in H. discriminate H.
    + apply label_idoms_changed in H. discriminate H.
Qed.

(** The map M that `idom_fixpoint/5` returns is a fixpoint: one more sweep
    over the labels changes nothing. *)
Lemma idom_fixpoint_final : forall fuel ls preds num cf t M,
  idom_fixpoint fuel ls preds num cf t = Some M ->
  fold_left (label_idoms preds num cf) ls (Some (M, false)) = Some (M, false).
Proof.
  induction fuel as [|fuel IH]; intros ls preds num cf t M H; simpl in H; [discriminate H|].
  destruct (fold_left (label_idoms preds num cf) ls (Some (t, false))) as [[t1 c]|] eqn:E; [|discriminate H].
  destruct c; [exact (IH _ _ _ _ _ _ H)|].
  injection H as <-. destruct (label_idoms_unchanged _ _ _ _ _ _ E) as [-> _]. exact E.
Qed.

(** A label k that a sweep does not visit keeps its entry in the map through
    the sweep. *)
Lemma label_idoms_other : forall preds num cf ls k t c t' c',
  ~ In k ls -> fold_left (label_idoms preds num cf) ls (Some (t, c)) = Some (t', c') ->
  nm_find k t' = nm_find k t.
Proof.
  intros preds num cf ls. induction ls as [|b ls IH]; simpl; intros k t c t' c' Hk H.
  - injection H as <- _. reflexivity.
  - simpl in H.
    destruct (nm_find b preds) as [ps|]; [|rewrite label_idoms_none in H; discriminate H].
    destruct (filter _ ps) as [|first others]; [rewrite label_idoms_none in H; discriminate H|].
    destruct (fold_left _ others (Some first)) as [nw|]; [|rewrite label_idoms_none in H; discriminate H].
    assert (Hkb : name_eqb k b = false) by (apply name_eqb_false; intros ->; apply Hk; left; reflexivity).
    destruct (nm_find b t) as [old|].
    + destruct (name_eqb old nw).
      * exact (IH _ _ _ _ _ (fun Hin => Hk (or_intror Hin)) H).
      * rewrite (IH _ _ _ _ _ (fun Hin => Hk (or_intror Hin)) H), nm_find_add, Hkb. reflexivity.
    + rewrite (IH _ _ _ _ _ (fun Hin => Hk (or_intror Hin)) H), nm_find_add, Hkb. reflexivity.
Qed.

(** A label k outside the sweep list ls keeps its initial parent across
    all iterations of [idom_fixpoint]. In particular, the function entry
    retains itself as its own parent throughout the sweeps. *)
Lemma idom_fixpoint_other : forall fuel ls preds num cf t M k,
  ~ In k ls -> idom_fixpoint fuel ls preds num cf t = Some M -> nm_find k M = nm_find k t.
Proof.
  induction fuel as [|fuel IH]; intros ls preds num cf t M k Hk H; simpl in H; [discriminate H|].
  destruct (fold_left (label_idoms preds num cf) ls (Some (t, false))) as [[t1 c]|] eqn:E; [|discriminate H].
  rewrite <- (label_idoms_other _ _ _ _ _ _ _ _ _ Hk E).
  destruct c; [exact (IH _ _ _ _ _ _ _ Hk H)|]. injection H as <-. reflexivity.
Qed.

(** ### What the fixpoint satisfies *)

(** When the immediate-dominator loop stops changing, the resulting parent
    map links every reachable block to its immediate dominator. Before the
    final step removes the entry block's self-loop, the entry maps to
    itself, every other block in reverse postorder has a parent that is a
    common ancestor of its active predecessors, and only blocks in reverse
    postorder appear in the map.

    To prove that those parents are the nearest common ancestors, this
    record also tracks two structural facts: every parent equals the meet
    of its predecessors, and the reverse postorder contains no duplicates
    while placing each non-entry block after at least one predecessor. *)
Record idoms_ok (g : cfg) (M : nmap name) : Prop := {
  idoms_entry : nm_find (cfg_entry g) M = Some (cfg_entry g);
  idoms_meet : forall b, In b (cfg_rpo g) -> b <> cfg_entry g ->
               exists nw, nm_find b M = Some nw /\
               forall p ps, nm_find b (cfg_preds g) = Some ps -> In p ps -> nm_mem p M = true -> anc M nw p;
  idoms_dom : forall x, nm_mem x M = true -> In x (cfg_rpo g);
  idoms_fold : forall b, In b (cfg_rpo g) -> b <> cfg_entry g ->
               exists cf ps first others nw,
               nm_find b (cfg_preds g) = Some ps /\ filter (fun p => nm_mem p M) ps = first :: others /\
               fold_left (common_step cf (labels_numbered (cfg_rpo g)) M) others (Some first) = Some nw /\
               nm_find b M = Some nw;
  idoms_nodup : NoDup (cfg_rpo g);
  idoms_parent : forall u x v, cfg_rpo g = u ++ x :: v -> x <> cfg_entry g ->
                 exists p ps, In p u /\ nm_find x (cfg_preds g) = Some ps /\ In p ps
}.

(** Combining the graph and fixpoint steps shows that [cfg_idoms]
    produces a valid immediate-dominator map for any function. The
    returned map t equals a map M satisfying [idoms_ok] with the entry
    label removed. *)
Lemma cfg_idoms_ok : forall bs g t,
  func_cfg bs = Some g -> cfg_idoms g = Some t ->
  exists M, idoms_ok g M /\ t = nm_remove (cfg_entry g) M.
Proof.
  intros bs g t Hg H. destruct (func_cfg_ok _ _ Hg) as [Hok _].
  destruct (cfg_ok_rpo _ _ Hok) as (rest & Hr & Hent).
  unfold cfg_idoms in H. rewrite Hr in H.
  destruct (idom_fixpoint _ _ _ _ _ _) as [M|] eqn:Ef; [|discriminate H]. injection H as <-.
  destruct (label_idoms_unchanged _ _ _ _ _ _ (idom_fixpoint_final _ _ _ _ _ _ _ Ef)) as [_ Hall].
  exists M. split; [|reflexivity]. constructor.
  - rewrite (idom_fixpoint_other _ _ _ _ _ _ _ _ Hent Ef), nm_find_add, term_eqb_refl. reflexivity.
  - intros b Hb Hne. rewrite Hr in Hb. destruct Hb as [E | Hb]; [congruence|].
    destruct (Hall _ Hb) as (ps & first & others & nw & Hp & Hf & Hc & Hb').
    exists nw. split; [exact Hb'|]. intros p ps' Hp' Hin Hm. rewrite Hp in Hp'. injection Hp' as <-.
    assert (Hpin : In p (first :: others)) by (rewrite <- Hf; apply filter_In; auto).
    destruct (common_fold_anc _ _ _ _ _ _ Hc) as [H1 H2].
    destruct Hpin as [<- | Hpin]; [exact H1 | exact (H2 _ Hpin)].
  - intros x Hx. rewrite Hr. destruct (name_eqb x (cfg_entry g)) eqn:Ex.
    + apply name_eqb_true in Ex. left. symmetry. exact Ex.
    + right. destruct (mem x rest) eqn:Em; [apply mem_in; exact Em|].
      assert (Hn : ~ In x rest) by (intros Hin; apply mem_in in Hin; congruence).
      rewrite nm_mem_find, (idom_fixpoint_other _ _ _ _ _ _ _ _ Hn Ef), nm_find_add, Ex, nm_find_empty in Hx.
      destruct Hx as [v Hv]. discriminate Hv.
  - intros b Hb Hne. rewrite Hr in Hb. destruct Hb as [E | Hb]; [congruence|].
    destruct (Hall _ Hb) as (ps & first & others & nw & Hp & Hf & Hc & Hb').
    rewrite Hr. exists (S (2 * length (cfg_entry g :: rest))), ps, first, others, nw. auto.
  - exact (func_cfg_nodup _ _ Hg).
  - exact (func_cfg_parent _ _ Hg).
Qed.

(** ## The nearest common ancestor

    When two paths merge at a block, [common_dominator] walks up from
    whichever label appears later in reverse postorder until both paths
    meet. That walk finds their nearest common ancestor whenever every
    ancestor of a block precedes it in the order. At the fixpoint, each
    non-entry block has a parent that dominates a predecessor listed
    before it. By induction on the order, every ancestor of that
    predecessor also precedes it, so [idoms_nca] shows that any common
    ancestor of the predecessors is an ancestor of the block's parent. *)

(** ### Ranks in the reverse postorder *)

(** One step of [labels_numbered] assigns the next integer index to
    label l and increments the counter. *)
Definition number_step (acc : Z * nmap Z) (l : name) : Z * nmap Z :=
  (fst acc + 1, nm_add l (fst acc) (snd acc)).

(** Numbering the labels ls leaves the number of a label not in ls as it
    was. *)
Lemma number_fold_out : forall ls x acc,
  ~ In x ls -> nm_find x (snd (fold_left number_step ls acc)) = nm_find x (snd acc).
Proof.
  induction ls as [|l ls IH]; simpl; intros x acc Hx; [reflexivity|].
  rewrite IH by (intros Hin; apply Hx; right; exact Hin). unfold number_step. simpl.
  rewrite nm_find_add. destruct (name_eqb x l) eqn:E; [|reflexivity].
  apply name_eqb_true in E. subst. exfalso. apply Hx. left. reflexivity.
Qed.

(** In a list ls without repeats, numbering from a counter at n gives the
    label x, written ls = u ++ x :: v, the number n plus the length of u. *)
Lemma number_fold_at : forall u ls x v acc, NoDup ls -> ls = u ++ x :: v ->
  nm_find x (snd (fold_left number_step ls acc)) = Some (fst acc + Z.of_nat (length u)).
Proof.
  induction u as [|y u IH]; simpl; intros ls x v acc Hnd ->.
  - inversion Hnd as [|? ? Hx _]. cbn [fold_left]. rewrite number_fold_out by exact Hx.
    unfold number_step. simpl. rewrite nm_find_add, term_eqb_refl. f_equal. lia.
  - inversion Hnd as [|? ? _ Hnd']. cbn [fold_left]. rewrite (IH _ x v _ Hnd' eq_refl).
    unfold number_step. simpl. f_equal. lia.
Qed.

(** This section fixes a control-flow graph g whose immediate
    dominators form a valid parent map M starting at the function entry. *)
Section Nca.

Variables (g : cfg) (M : nmap name).
Hypothesis HM : idoms_ok g M.
Hypothesis Hr0 : exists rest, cfg_rpo g = cfg_entry g :: rest.

(** The function [rank] returns the zero-based position of label x in
    g's reverse postorder, or -1 if x does not appear in the order. *)
Definition rank (x : name) : Z :=
  match nm_find x (labels_numbered (cfg_rpo g)) with Some i => i | None => -1 end.

(** The label x of the order, written u ++ x :: v, is numbered by the length
    of u, and that is its rank. *)
Lemma rank_at : forall u x v, cfg_rpo g = u ++ x :: v ->
  nm_find x (labels_numbered (cfg_rpo g)) = Some (Z.of_nat (length u)) /\ rank x = Z.of_nat (length u).
Proof.
  intros u x v E. unfold rank, labels_numbered.
  change (fun acc l => (fst acc + 1, nm_add l (fst acc) (snd acc))) with number_step.
  rewrite (number_fold_at u _ x v (0, nm_empty) (idoms_nodup _ _ HM) E). split; reflexivity.
Qed.

(** Every label of the order is numbered, with its rank. *)
Lemma rank_find : forall x, In x (cfg_rpo g) -> nm_find x (labels_numbered (cfg_rpo g)) = Some (rank x).
Proof.
  intros x Hx. destruct (in_split _ _ Hx) as (u & v & E). destruct (rank_at _ _ _ E) as [-> ->]. reflexivity.
Qed.

(** A label of the order has a rank of 0 or more. *)
Lemma rank_nonneg : forall x, In x (cfg_rpo g) -> 0 <= rank x.
Proof.
  intros x Hx. destruct (in_split _ _ Hx) as (u & v & E). rewrite (proj2 (rank_at _ _ _ E)). lia.
Qed.

(** A label listed before another has a smaller rank. *)
Lemma rank_before : forall u x v p, cfg_rpo g = u ++ x :: v -> In p u -> rank p < rank x.
Proof.
  intros u x v p E Hp. destruct (in_split _ _ Hp) as (u1 & u2 & ->).
  rewrite (proj2 (rank_at _ _ _ E)).
  rewrite <- app_assoc in E. simpl in E. rewrite (proj2 (rank_at _ _ _ E)).
  rewrite length_app. simpl. lia.
Qed.

(** The function entry always appears in the reverse postorder of g. *)
Lemma entry_in : In (cfg_entry g) (cfg_rpo g).
Proof. destruct Hr0 as (rest & ->). left. reflexivity. Qed.

(** Every label of the order has a parent in M. *)
Lemma rpo_mem : forall x, In x (cfg_rpo g) -> nm_mem x M = true.
Proof.
  intros x Hx. apply nm_mem_find. destruct (name_eqb x (cfg_entry g)) eqn:E.
  - apply name_eqb_true in E. subst. exists (cfg_entry g). exact (idoms_entry _ _ HM).
  - apply name_eqb_false in E. destruct (idoms_meet _ _ HM _ Hx E) as (nw & Hnw & _). eauto.
Qed.

(** Walking up the dominator tree must terminate because every parent
    precedes its child in reverse postorder. For any label b in the
    order, its parent c also lies in the order and has a strictly
    smaller rank unless b is the entry. *)
Lemma idom_rank : forall b c, In b (cfg_rpo g) -> nm_find b M = Some c ->
  In c (cfg_rpo g) /\ ((b = cfg_entry g /\ c = b) \/ rank c < rank b).
Proof.
  assert (Main : forall k b c, (Z.to_nat (rank b) < k)%nat -> In b (cfg_rpo g) -> nm_find b M = Some c ->
                 In c (cfg_rpo g) /\ ((b = cfg_entry g /\ c = b) \/ rank c < rank b)).
  { induction k as [|k IH]; intros b c Hk Hb Hc; [lia|].
    destruct (name_eqb b (cfg_entry g)) eqn:Eb.
    - apply name_eqb_true in Eb. subst b. rewrite (idoms_entry _ _ HM) in Hc. injection Hc as <-.
      split; [exact entry_in | left; auto].
    - apply name_eqb_false in Eb.
      destruct (idoms_meet _ _ HM _ Hb Eb) as (nw & Hnw & Hanc). rewrite Hc in Hnw. injection Hnw as <-.
      destruct (in_split _ _ Hb) as (u & v & E).
      destruct (idoms_parent _ _ HM _ _ _ E Eb) as (p & ps & Hp & Hps & Hin).
      assert (HpR : In p (cfg_rpo g)) by (rewrite E; apply in_or_app; left; exact Hp).
      pose proof (rank_before _ _ _ _ E Hp) as Hlt.
      pose proof (Hanc _ _ Hps Hin (rpo_mem _ HpR)) as Hcp.
      assert (Up : forall a y, anc M a y -> In y (cfg_rpo g) -> rank y < rank b ->
                   In a (cfg_rpo g) /\ rank a <= rank y).
      { intros a y Ha. induction Ha as [|y z Hf _ IHa]; intros Hy Hyb; [split; [exact Hy | lia]|].
        assert (Hyk : (Z.to_nat (rank y) < k)%nat) by (pose proof (rank_nonneg _ Hy); lia).
        destruct (IH _ _ Hyk Hy Hf) as [Hz Hzy].
        assert (rank z <= rank y) by (destruct Hzy as [[_ ->] | Hzy]; lia).
        destruct (IHa Hz ltac:(lia)) as [Ha Hrz]. split; [exact Ha | lia]. }
      destruct (Up _ _ Hcp HpR Hlt) as [HcR Hrc]. split; [exact HcR | right; lia]. }
  intros b c Hb Hc. exact (Main (S (Z.to_nat (rank b))) b c ltac:(lia) Hb Hc).
Qed.

(** An ancestor a of a label y of the order is in the order, and is y or
    comes before it. *)
Lemma anc_rank : forall a y, anc M a y -> In y (cfg_rpo g) ->
  In a (cfg_rpo g) /\ (a = y \/ rank a < rank y).
Proof.
  intros a y H. induction H as [|y z Hf _ IH]; intros Hy; [auto|].
  destruct (idom_rank _ _ Hy Hf) as [Hz Hzy]. destruct (IH Hz) as [Ha Haz]. split; [exact Ha|].
  destruct Hzy as [[_ ->] | Hzy]; destruct Haz as [-> | Haz]; auto; right; lia.
Qed.

(** ### The meet is the nearest common ancestor *)

(** Meeting two labels a and b of the order with [common_dominator] gives a
    label c of the order below every common ancestor of a and b: whatever is
    an ancestor of both is an ancestor of c. *)
Lemma common_dominator_nca : forall fuel a b c,
  In a (cfg_rpo g) -> In b (cfg_rpo g) ->
  common_dominator fuel (labels_numbered (cfg_rpo g)) M a b = Some c ->
  In c (cfg_rpo g) /\ forall D, anc M D a -> anc M D b -> anc M D c.
Proof.
  induction fuel as [|fuel IH]; intros a b c Ha Hb H; simpl in H; [discriminate H|].
  destruct (name_eqb a b) eqn:E.
  - injection H as <-. split; [exact Ha | auto].
  - apply name_eqb_false in E. rewrite (rank_find _ Ha), (rank_find _ Hb) in H.
    destruct (rank b <? rank a) eqn:Elt.
    + apply Z.ltb_lt in Elt.
      destruct (nm_find a M) as [a1|] eqn:Ea; [|discriminate H].
      destruct (idom_rank _ _ Ha Ea) as [Ha1 _].
      destruct (IH _ _ _ Ha1 Hb H) as [Hc Hn]. split; [exact Hc|].
      intros D Hda Hdb. apply Hn; [|exact Hdb].
      inversion Hda as [Eq | a' c' Hf Hdc]; subst.
      * destruct (anc_rank _ _ Hdb Hb) as [_ [-> | Hlt]]; [congruence | lia].
      * rewrite Ea in Hf. injection Hf as <-. exact Hdc.
    + apply Z.ltb_ge in Elt.
      destruct (nm_find b M) as [b1|] eqn:Eb; [|discriminate H].
      destruct (idom_rank _ _ Hb Eb) as [Hb1 _].
      destruct (IH _ _ _ Ha Hb1 H) as [Hc Hn]. split; [exact Hc|].
      intros D Hda Hdb. apply Hn; [exact Hda|].
      inversion Hdb as [Eq | b' c' Hf Hdc]; subst.
      * destruct (anc_rank _ _ Hda Ha) as [_ [-> | Hlt]]; [congruence | lia].
      * rewrite Eb in Hf. injection Hf as <-. exact Hdc.
Qed.

(** Folding [common_step] over a block's predecessors in reverse
    postorder preserves any common ancestor D. If D is an ancestor of
    every predecessor in the list, then D is also an ancestor of the
    folded meet nw. *)
Lemma common_fold_nca : forall cf others c0 nw,
  In c0 (cfg_rpo g) -> (forall p, In p others -> In p (cfg_rpo g)) ->
  fold_left (common_step cf (labels_numbered (cfg_rpo g)) M) others (Some c0) = Some nw ->
  forall D, anc M D c0 -> (forall p, In p others -> anc M D p) -> anc M D nw.
Proof.
  intros cf others. induction others as [|p others IH]; simpl; intros c0 nw Hc0 Ho H D Hd Hp.
  - injection H as <-. exact Hd.
  - simpl in H.
    destruct (common_dominator cf _ M p c0) as [c1|] eqn:E1; [|rewrite common_fold_none in H; discriminate H].
    destruct (common_dominator_nca _ _ _ _ (Ho p (or_introl eq_refl)) Hc0 E1) as [Hc1 Hn].
    refine (IH _ _ Hc1 (fun q Hq => Ho q (or_intror Hq)) H D _ (fun q Hq => Hp q (or_intror Hq))).
    exact (Hn _ (Hp p (or_introl eq_refl)) Hd).
Qed.

(** Any label D that dominates every active predecessor of a non-entry
    block b must also dominate b's parent. Theorem [dom_meet] uses this
    property to carry invariants across control-flow merge points. *)
Theorem idoms_nca : forall b D, In b (cfg_rpo g) -> b <> cfg_entry g ->
  (forall p ps, nm_find b (cfg_preds g) = Some ps -> In p ps -> nm_mem p M = true -> anc M D p) ->
  exists nw, nm_find b M = Some nw /\ anc M D nw.
Proof.
  intros b D Hb Hne Hd.
  destruct (idoms_fold _ _ HM _ Hb Hne) as (cf & ps & first & others & nw & Hps & Hf & Hc & Hnw).
  exists nw. split; [exact Hnw|].
  assert (Hin : forall p, In p (first :: others) -> In p ps /\ nm_mem p M = true)
    by (intros p Hp; rewrite <- Hf in Hp; apply filter_In in Hp; exact Hp).
  refine (common_fold_nca _ _ _ _ _ _ Hc D _ _).
  - exact (idoms_dom _ _ HM _ (proj2 (Hin first (or_introl eq_refl)))).
  - intros p Hp. exact (idoms_dom _ _ HM _ (proj2 (Hin p (or_intror Hp)))).
  - destruct (Hin first (or_introl eq_refl)) as [H1 H2]. exact (Hd _ _ Hps H1 H2).
  - intros p Hp. destruct (Hin p (or_intror Hp)) as [H1 H2]. exact (Hd _ _ Hps H1 H2).
Qed.

End Nca.

(** ## The children of each label

    `dom_children/3` turns the map of parents into a map of each
    label's children, which the preorder numbering walks down. *)

(** One step of [dom_children] prepends label l to its parent's child
    list if l has a parent in t, or fails if that parent has no entry. *)
Definition child_step (t : nmap name) (acc : option (nmap (list name))) (l : name)
  : option (nmap (list name)) :=
  let* kids := acc in
  match nm_find l t with
  | Some parent => let* cs := nm_find parent kids in Some (nm_add parent (l :: cs) kids)
  | None => Some kids
  end.

(** The children map kids after the labels D have been processed: each
    label's list holds, once each, exactly the labels of D whose parent in t
    it is, and every parent of a label of D has a list. *)
Definition kids_inv (t : nmap name) (kids : nmap (list name)) (D : name -> Prop) : Prop :=
  (forall x ks, nm_find x kids = Some ks -> NoDup ks /\ forall k, In k ks <-> D k /\ nm_find k t = Some x) /\
  (forall k x, D k -> nm_find k t = Some x -> nm_mem x kids = true).

(** [kids_inv] depends only on which labels have been processed, not on how
    that set is written. *)
Lemma kids_inv_iff : forall t kids (D D' : name -> Prop),
  (forall k, D k <-> D' k) -> kids_inv t kids D -> kids_inv t kids D'.
Proof.
  intros t kids D D' E [H1 H2]. split.
  - intros x ks Hf. destruct (H1 _ _ Hf) as [Hn Hk]. split; [exact Hn|].
    intros k. rewrite Hk, E. reflexivity.
  - intros k x Hd Ht. apply (H2 k x); [apply E; exact Hd | exact Ht].
Qed.

(** A failed fold of [child_step] stays failed. *)
Lemma child_fold_none : forall t ls, fold_left (child_step t) ls None = None.
Proof. intros t ls. induction ls as [|l ls IH]; [reflexivity | exact IH]. Qed.

(** Running one [child_step] on an unprocessed label l preserves
    [kids_inv] while adding l to the set of processed labels. *)
Lemma child_step_inv : forall t kids kids1 l (D : name -> Prop),
  ~ D l -> kids_inv t kids D -> child_step t (Some kids) l = Some kids1 ->
  kids_inv t kids1 (fun k => k = l \/ D k).
Proof.
  intros t kids kids1 l D Hd [H1 H2] Es. unfold child_step in Es. simpl in Es.
  destruct (nm_find l t) as [parent|] eqn:Et.
  - destruct (nm_find parent kids) as [cs|] eqn:Ec; [|discriminate Es]. injection Es as <-. split.
    + intros x ks Hf. rewrite nm_find_add in Hf. destruct (name_eqb x parent) eqn:Ex.
      * apply name_eqb_true in Ex. subst x. injection Hf as <-.
        destruct (H1 _ _ Ec) as [Hnc Hc]. split.
        -- constructor; [|exact Hnc]. intros Hin. apply Hc in Hin as [Hdl _]. exact (Hd Hdl).
        -- intros k. simpl. rewrite Hc. split.
           ++ intros [<- | [Hk Hkt]]; [auto | auto].
           ++ intros [[<- | Hk] Hkt]; [left; reflexivity | right; auto].
      * destruct (H1 _ _ Hf) as [Hnk Hk]. split; [exact Hnk|]. intros k. rewrite Hk. split.
        -- intros [Hk' Hkt]. auto.
        -- intros [[<- | Hk'] Hkt]; [|auto]. rewrite Et in Hkt. injection Hkt as Ex'.
           subst x. rewrite term_eqb_refl in Ex. discriminate Ex.
    + intros k x [<- | Hk] Hkt; rewrite nm_mem_add_iff.
      * rewrite Et in Hkt. injection Hkt as <-. left. reflexivity.
      * right. exact (H2 _ _ Hk Hkt).
  - injection Es as <-. split.
    + intros x ks Hf. destruct (H1 _ _ Hf) as [Hnk Hk]. split; [exact Hnk|]. intros k. rewrite Hk.
      split; [intros [Hk' Hkt]; auto|]. intros [[<- | Hk'] Hkt]; [congruence | auto].
    + intros k x [<- | Hk] Hkt; [congruence | exact (H2 _ _ Hk Hkt)].
Qed.

(** Folding [child_step] over a duplicate-free list ls of unprocessed
    labels preserves [kids_inv] and adds every label in ls to the
    processed set. *)
Lemma child_fold : forall t ls kids kids' (D : name -> Prop),
  NoDup ls -> (forall l, In l ls -> ~ D l) -> kids_inv t kids D ->
  fold_left (child_step t) ls (Some kids) = Some kids' ->
  kids_inv t kids' (fun k => In k ls \/ D k).
Proof.
  intros t ls. induction ls as [|l ls IH]; intros kids kids' D Hn Hd Hi H; cbn [fold_left] in H.
  - injection H as <-. apply (kids_inv_iff _ _ D); [|exact Hi]. intros k. split; auto. intros [[] | Hk]. exact Hk.
  - inversion Hn as [|l0 ls0 Hl Hn']. subst l0 ls0.
    destruct (child_step t (Some kids) l) as [kids1|] eqn:Es; [|rewrite child_fold_none in H; discriminate H].
    pose proof (child_step_inv _ _ _ _ _ (Hd l (or_introl eq_refl)) Hi Es) as Hi1.
    assert (Hd1 : forall l', In l' ls -> ~ (l' = l \/ D l')).
    { intros l' Hin [-> | Hdl]; [exact (Hl Hin) | exact (Hd l' (or_intror Hin) Hdl)]. }
    refine (kids_inv_iff _ _ _ _ _ (IH _ _ _ Hn' Hd1 Hi1 H)).
    intros k. simpl. split; [intros [Hk | [<- | Hk]]; auto | intros [[<- | Hk] | Hk]; auto].
Qed.

(** When the reverse postorder of g has no duplicates, [dom_children]
    builds a children map from parent map t that lists under each x
    exactly the reverse-postorder labels whose parent is x. Every label
    with a parent appears in that parent's child list. *)
Lemma dom_children_spec : forall g t kids,
  NoDup (cfg_rpo g) -> dom_children g t = Some kids ->
  (forall x ks, nm_find x kids = Some ks -> forall k, In k ks <-> In k (cfg_rpo g) /\ nm_find k t = Some x) /\
  (forall k x, In k (cfg_rpo g) -> nm_find k t = Some x -> exists ks, nm_find x kids = Some ks /\ In k ks).
Proof.
  intros g t kids Hn H. unfold dom_children in H.
  assert (H0 : kids_inv t (nm_of_list (map (fun l => (l, [])) (cfg_rpo g))) (fun _ => False)).
  { split; [|intros k x []]. intros x ks Hf. unfold nm_of_list in Hf.
    rewrite nm_find_fold_add, nm_find_empty in Hf.
    destruct (lookup x (rev _)) as [v|] eqn:E; [|discriminate Hf]. injection Hf as <-.
    destruct (lookup_some_in _ _ _ _ E) as (k' & _ & Hin). rewrite <- in_rev in Hin.
    apply in_map_iff in Hin as (l & El & _). injection El as _ <-. split; [constructor|]. intros k. split; [intros [] | intros [[] _]]. }
  destruct (child_fold t (rev (cfg_rpo g)) _ _ _ (NoDup_rev Hn) (fun l _ H => H) H0 H) as [H1 H2].
  split.
  - intros x ks Hf k. destruct (H1 _ _ Hf) as [_ Hk]. rewrite Hk, <- in_rev. tauto.
  - intros k x Hk Ht. destruct (proj1 (nm_mem_find _ _ _) (H2 k x (or_introl (proj1 (in_rev (cfg_rpo g) k) Hk)) Ht))
      as [ks Hf].
    exists ks. split; [exact Hf|]. apply (proj2 (H1 _ _ Hf)). split; [left; rewrite <- in_rev; exact Hk | exact Ht].
Qed.

(** ## Subtrees and their intervals

    After building the children map, [subtree_intervals] walks down the
    dominator tree and numbers every node in preorder. Each node
    receives an interval from its own preorder number to the highest
    number in its subtree. One node's interval therefore contains
    another's entry number exactly when the second node is a descendant
    of the first. *)

(** Fixes the children map K: the tree given by each label's list of
    children. *)
Section Tree.

Variable K : nmap (list name).

(** In the children map K, b is a descendant of a k generations down: a
    itself at 0, or a child of a descendant one generation up. *)
Inductive descn (a : name) : name -> nat -> Prop :=
| descn_refl : descn a a 0
| descn_kid : forall p ks b k, descn a p k -> nm_find p K = Some ks -> In b ks -> descn a b (S k).

(** b is a descendant of a in K, at some depth; a label is its own
    descendant. *)
Definition desc (a b : name) : Prop := exists k, descn a b k.

(** Takes [descn] apart: a descendant at depth k is a itself at depth 0, or
    a child of a descendant one generation up. *)
Lemma descn_inv : forall a b k, descn a b k ->
  (b = a /\ k = 0%nat) \/ exists p ks k', k = S k' /\ descn a p k' /\ nm_find p K = Some ks /\ In b ks.
Proof. intros a b k H. destruct H as [|p ks b k Hp Hf Hb]; [left; auto | right; eauto 8]. Qed.

(** A descendant at depth j of a descendant at depth k of a is a descendant
    of a at depth k + j. *)
Lemma descn_trans : forall a b c k j, descn a b k -> descn b c j -> descn a c (k + j).
Proof.
  intros a b c k j Hab Hbc. induction Hbc as [|p ks c' j Hbp IH Hp Hc].
  - rewrite Nat.add_0_r. exact Hab.
  - rewrite Nat.add_succ_r. exact (descn_kid _ _ _ _ _ IH Hp Hc).
Qed.

(** Every label is its own descendant. *)
Lemma desc_refl : forall a, desc a a.
Proof. intros a. exists 0%nat. constructor. Qed.

(** A descendant of a descendant of a is a descendant of a. *)
Lemma desc_trans : forall a b c, desc a b -> desc b c -> desc a c.
Proof. intros a b c [k Hk] [j Hj]. exists (k + j)%nat. exact (descn_trans _ _ _ _ _ Hk Hj). Qed.

(** A child of a descendant of a is a descendant of a. *)
Lemma desc_kid : forall a p ks b, desc a p -> nm_find p K = Some ks -> In b ks -> desc a b.
Proof. intros a p ks b [k Hk] Hp Hb. exists (S k). exact (descn_kid _ _ _ _ _ Hk Hp Hb). Qed.

(** A descendant b of a at depth k + 1 is, going down from a, a descendant
    at depth k of one of a's children. *)
Lemma descn_first : forall a b k, descn a b (S k) ->
  exists ks c, nm_find a K = Some ks /\ In c ks /\ descn c b k.
Proof.
  intros a b k H. remember (S k) as n eqn:En. revert k En.
  induction H as [|p ks b' n Hp IH Hf Hb]; intros k En; [discriminate En|].
  injection En as <-. destruct n as [|n].
  - destruct (descn_inv _ _ _ Hp) as [[-> _] | (p' & ks' & k' & E & _)]; [|discriminate E].
    exists ks, b'. split; [exact Hf|]. split; [exact Hb | constructor].
  - destruct (IH _ eq_refl) as (ks' & c & Ha & Hc & Hcp). exists ks', c. split; [exact Ha|].
    split; [exact Hc | exact (descn_kid _ _ _ _ _ Hcp Hf Hb)].
Qed.

(** A descendant of a is a itself or a descendant of one of its
    children. *)
Lemma desc_split : forall a ks b, nm_find a K = Some ks -> desc a b ->
  b = a \/ exists c, In c ks /\ desc c b.
Proof.
  intros a ks b Ha [k Hk]. destruct k as [|k].
  - left. destruct (descn_inv _ _ _ Hk) as [[Eb _] | (p0 & ks0 & k0 & E & _)]; [exact Eb | discriminate E].
  - right. destruct (descn_first _ _ _ Hk) as (ks' & c & Ha' & Hc & Hcb). rewrite Ha in Ha'.
    injection Ha' as <-. exists c. split; [exact Hc|]. exists k. exact Hcb.
Qed.

(** A path of k generations from a back down to a can be repeated m times,
    giving one of k times m generations: a cycle would make the tree as deep
    as one likes. *)
Lemma descn_iter : forall a k m, descn a a k -> descn a a (k * m).
Proof.
  intros a k m H. induction m as [|m IH].
  - rewrite Nat.mul_0_r. constructor.
  - rewrite Nat.mul_succ_r. exact (descn_trans _ _ _ _ _ IH H).
Qed.

(** Each label is a child of at most one label: two lists of children that
    hold the same label are the same parent's. *)
Hypothesis kids_unique : forall x y ks ks' k,
  nm_find x K = Some ks -> In k ks -> nm_find y K = Some ks' -> In k ks' -> x = y.

(** Two labels with a descendant in common are one below the other:
    walking up from it, each label has one parent. *)
Lemma descn_back : forall c z k, descn c z k -> forall c' j, descn c' z j -> desc c c' \/ desc c' c.
Proof.
  intros c z k H. induction H as [|p ks z k Hcp IH Hp Hz]; intros c' j H'.
  - right. exists j. exact H'.
  - destruct (descn_inv _ _ _ H') as [[-> _] | (p' & ks' & j' & _ & Hcp' & Hp' & Hz')].
    + left. exists (S k). exact (descn_kid _ _ _ _ _ Hcp Hp Hz).
    + rewrite <- (kids_unique _ _ _ _ _ Hp Hz Hp' Hz') in Hcp'. exact (IH _ _ Hcp').
Qed.

(** ### The preorder numbering *)

(** One step of the fold `subtree_intervals/6` makes over a label's
    children: number the subtree of the child c from the counter and
    intervals so far. *)
Definition si_step (f : nat) (acc : option (Z * nmap (Z * Z))) (c : name) : option (Z * nmap (Z * Z)) :=
  let* a := acc in subtree_intervals f K c (fst a) (snd a).

(** Unfolding [subtree_intervals] by one step on label L numbers the
    subtrees of L's children starting from n0 + 1, then assigns L the
    interval from n0 to the last number used. *)
Lemma si_unfold : forall f L n0 ivs, subtree_intervals (S f) K L n0 ivs =
  match nm_find L K with
  | Some ks =>
      match fold_left (si_step f) ks (Some (n0 + 1, ivs)) with
      | Some (n, ivs1) => Some (n, nm_add L (n0, n - 1) ivs1)
      | None => None
      end
  | None => None
  end.
Proof. reflexivity. Qed.

(** A failed fold of [si_step] stays failed. *)
Lemma si_fold_none : forall f ks, fold_left (si_step f) ks None = None.
Proof. intros f ks. induction ks as [|c ks IH]; [reflexivity | exact IH]. Qed.

(** If numbering a whole list of child subtrees succeeds, then numbering
    each individual child c in ks also succeeded from some starting
    counter and interval map. *)
Lemma si_fold_each : forall f ks a r, fold_left (si_step f) ks (Some a) = Some r ->
  forall c, In c ks -> exists n0 iv r', subtree_intervals f K c n0 iv = Some r'.
Proof.
  intros f ks. induction ks as [|c0 ks IH]; intros a r H c Hin; [destruct Hin|]. cbn [fold_left] in H.
  change (si_step f (Some a) c0) with (subtree_intervals f K c0 (fst a) (snd a)) in H.
  destruct (subtree_intervals f K c0 (fst a) (snd a)) as [a1|] eqn:E;
    [|rewrite si_fold_none in H; discriminate H].
  destruct Hin as [<- | Hin]; [eauto | exact (IH _ _ H _ Hin)].
Qed.

(** The [[fuel]] of a numbering that succeeds bounds the depth of the
    subtree at L: every descendant of L is fewer generations down than the
    fuel. *)
Lemma si_depth : forall fuel L n0 ivs r, subtree_intervals fuel K L n0 ivs = Some r ->
  forall X k, descn L X k -> (k < fuel)%nat.
Proof.
  induction fuel as [|f IH]; intros L n0 ivs r H X k Hd; [discriminate H|].
  rewrite si_unfold in H. destruct (nm_find L K) as [ks|] eqn:Ek; [|discriminate H].
  destruct (fold_left (si_step f) ks _) as [[n ivs1]|] eqn:Ef; [|discriminate H].
  destruct k as [|k]; [lia|].
  destruct (descn_first _ _ _ Hd) as (ks' & c & Ek' & Hc & Hcx). rewrite Ek in Ek'. injection Ek' as <-.
  destruct (si_fold_each _ _ _ _ Ef _ Hc) as (m & iv & r' & Hs).
  pose proof (IH _ _ _ _ Hs _ _ Hcx). lia.
Qed.

(** So the subtree at L has no cycle: a path from a descendant X of L back
    down to X has no generations. *)
Lemma si_no_cycle : forall fuel L n0 ivs r, subtree_intervals fuel K L n0 ivs = Some r ->
  forall X, desc L X -> forall k, descn X X k -> k = 0%nat.
Proof.
  intros fuel L n0 ivs r H X [j Hj] k Hk. destruct k as [|k]; [reflexivity|]. exfalso.
  pose proof (si_depth _ _ _ _ _ H X _ (descn_trans _ _ _ _ _ Hj (descn_iter _ _ fuel Hk))) as Hl.
  simpl in Hl. lia.
Qed.

(** No descendant X of L but L itself has L as its descendant. *)
Lemma si_acyclic : forall fuel L n0 ivs r, subtree_intervals fuel K L n0 ivs = Some r ->
  forall X, desc L X -> desc X L -> X = L.
Proof.
  intros fuel L n0 ivs r H X Hx [j Hj]. destruct Hx as [i Hi].
  pose proof (si_no_cycle _ _ _ _ _ H L (desc_refl L) _ (descn_trans _ _ _ _ _ Hi Hj)) as E.
  assert (i = 0%nat) by lia. subst i.
  destruct (descn_inv _ _ _ Hi) as [[-> _] | (p0 & ks0 & k0 & E' & _)]; [reflexivity | discriminate E'].
Qed.

(** The predicate [si_ok] states what a successful call to
    [subtree_intervals] on node L guarantees. The returned interval for
    L spans up to the final counter, every descendant of L is numbered
    inside that interval, all other nodes remain untouched, and interval
    containment matches the descendant relation. *)
Definition si_ok (fuel : nat) : Prop :=
  forall L n0 ivs n ivs', subtree_intervals fuel K L n0 ivs = Some (n, ivs') ->
  n0 < n /\
  (forall X, ~ desc L X -> nm_find X ivs' = nm_find X ivs) /\
  (forall X, desc L X -> exists p l, nm_find X ivs' = Some (p, l) /\ n0 <= p <= l /\ l < n) /\
  nm_find L ivs' = Some (n0, n - 1) /\
  (forall X Y pX lX pY lY, desc L X -> desc L Y ->
     nm_find X ivs' = Some (pX, lX) -> nm_find Y ivs' = Some (pY, lY) ->
     (pX <= pY <= lX <-> desc X Y)) /\
  (forall X v, nm_find X ivs' = Some v -> nm_find X ivs = None -> desc L X).

(** The predicate [fold_ok] describes the state after numbering the
    already-visited children done from n0 + 1 up to m. Every visited
    child's subtree satisfies [si_ok], and no interval in one child's
    subtree contains the entry number of a label in another's. *)
Definition fold_ok (n0 : Z) (ivs : nmap (Z * Z)) (done : list name) (m : Z) (iv : nmap (Z * Z)) : Prop :=
  n0 + 1 <= m /\
  (forall X, (forall c, In c done -> ~ desc c X) -> nm_find X iv = nm_find X ivs) /\
  (forall c X, In c done -> desc c X -> exists p l, nm_find X iv = Some (p, l) /\ n0 + 1 <= p <= l /\ l < m) /\
  (forall c X Y pX lX pY lY, In c done -> desc c X -> desc c Y ->
     nm_find X iv = Some (pX, lX) -> nm_find Y iv = Some (pY, lY) -> (pX <= pY <= lX <-> desc X Y)) /\
  (forall c c' X Y pX lX pY lY, In c done -> In c' done -> c <> c' -> desc c X -> desc c' Y ->
     nm_find X iv = Some (pX, lX) -> nm_find Y iv = Some (pY, lY) -> ~ (pX <= pY <= lX)) /\
  (forall X v, nm_find X iv = Some v -> nm_find X ivs = None -> exists c, In c done /\ desc c X).

(** Each child of a node in the dominator tree owns a disjoint range of
    preorder numbers. Numbering the remaining children one by one
    preserves that disjointness whenever no two children share a
    descendant and each child's own subtree numbers cleanly. *)
Lemma si_fold : forall f, si_ok f -> forall n0 ivs rest done m iv n ivm,
  (forall c c' z, In c (done ++ rest) -> In c' (done ++ rest) -> c <> c' -> desc c z -> desc c' z -> False) ->
  fold_ok n0 ivs done m iv ->
  fold_left (si_step f) rest (Some (m, iv)) = Some (n, ivm) ->
  fold_ok n0 ivs (done ++ rest) n ivm.
Proof.
  intros f Hf n0 ivs rest. induction rest as [|c rest IH]; intros done m iv n ivm Hdis Hok H.
  - injection H as <- <-. rewrite app_nil_r. exact Hok.
  - cbn [fold_left] in H. change (si_step f (Some (m, iv)) c) with (subtree_intervals f K c m iv) in H.
    destruct (subtree_intervals f K c m iv) as [[m' iv']|] eqn:Es;
      [|rewrite si_fold_none in H; discriminate H].
    destruct (Hf _ _ _ _ _ Es) as (Q0 & Q1 & Q2 & _ & Q4 & Q5).
    destruct Hok as (F0 & F1 & F2 & F3 & F4 & F5).
    assert (Hc : In c (done ++ c :: rest)) by (apply in_or_app; right; left; reflexivity).
    assert (Hd : forall c0, In c0 done -> c0 <> c -> forall z, desc c0 z -> ~ desc c z).
    { intros c0 Hc0 Hne z H0 H1. apply (Hdis c0 c z); auto. apply in_or_app. left. exact Hc0. }
    replace (done ++ c :: rest) with ((done ++ [c]) ++ rest) by (rewrite <- app_assoc; reflexivity).
    assert (Hdis' : forall c1 c2 z, In c1 ((done ++ [c]) ++ rest) -> In c2 ((done ++ [c]) ++ rest) ->
                    c1 <> c2 -> desc c1 z -> desc c2 z -> False)
      by (rewrite <- app_assoc; exact Hdis).
    apply (IH (done ++ [c]) m' iv' n ivm Hdis'); [|exact H].
    split; [lia|]. split; [|split; [|split; [|split]]].
    + intros X HX. rewrite Q1 by (apply HX; apply in_or_app; right; left; reflexivity).
      apply F1. intros c0 Hc0. apply HX. apply in_or_app. left. exact Hc0.
    + intros c0 X Hc0 HX. destruct (name_eqb c0 c) eqn:E.
      * apply name_eqb_true in E. subst c0. destruct (Q2 _ HX) as (p & l & Hp & Hr). exists p, l.
        split; [exact Hp | lia].
      * apply name_eqb_false in E. apply in_app_or in Hc0 as [Hc0 | [<- | []]]; [|congruence].
        rewrite Q1 by exact (Hd _ Hc0 E _ HX). destruct (F2 _ _ Hc0 HX) as (p & l & Hp & Hr).
        exists p, l. split; [exact Hp | lia].
    + intros c0 X Y pX lX pY lY Hc0 HX HY EX EY. destruct (name_eqb c0 c) eqn:E.
      * apply name_eqb_true in E. subst c0. exact (Q4 _ _ _ _ _ _ HX HY EX EY).
      * apply name_eqb_false in E. apply in_app_or in Hc0 as [Hc0 | [<- | []]]; [|congruence].
        rewrite Q1 in EX by exact (Hd _ Hc0 E _ HX). rewrite Q1 in EY by exact (Hd _ Hc0 E _ HY).
        exact (F3 _ _ _ _ _ _ _ Hc0 HX HY EX EY).
    + intros c1 c2 X Y pX lX pY lY Hc1 Hc2 Hne HX HY EX EY.
      destruct (name_eqb c1 c) eqn:E1; destruct (name_eqb c2 c) eqn:E2.
      * apply name_eqb_true in E1, E2. congruence.
      * apply name_eqb_true in E1. subst c1. apply name_eqb_false in E2.
        apply in_app_or in Hc2 as [Hc2 | [<- | []]]; [|congruence].
        rewrite Q1 in EY by exact (Hd _ Hc2 E2 _ HY). destruct (Q2 _ HX) as (p & l & Hp & Hr).
        rewrite Hp in EX. injection EX as <- <-. destruct (F2 _ _ Hc2 HY) as (p' & l' & Hp' & Hr').
        rewrite Hp' in EY. injection EY as <- <-. lia.
      * apply name_eqb_true in E2. subst c2. apply name_eqb_false in E1.
        apply in_app_or in Hc1 as [Hc1 | [<- | []]]; [|congruence].
        rewrite Q1 in EX by exact (Hd _ Hc1 E1 _ HX). destruct (Q2 _ HY) as (p & l & Hp & Hr).
        rewrite Hp in EY. injection EY as <- <-. destruct (F2 _ _ Hc1 HX) as (p' & l' & Hp' & Hr').
        rewrite Hp' in EX. injection EX as <- <-. lia.
      * apply name_eqb_false in E1, E2.
        apply in_app_or in Hc1 as [Hc1 | [<- | []]]; [|congruence].
        apply in_app_or in Hc2 as [Hc2 | [<- | []]]; [|congruence].
        rewrite Q1 in EX by exact (Hd _ Hc1 E1 _ HX). rewrite Q1 in EY by exact (Hd _ Hc2 E2 _ HY).
        exact (F4 _ _ _ _ _ _ _ _ Hc1 Hc2 Hne HX HY EX EY).
    + intros X v Hv H0. destruct (nm_find X iv) as [v'|] eqn:Ev.
      * destruct (F5 _ _ Ev H0) as (c0 & Hc0 & Hd0). exists c0. split; [apply in_or_app; left; exact Hc0 | exact Hd0].
      * exists c. split; [apply in_or_app; right; left; reflexivity | exact (Q5 _ _ Hv Ev)].
Qed.

(** [si_ok] holds at every fuel: every call of `subtree_intervals/6` that
    succeeds numbers its subtree in preorder, with intervals that nest
    exactly as the tree does. *)
Lemma si_ok_all : forall fuel, si_ok fuel.
Proof.
  induction fuel as [|f IH]; intros L n0 ivs n ivs' H; [discriminate H|].
  pose proof H as Hsome. rewrite si_unfold in H.
  destruct (nm_find L K) as [ks|] eqn:Ek; [|discriminate H].
  destruct (fold_left (si_step f) ks (Some (n0 + 1, ivs))) as [[nf ivm]|] eqn:Ef; [|discriminate H].
  injection H as En Ei. subst n ivs'.
  (* no cycle passes through L *)
  assert (Hcyc : forall c, In c ks -> desc c L -> False).
  { intros c Hc [j Hj].
    pose proof (si_no_cycle _ _ _ _ _ Hsome L (desc_refl L) _
                  (descn_trans _ _ _ _ _ (descn_kid _ _ _ _ _ (descn_refl L) Ek Hc) Hj)) as E.
    discriminate E. }
  assert (Hdis : forall c c' z, In c ([] ++ ks) -> In c' ([] ++ ks) -> c <> c' -> desc c z -> desc c' z -> False).
  { intros c c' z Hc Hc' Hne [i Hi] [j Hj]. simpl in Hc, Hc'.
    assert (Hup : forall a b, In a ks -> In b ks -> a <> b -> desc a b -> False).
    { intros a b Ha Hb Hab [k Hk]. destruct (descn_inv _ _ _ Hk) as [[-> _] | (p & ks' & k' & _ & Hap & Hp & Hb')];
        [congruence|].
      rewrite <- (kids_unique _ _ _ _ _ Ek Hb Hp Hb') in Hap. exact (Hcyc a Ha (ex_intro _ _ Hap)). }
    destruct (descn_back _ _ _ Hi _ _ Hj) as [H1 | H1].
    - exact (Hup _ _ Hc Hc' Hne H1).
    - exact (Hup _ _ Hc' Hc (fun E => Hne (eq_sym E)) H1). }
  assert (H0 : fold_ok n0 ivs [] (n0 + 1) ivs).
  { split; [lia|]. split; [reflexivity|]. split; [intros c X []|]. split; [intros c X Y pX lX pY lY []|].
    split; [intros c c' X Y pX lX pY lY []|]. intros X v Hv H0. congruence. }
  destruct (si_fold _ IH _ _ _ _ _ _ _ _ Hdis H0 Ef) as (F0 & F1 & F2 & F3 & F4 & F5).
  simpl in F1, F2, F3, F4, F5.
  assert (Hsplit : forall X, desc L X -> X = L \/ exists c, In c ks /\ desc c X)
    by (intros X HX; exact (desc_split _ _ _ Ek HX)).
  assert (HnL : forall c X, In c ks -> desc c X -> X <> L) by (intros c X Hc HX ->; exact (Hcyc _ Hc HX)).
  split; [lia|]. split; [|split; [|split; [|split]]].
  - intros X HX. assert (Ex : name_eqb X L = false)
      by (apply name_eqb_false; intros ->; exact (HX (desc_refl L))).
    rewrite nm_find_add, Ex. apply F1. intros c Hc HcX. apply HX. exact (desc_trans _ _ _ (desc_kid _ _ _ _ (desc_refl L) Ek Hc) HcX).
  - intros X HX. destruct (Hsplit _ HX) as [-> | (c & Hc & HcX)].
    + exists n0, (nf - 1). rewrite nm_find_add, term_eqb_refl. split; [reflexivity | lia].
    + rewrite nm_find_add. rewrite (proj2 (name_eqb_false _ _) (HnL _ _ Hc HcX)).
      destruct (F2 _ _ Hc HcX) as (p & l & Hp & Hr). exists p, l. split; [exact Hp | lia].
  - rewrite nm_find_add, term_eqb_refl. reflexivity.
  - intros X Y pX lX pY lY HX HY EX EY.
    destruct (Hsplit _ HX) as [-> | (c & Hc & HcX)].
    + rewrite nm_find_add, term_eqb_refl in EX. injection EX as <- <-. split; [intros _; exact HY|].
      intros _. destruct (Hsplit _ HY) as [-> | (c' & Hc' & HcY)].
      * rewrite nm_find_add, term_eqb_refl in EY. injection EY as <- <-. lia.
      * rewrite nm_find_add, (proj2 (name_eqb_false _ _) (HnL _ _ Hc' HcY)) in EY.
        destruct (F2 _ _ Hc' HcY) as (p & l & Hp & Hr). rewrite Hp in EY. injection EY as <- <-. lia.
    + rewrite nm_find_add, (proj2 (name_eqb_false _ _) (HnL _ _ Hc HcX)) in EX.
      destruct (F2 _ _ Hc HcX) as (p & l & Hp & Hr). rewrite Hp in EX. injection EX as <- <-.
      destruct (Hsplit _ HY) as [-> | (c' & Hc' & HcY)].
      * rewrite nm_find_add, term_eqb_refl in EY. injection EY as <- <-. split; [lia|].
        intros HXL. exfalso. exact (Hcyc _ Hc (desc_trans _ _ _ HcX HXL)).
      * rewrite nm_find_add, (proj2 (name_eqb_false _ _) (HnL _ _ Hc' HcY)) in EY.
        destruct (name_eqb c c') eqn:Ecc.
        -- apply name_eqb_true in Ecc. subst c'. exact (F3 _ _ _ _ _ _ _ Hc HcX HcY Hp EY).
        -- apply name_eqb_false in Ecc. split.
           ++ intros Hn. exfalso. exact (F4 _ _ _ _ _ _ _ _ Hc Hc' Ecc HcX HcY Hp EY Hn).
           ++ intros HXY. exfalso. exact (Hdis _ _ _ Hc Hc' Ecc (desc_trans _ _ _ HcX HXY) HcY).
  - intros X v Hv Hn. rewrite nm_find_add in Hv. destruct (name_eqb X L) eqn:Ex.
    + apply name_eqb_true in Ex. subst X. apply desc_refl.
    + destruct (F5 _ _ Hv Hn) as (c & Hc & HcX).
      exact (desc_trans _ _ _ (desc_kid _ _ _ _ (desc_refl L) Ek Hc) HcX).
Qed.

End Tree.

(** ## The dominator intervals of a function

    We now combine the control-flow graph, the immediate dominator map,
    the children map, and the preorder intervals into one package for a
    whole function. Lemma [tree_facts] shows that [block_intervals]
    produces a valid dominator tree whose intervals match ancestor
    relationships in that tree. *)

(** Every ancestor of a block in the child tree also belongs to that
    tree. When the entry E is its own parent and each child in kids maps
    to its parent in M, walking up parent pointers from p reaches only
    ancestors q that have p as a descendant. *)
Lemma anc_desc : forall M kids E,
  nm_find E M = Some E ->
  (forall x ks k, nm_find x kids = Some ks -> In k ks -> nm_find k (nm_remove E M) = Some x) ->
  forall q p, anc M q p -> desc kids E p -> desc kids E q /\ desc kids q p.
Proof.
  intros M kids E HE Hk q p H. induction H as [|b c Hf Hanc IH]; intros Hb.
  - split; [exact Hb | apply desc_refl].
  - destruct (name_eqb b E) eqn:Eb.
    + apply name_eqb_true in Eb. subst b. rewrite HE in Hf. injection Hf as <-. exact (IH Hb).
    + apply name_eqb_false in Eb. destruct Hb as [k Hb].
      destruct (descn_inv _ _ _ _ Hb) as [[-> _] | (p0 & ks & k' & _ & Hp0 & Hks & Hin)]; [congruence|].
      pose proof (Hk _ _ _ Hks Hin) as Ht. rewrite nm_find_remove, (proj2 (name_eqb_false _ _) Eb), Hf in Ht.
      injection Ht as <-. destruct (IH (ex_intro _ _ Hp0)) as [H1 H2].
      split; [exact H1 | exact (desc_kid _ _ _ _ _ H2 Hks Hin)].
Qed.

(** Lemma [tree_facts] packages everything [block_intervals] computes
    for a nonempty block list b0 :: rest. It yields a [cfg_ok] graph g
    starting at b0, an [idoms_ok] parent map M, and a child tree kids
    without cycles. A label has an interval exactly when it lies in the
    tree, and [dominates_by_interval] holds exactly when the first label
    is an ancestor of the second. *)
Lemma tree_facts : forall b0 rest doms, block_intervals (b0 :: rest) = Some doms ->
  exists g M kids,
    cfg_ok (b0 :: rest) g /\ cfg_entry g = b_label b0 /\ idoms_ok g M /\
    (forall x ks k, nm_find x kids = Some ks -> In k ks ->
       In k (cfg_rpo g) /\ nm_find k (nm_remove (cfg_entry g) M) = Some x) /\
    (forall k x, In k (cfg_rpo g) -> nm_find k (nm_remove (cfg_entry g) M) = Some x ->
       exists ks, nm_find x kids = Some ks /\ In k ks) /\
    (forall X, nm_mem X doms = true <-> desc kids (b_label b0) X) /\
    (forall a b, dominates_by_interval doms a b = true <->
       desc kids (b_label b0) a /\ desc kids (b_label b0) b /\ desc kids a b) /\
    (forall X Y, desc kids (b_label b0) X -> desc kids X Y -> desc kids Y X -> X = Y).
Proof.
  intros b0 rest doms H. unfold block_intervals in H.
  destruct (func_cfg (b0 :: rest)) as [g|] eqn:Eg; [|discriminate H].
  destruct (cfg_idoms g) as [t|] eqn:Et; [|discriminate H].
  unfold dom_intervals in H. destruct (dom_children g t) as [kids|] eqn:Ek; [|discriminate H].
  destruct (subtree_intervals _ kids (cfg_entry g) 0 nm_empty) as [[n doms']|] eqn:Es; [|discriminate H].
  injection H as <-.
  destruct (func_cfg_ok _ _ Eg) as [Hok (b0' & rest' & Eb & He)]. injection Eb as <- <-.
  destruct (cfg_idoms_ok _ _ _ Eg Et) as (M & HM & ->).
  destruct (dom_children_spec _ _ _ (func_cfg_nodup _ _ Eg) Ek) as [Hk1 Hk2].
  assert (Huniq : forall x y ks ks' k, nm_find x kids = Some ks -> In k ks ->
                  nm_find y kids = Some ks' -> In k ks' -> x = y).
  { intros x y ks ks' k Hx Hkx Hy Hky. destruct (proj1 (Hk1 _ _ Hx k) Hkx) as [_ E1].
    destruct (proj1 (Hk1 _ _ Hy k) Hky) as [_ E2]. congruence. }
  destruct (si_ok_all kids Huniq _ _ _ _ _ _ Es) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite He in Q1, Q2, Q3, Q4, Q5, Es.
  assert (Hmem : forall X, nm_mem X doms' = true <-> desc kids (b_label b0) X).
  { intros X. split.
    - intros Hm. destruct (proj1 (nm_mem_find _ _ _) Hm) as [v Hv].
      exact (Q5 _ _ Hv (nm_find_empty _ X)).
    - intros Hd. destruct (Q2 _ Hd) as (p & l & Hp & _). apply nm_mem_find. eauto. }
  exists g, M, kids. split; [exact Hok|]. split; [exact He|]. split; [exact HM|].
  split; [intros x ks k Hx Hkx; exact (proj1 (Hk1 _ _ Hx k) Hkx)|].
  split; [exact Hk2|]. split; [exact Hmem|]. split.
  - intros a b. unfold dominates_by_interval. split.
    + destruct (nm_find a doms') as [[pa la]|] eqn:Ea; [|discriminate].
      destruct (nm_find b doms') as [[pb lb]|] eqn:Eb'; [|discriminate].
      intros Hn. apply andb_true_iff in Hn as [H1 H2]. apply Z.leb_le in H1, H2.
      assert (Ha : desc kids (b_label b0) a) by (apply Hmem, nm_mem_find; eauto).
      assert (Hb : desc kids (b_label b0) b) by (apply Hmem, nm_mem_find; eauto).
      split; [exact Ha|]. split; [exact Hb|]. exact (proj1 (Q4 _ _ _ _ _ _ Ha Hb Ea Eb') (conj H1 H2)).
    + intros (Ha & Hb & Hab). destruct (Q2 _ Ha) as (pa & la & Ea & _). destruct (Q2 _ Hb) as (pb & lb & Eb' & _).
      rewrite Ea, Eb'. destruct (proj2 (Q4 _ _ _ _ _ _ Ha Hb Ea Eb') Hab) as [H1 H2].
      apply andb_true_iff. split; apply Z.leb_le; assumption.
  - intros X Y HX [i Hi] [j Hj].
    pose proof (si_no_cycle _ _ _ _ _ _ Es X HX _ (descn_trans _ _ _ _ _ _ Hi Hj)) as E.
    assert (i = 0%nat) by lia. subst i.
    destruct (descn_inv _ _ _ _ Hi) as [[Ey _] | (p0 & ks0 & k0 & E' & _)]; [exact (eq_sym Ey) | discriminate E'].
Qed.

(** ## What the validator's dominance means

    The rest of the soundness proof never looks inside intervals or tree
    walks again. Instead, it uses the exported theorems below to reason
    about reachability, reflexivity, antisymmetry, control-flow edges,
    and predecessor meets directly on [dominates] and [is_reachable]. *)

(** Fixes a function's blocks b0 :: rest, b0 the entry, and the intervals
    doms that [block_intervals] computed for them. *)
Section Dominance.

Variables (b0 : block) (rest : list block) (doms : nmap (Z * Z)).
Hypothesis Hdoms : block_intervals (b0 :: rest) = Some doms.

(** The entry block is reachable: it has an interval ([is_reachable]). *)
Theorem dom_entry : is_reachable doms (b_label b0) = true.
Proof.
  destruct (tree_facts _ _ _ Hdoms) as (g & M & kids & _ & _ & _ & _ & _ & Hmem & _).
  apply Hmem, desc_refl.
Qed.

(** A label that dominates another is reachable, and so is the other. *)
Lemma dominates_reachable : forall a b, dominates doms a b = true ->
  is_reachable doms a = true /\ is_reachable doms b = true.
Proof.
  intros a b H. destruct (tree_facts _ _ _ Hdoms) as (g & M & kids & _ & _ & _ & _ & _ & Hmem & Hdom & _).
  apply Hdom in H as (Ha & Hb & _). split; apply Hmem; assumption.
Qed.

(** A reachable label dominates itself. *)
Lemma dominates_refl : forall a, is_reachable doms a = true -> dominates doms a a = true.
Proof.
  intros a H. destruct (tree_facts _ _ _ Hdoms) as (g & M & kids & _ & _ & _ & _ & _ & Hmem & Hdom & _).
  apply Hdom. apply Hmem in H. split; [exact H|]. split; [exact H | apply desc_refl].
Qed.

(** Dominance is transitive: if a dominates b and b dominates c, then a
    dominates c. *)
Lemma dominates_trans : forall a b c, dominates doms a b = true -> dominates doms b c = true ->
  dominates doms a c = true.
Proof.
  intros a b c H1 H2. destruct (tree_facts _ _ _ Hdoms) as (g & M & kids & _ & _ & _ & _ & _ & Hmem & Hdom & _).
  apply Hdom in H1 as (Ha & _ & Hab). apply Hdom in H2 as (_ & Hc & Hbc).
  apply Hdom. split; [exact Ha|]. split; [exact Hc | exact (desc_trans _ _ _ _ Hab Hbc)].
Qed.

(** Two labels that dominate each other are the same label. *)
Theorem dom_antisym : forall a b, dominates doms a b = true -> dominates doms b a = true -> a = b.
Proof.
  intros a b H1 H2. destruct (tree_facts _ _ _ Hdoms) as (g & M & kids & _ & _ & _ & _ & _ & _ & Hdom & Hacyc).
  apply Hdom in H1 as (Ha & _ & Hab). apply Hdom in H2 as (_ & _ & Hba). exact (Hacyc _ _ Ha Hab Hba).
Qed.

(** Only the entry dominates the entry. *)
Theorem dom_entry_top : forall a, dominates doms a (b_label b0) = true -> a = b_label b0.
Proof.
  intros a H. destruct (tree_facts _ _ _ Hdoms) as (g & M & kids & _ & He & _ & Hk1 & _ & _ & Hdom & _).
  apply Hdom in H as (_ & _ & [k Hk]).
  destruct (descn_inv _ _ _ _ Hk) as [[E _] | (p0 & ks & k' & _ & _ & Hks & Hin)]; [exact (eq_sym E)|].
  destruct (Hk1 _ _ _ Hks Hin) as [_ Ht]. rewrite He, nm_find_remove, term_eqb_refl in Ht. discriminate Ht.
Qed.

(** When block labels are unique, the immediate dominator nw of a
    non-entry successor s of a reachable block p is an ancestor of p.
    This lemma also returns the underlying tree facts that [dom_closed]
    and [dom_edge] need. *)
Lemma succ_parent : forall p s, no_dups (map b_label (b0 :: rest)) = true ->
  is_reachable doms p = true -> edge (b0 :: rest) p s -> s <> b_label b0 ->
  exists g M kids nw,
    (forall a b, dominates doms a b = true <->
       desc kids (b_label b0) a /\ desc kids (b_label b0) b /\ desc kids a b) /\
    (forall x ks k, nm_find x kids = Some ks -> In k ks -> nm_find k (nm_remove (cfg_entry g) M) = Some x) /\
    cfg_entry g = b_label b0 /\
    desc kids (b_label b0) nw /\ desc kids nw p /\ exists ks, nm_find nw kids = Some ks /\ In s ks.
Proof.
  intros p s Hnd Hp He Hs.
  destruct (tree_facts _ _ _ Hdoms) as (g & M & kids & Hok & Hent & HM & Hk1 & Hk2 & Hmem & Hdom & _).
  apply Hmem in Hp.
  assert (Hrpo : forall x, desc kids (b_label b0) x -> In x (cfg_rpo g)).
  { intros x [k Hx]. destruct (descn_inv _ _ _ _ Hx) as [[-> _] | (p0 & ks & k' & _ & _ & Hks & Hin)].
    - destruct (cfg_ok_rpo _ _ Hok) as (r & Er & _). rewrite Er, Hent. left. reflexivity.
    - exact (proj1 (Hk1 _ _ _ Hks Hin)). }
  assert (HsR : In s (cfg_rpo g)).
  { destruct He as (b & Hb & Ebp & Hsj). destruct (cfg_ok_closed _ _ Hok _ (Hrpo _ Hp)) as (ss & Ess & Hss).
    rewrite (cfg_ok_succs _ _ Hok), <- Ebp, (block_succs_find _ _ Hnd Hb) in Ess. injection Ess as <-.
    exact (Hss _ Hsj). }
  rewrite <- Hent in Hs.
  destruct (idoms_meet _ _ HM _ HsR Hs) as (nw & Enw & Hanc).
  destruct (cfg_ok_preds _ _ Hok _ _ He) as (ps & Eps & Hpin).
  assert (HpM : nm_mem p M = true).
  { destruct (name_eqb p (cfg_entry g)) eqn:Ep.
    - apply name_eqb_true in Ep. subst p. apply nm_mem_find. exists (cfg_entry g). exact (idoms_entry _ _ HM).
    - apply name_eqb_false in Ep. destruct (idoms_meet _ _ HM _ (Hrpo _ Hp) Ep) as (nw' & E' & _).
      apply nm_mem_find. eauto. }
  assert (Hk1' : forall x ks k, nm_find x kids = Some ks -> In k ks -> nm_find k (nm_remove (cfg_entry g) M) = Some x)
    by (intros x ks k Hx Hkx; exact (proj2 (Hk1 _ _ _ Hx Hkx))).
  destruct (anc_desc M kids (cfg_entry g) (idoms_entry _ _ HM) Hk1' _ _ (Hanc _ _ Eps Hpin HpM)
              ltac:(rewrite Hent; exact Hp)) as [Hnw Hnwp].
  rewrite Hent in Hnw.
  assert (Ht : nm_find s (nm_remove (cfg_entry g) M) = Some nw)
    by (rewrite nm_find_remove, (proj2 (name_eqb_false _ _) Hs); exact Enw).
  exists g, M, kids, nw. split; [exact Hdom|]. split; [exact Hk1'|]. split; [exact Hent|].
  split; [exact Hnw|]. split; [exact Hnwp|]. exact (Hk2 _ _ HsR Ht).
Qed.

(** Where no two blocks share a label, a successor s of a reachable block p
    is reachable: a run never leaves the blocks that have an interval. *)
Theorem dom_closed : forall p s, no_dups (map b_label (b0 :: rest)) = true ->
  is_reachable doms p = true -> edge (b0 :: rest) p s -> is_reachable doms s = true.
Proof.
  intros p s Hnd Hp He. destruct (name_eqb s (b_label b0)) eqn:Es.
  - apply name_eqb_true in Es. subst s. exact dom_entry.
  - apply name_eqb_false in Es.
    destruct (succ_parent _ _ Hnd Hp He Es) as (g & M & kids & nw & Hdom & _ & _ & Hnw & _ & ks & Hks & Hin).
    assert (Hd : dominates doms nw s = true).
    { apply Hdom. split; [exact Hnw|]. split; [exact (desc_kid _ _ _ _ _ Hnw Hks Hin)|].
      exact (desc_kid _ _ _ _ _ (desc_refl _ _) Hks Hin). }
    exact (proj2 (dominates_reachable _ _ Hd)).
Qed.

(** Where no two blocks share a label, whatever dominates a successor s of a
    reachable block p, and is not s, dominates p too: a run that crosses the
    edge from p to s has already passed every other dominator of s. *)
Theorem dom_edge : forall p s a, no_dups (map b_label (b0 :: rest)) = true ->
  is_reachable doms p = true -> edge (b0 :: rest) p s ->
  dominates doms a s = true -> a = s \/ dominates doms a p = true.
Proof.
  intros p s a Hnd Hp He Hd. destruct (name_eqb s (b_label b0)) eqn:Es.
  - apply name_eqb_true in Es. subst s. left. exact (dom_entry_top _ Hd).
  - apply name_eqb_false in Es.
    destruct (succ_parent _ _ Hnd Hp He Es)
      as (g & M & kids & nw & Hdom & Hk1 & Hent & Hnw & Hnwp & ks & Hks & Hin).
    apply Hdom in Hd as (Ha & _ & [k Hk]).
    destruct (descn_inv _ _ _ _ Hk) as [[E _] | (p1 & ks1 & k' & _ & Hap1 & Hks1 & Hin1)]; [left; exact (eq_sym E)|].
    right. pose proof (Hk1 _ _ _ Hks Hin) as T1. pose proof (Hk1 _ _ _ Hks1 Hin1) as T2.
    rewrite T1 in T2. injection T2 as <-.
    apply Hdom. split; [exact Ha|]. split; [exact (desc_trans _ _ _ _ Hnw Hnwp)|].
    exact (desc_trans _ _ _ _ (ex_intro _ _ Hap1) Hnwp).
Qed.

(** When block labels are unique, any label a that dominates every
    reachable predecessor of a non-entry reachable block l also
    dominates l, and a differs from l. This converse of [dom_edge]
    relies on [idoms_nca] and lets an invariant pass through a merge
    block whenever it holds on all incoming edges. *)
Theorem dom_meet : forall l a, no_dups (map b_label (b0 :: rest)) = true ->
  is_reachable doms l = true -> l <> b_label b0 ->
  (forall p, edge (b0 :: rest) p l -> is_reachable doms p = true -> dominates doms a p = true) ->
  dominates doms a l = true /\ a <> l.
Proof.
  intros l a Hnd Hl Hne Ha.
  destruct (tree_facts _ _ _ Hdoms) as (g & M & kids & Hok & Hent & HM & Hk1 & Hk2 & Hmem & Hdom & _).
  assert (Hr0 : exists r, cfg_rpo g = cfg_entry g :: r)
    by (destruct (cfg_ok_rpo _ _ Hok) as (r & Er & _); eauto).
  assert (Hrpo : forall x, desc kids (b_label b0) x -> In x (cfg_rpo g)).
  { intros x [k Hx]. destruct (descn_inv _ _ _ _ Hx) as [[-> _] | (p0 & ks & k' & _ & _ & Hks & Hin)].
    - rewrite <- Hent. exact (entry_in g Hr0).
    - exact (proj1 (Hk1 _ _ _ Hks Hin)). }
  (* Every label of the order is in the tree. *)
  assert (Hdesc : forall x, In x (cfg_rpo g) -> desc kids (b_label b0) x).
  { assert (Main : forall k x, (Z.to_nat (rank g x) < k)%nat -> In x (cfg_rpo g) -> desc kids (b_label b0) x).
    { induction k as [|k IH]; intros x Hk Hx; [lia|].
      destruct (name_eqb x (cfg_entry g)) eqn:Ex.
      - apply name_eqb_true in Ex. rewrite Ex, Hent. apply desc_refl.
      - apply name_eqb_false in Ex. destruct (idoms_meet _ _ HM _ Hx Ex) as (c & Hc & _).
        destruct (idom_rank g M HM Hr0 _ _ Hx Hc) as [HcR [[E _] | Hlt]]; [congruence|].
        assert (Ht : nm_find x (nm_remove (cfg_entry g) M) = Some c)
          by (rewrite nm_find_remove, (proj2 (name_eqb_false _ _) Ex); exact Hc).
        destruct (Hk2 _ _ Hx Ht) as (ks & Hks & Hin).
        pose proof (rank_nonneg g M HM _ HcR).
        exact (desc_kid _ _ _ _ _ (IH c ltac:(lia) HcR) Hks Hin). }
    intros x Hx. exact (Main (S (Z.to_nat (rank g x))) x ltac:(lia) Hx). }
  (* The tree's descendants are ancestors in M. *)
  assert (Hanc : forall q p, desc kids q p -> anc M q p).
  { intros q p [k Hk]. induction Hk as [|p0 ks b k _ IH Hks Hin]; [constructor|].
    pose proof (proj2 (Hk1 _ _ _ Hks Hin)) as Ht. rewrite nm_find_remove in Ht.
    destruct (name_eqb b (cfg_entry g)); [discriminate Ht|]. exact (anc_up _ _ _ _ Ht IH). }
  assert (Hk1' : forall x ks k, nm_find x kids = Some ks -> In k ks -> nm_find k (nm_remove (cfg_entry g) M) = Some x)
    by (intros x ks k Hx Hkx; exact (proj2 (Hk1 _ _ _ Hx Hkx))).
  apply Hmem in Hl. pose proof (Hrpo _ Hl) as HlR. rewrite <- Hent in Hne.
  destruct (idoms_nca g M HM Hr0 l a HlR Hne) as (nw & Hnw & Hanw).
  { intros p ps Hps Hin Hm. pose proof (idoms_dom _ _ HM _ Hm) as HpR.
    pose proof (cfg_ok_pred_edge _ _ Hok _ _ _ Hps Hin) as He.
    pose proof (Ha p He (proj2 (Hmem p) (Hdesc _ HpR))) as Hd.
    apply Hdom in Hd as (_ & _ & Hd). exact (Hanc _ _ Hd). }
  assert (Hal : anc M a l) by exact (anc_up _ _ _ _ Hnw Hanw).
  destruct (anc_desc M kids (cfg_entry g) (idoms_entry _ _ HM) Hk1' _ _ Hal ltac:(rewrite Hent; exact Hl))
    as [Hea Hdl].
  rewrite Hent in Hea. split.
  - apply Hdom. auto.
  - intros ->. destruct (idom_rank g M HM Hr0 _ _ HlR Hnw) as [HnR [[E _] | Hlt]]; [congruence|].
    destruct (anc_rank g M HM Hr0 _ _ Hanw HnR) as [_ [-> | Hlt']]; lia.
Qed.

End Dominance.
