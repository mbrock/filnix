(** The [[evidence pass]] read back for Campaign 3's run-level invariant
    (Persistence.v; [rocq.md, The evidence invariant over runs](../../docs/rocq.md#the-evidence-invariant-over-runs)).

    Validate.v's [evidence_pass] transcribes ir.pl's pass as it runs: a
    fold over the blocks, and within each block `checked_insts/5`. The
    invariant needs to know what the pass said at each point a run can
    reach, so this file reads the pass back: the facts each block was
    passed from ([pass_fold]), where the pass is within a block
    ([walks]), and the instructions before which it keeps its facts
    ([relies]).

    A block reached by a back edge saw nothing on that edge (the fold
    had not reached its source), and the meet over an empty set is
    empty: a back edge without a poll gives no fact the proof must
    justify. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Coverage Evidence.
Import ListNotations.
Open Scope Z_scope.

(** ## Names *)

(** Every name equals itself by [name_eqb]. *)
Lemma name_eqb_refl : forall n, name_eqb n n = true.
Proof. exact term_eqb_refl. Qed.

(** [name_eqb] is symmetric. *)
Lemma name_eqb_sym : forall a b, name_eqb a b = name_eqb b a.
Proof.
  intros a b. destruct (name_eqb a b) eqn:E, (name_eqb b a) eqn:E'; auto.
  - apply term_eqb_eq in E. subst. rewrite name_eqb_refl in E'. discriminate E'.
  - apply term_eqb_eq in E'. subst. rewrite name_eqb_refl in E. discriminate E.
Qed.

(** If n is not in the list ns by [mem], [name_eqb] finds n different from
    every name of ns. *)
Lemma mem_false : forall n ns, mem n ns = false -> forall n', In n' ns -> name_eqb n n' = false.
Proof.
  unfold mem. intros n ns H n' Hin. destruct (name_eqb n n') eqn:E; auto.
  rewrite <- H. symmetry. apply existsb_exists. eauto.
Qed.

(** Looking k up after [put] k' v answers v if k is k', and otherwise what
    it answered before. *)
Lemma lookup_put : forall (A : Type) k k' (v : A) ps,
  lookup k (put k' v ps) = if name_eqb k k' then Some v else lookup k ps.
Proof.
  intros A k k' v ps. destruct (name_eqb k k') eqn:E.
  - apply term_eqb_eq in E. subst. apply lookup_put_same.
  - apply lookup_put_other. exact E.
Qed.

(** The block that the label l finds in the blocks bs ([find_block]) is one
    of bs and is labelled l. *)
Lemma find_block_in : forall l bs b, find_block l bs = Some b -> In b bs /\ b_label b = l.
Proof.
  induction bs as [|b0 bs IH]; simpl; intros b H; [discriminate H|].
  destruct (name_eqb (b_label b0) l) eqn:E.
  - injection H as <-. split; [left; reflexivity | apply term_eqb_eq; exact E].
  - destruct (IH _ H). split; [right|]; auto.
Qed.

(** ## The pass, block by block

    `evidence_pass` folds `pass_block` over the blocks in order. Each
    block's entry facts are the meet of the sets on its incoming edges
    (`edge_set`): nothing over a poll edge, the exit facts of a block
    the fold has passed, and nothing for one it has not reached yet, a
    back edge. *)

(** The facts the pass carries along the incoming edge e, a source label and
    whether it is a [[poll|poll edge]]: none over a poll edge, else the exit
    facts exits gives the source, or none if the fold has not passed the
    source yet. *)
Definition edge_set (exits : list (name * list fact)) (e : name * bool) : list fact :=
  if snd e then [] else match lookup (fst e) exits with Some fs => fs | None => [] end.

(** The [[live fact|live facts]] at the entry of the block b of f, given the
    exit facts so far: the meet of the sets on b's incoming edges
    ([evidence_meet]), less the facts about b's [[phi]] temporaries
    ([entry_kill]). *)
Definition entry_live (f : func) (exits : list (name * list fact)) (b : block) : list fact :=
  entry_kill (b_phis b) (evidence_meet (map (edge_set exits) (incoming (fn_blocks f) (b_label b)))).

(** One step of the pass's fold over the blocks: run `checked_insts/5` over
    b's instructions from b's entry facts, and record what it ends with as
    b's exit facts. Fails where the pass fails. *)
Definition pass_block (s : src) (f : func) (acc : option (list (name * list fact))) (b : block)
  : option (list (name * list fact)) :=
  let* exits := acc in
  let* out := checked_insts s (S (length (b_insts b))) (b_insts b) (entry_live f exits b) in
  Some (put (b_label b) out exits).

(** The exit facts of every block of the function f, as the pass, with the
    sources s of the function, leaves them. *)
Definition pass_exits (s : src) (f : func) : option (list (name * list fact)) :=
  fold_left (pass_block s f) (fn_blocks f) (Some []).

(** The [[evidence pass]] accepts a function exactly when [pass_exits]
    computes its exit facts. *)
Lemma evidence_pass_exits : forall s f,
  evidence_pass s f = match pass_exits s f with Some _ => true | None => false end.
Proof. reflexivity. Qed.

(** A failed fold of [pass_block] stays failed. *)
Lemma pass_fold_none : forall s f bs, fold_left (pass_block s f) bs None = None.
Proof. intros s f bs. induction bs; simpl; auto. Qed.

(** One unfolding of [pass_block] from the exit facts ex. *)
Lemma pass_block_some : forall s f ex b,
  pass_block s f (Some ex) b =
    match checked_insts s (S (length (b_insts b))) (b_insts b) (entry_live f ex b) with
    | Some out => Some (put (b_label b) out ex)
    | None => None
    end.
Proof. reflexivity. Qed.

(** The exit facts the fold ends with, E, give a label n that no block of bs
    carries what they gave it before the fold, in ex. *)
Lemma pass_fold_keeps : forall s f bs ex E n,
  fold_left (pass_block s f) bs (Some ex) = Some E ->
  (forall b, In b bs -> name_eqb n (b_label b) = false) -> lookup n E = lookup n ex.
Proof.
  intros s f. induction bs as [|b bs IH]; cbn [fold_left]; intros ex E n H Hn.
  - injection H as <-. reflexivity.
  - rewrite pass_block_some in H.
    destruct (checked_insts _ _ _ _) as [out|]; [|rewrite pass_fold_none in H; discriminate H].
    rewrite (IH _ _ _ H) by (intros b' Hb'; apply Hn; right; exact Hb').
    rewrite lookup_put, (Hn b) by (left; reflexivity). reflexivity.
Qed.

(** Folding [pass_block] over blocks bs with distinct labels, none of which
    had exit facts in ex yet, passes each block b of bs from the exit facts
    the fold had when it reached b, all of which it keeps to the end E, and
    records b's exit facts out in E. *)
Lemma pass_fold : forall s f bs ex E,
  fold_left (pass_block s f) bs (Some ex) = Some E ->
  no_dups (map b_label bs) = true ->
  (forall b, In b bs -> lookup (b_label b) ex = None) ->
  forall b, In b bs ->
    exists exits out,
      (forall n v, lookup n exits = Some v -> lookup n E = Some v) /\
      lookup (b_label b) E = Some out /\
      checked_insts s (S (length (b_insts b))) (b_insts b) (entry_live f exits b) = Some out.
Proof.
  intros s f. induction bs as [|b0 bs IH]; cbn [fold_left]; intros ex E H Hd Hex b Hb; [destruct Hb|].
  cbn [map no_dups] in Hd. apply andb_true_iff in Hd as [Hd0 Hd]. apply negb_true_iff in Hd0.
  rewrite pass_block_some in H.
  destruct (checked_insts _ _ _ (entry_live f ex b0)) as [out|] eqn:Ec;
    [|rewrite pass_fold_none in H; discriminate H].
  assert (Hlater : forall b', In b' bs -> name_eqb (b_label b0) (b_label b') = false).
  { intros b' Hb'. eapply mem_false; [exact Hd0|]. apply in_map. exact Hb'. }
  destruct Hb as [<- | Hb].
  - exists ex, out. split; [|split; [|exact Ec]].
    + intros n v Hv. rewrite (pass_fold_keeps _ _ _ _ _ _ H).
      * rewrite lookup_put. destruct (name_eqb n (b_label b0)) eqn:E0; [|exact Hv].
        apply term_eqb_eq in E0. subst. rewrite Hex in Hv by (left; reflexivity). discriminate Hv.
      * intros b' Hb'. destruct (name_eqb n (b_label b')) eqn:E1; auto.
        apply term_eqb_eq in E1. subst. rewrite Hex in Hv by (right; exact Hb'). discriminate Hv.
    + rewrite (pass_fold_keeps _ _ _ _ _ _ H Hlater). rewrite lookup_put, name_eqb_refl. reflexivity.
  - apply (IH _ _ H Hd); [|exact Hb].
    intros b' Hb'. rewrite lookup_put. rewrite name_eqb_sym, (Hlater b' Hb'). apply Hex. right. exact Hb'.
Qed.

(** A jump of the block bp of bs to the [[block]] labelled l gives l an
    incoming edge from bp, marked as a poll edge where the target is one
    ([is_poll]). *)
Lemma incoming_in : forall bs bp t,
  In bp bs -> In t (jump_targets (b_jump bp)) ->
  In (b_label bp, is_poll t) (incoming bs (edge_label t)).
Proof.
  unfold incoming. intros bs bp t Hb Ht. apply (proj1 (in_rev _ _)).
  apply (proj2 (in_flat_map _ _ _)). exists bp. split; [exact Hb|].
  apply (proj2 (in_flat_map _ _ _)). exists t. split; [exact Ht|]. rewrite name_eqb_refl. left. reflexivity.
Qed.

(** A label that no jump of bs can go to has no incoming edges; the entry is
    such a label. *)
Lemma incoming_nil : forall bs l,
  existsb (fun b => mem l (succ_labels (b_jump b))) bs = false -> incoming bs l = [].
Proof.
  unfold incoming. intros bs l H.
  assert (flat_map (fun b => flat_map (fun t => if name_eqb (edge_label t) l
                                                then [(b_label b, is_poll t)] else [])
                                      (jump_targets (b_jump b))) bs = []) as -> ; [|reflexivity].
  induction bs as [|b bs IH]; simpl in *; auto.
  apply orb_false_iff in H as [Hb Hbs]. rewrite IH by exact Hbs. rewrite app_nil_r.
  unfold succ_labels in Hb. induction (jump_targets (b_jump b)) as [|t ts IHt]; simpl in *; auto.
  unfold mem in Hb. simpl in Hb. apply orb_false_iff in Hb as [Ht Hts].
  rewrite name_eqb_sym, Ht. apply IHt. exact Hts.
Qed.

(** ## Where the pass is within a block *)

(** From the facts live before the instructions is, the pass, with [[fuel]]
    enough, reaches the block's end with the facts out (`checked_insts/5`). *)
Definition walks (s : src) (is : list inst) (live out : list fact) : Prop :=
  exists n, checked_insts s n is live = Some out.

(** With no instructions left, the pass ends with the facts it had. *)
Lemma walks_nil : forall s live out, walks s [] live out -> out = live.
Proof. intros s live out [n H]. destruct n; cbn [checked_insts] in H; congruence. Qed.

(** A walk over i :: rest takes i with what follows it by
    `checked_inst_rest/7`, which may consume the next instructions too, and
    walks on over what is left. *)
Lemma walks_cons : forall s i rest live out,
  walks s (i :: rest) live out ->
  exists rest' live', checked_inst_rest s i rest live = Some (rest', live') /\ walks s rest' live' out.
Proof.
  intros s i rest live out [n H]. destruct n as [|n]; cbn [checked_insts] in H; [discriminate H|].
  destruct (checked_inst_rest s i rest live) as [[rest' live']|]; [|discriminate H].
  exists rest', live'. split; [reflexivity | exists n; exact H].
Qed.

(** ## Where the pass relies on facts

    The pass reads its live facts at a raw access (its coverage), and
    keeps them across an evidence-preserving instruction, a
    `check_local` and a repeated getter. Before any other instruction
    it keeps none: what it says after does not depend on them. *)

(** The instruction i copies a global g into a temporary d that the sources
    s record as a getter of g ([[getter]]): a repeated getter, after which
    the pass keeps its facts. *)
Definition repeated_getter (s : src) (i : inst) : bool :=
  match i with
  | Let d P Copy [Global g] =>
      match lookup d (s_getters s) with Some g1 => name_eqb g1 g | None => false end
  | _ => false
  end.

(** The instruction i is a `check_local`, an access check of a named local. *)
Definition is_check_local (i : inst) : bool :=
  match i with Let _ A (CheckLocal _ _ _ _ _) [] => true | _ => false end.

(** The instructions before which the pass keeps its live facts: an
    evidence-preserving one ([evidence_preserving]), a `check_local`, a
    repeated getter, or a [[raw access]], which reads them as its coverage. *)
Definition relies (s : src) (i : inst) : bool :=
  evidence_preserving i || is_check_local i || repeated_getter s i
  || match raw_access i with Some _ => true | None => false end.

(** An instruction after which the pass adds a fact ([check_fact]) is
    evidence preserving. *)
Lemma check_fact_preserving : forall i fa, check_fact i = Some fa -> evidence_preserving i = true.
Proof.
  intros i fa H. destruct i as [q k o args | | | | | | | | ]; try discriminate H.
  destruct o; try (destruct k; discriminate H); destruct k; try discriminate H;
    destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; try discriminate H; reflexivity.
Qed.

(** Before an instruction it does not rely on facts for ([relies]), the pass
    keeps none: it goes on with no live facts. *)
Lemma relies_false : forall s i rest live rest' live',
  relies s i = false -> checked_inst_rest s i rest live = Some (rest', live') -> live' = [].
Proof.
  intros s i rest live rest' live' Hr Hc. unfold relies in Hr.
  apply orb_false_iff in Hr as [Hr _]. apply orb_false_iff in Hr as [Hr Hg].
  apply orb_false_iff in Hr as [Hp Hl].
  destruct (check_fact i) as [fa|] eqn:Hf.
  - rewrite (check_fact_preserving _ _ Hf) in Hp. discriminate Hp.
  - destruct (pass_special i) eqn:Hs.
    + unfold pass_special in Hs. rewrite Hf in Hs.
      destruct i as [q k o args | | | | | | | | ]; try discriminate Hs.
      destruct k; try discriminate Hs; destruct o; try discriminate Hs.
      * destruct args; [discriminate Hl | discriminate Hs].
      * exact (checked_inst_rest_function _ _ _ _ _ _ _ Hc).
    + rewrite (checked_inst_rest_generic _ _ _ _ Hs) in Hc. unfold generic_rest in Hc.
      cbn zeta in Hc.
      match type of Hc with (if ?b then _ else _) = _ => destruct b; [|discriminate Hc] end.
      injection Hc as _ <-. unfold evidence_after. rewrite Hp.
      destruct i as [d k o args | | | | | | | | ]; try reflexivity.
      destruct o; try reflexivity; destruct k; try reflexivity;
        destruct args as [|[n|c|g] [|a2 args]]; try reflexivity.
      unfold repeated_getter in Hg. destruct (lookup d (s_getters s)) as [g1|]; [|reflexivity].
      rewrite Hg. reflexivity.
Qed.

(** ## The forms the pass pairs with their access *)

(** A `check_local` of the local x that continues binds its result q to the
    pointer at offset off of x's object, changes no memory, and its access
    check passed ([access_res]). *)
Lemma check_local_step : forall ge fr m q x off bytes r al e1 l1 m1,
  inst_step ge fr m (Let q A (CheckLocal x off bytes r al) []) = Some (IContinue e1 l1 m1) ->
  exists base, lookup x (fr_locals fr) = Some (Some base) /\ m1 = m /\
    e1 = put q (WPtr (mkPtr (base + off) (Obj base))) (fr_env fr) /\
    access_res m (base + off) (Obj base) bytes r al = Some ok.
Proof.
  intros ge fr m q x off bytes r al e1 l1 m1 H. unfold inst_step in H. cbn iota beta zeta in H.
  destruct (lookup x (fr_locals fr)) as [[base|]|]; try discriminate H.
  destruct (access_res m (base + off) (Obj base) bytes r al) as [[[] | w | w]|] eqn:E;
    try discriminate H.
  injection H as <- <- <-. eauto.
Qed.

(** A `check_function` that continues binds its result q to a pointer p
    whose function check passed ([function_check_res]). *)
Lemma check_function_step : forall ge fr m q args e1 l1 m1,
  inst_step ge fr m (Let q F CheckFunction args) = Some (IContinue e1 l1 m1) ->
  exists p, function_check_res ge p = Some ok /\ e1 = put q (WPtr p) (fr_env fr).
Proof.
  intros ge fr m q args e1 l1 m1 H.
  destruct args as [|v [|v' args]]; unfold inst_step in H; cbn iota beta zeta in H; try discriminate H.
  destruct (value_x ge (fr_env fr) P v) as [[n | p | c size]|]; try discriminate H.
  destruct (function_check_res ge p) as [[[] | w | w]|] eqn:E; try discriminate H.
  injection H as <- <- <-. eauto.
Qed.

(** An access check that passes on the object at base, for size bytes at
    address a, finds base's [[region]] in memory and the bytes inside it,
    from base up to its end. *)
Lemma access_res_obj : forall m a base size r al,
  access_res m a (Obj base) size r al = Some ok ->
  exists reg, object_region base (m_regions m) = Some reg /\ base <= a /\ a + size <= r_end reg.
Proof.
  unfold access_res, cap_access_res. intros m a base size r al H.
  destruct (object_region base (m_regions m)) as [reg|]; [|discriminate H].
  destruct ((base <=? a) && (a + size <=? r_end reg)) eqn:E; [|discriminate H].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. eauto.
Qed.

(** A [[covered access|covered]] access lies inside the checked range, from
    lo up to hi, so that range is not empty. *)
Lemma covered_nonempty : forall i q lo hi r al, covered_access i q lo hi r al = true -> lo < hi.
Proof.
  unfold covered_access. intros i q lo hi r al H.
  destruct (raw_access i) as [[[[q' x] off] need]|]; [|discriminate H].
  pose proof (access_size_align_pos x) as [Hs _].
  destruct (access_size_align x) as [size aa]. simpl in Hs.
  repeat match goal with Hb : (_ && _) = true |- _ => apply andb_true_iff in Hb as [? ?] end.
  repeat match goal with Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb end. lia.
Qed.

(** The pass takes a `check_local` together with the access after it: that
    access is covered by the check's range, from 0 up to bytes, and the
    facts after are what the access ([evidence_after]) leaves of the live
    facts less those about q ([kill]). *)
Lemma checked_inst_rest_local_cov : forall s q x off bytes r al rest live rest' live',
  checked_inst_rest s (Let q A (CheckLocal x off bytes r al) []) rest live = Some (rest', live') ->
  exists access, rest = access :: rest' /\ covered_access access q 0 bytes r al = true /\
    live' = evidence_after access (kill q live).
Proof.
  intros s q x off bytes r al rest live rest' live' H. unfold checked_inst_rest in H. cbn zeta in H.
  destruct rest as [|access rest0]; [discriminate H|].
  destruct (raw_access access) as [[[[q' xa] o] need]|]; [|discriminate H].
  destruct o; try discriminate H.
  destruct (name_eqb q' q && covered_access access q 0 bytes r al && storage_effects access Local')
    eqn:E; [|discriminate H].
  injection H as <- <-. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [_ E]. eauto.
Qed.

(** After a `check_local` q of the local x that continues, in a memory whose
    objects fit ([objects_fit]) and a frame whose locals lie above address
    0, the memory is unchanged, the environment changed only at q, and the
    check's access holds as a fact of q ([fact_holds]). *)
Lemma check_local_fact : forall ge fr m q x off bytes r al e1 l1 m1 access,
  objects_fit (m_regions m) ->
  (forall y base, lookup y (fr_locals fr) = Some (Some base) -> 0 < base) ->
  covered_access access q 0 bytes r al = true ->
  inst_step ge fr m (Let q A (CheckLocal x off bytes r al) []) = Some (IContinue e1 l1 m1) ->
  m1 = m /\ env_agree q (fr_env fr) e1 /\ fact_holds ge m1 e1 (mkFact q (Tmp q) 0 bytes r al).
Proof.
  intros ge fr m q x off bytes r al e1 l1 m1 access Hfit Hpos Hcov H.
  destruct (check_local_step _ _ _ _ _ _ _ _ _ _ _ _ H) as (base & Hl & -> & -> & Hc).
  split; [reflexivity|]. split; [apply env_agree_put|].
  pose proof (covered_nonempty _ _ _ _ _ _ Hcov) as Hb.
  pose proof (Hpos _ _ Hl) as Hbase.
  destruct (access_res_obj _ _ _ _ _ _ Hc) as (reg & Er & H1 & H2).
  pose proof (Hfit _ _ Er) as Hend.
  exists (mkPtr (base + off) (Obj base)). cbn [f_q f_p f_lo f_hi f_r f_al].
  split; [apply lookup_put_same|].
  split; [unfold value_x; rewrite lookup_put_same; reflexivity|].
  unfold check_passes, raw_address. simpl ptr_addr. simpl ptr_cap. rewrite Z.sub_0_r, Z.add_0_r, Z.mod_small by lia. exact Hc.
Qed.

(** ## The pass's sources of a function *)

(** The sources ([src]) the pass reads for the function f of the module md:
    what `stage_sources/4` computes from f's
    [[dominance|dominator intervals]], or from no intervals where there are
    none. *)
Definition fn_src (md : module) (f : func) : src :=
  stage_sources md f (match block_intervals (fn_blocks f) with Some doms => doms | None => nm_empty end).

(** The function f's dominator intervals, as [fn_src] reads them. *)
Definition fn_doms (f : func) : nmap (Z * Z) :=
  match block_intervals (fn_blocks f) with Some doms => doms | None => nm_empty end.

(** [fn_src] by cases: empty in a function with a `setjmp`, else what
    the single definitions give. The proofs of the reuse forms rewrite
    by it, so a hypothesis about a source becomes one about
    [single_definitions] or about an empty list. *)
Lemma fn_src_cases : forall md f,
  (setjmp_func f = true /\ fn_src md f = mkSrc [] [] [] []) \/
  (setjmp_func f = false /\
   fn_src md f =
     mkSrc (flat_map (fun b => flat_map (fun i => match renew_source (single_definitions f) i with
                                                  | Some r => [r]
                                                  | None => []
                                                  end) (b_insts b)) (fn_blocks f))
           (single_definitions f) (ahead_justified f (single_definitions f))
           (repeated_getters md f (fn_doms f) (single_definitions f))).
Proof.
  intros md f. unfold fn_src, fn_doms, stage_sources. destruct (setjmp_func f); auto.
Qed.

(** The first answer of a function that answers nothing is none. *)
Lemma first_some_none : forall {X Y : Type} (g : X -> option Y) xs,
  (forall x, g x = None) -> first_some g xs = None.
Proof. intros X Y g xs H. induction xs as [|x xs IH]; [reflexivity|]. simpl. rewrite H. exact IH. Qed.

(** With no single definitions there is no exact base, so no distance. *)
Lemma pointer_distance_nil : forall p p1, pointer_distance [] p p1 = None.
Proof.
  intros p p1. unfold pointer_distance. apply first_some_none.
  intros [[n| | ] [k k']]; try reflexivity. unfold exact_base, once_has. simpl.
  rewrite andb_false_r. reflexivity.
Qed.

(** With no single definitions no hull covers an access. *)
Lemma hull_covered_nil : forall i q p lo al live, hull_covered i q p lo al live [] = false.
Proof.
  intros i q p lo al live. unfold hull_covered.
  destruct (raw_access i) as [[[[q' x] off] need]|]; [|reflexivity].
  destruct (access_size_align x) as [size aa]. cbv zeta.
  assert (E : forall (live : list fact),
    flat_map (fun f => match pointer_distance [] (f_p f) p with
                       | Some d => if near_offset d && near_offset (f_lo f + d) && near_offset (f_hi f + d)
                                   then [(f_lo f + d, f_hi f + d, f_r f)] else []
                       | None => []
                       end) live = []).
  { intros l. induction l as [|a rest IH]; [reflexivity|]. cbn [flat_map]. rewrite pointer_distance_nil. exact IH. }
  rewrite E. cbn [existsb]. rewrite !andb_false_r. reflexivity.
Qed.

(** The label of the function f's entry block, its first, if it has blocks. *)
Definition entry_label (f : func) : option name :=
  match fn_blocks f with b :: _ => Some (b_label b) | [] => None end.

(** md is valid and in the [[stage|checked stage]], so each of its functions
    passed the [[evidence pass]]. *)
Definition checked_module (md : module) : Prop := valid md = Some true /\ module_checked md = true.

(** Every function f of a [checked_module] md has distinct block labels and
    an entry block that no jump goes to, and the pass computes its exit
    facts. *)
Lemma module_func : forall md f,
  checked_module md -> In (IFunc f) md ->
  no_dups (map b_label (fn_blocks f)) = true /\
  (exists b0 bs, fn_blocks f = b0 :: bs /\
     existsb (fun b => mem (b_label b0) (succ_labels (b_jump b))) (fn_blocks f) = false) /\
  exists E, pass_exits (fn_src md f) f = Some E.
Proof.
  unfold checked_module, valid. intros md f [Hv Hc] Hin.
  destruct (existsb _ md); [discriminate Hv|]. injection Hv as Hv.
  unfold valid_items in Hv. apply andb_true_iff in Hv as [_ Hv]. rewrite forallb_forall in Hv.
  specialize (Hv _ Hin). simpl in Hv. unfold valid_func, fn_src in *.
  destruct (fn_blocks f) as [|b0 bs] eqn:Eb; [discriminate Hv|].
  destruct (block_intervals (b0 :: bs)) as [doms|]; [|discriminate Hv].
  rewrite Hc in Hv. unfold stage_func in Hv. cbn [negb orb] in Hv.
  repeat match goal with Hb : (_ && _) = true |- _ => apply andb_true_iff in Hb as [? ?] end.
  split; [assumption|]. split.
  - exists b0, bs. split; [reflexivity|].
    apply negb_true_iff. assumption.
  - match goal with Hb : evidence_pass _ _ = true |- _ => rewrite evidence_pass_exits in Hb end.
    destruct (pass_exits _ _); [eauto | discriminate].
Qed.

(** A local of a frame's starting locals, each object paired with none, has
    no base: none is allocated yet. *)
Lemma lookup_unallocated : forall x base (objs : list (name * Z)),
  lookup x (map (fun xs => (fst xs, @None Z)) objs) <> Some (Some base).
Proof.
  intros x base. induction objs as [|[y z] objs IH]; simpl; [discriminate|].
  destruct (name_eqb x y); [discriminate | exact IH].
Qed.

(** ## The pass's own forms *)

(** The instruction i is a `check_function`, the check that a pointer
    designates a function. *)
Definition is_check_function (i : inst) : bool :=
  match i with Let _ F CheckFunction _ => true | _ => false end.

(** An instruction the pass treats apart ([pass_special]) that adds no fact
    is a `check_local` or a `check_function`. *)
Lemma pass_special_cases : forall i,
  pass_special i = true -> check_fact i = None -> is_check_local i = true \/ is_check_function i = true.
Proof.
  intros i H Hf. destruct i as [q k o args | | | | | | | | ]; try discriminate H.
  destruct o; destruct k; try discriminate H; try discriminate Hf; auto;
    destruct args as [|a1 [|a2 [|a3 [|a4 args]]]]; auto; discriminate.
Qed.

(** An instruction the pass does not rely on facts for is not evidence
    preserving. *)
Lemma relies_preserving : forall s i, relies s i = false -> evidence_preserving i = false.
Proof.
  unfold relies. intros s i H. apply orb_false_iff in H as [H _]. apply orb_false_iff in H as [H _].
  apply orb_false_iff in H as [H _]. exact H.
Qed.

(** An instruction the pass does not rely on facts for is not a
    `check_local`. *)
Lemma relies_local : forall s i, relies s i = false -> is_check_local i = false.
Proof.
  unfold relies. intros s i H. apply orb_false_iff in H as [H _]. apply orb_false_iff in H as [H _].
  apply orb_false_iff in H as [_ H]. exact H.
Qed.

(** Where the pass relies on nothing, it goes on to the next instruction
    with no facts, but after a `check_function`, which takes the raw call
    after it too. *)
Lemma relies_false_rest : forall s i rest live rest' live',
  relies s i = false -> is_check_function i = false ->
  checked_inst_rest s i rest live = Some (rest', live') -> rest' = rest /\ live' = [].
Proof.
  intros s i rest live rest' live' Hr Hcf Hc. split; [|exact (relies_false _ _ _ _ _ _ Hr Hc)].
  destruct (check_fact i) as [fa|] eqn:Hf.
  { pose proof (check_fact_preserving _ _ Hf) as Hp.
    rewrite (relies_preserving _ _ Hr) in Hp. discriminate Hp. }
  destruct (pass_special i) eqn:Hs.
  - destruct (pass_special_cases _ Hs Hf) as [Hl | Hl].
    + rewrite (relies_local _ _ Hr) in Hl. discriminate Hl.
    + rewrite Hcf in Hl. discriminate Hl.
  - rewrite (checked_inst_rest_generic _ _ _ _ Hs) in Hc. exact (proj1 (generic_rest_shape _ _ _ _ _ _ Hc)).
Qed.

(** The pass takes a `check_function` q together with the raw call through q
    after it, and goes on with no facts. *)
Lemma checked_inst_rest_function_rest : forall s q args rest live rest' live',
  checked_inst_rest s (Let q F CheckFunction args) rest live = Some (rest', live') ->
  live' = [] /\ exists r cargs, rest = RawCall r (Tmp q) cargs :: rest'.
Proof.
  intros s q args rest live rest' live' H. unfold checked_inst_rest in H.
  destruct rest as [|[] rest0]; try discriminate H; cbn iota beta in H.
  destruct callee as [q'| |]; try discriminate H. destruct (name_eqb q' q) eqn:E; [|discriminate H].
  injection H as <- <-. apply term_eqb_eq in E. subst q'. eauto.
Qed.

(** A [[raw access]] is not one of the instructions the pass treats apart. *)
Lemma raw_access_not_special : forall i a, raw_access i = Some a -> pass_special i = false.
Proof.
  intros i a H. destruct i as [q k o args | | | | | | | | ]; try reflexivity.
  destruct o; simpl in H; try discriminate H; destruct k; reflexivity.
Qed.

(** The pass never takes a raw call on its own: only after the
    `check_function` of its callee. *)
Lemma raw_call_alone : forall s r cl args rest live, checked_inst_rest s (RawCall r cl args) rest live = None.
Proof.
  intros s r cl args rest live. rewrite checked_inst_rest_generic by reflexivity. reflexivity.
Qed.
