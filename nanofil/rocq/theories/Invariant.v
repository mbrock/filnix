(** Campaign 3's run-level invariant, stated (docs/rocq.md, "The
    evidence invariant over runs"): what holds at each point of a frame
    of `Machine R` (Machine.v), and the lemmas each kind of step needs.
    Persistence.v proves that every step keeps it.

    | Name | Says |
    |---|---|
    | `at_pos` | where the pass is in a block, and what holds there: the facts the next instruction relies on, those the unpolled edge at the end carries, or the fact covering the access taken with a check (`pair_claim`) |
    | `point_ok` | what holds at a frame's point: a function's entry, a block's entry from a predecessor whose exit facts hold unless the edge polls, or `at_pos` |
    | `frame_ok`, `parked`, `inv` | the running frame, unless doomed, is `point_ok`; each waiting caller has no fact |
    | `spares` | the runtime changes no region at a safepoint before an instruction the pass relies on facts for |
    | `pass_step` | an instruction the pass took, that continues, leaves the pass's next position true |
    | `enter_point_ok` | entering a block, the pass's entry facts hold |
    | `at_pos_continue`, `walks_after` | the next position after an instruction that continues, or after one the pass keeps no fact across | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Coverage Evidence Walk Steps.
Import ListNotations.
Open Scope Z_scope.

(** ## The invariant, frame by frame *)

Module Invariant (R : Runtime).

Module RM := Machine R.
Import RM.

(** The edge a jump takes is one of its targets. *)
Lemma taken_target_in : forall ge fr j t, taken_target ge fr j = Some t -> In t (jump_targets j).
Proof.
  unfold taken_target. intros ge fr j t H. destruct j; try discriminate H.
  - injection H as <-. left. reflexivity.
  - destruct (value_x _ _ _ _) as [[n| |]|]; try discriminate H. injection H as <-.
    destruct (n =? 0); simpl; auto.
Qed.

Lemma edge_step_next' : forall c from t c',
  edge_step c from t = Next c' ->
  c' = continue_at c (with_point (c_frame c) (Enter (edge_label t) (Some from))) (c_mem c) (c_fuel c) /\
  (fr_doomed (c_frame c) = None \/ is_poll t = false).
Proof.
  unfold edge_step. intros c from t c' H.
  destruct t, (fr_doomed (c_frame c)); try discriminate H; injection H as <-; auto.
Qed.

(** A jump takes an edge, the one `taken_target` names, or returns from
    a frame that is not doomed. *)
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

    `at_pos` says where the pass is in a block and what holds there:
    between two of the pass's steps, the live facts the next
    instruction relies on (and, at the block's end, the facts the next
    unpolled edge carries); or between a check and the access the pass
    took with it, the fact that covers the access (`pair_claim`). A
    `check_function`'s raw call needs no fact but its function check. *)

Definition jump_claim (ge : genv) (m : Memory.mem) (fr : frame) (j : jump) (live : list fact) : Prop :=
  forall t, taken_target ge fr j = Some t -> is_poll t = false -> facts_hold ge m (fr_env fr) live.

Definition pair_claim (ge : genv) (m : Memory.mem) (fr : frame) (access : inst) (live' : list fact) : Prop :=
  (exists fb pre, covered_access access (f_q fb) (f_lo fb) (f_hi fb) (f_r fb) (f_al fb) = true /\
     live' = evidence_after access pre /\ facts_hold ge m (fr_env fr) (fb :: pre)) \/
  (live' = [] /\ exists r q args p, access = RawCall r (Tmp q) args /\
     lookup q (fr_env fr) = Some (WPtr p) /\ function_check_res ge p = Some ok).

Definition at_pos (ge : genv) (s : src) (m : Memory.mem) (fr : frame) (is : list inst) (j : jump)
    (out : list fact) : Prop :=
  (exists live, walks s is live out /\
     match is with
     | i :: _ => relies s i = true -> facts_hold ge m (fr_env fr) live
     | [] => jump_claim ge m fr j live
     end) \/
  (exists access rest' live', is = access :: rest' /\ walks s rest' live' out /\
     pair_claim ge m fr access live').

(** `point_ok`: what holds at the frame's point. A block is entered
    from the entry of the function, or by an edge of a block whose exit
    facts hold unless the edge polls; within a block, `at_pos`. *)
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
  | Exec l is j =>
      exists b out, find_block l (fn_blocks f) = Some b /\ lookup l E = Some out /\
        j = b_jump b /\ at_pos ge (fn_src md f) m fr is j out
  end.

(** Every named local the frame has allocated lies above 0. *)
Definition locals_pos (fr : frame) : Prop :=
  forall x base, lookup x (fr_locals fr) = Some (Some base) -> 0 < base.

(** The running frame: a function of the module, its locals, and
    `point_ok` unless a `check_ahead` doomed it. *)
Definition frame_ok (ge : genv) (md : module) (m : Memory.mem) (fr : frame) : Prop :=
  In (IFunc (fr_fn fr)) md /\ locals_pos fr /\ (fr_doomed fr <> None \/ point_ok ge md m fr).

(** A caller waits after its call with no live fact. *)
Definition parked (md : module) (fr : frame) : Prop :=
  In (IFunc (fr_fn fr)) md /\ locals_pos fr /\ fr_doomed fr = None /\
  exists E l rest j b out, pass_exits (fn_src md (fr_fn fr)) (fr_fn fr) = Some E /\
    fr_at fr = Exec l rest j /\ find_block l (fn_blocks (fr_fn fr)) = Some b /\
    lookup l E = Some out /\ j = b_jump b /\ walks (fn_src md (fr_fn fr)) rest [] out.

Definition inv (ge : genv) (md : module) (st : mstate) : Prop :=
  frame_ok ge md (c_mem (fst st)) (c_frame (fst st)) /\
  Forall (fun fp => parked md (fst fp)) (c_callers (fst st)).

(** `spares ge md`: the runtime's action at a safepoint leaves every
    region where the pass relies on facts across the instruction. *)
Definition spares (ge : genv) (md : module) : Prop :=
  forall c s s' m',
    safepoint_due ge c = true -> R.safepoint s (c_mem c) s' m' ->
    forall l i rest j, fr_at (c_frame c) = Exec l (i :: rest) j ->
    relies (fn_src md (fr_fn (c_frame c))) i = true -> m_regions m' = m_regions (c_mem c).

Lemma facts_hold_nil : forall ge m e, facts_hold ge m e [].
Proof. intros ge m e fa []. Qed.

(** Where the facts after a step hold, whatever comes next may rely on
    them. *)
Lemma at_pos_between : forall ge s m fr is j live out,
  walks s is live out -> facts_hold ge m (fr_env fr) live -> at_pos ge s m fr is j out.
Proof.
  intros ge s m fr is j live out Hw Hl. left. exists live. split; [exact Hw|].
  destruct is; [intros t _ _; exact Hl | intros _; exact Hl].
Qed.

(** A parked caller resumes with any result and memory. *)
Lemma parked_resume : forall ge md m fr e,
  parked md fr -> frame_ok ge md m (mkFrame (fr_fn fr) e (fr_locals fr) (fr_doomed fr) (fr_at fr)).
Proof.
  intros ge md m fr e (Hin & Hpos & Hd & E & l & rest & j & b & out & HE & Ha & Hb & Hout & Hj & Hw).
  split; [exact Hin|]. split; [exact Hpos|]. right. exists E. split; [exact HE|]. simpl. rewrite Ha.
  exists b, out. split; [exact Hb|]. split; [exact Hout|]. split; [exact Hj|].
  eapply at_pos_between; [exact Hw | apply facts_hold_nil].
Qed.

(** A callee starts at its entry. *)
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

(** `pass_step`: an instruction the pass took, that continues, leaves
    the pass's next position true: the facts after it, or the fact that
    covers the access the pass took with it. *)
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
    apply andb_true_iff in Hu as [Hcov _]. split; [exact Hcov|]. split; [reflexivity|].
    rewrite He. apply facts_hold_cons; [exact Hb|]. apply facts_hold_cons; [exact Ha|].
    eapply evidence_after_holds; eauto.
  - destruct (is_check_local i) eqn:Hcl.
    + destruct i as [q k o args | | | | | | |]; try discriminate Hcl.
      destruct k; try discriminate Hcl; destruct o; try discriminate Hcl;
        destruct args; try discriminate Hcl.
      specialize (Hl eq_refl).
      destruct (checked_inst_rest_local_cov _ _ _ _ _ _ _ _ _ _ _ Hc) as (access & -> & Hcov & ->).
      destruct (check_local_fact _ _ _ _ _ _ _ _ _ _ _ _ _ Hfit Hpos Hcov Hs) as (-> & Hag & Hq).
      destruct (let_step _ _ _ _ _ _ _ _ _ _ Hs) as [Hreg _].
      right. exists access. split; [reflexivity|]. left.
      exists (mkFact q (Tmp q) 0 bytes r align), (kill q live). split; [exact Hcov|].
      split; [reflexivity|]. rewrite He. apply facts_hold_cons; [exact Hq|].
      eapply facts_hold_kill; [reflexivity | exact Hag | exact Hl].
    + destruct (is_check_function i) eqn:Hcf.
      * destruct i as [q k o args | | | | | | |]; try discriminate Hcf.
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

(** The access the pass took with its check, if it continues, leaves
    the facts the pass has after it. *)
Lemma pair_continue : forall ge m fr access live' e1 l1 m1,
  pair_claim ge m fr access live' ->
  inst_step ge fr m access = Some (IContinue e1 l1 m1) -> facts_hold ge m1 e1 live'.
Proof.
  intros ge m fr access live' e1 l1 m1 [(fb & pre & _ & -> & Hh) | (-> & _)] Hs; [|apply facts_hold_nil].
  eapply evidence_after_holds; [|exact Hs]. intros fa Hin. apply Hh. right. exact Hin.
Qed.

(** `at_pos_continue`: where the instruction at the pass's position
    continues, the next position holds. *)
Lemma at_pos_continue : forall ge s m fr i rest j out e1 l1 m1 fr1,
  objects_fit (m_regions m) -> locals_pos fr ->
  at_pos ge s m fr (i :: rest) j out ->
  inst_step ge fr m i = Some (IContinue e1 l1 m1) -> fr_env fr1 = e1 ->
  at_pos ge s m1 fr1 rest j out.
Proof.
  intros ge s m fr i rest j out e1 l1 m1 fr1 Hfit Hpos Hat Hs He.
  destruct Hat as [(live & Hw & Hl) | (access & rest' & live' & E & Hw & Hp)].
  - destruct (walks_cons _ _ _ _ _ Hw) as (rest' & live' & Hc & Hw').
    destruct (pass_step _ _ _ _ _ _ _ _ _ _ _ _ _ Hfit Hpos Hl Hc Hs He)
      as [(-> & Hh) | (access & -> & Hp)].
    + eapply at_pos_between; [exact Hw' | rewrite He; exact Hh].
    + right. exists access, rest', live'. auto.
  - injection E as <- <-. eapply at_pos_between; [exact Hw|]. rewrite He.
    eapply pair_continue; eauto.
Qed.

(** After an instruction the pass relies on nothing for, and that is
    not a `check_function`, the pass goes on with no facts. *)
Lemma walks_after : forall ge s m fr i rest j out,
  at_pos ge s m fr (i :: rest) j out -> relies s i = false -> is_check_function i = false ->
  walks s rest [] out.
Proof.
  intros ge s m fr i rest j out Hat Hr Hcf.
  destruct Hat as [(live & Hw & _) | (access & rest' & live' & E & Hw & Hp)].
  - destruct (walks_cons _ _ _ _ _ Hw) as (rest' & live' & Hc & Hw').
    destruct (relies_false_rest _ _ _ _ _ _ Hr Hcf Hc) as [-> ->]. exact Hw'.
  - injection E as <- <-.
    destruct Hp as [(fb & pre & _ & -> & _) | (-> & _)]; [|exact Hw].
    unfold evidence_after in Hw. rewrite (relies_preserving _ _ Hr) in Hw. exact Hw.
Qed.

(** ### Reading and making `point_ok` *)

Lemma point_ok_exec : forall ge md m fr l is j E b out,
  pass_exits (fn_src md (fr_fn fr)) (fr_fn fr) = Some E -> fr_at fr = Exec l is j ->
  find_block l (fn_blocks (fr_fn fr)) = Some b -> lookup l E = Some out -> j = b_jump b ->
  at_pos ge (fn_src md (fr_fn fr)) m fr is j out -> point_ok ge md m fr.
Proof.
  intros ge md m fr l is j E b out HE Ha Hb Ho Hj Hat. unfold point_ok. cbv zeta.
  exists E. split; [exact HE|]. rewrite Ha. eauto 7.
Qed.

Lemma point_ok_exec_inv : forall ge md m fr l is j,
  point_ok ge md m fr -> fr_at fr = Exec l is j ->
  exists E b out, pass_exits (fn_src md (fr_fn fr)) (fr_fn fr) = Some E /\
    find_block l (fn_blocks (fr_fn fr)) = Some b /\ lookup l E = Some out /\ j = b_jump b /\
    at_pos ge (fn_src md (fr_fn fr)) m fr is j out.
Proof.
  intros ge md m fr l is j H Ha. unfold point_ok in H. cbv zeta in H.
  destruct H as (E & HE & H). rewrite Ha in H. destruct H as (b & out & ?). eauto 8.
Qed.

(** A function's entry is where its snapshot leads. *)
Lemma point_ok_entry : forall ge md m m' fr fr' xs l,
  point_ok ge md m fr -> fr_at fr = Snapshot xs l \/ fr_at fr = Enter l None ->
  fr_fn fr' = fr_fn fr -> fr_at fr' = Enter l None -> point_ok ge md m' fr'.
Proof.
  intros ge md m m' fr fr' xs l H Ha Hf Ha'. unfold point_ok in *. cbv zeta in *. rewrite Hf, Ha'.
  destruct H as (E & HE & H). exists E. split; [exact HE|].
  destruct Ha as [Ha | Ha]; rewrite Ha in H; exact H.
Qed.

Lemma lookup_nil_none : forall (A : Type) n, @lookup A n [] = None.
Proof. reflexivity. Qed.

(** `enter_point_ok`: entering a block, the pass's entry facts hold. *)
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
  eapply point_ok_exec with (b := b) (out := out); simpl; [exact HE | reflexivity | exact Hb
                                                         | rewrite <- Hbl; exact Hout | reflexivity |].
  eapply at_pos_between; [exists (S (length (b_insts b))); exact Hc|]. simpl.
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
