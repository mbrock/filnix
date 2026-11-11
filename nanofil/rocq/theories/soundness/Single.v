(** Campaign 3's [[single-definition invariant]] over runs
    (docs/formal.md, Campaign 3;
    [docs/rocq.md, The single-definition invariant](../../../docs/rocq.md#the-single-definition-invariant)).

    The [[reuse]] forms' rules read relations between the values of
    names that have one definition each: a [[flight]] and its base, a
    [[proof]] and the pointer it checked, a [[span test]] or a [[limit]]
    and the pointer it read. Such a relation holds at a point of a run
    only where the name's definition [[dominates]] the point, and only
    while the definition's operands hold the values it read. This file
    states that for every frame of every run ([sinv]), and proves that
    every machine step keeps it ([mreachable_sinv]).

    At a frame's point, each single definition whose [[site]] dominates
    the point [[replays]] ([replays]): the name holds what its
    instruction made in some earlier frame and memory, that frame agrees
    with the current environment on the instruction's single-definition
    operands, and the current memory [[identity|persists]] from the
    memory the instruction left (Identity.v), which lay in the address
    space. A check that passed then passes again or traps; a flight's
    capability is its lower donor's.

    ## Decisions

    | Decision | Why |
    |---|---|
    | the relation is the instruction's own step, replayed | one statement covers every op; each reuse form reads off what it needs from [inst_step] |
    | the operands a replay fixes are the single definitions | [no_use_redefined] (Sites.v) keeps exactly those; a name defined twice may change, and no reuse rule follows one |
    | a call and an `alloc` do not replay | their step is not one that continues; no reuse rule reads through them |
    | a doomed frame claims nothing | its `check_ahead` did not pass; a doomed frame never returns to a caller or calls one |
    | memory is handled once, for every step | each step's memory persists ([mstep_persists]), so the step lemmas carry frames and a replay's memory follows by [scope_mem] |
    | a replay keeps that the memory it left fit the address space ([objects_fit]) | the object of a check that passed then ended below 2^48; once the object is freed, the current memory no longer says where it ended |
    | free keeps identities by Runtime.v's axiom [free_keeps_ids] | mbrock's decision ([docs/rocq.md, Identities persist](../../../docs/rocq.md#identities-persist)) | *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Sites Identity Walk Steps Invariant.
Import ListNotations.
Open Scope Z_scope.

(** ## The invariant *)

(** The instructions a replay speaks of: a `let` that is not an `alloc`,
    and a [[flight]]. Their step continues and defines a name; a call's
    or an allocation's does not continue with a value, and no reuse rule
    reads through one. *)
Definition replayable (i : inst) : bool :=
  match i with
  | Let _ _ (Alloc _) _ => false
  | Let _ _ _ _ | Flight _ _ _ _ => true
  | _ => false
  end.

(** The name n, defined by the instruction i, [[replays]] in the
    environment e and memory m: in some earlier frame fr0 and memory m0,
    i's step continued and gave n the value it has in e; fr0 agrees with
    e on i's single-definition operands (once being the function's
    [single_definitions]); and m [persists] from the memory m1 the step
    left, whose objects fit the address space ([objects_fit]). *)
Definition replays (ge : genv) (once : list (name * def)) (e : env) (m : Memory.mem) (n : name) (i : inst)
  : Prop :=
  exists fr0 m0 e1 l1 m1,
    inst_step ge fr0 m0 i = Some (IContinue e1 l1 m1) /\ lookup n e1 = lookup n e /\
    (forall a, In a (inst_uses i) -> once_has once a = true -> lookup a (fr_env fr0) = lookup a e) /\
    persists m1 m /\ objects_fit (m_regions m1).

(** The block and index of the point pt of f, as `site_dominates/4`
    reads them: a block's entry is before its phis, at index -1; a
    [[snapshot]] has none. *)
Definition point_site (f : func) (pt : point) : option (name * Z) :=
  match pt with
  | Snapshot _ _ => None
  | Enter l _ => Some (l, -1)
  | Exec l is _ =>
      match find_block l (fn_blocks f) with
      | Some b => Some (l, Z.of_nat (length (b_insts b) - length is))
      | None => None
      end
  end.

(** At the point of the frame fr, each replayable single definition (the
    name n, defined by i at the site s) whose [[site]] dominates the
    point satisfies the property rp in fr's environment and the memory
    m. [scope_holds] takes [replays] for rp; [scope_plain] a weaker
    one. *)
Definition scope_with (rp : list (name * def) -> env -> Memory.mem -> name -> inst -> Prop)
    (fr : frame) (m : Memory.mem) : Prop :=
  let f := fr_fn fr in
  forall l k n s i,
    point_site f (fr_at fr) = Some (l, k) ->
    lookup n (single_definitions f) = Some (DInst i) -> replayable i = true ->
    In (n, s, DInst i) (def_positions f) -> site_dominates (fn_doms f) l k s = true ->
    rp (single_definitions f) (fr_env fr) m n i.

(** At the point of the frame fr, each replayable single definition
    whose site dominates the point [replays] in fr's environment and the
    memory m: fr holds its scope. *)
Definition scope_holds (ge : genv) (fr : frame) (m : Memory.mem) : Prop :=
  scope_with (replays ge) fr m.

(** The frame fr runs a function of the module md, at a point of a
    reachable block: a [[snapshot]] that leads to the entry, a block's
    entry (from no block only at the function's entry), or a suffix of
    a block's instructions before its jump. *)
Definition shaped (md : module) (fr : frame) : Prop :=
  let f := fr_fn fr in
  In (IFunc f) md /\
  match fr_at fr with
  | Snapshot _ l => entry_label f = Some l
  | Enter l from => is_reachable (fn_doms f) l = true /\ (from = None -> entry_label f = Some l)
  | Exec l is j =>
      is_reachable (fn_doms f) l = true /\
      exists b k, find_block l (fn_blocks f) = Some b /\ (k <= length (b_insts b))%nat /\
        is = skipn k (b_insts b) /\ j = b_jump b
  end.

(** The names a call's result r defines. *)
Definition result_names (r : call_result) : list name :=
  match r with CVoid => [] | CResult d _ => [d] | CTuple rs => map fst rs end.

(** The frame fr is just after a call or raw call whose result is the
    pending result pd's: it waits for its callee to return. *)
Definition waits (fr : frame) (pd : pending) : Prop :=
  exists l rest j b k ci,
    fr_at fr = Exec l rest j /\ find_block l (fn_blocks (fr_fn fr)) = Some b /\
    nth_error (b_insts b) k = Some ci /\ rest = skipn (S k) (b_insts b) /\
    ((exists cl args, ci = Call (pd_res pd) cl args) \/ (exists cl args, ci = RawCall (pd_res pd) cl args)).

(** The running frame fr is [shaped] and, unless doomed, holds its scope
    in the memory m. *)
Definition running (ge : genv) (md : module) (m : Memory.mem) (fr : frame) : Prop :=
  shaped md fr /\ (fr_doomed fr <> None \/ scope_holds ge fr m).

(** A waiting caller fp, its frame and the result it waits for, is
    [shaped], not doomed, just after the call it waits on ([waits]), and
    holds its scope in the memory m. *)
Definition waiting (ge : genv) (md : module) (m : Memory.mem) (fp : frame * pending) : Prop :=
  shaped md (fst fp) /\ fr_doomed (fst fp) = None /\ waits (fst fp) (snd fp) /\ scope_holds ge (fst fp) m.

(** The single-definition invariant of a configuration c: in c's
    memory, the running frame is [running] and every waiting caller is
    [waiting]. *)
Definition sinv (ge : genv) (md : module) (c : config) : Prop :=
  running ge md (c_mem c) (c_frame c) /\ Forall (waiting ge md (c_mem c)) (c_callers c).

(** ## Sites *)

(** A name an instruction defines ([DInst]) is at an instruction's site
    [SAt] d j, not at a parameter's ([SParam]). *)
Lemma dinst_site : forall f n s i, In (n, s, DInst i) (def_positions f) -> exists d j, s = SAt d j.
Proof.
  intros f n s i H. unfold def_positions in H. apply in_app_or in H as [H | H].
  - apply in_map_iff in H as (p & E & _). discriminate E.
  - apply in_flat_map in H as (b & _ & H). unfold block_positions in H. apply in_app_or in H as [H | H].
    + apply in_map_iff in H as ([d' k' pairs] & E & _). discriminate E.
    + destruct (inst_positions_in _ _ _ _ _ _ H) as (k & i' & _ & -> & _). eauto.
Qed.

(** One step on in a block: what dominates index k+1 is index k's
    instruction, or dominates index k. *)
Lemma site_next : forall doms l k s,
  site_dominates doms l (k + 1) s = true -> s = SAt l k \/ site_dominates doms l k s = true.
Proof.
  intros doms l k s H. destruct s as [| d j]; [right; reflexivity|]. simpl in *.
  destruct (name_eqb d l) eqn:E; [|right; exact H]. apply Z.ltb_lt in H.
  destruct (Z.eq_dec j k) as [-> | Hne].
  - left. apply name_eqb_true in E. subst. reflexivity.
  - right. apply Z.ltb_lt. lia.
Qed.

(** An instruction's site dominates a block's first instruction where
    it dominates the block's entry. *)
Lemma site_first : forall f doms l n s i,
  In (n, s, DInst i) (def_positions f) ->
  site_dominates doms l 0 s = true -> site_dominates doms l (-1) s = true.
Proof.
  intros f doms l n s i Hp H. destruct (dinst_site _ _ _ _ Hp) as (d & j & ->).
  destruct (position_inst _ _ _ _ _ Hp) as (b & kk & _ & _ & _ & -> & _).
  simpl in *. destruct (name_eqb d l); [apply Z.ltb_lt in H; lia | exact H].
Qed.

(** Across an edge from a reachable block p: what dominates the entry
    of s dominated the end of p. *)
Lemma site_edge : forall f b0 rest doms bp l n s i,
  fn_blocks f = b0 :: rest -> block_intervals (b0 :: rest) = Some doms ->
  no_dups (map b_label (fn_blocks f)) = true ->
  find_block (b_label bp) (fn_blocks f) = Some bp -> is_reachable doms (b_label bp) = true ->
  In l (jump_succs (b_jump bp)) ->
  In (n, s, DInst i) (def_positions f) -> site_dominates doms l (-1) s = true ->
  site_dominates doms (b_label bp) (Z.of_nat (length (b_insts bp))) s = true.
Proof.
  intros f b0 rest doms bp l n s i Hf Hd Hnd Hbp Hr Hl Hp H.
  destruct (dinst_site _ _ _ _ Hp) as (d & j & ->).
  destruct (position_inst _ _ _ _ _ Hp) as (b & kk & Hb & Hlb & Hk & -> & _).
  simpl in *. destruct (name_eqb d l) eqn:Edl; [apply Z.ltb_lt in H; lia|].
  assert (He : edge (b0 :: rest) (b_label bp) l).
  { exists bp. rewrite <- Hf. split; [exact (proj1 (find_block_in _ _ _ Hbp)) | auto]. }
  rewrite Hf in Hnd.
  destruct (dom_edge _ _ _ Hd _ _ _ Hnd Hr He H) as [E | Hdp].
  - subst d. apply name_eqb_false in Edl. contradiction.
  - destruct (name_eqb d (b_label bp)) eqn:E; [|exact Hdp].
    apply name_eqb_true in E. rewrite <- Hf in Hnd.
    rewrite (find_block_unique _ _ _ _ Hnd Hbp Hb (eq_trans Hlb E)) in Hk.
    assert (Hlt : (kk < length (b_insts bp))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
    apply Z.ltb_lt. lia.
Qed.

(** ## What a step changes in the environment *)

(** Putting d leaves the value of every name a not among d :: ds. *)
Lemma lookup_put_not : forall (A : Type) a d (v : A) ds e, ~ In a (d :: ds) -> lookup a (put d v e) = lookup a e.
Proof.
  intros A a d v ds e H. rewrite lookup_put. destruct (name_eqb a d) eqn:E; [|reflexivity].
  apply name_eqb_true in E. subst. exfalso. apply H. left. reflexivity.
Qed.

(** An instruction that continues changes only the names it defines
    ([inst_temp_defs]). *)
Lemma inst_step_env : forall ge fr m i e1 l1 m1,
  inst_step ge fr m i = Some (IContinue e1 l1 m1) ->
  forall a, ~ In a (map fst (inst_temp_defs i)) -> lookup a e1 = lookup a (fr_env fr).
Proof.
  intros ge fr m i e1 l1 m1 H a Ha. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: simpl in Ha; unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst;
    first [ reflexivity | exact (lookup_put_not _ _ _ _ [] _ Ha) ].
Qed.

(** An allocation's continuation changes only the names it defines. *)
Lemma inst_step_fresh_env : forall ge fr m i q k,
  inst_step ge fr m i = Some (IFresh q k) ->
  forall base a, ~ In a (map fst (inst_temp_defs i)) -> lookup a (fst (fst (k base))) = lookup a (fr_env fr).
Proof.
  intros ge fr m i q k H base a Ha. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: simpl in Ha; unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst.
  all: first
    [ reflexivity
    | match goal with |- ?g => match g with context [match ?t with pair _ _ => _ end] => destruct t as [x m'] end end;
      simpl;
      exact (lookup_put_not _ _ _ _ [] _ Ha) ].
Qed.

(** A fold of environment updates that starts from failure fails. *)
Lemma fold_env_none : forall (A : Type) (g : env -> A -> option env) xs,
  fold_left (fun acc x => let* e := acc in g e x) xs None = None.
Proof. intros A g xs. induction xs; simpl; auto. Qed.

(** A fold of puts changes only the names it puts. *)
Lemma fold_env_other : forall (A : Type) (key : A -> name) (g : env -> A -> option env) xs a,
  (forall e x e', g e x = Some e' -> lookup a e' = if name_eqb a (key x) then lookup a e' else lookup a e) ->
  ~ In a (map key xs) ->
  forall e0 e, fold_left (fun acc x => let* e := acc in g e x) xs (Some e0) = Some e -> lookup a e = lookup a e0.
Proof.
  intros A key g xs a Hg. induction xs as [|x xs IH]; simpl; intros Ha e0 e H.
  - injection H as <-. reflexivity.
  - destruct (g e0 x) as [e1|] eqn:E; [|rewrite fold_env_none in H; discriminate H].
    rewrite (IH (fun Hin => Ha (or_intror Hin)) _ _ H). rewrite (Hg _ _ _ E).
    destruct (name_eqb a (key x)) eqn:Ek; [|reflexivity].
    apply name_eqb_true in Ek. subst. exfalso. apply Ha. left. reflexivity.
Qed.

(** The name a phi defines. *)
Definition phi_name (ph : phi) : name := match ph with Phi d _ _ => d end.

(** Putting d leaves the value of every other name a. *)
Lemma lookup_put_ne : forall (A : Type) a d (v : A) e, a <> d -> lookup a (put d v e) = lookup a e.
Proof. intros A a d v e H. apply (lookup_put_not _ _ _ _ []). intros [E | []]. exact (H (eq_sym E)). Qed.

(** A block's phis change only the names they define. *)
Lemma phis_env_other : forall ge phis from e0 e a,
  phis_env ge phis from e0 = Some e -> ~ In a (map phi_name phis) -> lookup a e = lookup a e0.
Proof.
  intros ge phis from e0 e a H Ha. unfold phis_env in H. destruct from as [pred|];
    [|destruct phis; [injection H as <-; reflexivity | discriminate H]].
  assert (G : forall ps acc e', ~ In a (map phi_name ps) ->
            (forall ea, acc = Some ea -> lookup a ea = lookup a e0) ->
            fold_left (fun acc ph => let* e := acc in
                         match ph with
                         | Phi d k pairs => let* v := lookup pred pairs in
                                            let* x := value_x ge e0 k v in Some (put d x e)
                         end) ps acc = Some e' -> lookup a e' = lookup a e0).
  { intros ps. induction ps as [|[d k pairs] ps IH]; intros acc e1 Hn Hacc Hf; simpl in Hf.
    - exact (Hacc _ Hf).
    - eapply (IH _ e1 (fun Hin => Hn (or_intror Hin))); [|exact Hf].
      intros ea Ea. destruct acc as [eb|]; [|discriminate Ea]. simpl in Ea.
      destruct (lookup pred pairs) as [v|]; [|discriminate Ea]. simpl in Ea.
      destruct (value_x ge e0 k v); [|discriminate Ea]. simpl in Ea. injection Ea as <-.
      rewrite lookup_put_ne by (intros ->; apply Hn; left; reflexivity).
      exact (Hacc _ eq_refl). }
  apply (G phis (Some e0) e Ha); [intros ea E; injection E as <-; reflexivity | exact H].
Qed.

(** A call's result changes only the names it defines. *)
Lemma returned_env_other : forall r o e e' a,
  returned_env r o e = Some e' -> ~ In a (result_names r) -> lookup a e' = lookup a e.
Proof.
  intros r o e e' a H Ha. unfold returned_env in H.
  destruct o as [x | xs | | | | | | ]; destruct r as [| d k | rs]; try discriminate H; try (injection H as <-; reflexivity).
  - destruct (word_at_class k x); [|discriminate H]. injection H as <-.
    apply lookup_put_ne. intros ->. apply Ha. left. reflexivity.
  - destruct (negb _); [discriminate H|].
    assert (G : forall ps acc e', (forall p, In p ps -> In (fst (fst p)) (map fst rs)) ->
              (forall ea, acc = Some ea -> lookup a ea = lookup a e) ->
              fold_left (fun acc rx => let* e := acc in
                           let* y := word_at_class (snd (fst rx)) (snd rx) in
                           Some (put (fst (fst rx)) y e)) ps acc = Some e' -> lookup a e' = lookup a e).
    { intros ps. induction ps as [|p ps IH]; intros acc e1 Hps Hacc Hf; simpl in Hf.
      - exact (Hacc _ Hf).
      - eapply (IH _ e1 (fun q Hq => Hps q (or_intror Hq))); [|exact Hf].
        intros ea Ea. destruct acc as [eb|]; [|discriminate Ea]. simpl in Ea.
        destruct (word_at_class _ _); [|discriminate Ea]. simpl in Ea. injection Ea as <-.
        rewrite lookup_put_ne by (intros E; apply Ha; rewrite E; exact (Hps p (or_introl eq_refl))).
        exact (Hacc _ eq_refl). }
    apply (G (combine rs xs) (Some e) e'); [| intros ea E; injection E as <-; reflexivity | exact H].
    intros [[n k] y] Hp. apply in_map_iff. exists (n, k). split; [reflexivity | exact (in_combine_l _ _ _ _ Hp)].
Qed.

(** A call's result names are the names it defines. *)
Lemma call_defs : forall r cl args, map fst (inst_temp_defs (Call r cl args)) = result_names r.
Proof. intros r cl args. destruct r; reflexivity. Qed.

(** So are a raw call's. *)
Lemma raw_call_defs : forall r cl args, map fst (inst_temp_defs (RawCall r cl args)) = result_names r.
Proof. intros r cl args. destruct r; reflexivity. Qed.

(** A call's pending result is the call's. *)
Lemma inst_step_call_pending : forall ge fr m i g xs pd,
  inst_step ge fr m i = Some (ICall g xs pd) ->
  (exists cl args, i = Call (pd_res pd) cl args) \/ (exists cl args, i = RawCall (pd_res pd) cl args).
Proof.
  intros ge fr m i g xs pd H. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst; simpl; eauto.
Qed.

(** ## Points *)

(** Where dropping k elements of l, with k at most l's length, leaves
    nothing, k is l's length. *)
Lemma skipn_nil_length : forall (A : Type) k (l : list A), skipn k l = [] -> (k <= length l)%nat -> k = length l.
Proof.
  intros A k l H Hk. pose proof (length_skipn k l) as E. rewrite H in E. simpl in E. lia.
Qed.

(** The point k instructions into a block is at index k. *)
Lemma point_site_exec : forall f l b k j,
  find_block l (fn_blocks f) = Some b -> (k <= length (b_insts b))%nat ->
  point_site f (Exec l (skipn k (b_insts b)) j) = Some (l, Z.of_nat k).
Proof.
  intros f l b k j Hb Hk. simpl. rewrite Hb, length_skipn. f_equal. f_equal. lia.
Qed.

(** Nothing is in scope at a function's entry. *)
Lemma scope_entry : forall md f l n s i,
  checked_module md -> In (IFunc f) md -> entry_label f = Some l ->
  In (n, s, DInst i) (def_positions f) -> site_dominates (fn_doms f) l (-1) s = false.
Proof.
  intros md f l n s i Hmd Hin He Hp. destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & _ & _).
  unfold entry_label in He. rewrite Hf in He. injection He as <-.
  destruct (dinst_site _ _ _ _ Hp) as (d & j & ->).
  destruct (position_inst _ _ _ _ _ Hp) as (b & kk & _ & _ & _ & -> & _). simpl.
  destruct (name_eqb d (b_label b0)) eqn:E; [apply Z.ltb_ge; lia|].
  destruct (dominates (fn_doms f) d (b_label b0)) eqn:Ed; [|reflexivity].
  rewrite (dom_entry_top _ _ _ Hd _ Ed), name_eqb_refl in E. discriminate E.
Qed.

(** ## A single definition's relation survives a step *)

(** A replay holds of any environment e' that agrees with e on the name
    n and its single-definition operands, in any memory m' that persists
    from m. *)
Lemma replays_change : forall ge once e e' m m' n i,
  replays ge once e m n i -> lookup n e' = lookup n e ->
  (forall a, In a (inst_uses i) -> once_has once a = true -> lookup a e' = lookup a e) ->
  persists m m' -> replays ge once e' m' n i.
Proof.
  intros ge once e e' m m' n i (fr0 & m0 & e1 & l1 & m1 & Hs & Hn & Ha & Hp & Hfit) Hn' Ha' Hp'.
  exists fr0, m0, e1, l1, m1. split; [exact Hs|]. split; [congruence|].
  split; [intros a Hu Ho; rewrite (Ha' _ Hu Ho); exact (Ha _ Hu Ho)|].
  exact (conj (persists_trans _ _ _ Hp Hp') Hfit).
Qed.

(** The property rp of a name survives what [replays_change] allows: an
    environment that keeps the name and its single-definition operands,
    and a memory that persists. The scope lemmas hold of any such rp. *)
Definition moves (rp : list (name * def) -> env -> Memory.mem -> name -> inst -> Prop) : Prop :=
  forall once e e' m m' n i,
    rp once e m n i -> lookup n e' = lookup n e ->
    (forall a, In a (inst_uses i) -> once_has once a = true -> lookup a e' = lookup a e) ->
    persists m m' -> rp once e' m' n i.

(** A frame's scope of a property rp that [moves] holds in any memory m'
    that persists from m. *)
Lemma scope_with_mem : forall rp fr m m',
  moves rp -> scope_with rp fr m -> persists m m' -> scope_with rp fr m'.
Proof.
  intros rp fr m m' Hmv H Hp l k n s i Hpt Hn Hr Hpos Hsd.
  exact (Hmv _ _ _ _ _ _ _ (H _ _ _ _ _ Hpt Hn Hr Hpos Hsd) eq_refl (fun _ _ _ => eq_refl) Hp).
Qed.

(** So [scope_holds] holds in any memory that persists. *)
Lemma scope_mem : forall ge fr m m', scope_holds ge fr m -> persists m m' -> scope_holds ge fr m'.
Proof. intros ge. exact (fun fr m m' => scope_with_mem _ fr m m' (replays_change ge)). Qed.

(** The instruction i is not a [[check_ahead]], whose result a doomed
    frame holds though its check did not pass. *)
Definition ahead_free (i : inst) : bool :=
  match i with Let _ _ (CheckAhead _ _ _ _ _) _ => false | _ => true end.

(** Each single definition in scope at fr's point that is not a
    `check_ahead` replays. [[guard chain|Guard chains]], [[offset intervals]] and
    pointer distances read only such definitions. *)
Definition scope_plain (ge : genv) (fr : frame) (m : Memory.mem) : Prop :=
  scope_with (fun once e m n i => ahead_free i = true -> replays ge once e m n i) fr m.

(** A frame that holds its scope holds its plain scope. *)
Lemma scope_plain_of : forall ge fr m, scope_holds ge fr m -> scope_plain ge fr m.
Proof. intros ge fr m H l k n s i Hpt Hn Hr Hpos Hsd _. exact (H _ _ _ _ _ Hpt Hn Hr Hpos Hsd). Qed.

(** The names X defined at index k of a reachable block l change
    neither a single definition n in scope there nor its
    single-definition operands: where the environment e' differs from e
    only on X, both read the same values. This rests on
    [no_use_redefined]. *)
Lemma scope_moves : forall f b0 rest l k (X : list name) n s i (e e' : env),
  fn_blocks f = b0 :: rest -> block_intervals (b0 :: rest) = Some (fn_doms f) ->
  definitions_dominate f (fn_doms f) = true -> is_reachable (fn_doms f) l = true ->
  (forall x, In x X -> exists D, In (x, SAt l k, D) (def_positions f)) ->
  (forall a, ~ In a X -> lookup a e' = lookup a e) ->
  lookup n (single_definitions f) = Some (DInst i) -> In (n, s, DInst i) (def_positions f) ->
  site_dominates (fn_doms f) l k s = true ->
  lookup n e' = lookup n e /\
  forall a, In a (inst_uses i) -> once_has (single_definitions f) a = true -> lookup a e' = lookup a e.
Proof.
  intros f b0 rest l k X n s i e e' Hf Hd Hdd Hr HX He Hn Hp Hs. split.
  - apply He. intros Hin. destruct (HX _ Hin) as [D HD].
    destruct (once_position _ _ _ Hn) as (s0 & _ & Hu).
    destruct (Hu _ _ HD) as [E1 _]. destruct (Hu _ _ Hp) as [E2 _]. rewrite E2, <- E1 in Hs.
    simpl in Hs. rewrite name_eqb_refl, Z.ltb_irrefl in Hs. discriminate Hs.
  - intros a Hu Ho. apply He. intros Hin. destruct (HX _ Hin) as [D HD].
    destruct (dinst_site _ _ _ _ Hp) as (d & j & ->).
    exact (no_use_redefined _ _ _ _ _ _ _ _ _ _ _ D Hf Hd Hdd Hn Hp Hr Hs HD Ho Hu).
Qed.

(** An instruction defines its names at its own index. *)
Lemma inst_defs_here : forall f b k i,
  In b (fn_blocks f) -> nth_error (b_insts b) k = Some i ->
  forall x, In x (map fst (inst_temp_defs i)) -> exists D, In (x, SAt (b_label b) (Z.of_nat k), D) (def_positions f).
Proof.
  intros f b k i Hb Hk x Hx. apply in_map_iff in Hx as (dk & <- & Hdk).
  exists (DInst i). exact (inst_position _ _ _ _ _ Hb Hk Hdk).
Qed.

(** A block's phis define their names before its first instruction. *)
Lemma phi_defs_here : forall f b,
  In b (fn_blocks f) -> forall x, In x (map phi_name (b_phis b)) ->
  exists D, In (x, SAt (b_label b) (-1), D) (def_positions f).
Proof.
  intros f b Hb x Hx. apply in_map_iff in Hx as ([d k pairs] & <- & Hph).
  exists (DPhi (Phi d k pairs)). exact (phi_position _ _ _ _ _ Hb Hph).
Qed.

(** An instruction's single-definition operand is not one of the names
    it defines. *)
Lemma operand_not_defined : forall f b0 rest b k i a,
  fn_blocks f = b0 :: rest -> block_intervals (b0 :: rest) = Some (fn_doms f) ->
  definitions_dominate f (fn_doms f) = true -> In b (fn_blocks f) ->
  is_reachable (fn_doms f) (b_label b) = true -> nth_error (b_insts b) k = Some i ->
  In a (inst_uses i) -> once_has (single_definitions f) a = true -> ~ In a (map fst (inst_temp_defs i)).
Proof.
  intros f b0 rest b k i a Hf Hd Hdd Hb Hr Hk Hu Ho Hin.
  unfold once_has in Ho. destruct (lookup a (single_definitions f)) as [D|] eqn:Ea; [|discriminate Ho].
  destruct (use_dominated _ _ _ _ _ _ _ Hdd Hb Hr Hk Hu Ea) as (s & Hs & Hsd).
  destruct (inst_defs_here _ _ _ _ Hb Hk _ Hin) as [D' HD'].
  destruct (once_position _ _ _ Ea) as (s0 & _ & Hun).
  destruct (Hun _ _ Hs) as [-> _]. destruct (Hun _ _ HD') as [E _]. rewrite <- E in Hsd.
  simpl in Hsd. rewrite name_eqb_refl, Z.ltb_irrefl in Hsd. discriminate Hsd.
Qed.

(** ## Scope along a block *)

(** A [shaped] frame inside block l: its function is the module's, l is
    reachable, and its instructions are the suffix of l's block b from
    an index k, before b's jump. *)
Lemma shaped_exec : forall md fr l is j,
  shaped md fr -> fr_at fr = Exec l is j ->
  In (IFunc (fr_fn fr)) md /\ is_reachable (fn_doms (fr_fn fr)) l = true /\
  exists b k, find_block l (fn_blocks (fr_fn fr)) = Some b /\ (k <= length (b_insts b))%nat /\
    is = skipn k (b_insts b) /\ j = b_jump b.
Proof. intros md fr l is j H Ha. unfold shaped in H. cbv zeta in H. rewrite Ha in H. exact H. Qed.

(** The instruction at index k of block l is i. *)
Lemma site_inst : forall md f l b k s n i',
  checked_module md -> In (IFunc f) md -> find_block l (fn_blocks f) = Some b ->
  In (n, s, DInst i') (def_positions f) -> s = SAt l (Z.of_nat k) -> nth_error (b_insts b) k = Some i'.
Proof.
  intros md f l b k s n i' Hmd Hin Hb Hp ->.
  destruct (func_facts _ _ Hmd Hin) as (_ & _ & _ & _ & Hnd & _).
  destruct (position_inst _ _ _ _ _ Hp) as (b' & kk & Hb' & Hl & Hk & Ej & _).
  rewrite (find_block_unique _ _ _ _ Hnd Hb Hb' Hl) in Hk. apply Nat2Z.inj in Ej. subst. exact Hk.
Qed.

(** From index k to k + 1 of block l, over the instruction i at k: where
    the next frame fr' differs from fr only on i's names and memory
    persists from m to m', a scope of a property rp that [moves] holds
    at fr' if it held at fr, provided i's own name satisfies rp when i is
    replayable. *)
Lemma scope_step_with : forall rp md fr fr' m m' l b k i,
  moves rp -> checked_module md -> In (IFunc (fr_fn fr)) md -> fr_fn fr' = fr_fn fr ->
  is_reachable (fn_doms (fr_fn fr)) l = true ->
  find_block l (fn_blocks (fr_fn fr)) = Some b -> nth_error (b_insts b) k = Some i ->
  point_site (fr_fn fr) (fr_at fr) = Some (l, Z.of_nat k) ->
  point_site (fr_fn fr) (fr_at fr') = Some (l, Z.of_nat (S k)) ->
  (forall a, ~ In a (map fst (inst_temp_defs i)) -> lookup a (fr_env fr') = lookup a (fr_env fr)) ->
  persists m m' ->
  (forall n, replayable i = true -> lookup n (single_definitions (fr_fn fr)) = Some (DInst i) ->
     rp (single_definitions (fr_fn fr)) (fr_env fr') m' n i) ->
  scope_with rp fr m -> scope_with rp fr' m'.
Proof.
  intros rp md fr fr' m m' l b k i Hmv Hmd Hin Hf' Hr Hb Hk Hpt0 Hpt1 He Hp Hself Hold l' k' n s i' Hpt Hn Hrp Hpos Hsd.
  rewrite Hf' in *. rewrite Hpt1 in Hpt. injection Hpt as <- <-.
  assert (Hsd1 : site_dominates (fn_doms (fr_fn fr)) l (Z.of_nat k + 1) s = true)
    by (rewrite <- Hsd; f_equal; lia).
  clear Hsd.
  destruct (site_next _ _ _ _ Hsd1) as [Es | Hsd0].
  - pose proof (site_inst _ _ _ _ _ _ _ _ Hmd Hin Hb Hpos Es) as Hk'. rewrite Hk in Hk'. injection Hk' as <-.
    exact (Hself _ Hrp Hn).
  - destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & _ & Hdd).
    destruct (find_block_in _ _ _ Hb) as [Hbin Hl].
    assert (HX : forall x, In x (map fst (inst_temp_defs i)) ->
                   exists D, In (x, SAt l (Z.of_nat k), D) (def_positions (fr_fn fr)))
      by (intros x Hx; rewrite <- Hl; exact (inst_defs_here _ _ _ _ Hbin Hk _ Hx)).
    destruct (scope_moves _ _ _ _ _ _ _ _ _ _ _ Hf Hd Hdd Hr HX He Hn Hpos Hsd0) as [Hn' Ha'].
    exact (Hmv _ _ _ _ _ _ _ (Hold _ _ _ _ _ Hpt0 Hn Hrp Hpos Hsd0) Hn' Ha' Hp).
Qed.

(** [scope_step_with] for [replays]: the step lemma of [scope_holds]. *)
Lemma scope_step : forall ge md fr fr' m m' l b k i,
  checked_module md -> In (IFunc (fr_fn fr)) md -> fr_fn fr' = fr_fn fr ->
  is_reachable (fn_doms (fr_fn fr)) l = true ->
  find_block l (fn_blocks (fr_fn fr)) = Some b -> nth_error (b_insts b) k = Some i ->
  point_site (fr_fn fr) (fr_at fr) = Some (l, Z.of_nat k) ->
  point_site (fr_fn fr) (fr_at fr') = Some (l, Z.of_nat (S k)) ->
  (forall a, ~ In a (map fst (inst_temp_defs i)) -> lookup a (fr_env fr') = lookup a (fr_env fr)) ->
  persists m m' ->
  (forall n, replayable i = true -> lookup n (single_definitions (fr_fn fr)) = Some (DInst i) ->
     replays ge (single_definitions (fr_fn fr)) (fr_env fr') m' n i) ->
  scope_holds ge fr m -> scope_holds ge fr' m'.
Proof.
  intros ge md fr fr' m m' l b k i. exact (scope_step_with (replays ge) md fr fr' m m' l b k i (replays_change ge)).
Qed.

(** Just after the instruction i at index k, whose own names do not
    replay (a call, an allocation), a frame whose environment changed
    only on i's names keeps the scope it had there, in a memory that
    persists. *)
Lemma scope_after : forall ge md fr fr' m m' l b k i,
  checked_module md -> In (IFunc (fr_fn fr)) md -> fr_fn fr' = fr_fn fr -> fr_at fr' = fr_at fr ->
  is_reachable (fn_doms (fr_fn fr)) l = true ->
  find_block l (fn_blocks (fr_fn fr)) = Some b -> nth_error (b_insts b) k = Some i -> replayable i = false ->
  point_site (fr_fn fr) (fr_at fr) = Some (l, Z.of_nat (S k)) ->
  (forall a, ~ In a (map fst (inst_temp_defs i)) -> lookup a (fr_env fr') = lookup a (fr_env fr)) ->
  persists m m' -> scope_holds ge fr m -> scope_holds ge fr' m'.
Proof.
  intros ge md fr fr' m m' l b k i Hmd Hin Hf' Ha' Hr Hb Hk Hrp Hpt0 He Hp Hold l' k' n s i' Hpt Hn Hrp' Hpos Hsd.
  rewrite Hf' in *. rewrite Ha', Hpt0 in Hpt. injection Hpt as <- <-.
  assert (Hsd1 : site_dominates (fn_doms (fr_fn fr)) l (Z.of_nat k + 1) s = true)
    by (rewrite <- Hsd; f_equal; lia).
  destruct (site_next _ _ _ _ Hsd1) as [Es | Hsd0].
  - pose proof (site_inst _ _ _ _ _ _ _ _ Hmd Hin Hb Hpos Es) as Hk'. rewrite Hk in Hk'.
    injection Hk' as <-. rewrite Hrp in Hrp'. discriminate Hrp'.
  - destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & _ & Hdd).
    destruct (find_block_in _ _ _ Hb) as [Hbin Hl].
    assert (HX : forall x, In x (map fst (inst_temp_defs i)) ->
                   exists D, In (x, SAt l (Z.of_nat k), D) (def_positions (fr_fn fr)))
      by (intros x Hx; rewrite <- Hl; exact (inst_defs_here _ _ _ _ Hbin Hk _ Hx)).
    destruct (scope_moves _ _ _ _ _ _ _ _ _ _ _ Hf Hd Hdd Hr HX He Hn Hpos Hsd0) as [Hn' Ha''].
    exact (replays_change _ _ _ _ _ _ _ _ (Hold _ _ _ _ _ Hpt0 Hn Hrp' Hpos Hsd) Hn' Ha'' Hp).
Qed.

(** ## Frames a step makes *)

(** What a jump can take is among the block's successors. *)
Lemma target_succ : forall j t, In t (jump_targets j) -> In (edge_label t) (jump_succs j).
Proof. intros j t H. destruct j; simpl in *; intuition (subst; simpl; auto). Qed.

(** A call's new frame is not doomed, at its function's entry. *)
Lemma call_frame_entry : forall g xs fr,
  call_frame g xs = Some fr -> fr_fn fr = g /\ fr_doomed fr = None /\
  exists l, entry_label g = Some l /\ (fr_at fr = Enter l None \/ exists ys, fr_at fr = Snapshot ys l).
Proof.
  intros g xs fr H. unfold call_frame in H.
  destruct (length xs <? length (fn_params g))%nat; [discriminate H|].
  unfold entry_label. destruct (fn_blocks g) as [|b bs]; [discriminate H|]. injection H as <-. simpl.
  split; [reflexivity|]. split; [reflexivity|]. exists (b_label b). split; [reflexivity|].
  destruct (variadic_func g); eauto.
Qed.

(** A frame at its function's entry, entered or about to take its
    [[snapshot]], is [shaped], with nothing in scope. *)
Lemma at_entry : forall ge md fr m l,
  checked_module md -> In (IFunc (fr_fn fr)) md -> entry_label (fr_fn fr) = Some l ->
  (fr_at fr = Enter l None \/ exists ys, fr_at fr = Snapshot ys l) ->
  shaped md fr /\ scope_holds ge fr m.
Proof.
  intros ge md fr m l Hmd Hin He Ha.
  destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & _ & _).
  assert (Hr : is_reachable (fn_doms (fr_fn fr)) l = true).
  { unfold entry_label in He. rewrite Hf in He. injection He as <-. exact (dom_entry _ _ _ Hd). }
  split.
  - unfold shaped. cbv zeta. split; [exact Hin|].
    destruct Ha as [Ha | (ys & Ha)]; rewrite Ha; [split; [exact Hr | intros _; exact He] | exact He].
  - intros l' k n s i Hpt Hn Hrp Hpos Hsd.
    destruct Ha as [Ha | (ys & Ha)]; rewrite Ha in Hpt; simpl in Hpt; [|discriminate Hpt].
    injection Hpt as <- <-. rewrite (scope_entry _ _ _ _ _ _ Hmd Hin He Hpos) in Hsd. discriminate Hsd.
Qed.

(** A return resumes the waiting caller at its point, with the call's
    result in its environment. *)
Lemma return_step_env : forall c o c',
  return_step c o = Next c' ->
  exists caller pd callers o' e,
    c_callers c = (caller, pd) :: callers /\ returned_env (pd_res pd) o' (fr_env caller) = Some e /\
    c' = mkConfig (mkFrame (fr_fn caller) e (fr_locals caller) (fr_doomed caller) (fr_at caller))
                  callers (c_mem c') (c_fuel c).
Proof.
  unfold return_step. intros c o c' H. apply or_stuck_next in H.
  destruct (invalidate_locals _ _) as [m|]; [|discriminate H].
  destruct (c_callers c) as [|[caller pd] callers]; [discriminate H|].
  destruct (match pd_conv pd with None => Some o | Some (cw, kw) => converted_outcome cw kw o end) as [o'|];
    [|discriminate H].
  destruct (returned_env _ _ _) as [e|] eqn:Ee; [|discriminate H]. injection H as <-. simpl. eauto 10.
Qed.

(** A caller that [waits] resumes with its scope, in a memory that
    persists, the call's result names being the only ones that
    changed. *)
Lemma scope_return : forall ge md fr e m m' pd,
  checked_module md -> shaped md fr -> waits fr pd ->
  (forall a, ~ In a (result_names (pd_res pd)) -> lookup a e = lookup a (fr_env fr)) ->
  persists m m' -> scope_holds ge fr m ->
  scope_holds ge (mkFrame (fr_fn fr) e (fr_locals fr) (fr_doomed fr) (fr_at fr)) m'.
Proof.
  intros ge md fr e m m' pd Hmd Hsh (l & rest & j & b & k & ci & Ha & Hb & Hk & Hrest & Hci) He Hp Hold.
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh. destruct Hsh as (Hin & Hr & _).
  assert (Hlen : (S k <= length (b_insts b))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
  refine (scope_after _ _ fr (mkFrame (fr_fn fr) e (fr_locals fr) (fr_doomed fr) (fr_at fr)) _ _ _ _ _ ci Hmd Hin eq_refl eq_refl Hr Hb Hk _ _ _ Hp Hold).
  - destruct Hci as [(cl & args & ->) | (cl & args & ->)]; reflexivity.
  - rewrite Ha, Hrest. exact (point_site_exec _ _ _ _ _ Hb Hlen).
  - simpl. destruct Hci as [(cl & args & ->) | (cl & args & ->)]; [rewrite call_defs | rewrite raw_call_defs];
      exact He.
Qed.

(** Waiting callers keep their scope in a memory that persists. *)
Lemma callers_mem : forall ge md cs m m',
  Forall (waiting ge md m) cs -> persists m m' -> Forall (waiting ge md m') cs.
Proof.
  intros ge md cs m m' H Hp. eapply Forall_impl; [|exact H].
  intros fp (Hs & Hd & Hw & Hsc). exact (conj Hs (conj Hd (conj Hw (scope_mem _ _ _ _ Hsc Hp)))).
Qed.

(** The running frame keeps its scope in a memory that persists. *)
Lemma running_mem : forall ge md fr m m', running ge md m fr -> persists m m' -> running ge md m' fr.
Proof.
  intros ge md fr m m' [Hs Hsc] Hp. split; [exact Hs|].
  destruct Hsc as [Hd | Hsc]; [left; exact Hd | right; exact (scope_mem _ _ _ _ Hsc Hp)].
Qed.

(** After an instruction, the frame is doomed, or it was not doomed and
    the instruction's result is its own. *)
Lemma doomed_cases : forall ge fr m i out od,
  doomed_result ge fr m i out = Some od ->
  snd od <> None \/ (fr_doomed fr = None /\ od = (out, None)).
Proof.
  intros ge fr m i out od H. destruct (fr_doomed fr) as [w|] eqn:Ew.
  - left. assert (Hnd : fr_doomed fr <> None) by (rewrite Ew; discriminate).
    exact (proj1 (doomed_result_doomed _ _ _ _ _ _ Hnd H)).
  - destruct (doomed_result_fresh _ _ _ _ _ _ Ew H) as [-> | (e & w & ->)]; [right; auto | left; simpl; discriminate].
Qed.

(** ## Every step keeps the invariant *)

(** The invariant over the runs of [Machine] R, for any [[runtime]]
    R. *)
Module Single (R : Runtime).

Module ID := Identity R.
Module I := Invariant R.
Import ID.
Import RM.

(** A [[snapshot]] step keeps [sinv]: it enters the entry block, where
    nothing is in scope. *)
Lemma next_sinv_snapshot : forall ge md c c' xs l,
  checked_module md -> fr_at (c_frame c) = Snapshot xs l -> step ge c = Next c' ->
  persists (c_mem c) (c_mem c') -> sinv ge md c -> sinv ge md c'.
Proof.
  intros ge md c c' xs l Hmd Ha Hs Hp [[Hsh _] Hcall].
  destruct (step_snapshot _ _ _ _ _ Ha Hs) as (Hc & Hf & _ & _ & Ha').
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh. destruct Hsh as [Hin He].
  rewrite <- Hf in Hin, He.
  destruct (at_entry ge _ _ (c_mem c') _ Hmd Hin He (or_introl Ha')) as [Hsh' Hsc'].
  split; [split; [exact Hsh' | right; exact Hsc'] | rewrite Hc; exact (callers_mem _ _ _ _ _ Hcall Hp)].
Qed.

(** Entering a block keeps [sinv]: its phis define their names at index
    -1, and its first instruction is at index 0. *)
Lemma next_sinv_enter : forall ge md c c' l from,
  checked_module md -> fr_at (c_frame c) = Enter l from -> step ge c = Next c' ->
  persists (c_mem c) (c_mem c') -> sinv ge md c -> sinv ge md c'.
Proof.
  intros ge md c c' l from Hmd Ha Hs Hp [[Hsh Hsc] Hcall].
  destruct (step_enter _ _ _ _ _ Ha Hs) as (b & e & Hb & Hphi & ->). simpl in Hp |- *.
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh. destruct Hsh as (Hin & Hr & _).
  split; [|exact (callers_mem _ _ _ _ _ Hcall Hp)]. split.
  - unfold shaped. cbv zeta. simpl. split; [exact Hin|]. split; [exact Hr|].
    exists b, O. split; [exact Hb|]. split; [lia | split; reflexivity].
  - destruct Hsc as [Hd | Hsc]; [left; exact Hd | right].
    destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & _ & Hdd).
    destruct (find_block_in _ _ _ Hb) as [Hbin Hl].
    intros l' k n s i Hpt Hn Hrp Hpos Hsd. simpl in Hpt. rewrite Hb in Hpt.
    injection Hpt as <- <-. rewrite Nat.sub_diag in Hsd.
    pose proof (site_first _ _ _ _ _ _ Hpos Hsd) as Hsd0.
    assert (HX : forall x, In x (map phi_name (b_phis b)) ->
                   exists D, In (x, SAt l (-1), D) (def_positions (fr_fn (c_frame c))))
      by (rewrite <- Hl; exact (phi_defs_here _ _ Hbin)).
    destruct (scope_moves _ _ _ _ _ _ _ _ _ _ _ Hf Hd Hdd Hr HX
                (fun a Ha => phis_env_other _ _ _ _ _ _ Hphi Ha) Hn Hpos Hsd0) as [Hn' Ha'].
    exact (replays_change _ _ _ _ _ _ _ _
             (Hsc l (-1) n s i ltac:(rewrite Ha; reflexivity) Hn Hrp Hpos Hsd0) Hn' Ha' Hp).
Qed.

(** A jump keeps [sinv]: it takes an edge, to the entry of a block whose
    dominators dominated the jump ([site_edge]); or it returns to a
    waiting caller, which resumes with its scope ([scope_return]). *)
Lemma next_sinv_jump : forall ge md c c' l j,
  checked_module md -> fr_at (c_frame c) = Exec l [] j -> step ge c = Next c' ->
  persists (c_mem c) (c_mem c') -> sinv ge md c -> sinv ge md c'.
Proof.
  intros ge md c c' l j Hmd Ha Hs Hp [[Hsh Hsc] Hcall].
  pose proof Hs as Hs0. unfold step in Hs. rewrite Ha in Hs.
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh.
  destruct Hsh as (Hin & Hr & b & k & Hb & Hk & Hnil & Hj).
  destruct (func_facts _ _ Hmd Hin) as (b0 & rest & Hf & Hd & Hnd & Hdd).
  destruct (find_block_in _ _ _ Hb) as [Hbin Hl]. subst l.
  pose proof (skipn_nil_length _ _ _ (eq_sym Hnil) Hk) as Hkl.
  destruct (I.jump_step_next _ _ _ _ _ Hs) as [(t & Ht & ->) | (Hdn & o & Hret)].
  - simpl in Hp |- *.
    assert (Hsucc : In (edge_label t) (jump_succs (b_jump b)))
      by (rewrite <- Hj; exact (target_succ _ _ (I.taken_target_in _ _ _ _ Ht))).
    assert (He : edge (b0 :: rest) (b_label b) (edge_label t))
      by (exists b; rewrite <- Hf; repeat split; assumption).
    split; [|exact (callers_mem _ _ _ _ _ Hcall Hp)]. split.
    + unfold shaped. cbv zeta. simpl. split; [exact Hin|]. split; [|discriminate].
      rewrite Hf in Hnd. exact (dom_closed _ _ _ Hd _ _ Hnd Hr He).
    + destruct Hsc as [Hdm | Hsc]; [left; exact Hdm | right].
      intros l' k' n s i Hpt Hn Hrp Hpos Hsd. simpl in Hpt. injection Hpt as <- <-.
      pose proof (site_edge _ _ _ _ _ _ _ _ _ Hf Hd Hnd Hb Hr Hsucc Hpos Hsd) as Hsd0.
      refine (replays_change _ _ _ _ _ _ _ _ (Hsc _ _ _ _ _ _ Hn Hrp Hpos Hsd0) eq_refl (fun _ _ _ => eq_refl) Hp).
      rewrite Ha, Hnil, Hkl. exact (point_site_exec _ _ _ _ _ Hb (le_n _)).
  - destruct (return_step_env _ _ _ Hret) as (caller & pd & callers & o' & e & Hcs & Hre & ->).
    rewrite Hcs in Hcall. inversion Hcall as [|fp fps Hw Hrest]; subst. simpl in Hp |- *.
    destruct Hw as (Hshc & Hdc & Hwt & Hscc).
    split; [|exact (callers_mem _ _ _ _ _ Hrest Hp)].
    split; [exact Hshc | right].
    exact (scope_return _ _ _ _ _ _ _ Hmd Hshc Hwt (fun a Ha => returned_env_other _ _ _ _ _ Hre Ha) Hp Hscc).
Qed.

(** An instruction keeps [sinv]: it continues, and its own name replays
    from where it ran; or it calls, the callee starting with nothing in
    scope and the caller waiting. *)
Lemma next_sinv_inst : forall ge md c c' l i rest j,
  ge_module ge = md -> checked_module md -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  step ge c = Next c' -> persists (c_mem c) (c_mem c') -> objects_fit (m_regions (c_mem c')) ->
  sinv ge md c -> sinv ge md c'.
Proof.
  intros ge md c c' l i rest j Hge Hmd Ha Hs Hp Hfit [[Hsh Hsc] Hcall].
  destruct (step_exec_cons _ _ _ _ _ _ _ Ha Hs ltac:(discriminate) ltac:(discriminate))
    as (Hdoom & out0 & od & Hi & Hdr & Hn).
  unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh.
  destruct Hsh as (Hin & Hr & b & k & Hb & Hk & Hsk & Hj).
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hsk)) as (Hki & Hrest & Hlen).
  assert (Hpt0 : point_site (fr_fn (c_frame c)) (fr_at (c_frame c)) = Some (l, Z.of_nat k))
    by (rewrite Ha, Hsk; exact (point_site_exec _ _ _ _ _ Hb Hk)).
  assert (Hpt1 : point_site (fr_fn (c_frame c)) (Exec l rest j) = Some (l, Z.of_nat (S k)))
    by (rewrite <- Hrest; exact (point_site_exec _ _ _ _ _ Hb Hlen)).
  assert (Hsh1 : forall e1 l1 d, shaped md (mkFrame (fr_fn (c_frame c)) e1 l1 d (Exec l rest j))).
  { intros e1 l1 d. unfold shaped. cbv zeta. simpl. split; [exact Hin|]. split; [exact Hr|].
    exists b, (S k). split; [exact Hb|]. split; [exact Hlen|]. split; [symmetry; exact Hrest | exact Hj]. }
  destruct (inst_next_next _ _ _ _ _ _ _ Hn) as [(e1 & l1 & m1 & Ho & ->) | (g & xs & pd & callee & Ho & Hcf & ->)];
    simpl in Hp |- *.
  - split; [|exact (callers_mem _ _ _ _ _ Hcall Hp)]. split; [apply Hsh1|].
    destruct (doomed_cases _ _ _ _ _ _ Hdr) as [Hdn | (Hfd & ->)]; [left; exact Hdn | right].
    simpl in Ho |- *. subst out0. destruct Hsc as [Hdm | Hsc]; [contradiction|].
    destruct (func_facts _ _ Hmd Hin) as (b0 & rs & Hf & Hd & _ & Hdd).
    destruct (find_block_in _ _ _ Hb) as [Hbin Hl].
    refine (scope_step _ _ (c_frame c) (mkFrame (fr_fn (c_frame c)) e1 l1 None (Exec l rest j)) _ _ _ _ _ i
              Hmd Hin eq_refl Hr Hb Hki Hpt0 Hpt1 (inst_step_env _ _ _ _ _ _ _ Hi) Hp _ Hsc).
    intros n Hrp Hn1. exists (c_frame c), (c_mem c), e1, l1, m1.
    split; [exact Hi|]. split; [reflexivity|]. split; [|exact (conj (persists_refl _) Hfit)].
    intros a Hu Ho1. symmetry. apply (inst_step_env _ _ _ _ _ _ _ Hi).
    rewrite <- Hl in Hr. exact (operand_not_defined _ _ _ _ _ _ _ Hf Hd Hdd Hbin Hr Hki Hu Ho1).
  - assert (Hd : fr_doomed (c_frame c) = None /\ out0 = ICall g xs pd /\ snd od = None).
    { destruct (doomed_cases _ _ _ _ _ _ Hdr) as [Hdn | (Hfd & ->)]; [exfalso | auto].
      destruct (fr_doomed (c_frame c)) as [w|] eqn:Ew.
      - assert (Hnd : fr_doomed (c_frame c) <> None) by (rewrite Ew; discriminate).
        destruct (doomed_result_doomed _ _ _ _ _ _ Hnd Hdr) as (_ & [Ho' | [(e' & Ho') | (o' & Ho')]]);
          rewrite Ho in Ho'; try discriminate Ho'.
        subst out0. destruct (inst_step_call_shape _ _ _ _ _ _ _ Hi) as (_ & [(r & cl & args & ->) | (r & cl & args & ->)]);
          destruct Hdoom as [Hdoom | Hdoom]; simpl in Hdoom; discriminate Hdoom.
      - destruct (doomed_result_fresh _ _ _ _ _ _ Ew Hdr) as [-> | (e' & w & ->)];
          [exact (Hdn eq_refl) | discriminate Ho]. }
    destruct Hd as (Hfd & -> & Hsd). rewrite Hsd.
    destruct (inst_step_call_shape _ _ _ _ _ _ _ Hi) as (Hg & _). rewrite Hge in Hg.
    destruct (call_frame_entry _ _ _ Hcf) as (Hfg & _ & le & He & Hat).
    rewrite <- Hfg in Hg, He.
    destruct (at_entry ge md callee (c_mem c) le Hmd Hg He Hat) as [Hsh' Hsc'].
    split; [split; [exact Hsh' | right; exact Hsc']|].
    destruct Hsc as [Hdm | Hsc]; [contradiction|].
    pose proof (inst_step_call_pending _ _ _ _ _ _ _ Hi) as Hpd.
    constructor; [|exact Hcall].
    split; [apply Hsh1|]. split; [reflexivity|]. split.
    + exists l, rest, j, b, k, i. simpl.
      split; [reflexivity|]. split; [exact Hb|]. split; [exact Hki|]. split; [symmetry; exact Hrest | exact Hpd].
    + refine (scope_step _ _ (c_frame c)
                (mkFrame (fr_fn (c_frame c)) (fr_env (c_frame c)) (fr_locals (c_frame c)) None (Exec l rest j))
                _ _ _ _ _ i Hmd Hin eq_refl Hr Hb Hki Hpt0 Hpt1
                (fun a _ => eq_refl) (persists_refl _) _ Hsc).
      intros n Hrp. destruct Hpd as [(cl & args & ->) | (cl & args & ->)]; discriminate Hrp.
Qed.

(** A step that allocates nothing keeps [sinv], where memory persists
    across it and fits the address space after it. *)
Lemma next_sinv : forall ge md c c',
  ge_module ge = md -> checked_module md -> step ge c = Next c' ->
  persists (c_mem c) (c_mem c') -> objects_fit (m_regions (c_mem c')) -> sinv ge md c -> sinv ge md c'.
Proof.
  intros ge md c c' Hge Hmd Hs Hp Hfit H.
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - exact (next_sinv_snapshot _ _ _ _ _ _ Hmd Ha Hs Hp H).
  - exact (next_sinv_enter _ _ _ _ _ _ Hmd Ha Hs Hp H).
  - exact (next_sinv_jump _ _ _ _ _ _ Hmd Ha Hs Hp H).
  - exact (next_sinv_inst _ _ _ _ _ _ _ _ Hge Hmd Ha Hs Hp Hfit H).
Qed.

(** An allocation keeps [sinv]: it defines names that do not replay, and
    memory persists across it. *)
Lemma fresh_sinv : forall ge md c q k base,
  checked_module md -> step ge c = Fresh q k -> persists (c_mem c) (c_mem (k base)) ->
  sinv ge md c -> sinv ge md (k base).
Proof.
  intros ge md c q k base Hmd Hs Hp [[Hsh Hsc] Hcall].
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - destruct (step_snapshot_fresh _ _ _ _ _ _ Ha Hs base) as (Hc & Hf & _ & _ & Ha').
    unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh. destruct Hsh as [Hin He].
    rewrite <- Hf in Hin, He.
    destruct (at_entry ge _ _ (c_mem (k base)) _ Hmd Hin He (or_introl Ha')) as [Hsh' Hsc'].
    split; [split; [exact Hsh' | right; exact Hsc'] | rewrite Hc; exact (callers_mem _ _ _ _ _ Hcall Hp)].
  - exfalso. exact (step_enter_fresh _ _ _ _ _ _ Ha Hs).
  - exfalso. unfold step in Hs. rewrite Ha in Hs. exact (jump_step_not_fresh _ _ _ _ _ _ Hs).
  - destruct (step_exec_cons _ _ _ _ _ _ _ Ha Hs ltac:(discriminate) ltac:(discriminate))
      as (_ & out0 & od & Hi & Hdr & Hn).
    destruct (inst_next_fresh _ _ _ _ _ _ _ _ Hn) as (k0 & Ho & Hk).
    unfold shaped in Hsh. cbv zeta in Hsh. rewrite Ha in Hsh.
    destruct Hsh as (Hin & Hr & b & ix & Hb & Hix & Hsk & Hj).
    destruct (skipn_cons _ _ _ _ _ (eq_sym Hsk)) as (Hki & Hrest & Hlen).
    rewrite Hk in Hp |- *. destruct (k0 base) as [[e locals] m'] eqn:Ek. simpl in Hp |- *.
    split; [|exact (callers_mem _ _ _ _ _ Hcall Hp)]. split.
    { unfold shaped. cbv zeta. simpl. split; [exact Hin|]. split; [exact Hr|].
      exists b, (S ix). split; [exact Hb|]. split; [exact Hlen|]. split; [symmetry; exact Hrest | exact Hj]. }
    destruct (doomed_cases _ _ _ _ _ _ Hdr) as [Hdn | (Hfd & ->)]; [left; exact Hdn | right].
    simpl in Ho |- *. subst out0. destruct Hsc as [Hdm | Hsc]; [contradiction|].
    pose proof (inst_step_fresh_env _ _ _ _ _ _ Hi base) as He. rewrite Ek in He. simpl in He.
    assert (Hpt0 : point_site (fr_fn (c_frame c)) (fr_at (c_frame c)) = Some (l, Z.of_nat ix))
      by (rewrite Ha, Hsk; exact (point_site_exec _ _ _ _ _ Hb Hix)).
    assert (Hpt1 : point_site (fr_fn (c_frame c)) (Exec l rest j) = Some (l, Z.of_nat (S ix)))
      by (rewrite <- Hrest; exact (point_site_exec _ _ _ _ _ Hb Hlen)).
    refine (scope_step _ _ (c_frame c) (mkFrame (fr_fn (c_frame c)) e locals None (Exec l rest j)) _ _ _ _ _ i
              Hmd Hin eq_refl Hr Hb Hki Hpt0 Hpt1 He Hp _ Hsc).
    intros n Hrp. destruct (inst_step_fresh_shape _ _ _ _ _ _ Hi) as [(d & cl & al & args & -> & _) | (x & size & -> & _)];
      discriminate Hrp.
Qed.

(** The runtime's action at a [[safepoint]] keeps [sinv]: it changes only
    the memory, which persists. *)
Lemma mem_sinv : forall ge md c m', persists (c_mem c) m' -> sinv ge md c -> sinv ge md (with_mem c m').
Proof.
  intros ge md c m' Hp [Hrun Hcall].
  exact (conj (running_mem _ _ _ _ _ Hrun Hp) (callers_mem _ _ _ _ _ Hcall Hp)).
Qed.

(** Every machine step from a [[ready]] state keeps [sinv], where the
    genv's free is R's, so keeps identities ([mstep_persists]). *)
Theorem mstep_sinv : forall ge md st st',
  ge_module ge = md -> checked_module md -> ge_free ge = R.free ->
  ready_state st -> mstep ge st st' -> sinv ge md (fst st) -> sinv ge md (fst st').
Proof.
  intros ge md st st' Hge Hmd Hfree Hr Hs H.
  pose proof (mstep_persists _ _ _ Hfree Hr Hs) as Hp.
  pose proof (R.address_space _ _ (mstep_ready _ _ _ Hfree Hs Hr)) as Hfit.
  destruct Hs as [c c' s E | c q k s base s' E He Hal | c s s' m' Hd Hact]; simpl in *.
  - exact (next_sinv _ _ _ _ Hge Hmd E Hp Hfit H).
  - exact (fresh_sinv _ _ _ _ _ base Hmd E Hp H).
  - exact (mem_sinv _ _ _ _ Hp H).
Qed.

(** From a ready start where it holds, [sinv] holds in every state a run
    reaches. *)
Theorem mreachable_sinv : forall ge md st st',
  ge_module ge = md -> checked_module md -> ge_free ge = R.free ->
  mreachable ge st st' -> ready_state st -> sinv ge md (fst st) -> sinv ge md (fst st').
Proof.
  intros ge md st st' Hge Hmd Hfree H.
  induction H as [st st' Hs | st | st1 st2 st3 H12 IH1 H23 IH2]; intros Hr Hi; auto.
  - eapply mstep_sinv; eauto.
  - apply IH2; [exact (mreachable_ready _ _ _ Hfree H12 Hr) | exact (IH1 Hr Hi)].
Qed.

(** [sinv] holds where a run starts: at the entry of a checked module's
    function, with no caller. *)
Lemma start_sinv : forall ge md f xs fr m fuel,
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> sinv ge md (mkConfig fr [] m fuel).
Proof.
  intros ge md f xs fr m fuel Hmd Hin Hc.
  destruct (call_frame_entry _ _ _ Hc) as (Hf & _ & l & He & Ha). rewrite <- Hf in Hin, He.
  destruct (at_entry ge md fr m l Hmd Hin He Ha) as [Hsh Hsc].
  split; [split; [exact Hsh | right; exact Hsc] | constructor].
Qed.

(** In every state of a run of a checked module's function that starts
    ready, [sinv] holds. *)
Corollary run_sinv : forall ge md f xs fr m fuel s0 st,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  mreachable ge (mkConfig fr [] m fuel, s0) st -> sinv ge md (fst st).
Proof.
  intros ge md f xs fr m fuel s0 st Hmd Hge Hfree Hin Hcf H0 Hreach.
  exact (mreachable_sinv _ _ _ _ Hge Hmd Hfree Hreach H0 (start_sinv _ _ _ _ _ _ _ Hmd Hin Hcf)).
Qed.

End Single.

(** ## The interpreter's runtime *)

(** The same for the interpreter's runtime. *)
Module InterpSingle := Single InterpRuntime.

(** Under the interpreter's runtime, whose free keeps identities, [sinv]
    needs no hypothesis but a ready start. *)
Corollary interp_sinv : forall md globals f xs fr m fuel s0 st,
  let ge := mkGenv md globals InterpRuntime.free in
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpSingle.ID.RM.mreachable ge (mkConfig fr [] m fuel, s0) st -> sinv ge md (fst st).
Proof.
  intros md globals f xs fr m fuel s0 st ge Hmd Hin Hcf H0 Hreach.
  exact (InterpSingle.run_sinv ge md f xs fr m fuel s0 st Hmd eq_refl eq_refl Hin Hcf H0 Hreach).
Qed.
