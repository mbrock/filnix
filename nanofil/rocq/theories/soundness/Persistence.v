(** Checking that pointer bounds hold at a single instruction is not
    enough for whole-program safety. We must also know that those
    bounds remain valid as execution moves across instructions, basic
    blocks, function calls, allocations, and garbage-collector
    safepoints.

    Single-step soundness only checks one instruction or edge in
    isolation. This module lifts that guarantee across whole execution
    runs by showing that every reachable state preserves the run-level
    invariant. As a result, no undoomed frame ever executes a raw access
    or raw call to an [[unchecked]] outcome outside the [[renew_hull]]
    case closed in [Chain](Chain.v).

    ## Decisions

    The evidence pass sometimes fuses a pointer check and its memory
    access into one step, so its position does not match the instruction
    counter one-to-one. Instead of indexing by program counter, the
    invariant relates the remaining instruction list to the pass with
    [walks] and [at_pos].

    When an ahead-of-bounds check fails early, execution continues only
    until the frame traps before any later memory access. Because that
    frame is already bound to fail, it carries no live pointer evidence.

    Garbage collection safepoints never free live objects, so every
    runtime satisfies [spares] via [spares_any] without an extra theorem
    hypothesis. Signal handlers are excluded from safepoints because a
    handler could free a checked object mid-store, so handlers must not
    free objects whose checks are in flight.

    Deallocating memory with `c: free` relies on runtime metadata checks
    rather than compiler-inserted bounds evidence.
    [Soundness](Soundness.v) proves `c: free` safe directly from
    [free_checked], so this module makes no separate claim for it. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Coverage Evidence Walk Steps Invariant.
Import ListNotations.
Open Scope Z_scope.

(** ## Every step keeps the invariant

    To prove that [inv] holds across an entire program execution, we
    first show that every individual transition of [Machine] R preserves
    it. One small subcase arises when a raw memory access relies on a
    pointer fact whose base only holds modulo a hull check, which
    [Chain](Chain.v) discharges separately. *)

(** A memory access can reuse an earlier check even when the pointer was
    offset inside a larger hull, as long as the base pointer's
    definition dominates the access. Predicate [hull_case] records that
    obligation so [Chain](Chain.v) can discharge it. *)
Definition hull_case (ge : genv) (md : module) (c : config) (l : name) (i : inst) (rest : list inst)
  : Prop :=
  let f := fr_fn (c_frame c) in
  exists b k live fa q,
    find_block l (fn_blocks f) = Some b /\ i :: rest = skipn k (b_insts b) /\
    facts_hold ge (c_mem c) (fr_env (c_frame c)) live /\ live_dom f l k live /\
    fact_of q live = Some fa /\ hull_covered i q (f_p fa) (f_lo fa) (f_al fa) live (s_once (fn_src md f)) = true.

(** Functor [Persistence] proves invariant preservation and access
    safety across all runs of [Machine] R for any concrete [[runtime]]
    R. *)
Module Persistence (R : Runtime).

Module I := Invariant R.
Import I.
Import RM.

(** ### Each step keeps the invariant

    Each transition of [Machine] R falls into one of three categories:
    non-allocating program steps, object allocations, and runtime
    safepoints. The lemmas below verify each case in turn and combine
    them into the inductive preservation theorem [mreachable_inv]. *)

(** Allocating the named local x at a base above 0 keeps every local
    above 0 ([locals_pos]). *)
Lemma locals_pos_put : forall fr x base,
  locals_pos fr -> 0 < base ->
  forall fr', fr_locals fr' = put x (Some base) (fr_locals fr) -> locals_pos fr'.
Proof.
  intros fr x base Hpos Hb fr' Hl y b H. rewrite Hl, lookup_put in H.
  destruct (name_eqb y x); [injection H as <-; exact Hb | exact (Hpos _ _ H)].
Qed.

(** A [[doomed]] frame may only execute [[ahead-transparent]]
    instructions before it traps, and a function call is never
    ahead-transparent. *)
Lemma ahead_call : forall r callee args, ahead_transparent (Call r callee args) = false.
Proof. reflexivity. Qed.

(** A raw function call can jump to arbitrary code and cannot be skipped
    safely when a frame is already failing. Like a direct call, it is
    not [[ahead-transparent]]. *)
Lemma ahead_raw_call : forall r callee args, ahead_transparent (RawCall r callee args) = false.
Proof. reflexivity. Qed.

(** When a variadic C function takes a [[snapshot]] of zero extra
    arguments, execution enters its first basic block without allocating
    memory. That transition leaves the call stack and locals intact and
    preserves [inv]. *)
Lemma next_inv_snapshot : forall ge md c c' s xs l,
  ge_module ge = md -> checked_module md -> ready_state (c, s) ->
  fr_at (c_frame c) = Snapshot xs l -> step ge c = Next c' -> inv ge md (c, s) -> inv ge md (c', s).
Proof.
  intros ge md c c' s xs l Hge Hmd Hr Ha Hs [(Hin & Hpos & Hpt) Hcall]. unfold inv. simpl in *.
  destruct (step_snapshot _ _ _ _ _ Ha Hs) as (Hc & Hf & Hl & Hd & Ha').
  rewrite Hc. split; [|exact Hcall]. split; [rewrite Hf; exact Hin|].
  split; [intros x b Hx; rewrite Hl in Hx; exact (Hpos _ _ Hx)|].
  destruct Hpt as [Hd0 | Hp]; [left; rewrite Hd; exact Hd0 | right].
  eapply point_ok_entry; [exact Hp | left; exact Ha | exact Hf | exact Ha'].
Qed.

(** Entering a block keeps [inv] ([enter_point_ok]). *)
Lemma next_inv_enter : forall ge md c c' s l from,
  ge_module ge = md -> checked_module md -> ready_state (c, s) ->
  fr_at (c_frame c) = Enter l from -> step ge c = Next c' -> inv ge md (c, s) -> inv ge md (c', s).
Proof.
  intros ge md c c' s l from Hge Hmd Hr Ha Hs [(Hin & Hpos & Hpt) Hcall]. unfold inv. simpl in *.
  pose proof (enter_point_ok _ _ _ _ _ _ Hmd Hin Ha Hs) as Hep.
  destruct (step_enter _ _ _ _ _ Ha Hs) as (b & e & _ & _ & ->). simpl in *.
  split; [|exact Hcall]. split; [exact Hin|]. split; [exact Hpos|].
  destruct Hpt as [Hd0 | Hp]; [left; exact Hd0 | right; exact (Hep Hp)].
Qed.

(** At the end of a basic block, control either branches to a successor
    block or returns to the caller. A non-polling edge carries its live
    facts forward, while a return resumes the [[parked]] caller with no
    cached facts, so both transitions preserve [inv]. *)
Lemma next_inv_jump : forall ge md c c' s l j,
  ge_module ge = md -> checked_module md -> ready_state (c, s) ->
  fr_at (c_frame c) = Exec l [] j -> step ge c = Next c' -> inv ge md (c, s) -> inv ge md (c', s).
Proof.
  intros ge md c c' s l j Hge Hmd Hr Ha Hs [(Hin & Hpos & Hpt) Hcall]. unfold inv. simpl in *.
  unfold step in Hs. rewrite Ha in Hs.
  destruct (jump_step_next _ _ _ _ _ Hs) as [(t & Ht & ->) | (Hd & o & Hret)].
  + simpl. split; [|exact Hcall]. split; [exact Hin|]. split; [exact Hpos|].
    destruct Hpt as [Hd0 | Hp]; [left; exact Hd0 | right].
    destruct (point_ok_exec_inv _ _ _ _ _ _ _ Hp Ha) as (E & b & out & k & HE & Hb & Ho & Hj & _ & Hat).
    unfold point_ok. cbv zeta. simpl. exists E. split; [exact HE|].
    exists b, t. split; [exact Hb|]. split; [rewrite <- Hj; exact (taken_target_in _ _ _ _ Ht)|].
    split; [reflexivity|]. destruct (is_poll t) eqn:Ep; [left; reflexivity | right].
    exists out. split; [exact Ho|].
    destruct Hat as [(live & Hw & _ & Hjc) | (access & rest' & live' & E' & _)]; [|discriminate E'].
    rewrite (walks_nil _ _ _ Hw). exact (Hjc t Ht Ep).
  + destruct (return_step_next _ _ _ Hret) as (caller & pd & callers & e & m' & Hc & ->).
    rewrite Hc in Hcall. inversion Hcall as [|fp fps Hpk Hrest]; subst. simpl.
    split; [exact (parked_resume _ _ _ _ _ Hpk) | exact Hrest].
Qed.

(** Most instructions inside a basic block either advance normally to
    the next instruction or trigger a failed [[check_ahead]] that marks
    the frame [[doomed]]. Lemma [next_inv_continue] shows that both
    outcomes preserve [inv]. *)
Lemma next_inv_continue : forall ge md c s l i rest j out0 od e1 l1 m1,
  checked_module md -> ready_state (c, s) -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  inst_step ge (c_frame c) (c_mem c) i = Some out0 ->
  doomed_result ge (c_frame c) (c_mem c) i out0 = Some od -> fst od = IContinue e1 l1 m1 ->
  inv ge md (c, s) ->
  inv ge md (mkConfig (mkFrame (fr_fn (c_frame c)) e1 l1 (snd od) (Exec l rest j)) (c_callers c) m1
                      (c_fuel c), s).
Proof.
  intros ge md c s l i rest j out0 od e1 l1 m1 Hmd Hr Ha Hi Hdr Ho [(Hin & Hpos & Hpt) Hcall].
  unfold inv. simpl in *.
  assert (Hfit : objects_fit (m_regions (c_mem c))) by exact (R.address_space _ _ Hr).
  split; [|exact Hcall]. split; [exact Hin|].
  destruct (fr_doomed (c_frame c)) as [w|] eqn:Ew.
  * assert (Hnd : fr_doomed (c_frame c) <> None) by (rewrite Ew; discriminate).
    destruct (doomed_result_doomed _ _ _ _ _ _ Hnd Hdr) as (Hsd & [Ho' | [(e' & Ho') | (o' & Ho')]]);
      rewrite Ho in Ho'; try discriminate Ho'.
    -- subst out0. pose proof (inst_step_locals _ _ _ _ _ _ _ Hi) as Hl1. subst l1. split; [exact Hpos | left; exact Hsd].
    -- injection Ho' as _ -> _. split; [exact Hpos | left; exact Hsd].
  * destruct Hpt as [Hd0 | Hp]; [congruence|].
    destruct (doomed_result_fresh _ _ _ _ _ _ Ew Hdr) as [-> | (e' & w & ->)]; simpl in Ho |- *.
    -- subst out0. pose proof (inst_step_locals _ _ _ _ _ _ _ Hi) as Hl1. subst l1. split; [exact Hpos|]. right.
       destruct (point_ok_exec_inv _ _ _ _ _ _ _ Hp Ha) as (E & b & out & k & HE & Hb & Hout & Hj & Hk & Hat).
       destruct (skipn_cons _ _ _ _ _ (eq_sym Hk)) as (_ & Hrest & _).
       eapply point_ok_exec; simpl; [exact HE | reflexivity | exact Hb | exact Hout | exact Hj | symmetry; exact Hrest |].
       eapply at_pos_continue; [exact Hmd | exact Hin | exact Hb | exact Hk | exact Hfit | exact Hpos | exact Hat | exact Hi | reflexivity].
    -- injection Ho as _ <- _. split; [exact Hpos | left; discriminate].
Qed.

(** A call keeps [inv]: the callee starts at its entry, and the caller
    waits with no fact ([parked]). *)
Lemma next_inv_call : forall ge md c s l i rest j out0 od g xs pd callee,
  ge_module ge = md -> checked_module md -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  (fr_doomed (c_frame c) = None \/ ahead_transparent i = true) ->
  inst_step ge (c_frame c) (c_mem c) i = Some out0 ->
  doomed_result ge (c_frame c) (c_mem c) i out0 = Some od -> fst od = ICall g xs pd ->
  call_frame g xs = Some callee -> inv ge md (c, s) ->
  inv ge md (mkConfig callee ((mkFrame (fr_fn (c_frame c)) (fr_env (c_frame c)) (fr_locals (c_frame c))
                                       (snd od) (Exec l rest j), pd) :: c_callers c)
                      (c_mem c) (c_fuel c), s).
Proof.
  intros ge md c s l i rest j out0 od g xs pd callee Hge Hmd Ha Hdoom Hi Hdr Ho Hcf
    [(Hin & Hpos & Hpt) Hcall]. unfold inv. simpl in *.
  assert (Hd : fr_doomed (c_frame c) = None /\ out0 = ICall g xs pd /\ snd od = None).
  { destruct (fr_doomed (c_frame c)) as [w|] eqn:Ew.
    - assert (Hnd : fr_doomed (c_frame c) <> None) by (rewrite Ew; discriminate).
      destruct (doomed_result_doomed _ _ _ _ _ _ Hnd Hdr) as (_ & [Ho' | [(e' & Ho') | (o' & Ho')]]);
        rewrite Ho in Ho'; try discriminate Ho'.
      subst out0. destruct (inst_step_call_shape _ _ _ _ _ _ _ Hi) as (_ & [(r & cl & args & ->) | (r & cl & args & ->)]);
        destruct Hdoom as [Hdoom | Hdoom]; simpl in Hdoom; discriminate Hdoom.
    - destruct (doomed_result_fresh _ _ _ _ _ _ Ew Hdr) as [-> | (e' & w & ->)]; simpl in Ho; [|discriminate Ho].
      auto. }
  destruct Hd as (Hd & -> & Hsd).
  destruct (inst_step_call_shape _ _ _ _ _ _ _ Hi) as (Hg & Hcl). rewrite Hge in Hg.
  destruct Hpt as [Hd0 | Hp]; [congruence|].
  destruct (point_ok_exec_inv _ _ _ _ _ _ _ Hp Ha) as (E & b & out & k & HE & Hb & Hout & Hj & Hk & Hat).
  destruct (skipn_cons _ _ _ _ _ (eq_sym Hk)) as (_ & Hrest & _).
  simpl. split; [exact (call_frame_ok _ _ _ _ _ _ Hmd Hg Hcf)|]. constructor; [|exact Hcall].
  split; [exact Hin|]. split; [exact Hpos|]. split; [exact Hsd|].
  exists E, l, rest, j, b, out, (S k). simpl. repeat (split; [assumption || reflexivity|]).
  split; [symmetry; exact Hrest|].
  eapply walks_after; [exact Hat | |];
    destruct Hcl as [(r & cl & args & ->) | (r & cl & args & ->)]; reflexivity.
Qed.

(** An instruction that continues or calls keeps [inv]. *)
Lemma next_inv_inst : forall ge md c c' s l i rest j,
  ge_module ge = md -> checked_module md -> ready_state (c, s) ->
  fr_at (c_frame c) = Exec l (i :: rest) j -> step ge c = Next c' -> inv ge md (c, s) -> inv ge md (c', s).
Proof.
  intros ge md c c' s l i rest j Hge Hmd Hr Ha Hs H.
  destruct (step_exec_cons _ _ _ _ _ _ _ Ha Hs ltac:(discriminate) ltac:(discriminate))
    as (Hdoom & out0 & od & Hi & Hdr & Hn).
  destruct (inst_next_next _ _ _ _ _ _ _ Hn) as [(e1 & l1 & m1 & Ho & ->) | (g & xs & pd & callee & Ho & Hcf & ->)].
  - eapply next_inv_continue; eassumption.
  - eapply next_inv_call; eassumption.
Qed.

(** A step that allocates nothing ([Next]) keeps [inv], whatever the
    frame's point. *)
Lemma next_inv : forall ge md c c' s,
  ge_module ge = md -> checked_module md -> ready_state (c, s) ->
  step ge c = Next c' -> inv ge md (c, s) -> inv ge md (c', s).
Proof.
  intros ge md c c' s Hge Hmd Hr Hs H.
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - exact (next_inv_snapshot _ _ _ _ _ _ _ Hge Hmd Hr Ha Hs H).
  - exact (next_inv_enter _ _ _ _ _ _ _ Hge Hmd Hr Ha Hs H).
  - exact (next_inv_jump _ _ _ _ _ _ _ Hge Hmd Hr Ha Hs H).
  - exact (next_inv_inst _ _ _ _ _ _ _ _ _ Hge Hmd Hr Ha Hs H).
Qed.

(** The pass relies on no fact across an allocation, of a heap object
    or of a named local, and an allocation is not a `check_function`. *)
Lemma relies_alloc_any : forall s i,
  (exists d c al args, i = Let d c (Alloc al) args) \/ (exists x size, i = LocalAlloc x size) ->
  relies s i = false /\ is_check_function i = false.
Proof.
  intros s i [(d & c & al & args & ->) | (x & size & ->)]; [destruct c|]; split; reflexivity.
Qed.

(** Heap allocations and stack local allocations invalidate all cached
    pointer facts, and a local allocation binds its new object above
    address 0. Lemma [alloc_inv_inst] proves that both preserve
    [inv]. *)
Lemma alloc_inv_inst : forall ge md c q k s base s' l i rest j,
  ready_state (c, s) -> fr_at (c_frame c) = Exec l (i :: rest) j -> step ge c = Fresh q k ->
  0 < base -> inv ge md (c, s) -> inv ge md (k base, s').
Proof.
  intros ge md c q k s base s' l i rest j Hr Ha Hs Hb0 [(Hin & Hpos & Hpt) Hcall]. unfold inv in *. simpl in *.
  destruct (step_exec_cons _ _ _ _ _ _ _ Ha Hs ltac:(discriminate) ltac:(discriminate))
    as (Hdoom & out0 & od & Hi & Hdr & Hn).
  destruct (inst_next_fresh _ _ _ _ _ _ _ _ Hn) as (k0 & Ho & Hk).
  assert (Hout : fst od = out0 /\ (fr_doomed (c_frame c) = None -> snd od = None)).
  { destruct (fr_doomed (c_frame c)) as [w|] eqn:Ew.
    - assert (Hnd : fr_doomed (c_frame c) <> None) by (rewrite Ew; discriminate).
      destruct (doomed_result_doomed _ _ _ _ _ _ Hnd Hdr) as (_ & [Ho' | [(e' & Ho') | (o' & Ho')]]);
        rewrite Ho in Ho'; try discriminate Ho'.
      split; [congruence | discriminate].
    - destruct (doomed_result_fresh _ _ _ _ _ _ Ew Hdr) as [-> | (e' & w & ->)]; simpl in Ho |- *;
        [auto | discriminate Ho]. }
  destruct Hout as [Hout Hsd]. rewrite Ho in Hout. subst out0.
  pose proof (inst_step_fresh_shape _ _ _ _ _ _ Hi) as Hshape.
  rewrite Hk. destruct (k0 base) as [[e locals] m'] eqn:Ek. simpl.
  assert (Hlocals : locals = fr_locals (c_frame c) \/
                    exists x size, i = LocalAlloc x size /\ locals = put x (Some base) (fr_locals (c_frame c))).
  { destruct Hshape as [(d & cl & al & args & -> & Hl) | (x & size & -> & Hl)];
      specialize (Hl base); rewrite Ek in Hl; simpl in Hl; eauto. }
  split; [|exact Hcall]. split; [exact Hin|]. split.
  { destruct Hlocals as [-> | (x & size & _ & ->)]; [exact Hpos|].
    eapply locals_pos_put; [exact Hpos | exact Hb0 | reflexivity]. }
  destruct (fr_doomed (c_frame c)) as [w|] eqn:Ew.
  + left. destruct (snd od) eqn:Esd; [discriminate|].
    assert (Hnd : fr_doomed (c_frame c) <> None) by (rewrite Ew; discriminate).
    exfalso. exact (proj1 (doomed_result_doomed _ _ _ _ _ _ Hnd Hdr) Esd).
  + rewrite (Hsd eq_refl). right. destruct Hpt as [Hd0 | Hp]; [congruence|].
    destruct (point_ok_exec_inv _ _ _ _ _ _ _ Hp Ha) as (E & b & out & kp & HE & Hb & Hout & Hj & Hkp & Hat).
    destruct (skipn_cons _ _ _ _ _ (eq_sym Hkp)) as (_ & Hrest & _).
    destruct (relies_alloc_any (fn_src md (fr_fn (c_frame c))) i
                ltac:(destruct Hshape as [(d & cl & al & args & -> & _) | (x & size & -> & _)]; eauto 6))
      as [Hrel Hcf].
    eapply point_ok_exec; simpl; [exact HE | reflexivity | exact Hb | exact Hout | exact Hj | symmetry; exact Hrest |].
    eapply at_pos_between; [exact (walks_after _ _ _ _ _ _ _ _ _ _ _ Hat Hrel Hcf) | apply live_dom_nil | apply facts_hold_nil].
Qed.

(** Every new heap or stack object returned by the runtime allocator
    starts at a positive base address. Lemma [alloc_inv] shows that
    allocating at that fresh base preserves [inv] for both variadic
    snapshots and instruction allocations. *)
Lemma alloc_inv : forall ge md c q k s base s',
  ready_state (c, s) -> step ge c = Fresh q k -> 0 <= req_extent q ->
  R.alloc s q = Some (base, s') -> inv ge md (c, s) -> inv ge md (k base, s').
Proof.
  intros ge md c q k s base s' Hr Hs He Hal [(Hin & Hpos & Hpt) Hcall]. unfold inv in *. simpl in *.
  destruct (step_fresh_kept _ _ _ _ Hs) as [Halign _].
  destruct (R.fresh_allocation _ _ _ _ _ Hr Halign He Hal) as [(Hb0 & _) _].
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - destruct (step_snapshot_fresh _ _ _ _ _ _ Ha Hs base) as (Hc & Hf & Hl & Hd & Ha').
    rewrite Hc. split; [|exact Hcall]. split; [rewrite Hf; exact Hin|].
    split; [intros x b Hx; rewrite Hl in Hx; exact (Hpos _ _ Hx)|].
    destruct Hpt as [Hd0 | Hp]; [left; rewrite Hd; exact Hd0 | right].
    eapply point_ok_entry; [exact Hp | left; exact Ha | exact Hf | exact Ha'].
  - exfalso. exact (step_enter_fresh _ _ _ _ _ _ Ha Hs).
  - exfalso. unfold step in Hs. rewrite Ha in Hs. exact (jump_step_not_fresh _ _ _ _ _ _ Hs).
  - exact (alloc_inv_inst _ _ _ _ _ _ base s' _ _ _ _ Hr Ha Hs Hb0 (conj (conj Hin (conj Hpos Hpt)) Hcall)).
Qed.

(** A raw memory access is only safe when the evidence pass verified its
    bounds beforehand. Whenever [covered_access] accepts a raw access,
    [relies] is true so the invariant guarantees that its cached facts
    hold. *)
Lemma covered_relies : forall s i q lo hi r al, covered_access i q lo hi r al = true -> relies s i = true.
Proof.
  unfold covered_access, relies. intros s i q lo hi r al H.
  destruct (raw_access i); [|discriminate H]. rewrite !orb_true_r. reflexivity.
Qed.

(** The garbage collector may run at a poll edge or right before an
    instruction that inspects memory. Because poll edges carry no cached
    evidence and the collector never frees live objects, a [[safepoint]]
    leaves [inv] intact. *)
Lemma safepoint_inv : forall ge md c s s' m',
  safepoint_due ge c = true -> R.safepoint s (c_mem c) s' m' ->
  inv ge md (c, s) -> inv ge md (with_mem c m', s').
Proof.
  intros ge md c s s' m' Hdue Hact [(Hin & Hpos & Hpt) Hcall]. unfold inv in *. simpl in *.
  split; [|exact Hcall]. split; [exact Hin|]. split; [exact Hpos|].
  destruct Hpt as [Hd0 | Hp]; [left; exact Hd0 | right].
  pose proof Hdue as Hdue0. unfold safepoint_due in Hdue.
  destruct (fr_at (c_frame c)) as [xs l | l from | l is j] eqn:Ha; try discriminate Hdue.
  destruct (point_ok_exec_inv _ _ _ _ _ _ _ Hp Ha) as (E & b & out & k & HE & Hb & Hout & Hj & Hk & Hat).
  eapply point_ok_exec; [exact HE | exact Ha | exact Hb | exact Hout | exact Hj | exact Hk |].
  destruct is as [|i rest].
  - destruct Hat as [(live & Hw & Hd & Hjc) | (access & rest' & live' & E' & _)]; [|discriminate E'].
    left. exists live. split; [exact Hw|]. split; [exact Hd|]. intros t Ht Hpoll. exfalso.
    unfold with_mem in Ht. simpl in Ht. rewrite Ht in Hdue. destruct t; simpl in Hdue, Hpoll; [discriminate Hdue | discriminate Hpoll].
  - assert (Hreg : relies (fn_src md (fr_fn (c_frame c))) i = true ->
                   m_regions m' = m_regions (c_mem c)) by (intros Hr; exact (spares_any ge md c s s' m' Hdue0 Hact l i rest j Ha Hr)).
    destruct Hat as [(live & Hw & Hd & Hl) | (access & rest' & live' & E' & Hw & Hd & Hpc)].
    + left. exists live. split; [exact Hw|]. split; [exact Hd|]. intros Hr.
      eapply facts_hold_same; [exact (Hreg Hr) | exact (Hl Hr)].
    + injection E' as <- <-. right. exists i, rest, live'. split; [reflexivity|]. split; [exact Hw|].
      split; [exact Hd|].
      destruct Hpc as [(fb & pre & Hcov & -> & Hh) | Hfn]; [left | right; exact Hfn].
      exists fb, pre. split; [exact Hcov|]. split; [reflexivity|].
      eapply facts_hold_same; [apply Hreg | exact Hh].
      destruct Hcov as [Hcov | ->]; [exact (covered_relies _ _ _ _ _ _ _ Hcov) | reflexivity].
Qed.

(** Every machine step from a [[ready]] state keeps [inv]. *)
Theorem mstep_inv : forall ge md st st',
  ge_module ge = md -> checked_module md ->
  ready_state st -> mstep ge st st' -> inv ge md st -> inv ge md st'.
Proof.
  intros ge md st st' Hge Hmd Hr Hs H.
  destruct Hs as [c c' s E | c q k s base s' E He Hal | c s s' m' Hd Hact].
  - eapply next_inv; eauto.
  - eapply alloc_inv; eauto.
  - eapply safepoint_inv; eauto.
Qed.

(** From a ready start where it holds, [inv] holds in every state a
    run reaches. *)
Theorem mreachable_inv : forall ge md st st',
  ge_module ge = md -> checked_module md -> ge_free ge = R.free ->
  mreachable ge st st' -> ready_state st -> inv ge md st -> inv ge md st'.
Proof.
  intros ge md st st' Hge Hmd Hfree H.
  induction H as [st st' Hs | st | st1 st2 st3 H12 IH1 H23 IH2]; intros Hr Hi; auto.
  - eapply mstep_inv; eauto.
  - apply IH2; [exact (mreachable_ready _ _ _ Hfree H12 Hr) | exact (IH1 Hr Hi)].
Qed.

(** [inv] holds where a run starts: at the entry of a checked module's
    function, with no caller. *)
Lemma start_inv : forall ge md f xs fr m fuel s,
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr ->
  inv ge md (mkConfig fr [] m fuel, s).
Proof.
  intros ge md f xs fr m fuel s Hmd Hin Hc. split; [|constructor].
  exact (call_frame_ok _ _ _ _ _ _ Hmd Hin Hc).
Qed.

(** ## No unchecked access

    Once [inv] holds at every reachable state, we can connect the
    run-level invariant back to individual memory accesses and raw calls.
    The two theorems in this section rule out [[unchecked]] errors for
    every validated instruction except the hull-covered case closed in
    [Chain](Chain.v). *)

(** In C, dereferencing an out-of-bounds pointer or calling through an
    invalid function pointer is unsafe unless the compiler already
    checked it. Theorem [access_not_unchecked] proves that in any ready
    state satisfying [inv], an undoomed frame never hits an
    [[unchecked]] raw access or raw call outside [hull_case]. *)
Theorem access_not_unchecked : forall ge md c s l i rest j why,
  inv ge md (c, s) -> ready_state (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  (raw_access i <> None \/ exists r cl args, i = RawCall r cl args) ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)) \/
  hull_case ge md c l i rest.
Proof.
  intros ge md c s l i rest j why [(_ & Hpos & Hpt) _] Hr Hd Ha Hi. simpl in *.
  assert (Hfit : objects_fit (m_regions (c_mem c))) by exact (R.address_space _ _ Hr).
  destruct Hpt as [Hd0 | Hp]; [congruence|].
  destruct (point_ok_exec_inv _ _ _ _ _ _ _ Hp Ha) as (E & b & out & k & _ & Hb & _ & _ & Hk & Hat).
  destruct Hat as [(live & Hw & Hdom & Hl) | (access & rest' & live' & E' & _ & _ & Hpc)].
  - destruct (walks_cons _ _ _ _ _ Hw) as (rest' & live' & Hc & _).
    destruct (raw_access i) as [[[[q x] off] need]|] eqn:Hra.
    + assert (Hrel : relies (fn_src md (fr_fn (c_frame c))) i = true)
        by (unfold relies; rewrite Hra, !orb_true_r; reflexivity).
      destruct (generic_access_not_unchecked _ _ _ _ _ _ _ _ _ q x off need why Hfit (Hl Hrel)
                  (raw_access_not_special _ _ Hra) Hc Hra) as [Hn | (fa & Hfa & Hh)];
        [left; exact Hn | right; exists b, k, live, fa, q].
      repeat (split; [eassumption|]). split; [exact (Hl Hrel)|]. repeat (split; [eassumption|]). exact Hh.
    + destruct Hi as [Hi | (r & cl & args & ->)]; [congruence|].
      rewrite raw_call_alone in Hc. discriminate Hc.
  - injection E' as <- _. left.
    destruct Hpc as [(fb & pre & Hcov & _ & Hh) | (_ & r & q & args & p & -> & Hq & Hc)].
    + destruct Hcov as [Hcov | ->]; [|cbn; discriminate].
      destruct (Hh fb (or_introl eq_refl)) as (p & Eq & _ & Hpass).
      exact (covered_access_not_unchecked _ _ _ _ _ _ _ _ _ _ _ Hfit Hcov Eq Hpass).
    + exact (raw_call_checked _ _ _ _ _ _ _ _ Hq Hc).
Qed.

(** Combining [mreachable_inv] with [access_not_unchecked], every state
    reachable from a ready function entry avoids [[unchecked]] raw
    accesses and raw calls, up to [hull_case]. *)
Theorem run_access_not_unchecked : forall ge md f xs fr m fuel s0 c s l i rest j why,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  (raw_access i <> None \/ exists r cl args, i = RawCall r cl args) ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)) \/
  hull_case ge md c l i rest.
Proof.
  intros ge md f xs fr m fuel s0 c s l i rest j why Hmd Hge Hfree Hin Hcf H0 Hreach.
  eapply access_not_unchecked.
  - eapply mreachable_inv; eauto. exact (start_inv _ _ _ _ _ _ _ s0 Hmd Hin Hcf).
  - exact (mreachable_ready _ _ _ Hfree Hreach H0).
Qed.

End Persistence.

(** ## The interpreter's runtime

    To apply these theorems to the executable reference interpreter, we
    instantiate the [Persistence] functor with [InterpRuntime]. This
    gives a concrete safety corollary for every run of the interpreter on
    a validated module. *)

(** Module [InterpPersistence] instantiates [Persistence] for the
    reference interpreter runtime [InterpRuntime]. *)
Module InterpPersistence := Persistence InterpRuntime.
Import InterpPersistence.I.

(** Instantiating the preservation theorem with [InterpRuntime] gives a
    concrete guarantee for the reference interpreter. In any reachable
    state from a ready entry, an undoomed frame never hits an
    [[unchecked]] raw access or raw call outside [hull_case]. *)
Corollary interp_access_not_unchecked : forall md globals f xs fr m fuel s0 c s l i rest j why,
  let ge := mkGenv md globals InterpRuntime.free in
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  fr_doomed (c_frame c) = None -> fr_at (c_frame c) = Exec l (i :: rest) j ->
  (raw_access i <> None \/ exists r cl args, i = RawCall r cl args) ->
  inst_step ge (c_frame c) (c_mem c) i <> Some (IStop (Unchecked why)) \/
  hull_case ge md c l i rest.
Proof.
  intros md globals f xs fr m fuel s0 c s l i rest j why ge Hmd Hin Hcf H0 Hreach Hd Ha Hi.
  exact (InterpPersistence.run_access_not_unchecked ge md f xs fr m fuel s0 c s l i rest j why
           Hmd eq_refl eq_refl Hin Hcf H0 Hreach Hd Ha Hi).
Qed.
