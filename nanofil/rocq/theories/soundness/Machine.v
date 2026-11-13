(** A Fil-C program cannot run in isolation from its [[runtime]]: it asks
    the allocator for fresh heap objects, calls `c: free`, and yields at
    GC safepoints. While the abstract semantics in [Semantics](Semantics.v)
    lets any [[fresh]] address stand in for an allocation, a real runtime
    chooses concrete base addresses and may sweep memory at safepoints.

    This module pairs the program's execution with a concrete [Runtime]
    R to form a [[machine]], and proves that R stays [[ready]] to
    allocate across every step of a run. It also proves that the runtime
    may act only before an instruction marked with [R.at_safepoint] or
    before a [[poll|poll edge]] is taken, which is what lets the
    [[validator]] keep [[evidence]] across every other instruction and
    edge.

    ## Decisions

    The runtime acts before an [at_safepoint] instruction or a poll edge
    rather than after it, so the instruction runs on whatever memory the
    runtime left behind, just as native code does after a pollcheck.

    An allocation with a negative extent has no machine step. The
    runtime's [fresh_allocation] axiom covers non-negative extents only;
    only a stack local's constant size can be negative, and validation
    rejects negative local sizes while heap sizes are read at unsigned
    length.

    Ending a stack local on function return is distinct from freeing a
    heap object. The [region_step] relation allows any live object to
    end, whereas [lifetime_step] speaks specifically of the runtime's
    `c: free`, which empties only heap objects. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Runtime.
Import ListNotations.
Open Scope Z_scope.

(** ## Case analysis

    Program steps in [Semantics](Semantics.v) branch on many runtime
    checks and instruction forms. When a proof examines a step
    assumption, this section provides a tactic to split those nested
    matches automatically and discard impossible branches. *)

(** The tactic [cases] splits on every match in hypothesis H whose
    scrutinee names no bound variable, working outermost first and
    discarding branches where H reaches a contradiction. *)
Ltac cases H :=
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             destruct x eqn:?; cbv beta iota zeta in H; try discriminate H
         end.

(** ## What the program does to memory

    To stay [[ready]] to allocate, the runtime needs to know that
    ordinary program steps never corrupt its allocator metadata or
    scribble outside live objects. The [kept] relation captures this
    contract: existing objects may only stay intact or be freed, and no
    bytes or capabilities may be written outside live objects. *)

(** Leaving memory as it is is [kept]. *)
Lemma kept_refl : forall m, kept m m.
Proof. intros m. split; [intros b reg' E; exists reg'; auto | auto]. Qed.

(** Two kept changes in a row, from m1 to m2 and m2 to m3, are one
    kept change. *)
Lemma kept_trans : forall m1 m2 m3, kept m1 m2 -> kept m2 m3 -> kept m1 m3.
Proof.
  intros m1 m2 m3 (R12 & O12) (R23 & O23). split.
  - intros b reg3 E3. destruct (R23 _ _ E3) as (reg2 & E2 & H23).
    destruct (R12 _ _ E2) as (reg1 & E1 & H12). exists reg1. split; auto.
    destruct H23 as [-> | (L2 & ->)]; destruct H12 as [-> | (L1 & ->)]; auto.
  - intros a Hn. assert (Hn2 : ~ in_object m2 a).
    { intros (b & reg2 & E2 & Hr). destruct (R12 _ _ E2) as (reg1 & E1 & [-> | (_ & ->)]).
      - apply Hn. exists b, reg1. auto.
      - simpl in Hr. lia. }
    destruct (O12 a Hn) as [B1 A1]. destruct (O23 a Hn2) as [B2 A2]. split; congruence.
Qed.

(** When the runtime frees an object via [lifetime_step], it only
    empties live heap regions, which satisfies the more general
    [region_step] relation used by the program semantics. *)
Lemma lifetime_region_step : forall m m', lifetime_step m m' -> region_step m m'.
Proof.
  intros m m' H b reg' E.
  destruct (H _ _ E) as (reg & E0 & [-> | (Hk & Hl & ->)]); exists reg; split; auto.
  right. rewrite Hk. auto.
Qed.

(** Every memory change the function free makes is [kept]: what a
    free that meets the lifetime and retention axioms does. *)
Definition free_keeps (free : word -> mem -> option (res unit * mem)) : Prop :=
  forall x m r m', free x m = Some (r, m') -> kept m m'.

(** A successful [[access]] check covers its bytes with one object's
    bounds: if the check of size bytes at a passes, every address from
    a up to a + size is inside an object. *)
Lemma access_in : forall m a c size r align u,
  access_res m a c size r align = Some (RVal u) ->
  forall b, a <= b < a + size -> in_object m b.
Proof.
  unfold access_res, cap_access_res. intros m a c size r align u H b Hb.
  destruct c as [| base | base | f | n]; try discriminate;
    destruct (object_region base (m_regions m)) as [reg|] eqn:E; try discriminate;
    destruct ((base <=? a) && (a + size <=? r_end reg)) eqn:Eb; try discriminate;
    apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2;
    exists base, reg; split; auto; lia.
Qed.

(** Writing size bytes at a is kept if they are all inside objects. *)
Lemma store_bytes_kept : forall m a size x,
  (forall b, a <= b < a + size -> in_object m b) -> kept m (store_bytes m a size x).
Proof.
  intros m a size x Hin. split.
  - intros b reg' E. exists reg'. split; [exact E | auto].
  - intros b Hn. simpl. split; auto.
    destruct ((a <=? b) && (b <? a + size)) eqn:E; auto.
    exfalso. apply Hn, Hin. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(** Storing a [[capability]] in the [[aux]] at a is kept if a is
    inside an object. *)
Lemma store_aux_kept : forall m a c, in_object m a -> kept m (store_aux m a c).
Proof.
  intros m a c Hin. split.
  - intros b reg' E. exists reg'. split; [exact E | auto].
  - intros b Hn. simpl. split; auto.
    destruct (Z.eqb b a) eqn:E; auto.
    apply Z.eqb_eq in E. subst. contradiction.
Qed.

(** Writes leave the objects where they were: an address inside an
    object before a byte write is inside one after it. *)
Lemma in_object_store_bytes : forall m a size x b,
  in_object m b -> in_object (store_bytes m a size x) b.
Proof. auto. Qed.

(** Storing a capability in the [[aux]] space at address a leaves
    objects intact as long as a lies inside a live object. *)
Lemma in_object_store_aux : forall m a c b, in_object m b -> in_object (store_aux m a c) b.
Proof. auto. Qed.

(** A store as `store_res/7` does it is kept: it writes the bytes, and
    a pointer's capability, only after its access check passed. *)
Lemma store_res_kept : forall w m a c x r m', store_res w m a c x = Some (r, m') -> kept m m'.
Proof.
  unfold store_res. intros w m a c x r m' H.
  destruct w, x; try discriminate; cases H; inversion H; subst; try apply kept_refl;
    match goal with
    | E : access_res _ _ _ _ _ _ = Some (RVal _) |- kept _ (store_aux _ _ _) =>
        eapply kept_trans; [|apply store_aux_kept];
        [ apply store_bytes_kept; intros b Hb; eapply access_in; [exact E | exact Hb]
        | apply in_object_store_bytes; eapply access_in; [exact E | simpl; lia] ]
    | E : access_res _ _ _ _ _ _ = Some (RVal _) |- _ =>
        apply store_bytes_kept; intros b Hb; eapply access_in; [exact E | exact Hb]
    end.
Qed.

(** A fold of memory changes that starts from no memory ends with
    none. *)
Lemma fold_left_none : forall (A : Type) (f : mem -> A -> option mem) xs,
  fold_left (fun acc x => let* m1 := acc in f m1 x) xs None = None.
Proof. intros A f xs. induction xs; simpl; auto. Qed.

(** Folding a list of memory updates over an initial memory state
    produces a [kept] transition if each individual update is [kept] and
    preserves a loop invariant P. *)
Lemma fold_kept : forall (A : Type) (P : mem -> Prop) (f : mem -> A -> option mem) xs m0 m',
  P m0 ->
  (forall m1 x m2, P m1 -> f m1 x = Some m2 -> P m2 /\ kept m1 m2) ->
  fold_left (fun acc x => let* m1 := acc in f m1 x) xs (Some m0) = Some m' ->
  kept m0 m'.
Proof.
  intros A P f xs. induction xs as [|x xs IH]; simpl; intros m0 m' H0 Hf H.
  - inversion H; subst. apply kept_refl.
  - destruct (f m0 x) as [m1|] eqn:E.
    + destruct (Hf _ _ _ H0 E) as [H1 K1]. eapply kept_trans; [exact K1|]. eapply IH; eauto.
    + rewrite fold_left_none in H. discriminate.
Qed.

(** Storing a pointer executes a sequence of byte and capability effects.
    When the 8-byte access check at address a has passed, every effect
    in [pointer_store_effects] writes inside a live object and preserves
    [kept]. *)
Lemma pointer_store_effects_kept : forall a x m es m',
  (forall b, a <= b < a + 8 -> in_object m b) ->
  pointer_store_effects a x m es = Some m' -> kept m m'.
Proof.
  intros a x m es m' Hin H.
  apply (fold_kept effect (fun m1 => m_regions m1 = m_regions m) (pointer_store_effect a x) es m m');
    auto.
  intros m1 e m2 Hr E.
  assert (Hin1 : forall b, a <= b < a + 8 -> in_object m1 b).
  { intros b Hb. unfold in_object. rewrite Hr. apply Hin. auto. }
  destruct e; simpl in E; try discriminate; inversion E; subst; split; auto using kept_refl.
  - apply store_aux_kept, Hin1. lia.
  - apply store_bytes_kept. exact Hin1.
  - eapply kept_trans; [|apply store_bytes_kept].
    + apply store_aux_kept, Hin1. lia.
    + intros b Hb. apply in_object_store_aux, Hin1. auto.
Qed.

(** Reading a variadic argument (`va_arg_res/4`) is kept: its one
    write is a checked store. *)
Lemma va_arg_res_kept : forall k p m r m', va_arg_res k p m = Some (r, m') -> kept m m'.
Proof.
  unfold va_arg_res. intros k p m r m' H. cases H;
    (* congruence, not inversion: inversion takes seconds over the
       loaded words' arithmetic *)
    match type of H with Some (_, ?x) = Some (_, ?y) => assert (x = y) as <- by congruence end;
    first [ apply kept_refl
          | match goal with E : store_res _ _ _ _ _ = Some _ |- _ => exact (store_res_kept _ _ _ _ _ _ _ E) end ].
Qed.

(** An atomic compare-and-swap ([cas_res]) first checks access to its
    target bytes and then writes data and any pointer capability inside
    those bounds, so it preserves [kept] and leaves regions unchanged. *)
Lemma cas_res_kept : forall t k m a c e n r m',
  cas_res t k m a c e n = Some (r, m') -> kept m m' /\ m_regions m' = m_regions m.
Proof.
  unfold cas_res. intros t k m a c e n r m' H. cases H; inversion H; subst;
    try (split; [apply kept_refl | reflexivity]).
  all: match goal with E : access_res _ _ _ _ _ _ = Some (RVal _) |- _ =>
         pose proof (access_in _ _ _ _ _ _ _ E) as Hin end.
  all: try (split; [apply store_bytes_kept; exact Hin | reflexivity]).
  match goal with E : pointer_store_effects _ _ _ _ = Some _ |- _ =>
    split; [exact (pointer_store_effects_kept _ _ _ _ _ Hin E)
           | cbn in E; injection E as <-; reflexivity] end.
Qed.

(** An integer op changes memory only by a [[cas]], which is kept and
    changes no region; every other one leaves memory as it is. *)
Lemma op_res_int_kept : forall o k xs m r m',
  op_res_int o k xs m = Some (OpRes r m') -> kept m m' /\ m_regions m' = m_regions m.
Proof.
  unfold op_res_int. intros o k xs m r m' H. destruct o; cases H; inversion H; subst;
    try (split; [apply kept_refl | reflexivity]).
  match goal with E : cas_res _ _ _ _ _ _ _ = Some ?rm |- _ =>
    destruct rm; exact (cas_res_kept _ _ _ _ _ _ _ _ _ E) end.
Qed.

(** An op that gives a result changes memory as [kept] allows. *)
Lemma op_res_kept : forall o k xs m r m', op_res o k xs m = Some (OpRes r m') -> kept m m'.
Proof.
  unfold op_res, float_integer. intros o k xs m r m' H.
  destruct o; cases H; inversion H; subst;
    first [ apply kept_refl
          | match goal with E : op_res_int _ _ _ _ = Some _ |- _ =>
              exact (proj1 (op_res_int_kept _ _ _ _ _ _ E)) end
          | match goal with E : va_arg_res _ _ _ = Some ?rm |- _ =>
              destruct rm; exact (va_arg_res_kept _ _ _ _ _ E) end ].
Qed.

(** Only the op `alloc` allocates: a heap object with a positive
    alignment, and it writes nothing into the new memory. *)
Lemma op_res_alloc : forall o k xs m q kont,
  op_res o k xs m = Some (OpAlloc q kont) ->
  0 < req_align q /\ forall base, kept (allocated m q base) (snd (kont base)).
Proof.
  unfold op_res, op_res_int, float_integer. intros o k xs m q kont H.
  destruct o; cases H; inversion H; subst.
  split; [simpl; lia | intros base; apply kept_refl].
Qed.

(** Ending an invocation's locals (`invalidate_locals/3`) is kept: it
    ends live stack objects, and writes nothing. *)
Lemma invalidate_locals_kept : forall locals m m', invalidate_locals locals m = Some m' -> kept m m'.
Proof.
  unfold invalidate_locals. intros locals m m' H.
  eapply (fold_kept (name * option Z) (fun _ => True)); [exact I| |exact H].
  intros m1 [x slot] m2 _ E. split; auto. simpl in E. cases E; inversion E; subst;
    try apply kept_refl.
  match goal with Er : replace_region ?base _ _ = Some _ |- _ => split; [intros b reg' Eb; simpl in Eb;
      rewrite (object_region_replace _ _ _ _ b Er eq_refl) in Eb;
      destruct (Z.eqb b base) eqn:Ez | intros a _; simpl; auto] end.
  - apply Z.eqb_eq in Ez. subst. inversion Eb; subst. eexists. split; [eassumption|].
    right. split; [assumption|]. f_equal. symmetry. assumption.
  - exists reg'. auto.
Qed.

(** ## What a step does to memory

    Every single memory write or deallocation in the interpreter stays
    inside live objects, so whole program steps preserve the allocator's
    invariants as well. The lemmas below lift [kept] from individual
    operations to entire instruction, jump, and function-return steps. *)

(** When a variadic C function starts, it copies its extra arguments
    into a newly allocated buffer. Writing those words with
    [snapshot_values] preserves [kept] as long as the buffer's addresses
    all lie inside live objects. *)
Lemma snapshot_kept : forall xs a m,
  (forall b, a <= b < a + 8 * Z.of_nat (length xs) -> in_object m b) ->
  kept m (snapshot_values xs a m).
Proof.
  induction xs as [|x xs IH]; simpl; intros a m Hin.
  - apply kept_refl.
  - destruct x as [n | p | c size].
    + eapply kept_trans; [|apply IH].
      * apply store_bytes_kept. intros b Hb. apply Hin. lia.
      * intros b Hb. apply in_object_store_bytes, Hin. lia.
    + eapply kept_trans; [|apply IH].
      * eapply kept_trans; [|apply store_aux_kept].
        -- apply store_bytes_kept. intros b Hb. apply Hin. lia.
        -- apply in_object_store_bytes, Hin. lia.
      * intros b Hb. apply in_object_store_aux, in_object_store_bytes, Hin. lia.
    + apply IH. intros b Hb. apply Hin. lia.
Qed.

(** A heap request's extent covers its size: the runtime is asked for
    at least as many bytes as the object needs. *)
Lemma heap_req_extent : forall align size, size <= req_extent (heap_req align size).
Proof.
  intros align size. simpl.
  pose proof (Z.div_mod (size + 15) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (size + 15) 16 ltac:(lia)). lia.
Qed.

(** The new object's bytes are inside it: after allocating q at base,
    every address from base up to base plus the extent is inside an
    object. *)
Lemma in_allocated : forall m q base b,
  base <= b < base + req_extent q -> in_object (allocated m q base) b.
Proof.
  intros m q base b Hb. exists base, (mkRegion base (base + req_extent q) (req_kind q) Live).
  simpl. rewrite Z.eqb_refl. auto.
Qed.

(** A variadic callee's snapshot is written into its new object. *)
Lemma snapshot_alloc_kept : forall xs m base,
  let q := heap_req 16 (8 * Z.of_nat (length xs)) in
  kept (allocated m q base) (snapshot_values xs base (allocated m q base)).
Proof.
  intros xs m base q. apply snapshot_kept. intros b Hb. apply in_allocated.
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length xs))). unfold q. lia.
Qed.

(** Predicate [ahead_inst] identifies a [[check_ahead]] instruction,
    which is the only instruction where [doomed_result] can mark a
    healthy frame as doomed. *)
Definition ahead_inst (i : inst) : bool :=
  match i with Let _ A (CheckAhead _ _ _ _ _) [_] => true | _ => false end.

(** When a frame is already [[doomed]], any later [[unchecked]] failure
    becomes an early trap unless it is an alias or limit error, while a
    healthy frame passes every non-[check_ahead] result through
    unchanged. *)
Lemma doomed_result_other : forall ge fr m i out,
  ahead_inst i = false ->
  doomed_result ge fr m i out =
    match out with
    | IStop (Unchecked w) =>
        match fr_doomed fr, w with
        | Some why, (Alias | WhyLimit) => Some (out, fr_doomed fr)
        | Some why, _ => Some (IStop (Trap (Early why)), fr_doomed fr)
        | None, _ => Some (out, None)
        end
    | _ => Some (out, fr_doomed fr)
    end.
Proof.
  intros ge fr m i out E. destruct i; try reflexivity.
  destruct k; try reflexivity. destruct o; try reflexivity.
  destruct args as [|v [|v' args]]; try reflexivity. discriminate E.
Qed.

(** [doomed_result] (`doomed_result/5`) passes the instruction's result
    on, or continues with the memory unchanged, or stops. *)
Lemma doomed_result_out : forall ge fr m i out od,
  doomed_result ge fr m i out = Some od ->
  fst od = out \/ (exists e l, fst od = IContinue e l m) \/ (exists o, fst od = IStop o).
Proof.
  intros ge fr m i out od H. destruct (ahead_inst i) eqn:Ea.
  - destruct i; try discriminate Ea. destruct k; try discriminate Ea.
    destruct o; try discriminate Ea. destruct args as [|v [|v' args]]; try discriminate Ea.
    unfold doomed_result in H. cases H; inversion H; subst; simpl; eauto.
  - rewrite (doomed_result_other _ _ _ _ _ Ea) in H. cases H; inversion H; subst; simpl; eauto.
Qed.

(** Most operations evaluate their arguments and run [op_res] uniformly,
    while local checks, function checks, and variadic argument queries
    take special paths in [inst_step]. Predicate [special_let] marks
    those three exceptions. *)
Definition special_let (o : op) : bool :=
  match o with CheckLocal _ _ _ _ _ | CheckFunction | VaArgs => true | _ => false end.

(** For any other op o, [inst_step] of a `let` is the generic case:
    read the arguments at their classes, run the op, and bind its
    result, stop, or allocate. *)
Lemma inst_step_let : forall ge fr m d k o args,
  special_let o = false ->
  inst_step ge fr m (Let d k o args) =
    let e := fr_env fr in
    let locals := fr_locals fr in
    let* classes := op_arg_classes o k in
    let* xs := map2_option (value_x ge e) classes args in
    let* out := op_res o k xs m in
    match out with
    | OpRes r m' => Some (bind_res d r e locals m')
    | OpUB why => Some (IStop (UB why))
    | OpAlloc q kont =>
        Some (IFresh q (fun base => let (x, m') := kont base in (put d x e, locals, m')))
    end.
Proof. intros ge fr m d k o args Es. destruct o; try discriminate Es; destruct k; reflexivity. Qed.

(** Any instruction that continues without allocating preserves [kept],
    provided the environment's `c: free` function satisfies
    [free_keeps]. *)
Lemma inst_step_kept : forall ge fr m i e l m',
  free_keeps (ge_free ge) ->
  inst_step ge fr m i = Some (IContinue e l m') -> kept m m'.
Proof.
  intros ge fr m i e l m' Hfree H. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst;
    first [ apply kept_refl
          | match goal with E : op_res _ _ _ _ = Some (OpRes _ _) |- _ => exact (op_res_kept _ _ _ _ _ _ E) end
          | match goal with E : ge_free _ _ _ = Some (_, _) |- _ => exact (Hfree _ _ _ _ E) end
          | match goal with E : store_res _ _ _ _ _ = Some (_, _) |- _ => exact (store_res_kept _ _ _ _ _ _ _ E) end
          | match goal with
            | A : access_res _ _ _ _ _ _ = Some (RVal _), E : pointer_store_effects _ _ _ _ = Some _ |- _ =>
                apply (pointer_store_effects_kept _ _ _ _ _ (access_in _ _ _ _ _ _ _ A) E)
            end ].
Qed.

(** An instruction that allocates asks for a positive alignment, and
    writes nothing yet into the memory with the new object. *)
Lemma inst_step_fresh : forall ge fr m i q k,
  inst_step ge fr m i = Some (IFresh q k) ->
  0 < req_align q /\ forall base, kept (allocated m q base) (snd (k base)).
Proof.
  intros ge fr m i q k H. destruct i.
  1: destruct (special_let o) eqn:Es;
       [destruct o; try discriminate Es | rewrite (inst_step_let _ _ _ _ _ _ _ Es) in H].
  all: unfold inst_step, external_call, bind_res, store_out in H; cases H; inversion H; subst.
  all: first
    [ split; [simpl; lia | intros base; simpl; apply kept_refl]
    | match goal with E : op_res _ _ _ _ = Some (OpAlloc _ _) |- _ =>
        destruct (op_res_alloc _ _ _ _ _ _ E) as [Ha Hk] end;
      split; [exact Ha | intros base; specialize (Hk base); simpl;
                         match goal with Hk : kept _ (snd ?t) |- _ => destruct t end;
                         exact Hk] ].
Qed.

(** [or_stuck] gives a next configuration only if it was given one. *)
Lemma or_stuck_next : forall why r c, or_stuck why r = Next c -> r = Some (Next c).
Proof. intros why r c H. destruct r; simpl in H; congruence. Qed.

(** [or_stuck] gives an allocation only if it was given one. *)
Lemma or_stuck_fresh : forall why r q k, or_stuck why r = Fresh q k -> r = Some (Fresh q k).
Proof. intros why r q k H. destruct r; simpl in H; congruence. Qed.

(** When a function call or memory access fails at runtime, helpers wrap
    the outcome in [or_stuck] to stop execution cleanly. If a proof
    assumes a step succeeded, tactic [unstuck] splits on the inner
    result so the proof can inspect the successful transition. *)
Ltac unstuck H :=
  lazymatch type of H with
  | or_stuck _ _ = Next _ => apply or_stuck_next in H; cases H
  | or_stuck _ _ = Fresh _ _ => apply or_stuck_fresh in H; cases H
  | _ => idtac
  end.

(** A return changes memory as [kept] allows: it only ends the
    invocation's locals. *)
Lemma return_step_kept : forall c o c', return_step c o = Next c' -> kept (c_mem c) (c_mem c').
Proof.
  unfold return_step. intros c o c' H. apply or_stuck_next in H.
  cases H; inversion H; subst; simpl.
  match goal with E : invalidate_locals _ _ = Some _ |- _ => exact (invalidate_locals_kept _ _ _ E) end.
Qed.

(** A jump changes memory as [kept] allows: only a return changes it
    at all. *)
Lemma jump_step_kept : forall ge c l j c', jump_step ge c l j = Next c' -> kept (c_mem c) (c_mem c').
Proof.
  unfold jump_step, edge_step. intros ge c l j c' H.
  cases H; unstuck H.
  all: first
    [ match goal with E : return_step _ _ = Next _ |- _ => exact (return_step_kept _ _ _ E) end
    | inversion H; subst;
      first [ exact (kept_refl _)
            | match goal with E : return_step _ _ = Next _ |- _ => exact (return_step_kept _ _ _ E) end ] ].
Qed.

(** A return never allocates. *)
Lemma return_step_not_fresh : forall c o q k, return_step c o <> Fresh q k.
Proof. unfold return_step. intros c o q k H. apply or_stuck_fresh in H. cases H. Qed.

(** A jump never allocates. *)
Lemma jump_step_not_fresh : forall ge c l j q k, jump_step ge c l j <> Fresh q k.
Proof.
  unfold jump_step, edge_step. intros ge c l j q k H. cases H; unstuck H;
    first [exact (return_step_not_fresh _ _ _ _ H) | discriminate H | idtac].
  all: injection H as H; exact (return_step_not_fresh _ _ _ _ H).
Qed.

(** When an instruction runs inside a [[doomed]] frame, it either
    proceeds with its normal memory update or skips the update to trap
    later. Tactic [doomed_continue] closes the [kept] goal in both
    cases. *)
Ltac doomed_continue Hfree :=
  match goal with
  | E : doomed_result _ _ _ _ _ = Some ?od, Hc : fst ?od = IContinue _ _ _ |- _ =>
      destruct (doomed_result_out _ _ _ _ _ _ E) as [Ho | [(e' & l' & Ho) | (o' & Ho)]];
      rewrite Ho in Hc; try discriminate Hc;
      [ subst;
        match goal with E2 : inst_step _ _ _ _ = Some (IContinue _ _ _) |- _ =>
          exact (inst_step_kept _ _ _ _ _ _ _ Hfree E2) end
      | inversion Hc; subst; apply kept_refl ]
  end.

(** Every non-allocating step of [step] preserves [kept] when `c: free`
    satisfies [free_keeps], because writes pass access checks and
    deallocations only end live objects. *)
Lemma step_next_kept : forall ge c c',
  free_keeps (ge_free ge) -> step ge c = Next c' -> kept (c_mem c) (c_mem c').
Proof.
  unfold step, inst_next. intros ge c c' Hfree H.
  cases H; unstuck H.
  all: first
    [ match goal with E : jump_step _ _ _ _ = Next _ |- _ => exact (jump_step_kept _ _ _ _ _ E) end
    | inversion H; subst; simpl; first [exact (kept_refl _) | doomed_continue Hfree] ].
Qed.

(** Every allocating step of [step] requests a positive alignment and
    only writes initial data, such as a variadic argument snapshot, into
    the newly allocated object. *)
Lemma step_fresh_kept : forall ge c q k,
  step ge c = Fresh q k ->
  0 < req_align q /\ forall base, kept (allocated (c_mem c) q base) (c_mem (k base)).
Proof.
  unfold step, inst_next. intros ge c q k H.
  cases H; unstuck H;
    try (exfalso; exact (jump_step_not_fresh _ _ _ _ _ _ H)).
  all: injection H as Hq Hk; subst q k.
  - split; [simpl; lia|]. intros base.
    match goal with Hp : fr_at _ = Snapshot ?xs _ |- _ =>
      exact (snapshot_alloc_kept xs (c_mem c) base) end.
  - match goal with
    | E : doomed_result _ _ _ _ _ = Some ?od, Hc : fst ?od = IFresh _ _ |- _ =>
        destruct (doomed_result_out _ _ _ _ _ _ E) as [Ho | [(e' & l' & Ho) | (o' & Ho)]];
        rewrite Ho in Hc; try discriminate Hc
    end.
    subst.
    match goal with E2 : inst_step _ _ _ _ = Some (IFresh _ _) |- _ =>
      destruct (inst_step_fresh _ _ _ _ _ _ E2) as [Ha Hk] end.
    split; auto. intros base. specialize (Hk base). simpl.
    match goal with Hk : kept _ (snd ?t) |- _ => destruct t as [[e1 l1] m1] end. exact Hk.
Qed.

(** ## The machine of a runtime

    We now combine the program's configuration with the runtime's state
    to define the full [[machine]] transition system. Each step either
    runs a non-allocating program step, asks the runtime for a fresh
    object on an allocation, or lets the runtime act at a safepoint. *)

(** Functor [Machine] instantiates one thread's execution under a
    concrete [[runtime]] R and proves that R stays [[ready]] throughout
    every reachable run. *)
Module Machine (R : Runtime).

(** A machine state [mstate] pairs the program's [[configuration]] with
    the runtime's internal state. *)
Definition mstate : Type := (config * R.state)%type.

(** Helper [with_mem] replaces the memory in configuration c with m
    after a safepoint update. *)
Definition with_mem (c : config) (m : mem) : config :=
  mkConfig (c_frame c) (c_callers c) m (c_fuel c).

(** Helper [taken_target] determines which outgoing edge the jump j of
    frame fr takes, returning None for returns and unreachable blocks. *)
Definition taken_target (ge : genv) (fr : frame) (j : jump) : option target :=
  match j with
  | JGoto t => Some t
  | JBranch v t1 t2 =>
      match value_x ge (fr_env fr) W v with
      | Some (WInt n) => Some (if n =? 0 then t2 else t1)
      | _ => None
      end
  | _ => None
  end.

(** The runtime may act now, in the configuration c: before c's next
    instruction where [R.at_safepoint] holds, or before a
    [[poll|poll edge]] is taken. *)
Definition safepoint_due (ge : genv) (c : config) : bool :=
  match fr_at (c_frame c) with
  | Exec _ (i :: _) _ => R.at_safepoint i
  | Exec _ [] j =>
      match taken_target ge (c_frame c) j with Some (Poll _) => true | _ => false end
  | _ => false
  end.

(** Relation [mstep] defines the three transitions of the combined
    machine. Constructor [mstep_next] runs a non-allocating program
    step, [mstep_alloc] allocates a fresh object from R (trapping if R
    refuses out of memory), and [mstep_safepoint] lets R update memory
    and its own state whenever a safepoint is due. *)
Inductive mstep (ge : genv) : mstate -> mstate -> Prop :=
| mstep_next : forall c c' s,
    step ge c = Next c' ->
    mstep ge (c, s) (c', s)
| mstep_alloc : forall c q k s base s',
    step ge c = Fresh q k ->
    0 <= req_extent q ->
    R.alloc s q = Some (base, s') ->
    mstep ge (c, s) (k base, s')
| mstep_safepoint : forall c s s' m',
    safepoint_due ge c = true ->
    R.safepoint s (c_mem c) s' m' ->
    mstep ge (c, s) (with_mem c m', s').

(** The machine state st' follows st after any number of machine
    steps. *)
Definition mreachable (ge : genv) : mstate -> mstate -> Prop :=
  clos_refl_trans mstate (mstep ge).

(** The runtime is [[ready]] to allocate in the memory: [R.ready] of
    the runtime's state and the configuration's memory. *)
Definition ready_state (st : mstate) : Prop := R.ready (snd st) (c_mem (fst st)).

(** Calling `c: free` in C may empty heap regions without corrupting
    other objects or writing arbitrary bytes. Because R satisfies
    [R.free_lifetime] and [R.retention], its `c: free` implementation
    obeys [free_keeps]. *)
Lemma free_kept : free_keeps R.free.
Proof.
  intros x m r m' H. split.
  - apply lifetime_region_step. eapply R.free_lifetime; eauto.
  - intros a _. destruct (R.retention _ _ _ _ H) as [-> ->]. auto.
Qed.

(** Every machine step preserves [ready_state] when the environment uses
    the runtime's `c: free` function. Non-allocating steps use
    [step_next_kept] and [R.ready_kept], allocations use
    [R.fresh_allocation] and [step_fresh_kept], and safepoints use
    [R.safepoint_ready]. *)
Theorem mstep_ready : forall ge st st',
  ge_free ge = R.free -> mstep ge st st' -> ready_state st -> ready_state st'.
Proof.
  unfold ready_state. intros ge st st' Hge Hs Hr. destruct Hs as [c c' s E | c q k s base s' E He Hal | c s s' m' _ Hsp].
  - simpl in *. eapply R.ready_kept; [exact Hr|]. eapply step_next_kept; [|exact E].
    rewrite Hge. exact free_kept.
  - simpl in *. destruct (step_fresh_kept _ _ _ _ E) as [Ha Hk].
    destruct (R.fresh_allocation _ _ _ _ _ Hr Ha He Hal) as [_ Hr'].
    eapply R.ready_kept; [exact Hr' | apply Hk].
  - simpl in *. eapply R.safepoint_ready; eauto.
Qed.

(** By induction over [mreachable], if the runtime starts ready in state
    st and the environment uses R's `c: free`, then the runtime remains
    ready in every reachable state. *)
Theorem mreachable_ready : forall ge st st',
  ge_free ge = R.free -> mreachable ge st st' -> ready_state st -> ready_state st'.
Proof.
  intros ge st st' Hge H. induction H as [st st' Hs | st | st1 st2 st3 _ IH1 _ IH2]; auto.
  eapply mstep_ready; eauto.
Qed.

(** Fil-C capabilities rely on pointers staying within the 48-bit user
    address space so pointer arithmetic never wraps around. Because the
    runtime stays ready at every reachable state, [R.address_space]
    guarantees that every object ends within 2^48 bytes, discharging
    [objects_fit] in [Coverage](Coverage.v). *)
Corollary mreachable_objects_fit : forall ge st st',
  ge_free ge = R.free -> mreachable ge st st' -> ready_state st ->
  objects_fit (m_regions (c_mem (fst st'))).
Proof.
  intros ge st st' Hge H Hr. apply (R.address_space (snd st')).
  exact (mreachable_ready _ _ _ Hge H Hr).
Qed.

(** Every step taken with a concrete runtime allocator corresponds to
    either a valid abstract execution step or a collector pause. Theorem
    [mstep_refines] proves that from a ready state, each machine step
    either [[refines]] [step_rel] with a [fresh] base address or
    performs a due safepoint action. *)
Theorem mstep_refines : forall ge c s c' s',
  ready_state (c, s) -> mstep ge (c, s) (c', s') ->
  step_rel ge c c' \/
  (safepoint_due ge c = true /\ exists m', c' = with_mem c m' /\ R.safepoint s (c_mem c) s' m').
Proof.
  unfold ready_state. simpl. intros ge c s c' s' Hr Hs.
  inversion Hs as [c0 c1 s0 E | c0 q k s0 base s1 E He Hal | c0 s0 s1 m' Hd Hsp]; subst.
  - left. apply step_next. exact E.
  - left. destruct (step_fresh_kept _ _ _ _ E) as [Ha _].
    destruct (R.fresh_allocation _ _ _ _ _ Hr Ha He Hal) as [Hf _].
    eapply step_fresh; eauto.
  - right. eauto.
Qed.

End Machine.
