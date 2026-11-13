(** When a C compiler optimizes away redundant bounds checks, a single
    wrong elimination can turn a safe trap into an out-of-bounds memory
    access. In the [[interpreter]], that failure appears as the
    [[unchecked]] outcome: an instruction that the [[validator]]
    accepted without a full check, but whose runtime justification
    failed.

    This module proves the top-level [[soundness]] theorem
    [valid_no_unchecked]. If the validator accepts a module, then any
    [[run]] starting from a [[ready]] [[runtime]] never steps to an
    [[unchecked]] outcome. Every access that skips a full check either
    lies in bounds or traps just as a checked access would.

    Each kind of unchecked failure has its own safety argument across the
    soundness development. This module combines the separate proofs for
    raw accesses, pointer renewals, conditional guards, doomed frames,
    and `c: free` into one theorem, stopping only at external calls
    other than `c: free` because those calls get stuck in the model.

    ## Decisions

    Guaranteeing that `c: free` never returns an unchecked error is an
    axiom of the runtime module type ([free_checked]), backed by the
    native test `axiom-free.c`.

    Garbage collection safepoints never free live memory objects, so
    cached pointer checks remain valid across every collector pause.
    Because every runtime preserves live regions automatically, the
    top-level theorem needs no extra safepoint hypothesis.

    When an ahead-of-bounds check fails early, the running frame enters
    a doomed state handled separately from healthy execution. Because
    both cases share the same runtime semantics, a small helper converts
    execution traces between the two machine instances. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Walk Steps Invariant Persistence Identity Single Chain Renew Guard Doomed.
Import ListNotations.
Open Scope Z_scope.

(** ## Where unchecked comes from

    To show that no validated run ever fails with [[unchecked]], we
    first classify every operation and instruction that can produce that
    outcome. Only raw accesses, reuse forms, raw calls, and calls to
    `c: free` can stop with an unchecked error; checked operations
    always trap or succeed. *)

(** Predicate [unchecked_op] lists the operations that can return an
    [[unchecked]] result: raw loads, raw atomic compare-and-swaps, and
    the [[reuse|reuse forms]] whose cached evidence may fail if
    unvalidated. *)
Definition unchecked_op (o : op) : bool :=
  match o with
  | RawLoad _ _ | RawLoadPointer _ _ | RawCas _ _ | Renew _ _ _ _ | RenewHull _ _ _ _
  | HalfCheck _ _ _ _ _ | RenewIf _ _ _ _ | CheckLimit _ _ _ _ => true
  | _ => false
  end.

(** Every ordinary checked operation either succeeds or traps cleanly.
    Lemma [op_unchecked_source] proves that only operations marked by
    [unchecked_op] can return [RUnchecked]. *)
Lemma op_unchecked_source : forall o k xs m r m',
  op_res o k xs m = Some (OpRes (RUnchecked r) m') -> unchecked_op o = true.
Proof.
  intros o k xs m r m' H. destruct o; try reflexivity; exfalso.
  all: unfold op_res, op_res_int in H; cases H.
  all: try discriminate H.
  all: try (match goal with E : access_res _ _ _ _ _ _ = Some (RUnchecked _) |- _ =>
              exact (access_res_checked _ _ _ _ _ _ _ E _ eq_refl) end).
  all: try (match goal with E : access_res _ _ _ _ _ _ = Some ?x |- _ =>
              destruct x; cbn [checked_res] in H; try discriminate H;
              exact (access_res_checked _ _ _ _ _ _ _ E _ eq_refl) end).
  all: try (unfold float_integer in H; cases H; fail).
  all: match goal with E : va_arg_res _ _ _ = Some ?p0 |- _ =>
         injection H as H3 _; exact (va_arg_reason _ _ _ _ _ E H3) end.
Qed.

(** Lifting [op_unchecked_source] to whole instructions, an instruction
    stops with [[unchecked]] only when it runs an [unchecked_op], a raw
    store, a raw call, or a call to `c: free` or `c: zgc_free`. *)
Lemma inst_unchecked_source : forall ge fr m i w,
  inst_step ge fr m i = Some (IStop (Unchecked w)) ->
  (exists q k o args, i = Let q k o args /\ unchecked_op o = true) \/
  (exists wd off v a, i = RawStore wd off v a) \/
  (exists off v a es, i = RawStorePointer off v a es) \/
  (exists r cl args, i = RawCall r cl args) \/
  (exists r g args x m', i = Call r (Global g) args /\ is_free_name g = true /\
     ge_free ge x m = Some (RUnchecked w, m')).
Proof.
  intros ge fr m i w H.
  destruct i as [q k o args | d o args lw | wd off v a | off v a es | r cl args | r cl args | x size | file line | tq].
  - left. exists q, k, o, args. split; [reflexivity|].
    destruct (special_let o) eqn:Es.
    + exfalso. destruct o; try discriminate Es; cbn -[access_res function_check_res] in H.
      * destruct k; try discriminate H; destruct args; try discriminate H; cases H;
          unfold bind_res, checked_res in H; cases H.
        match goal with E : access_res _ _ _ _ _ _ = Some ?x |- _ =>
          destruct x; try discriminate; exact (access_res_checked _ _ _ _ _ _ _ E _ eq_refl) end.
      * destruct k; try discriminate H; destruct args as [|v [|]]; try discriminate H; cases H;
          unfold bind_res, checked_res in H; cases H.
        match goal with E : function_check_res _ _ = Some ?x |- _ =>
          destruct x; try discriminate; unfold function_check_res in E; cases E end.
      * destruct k; try discriminate H; destruct args as [|v [|]]; try discriminate H; destruct v; cases H.
        all: discriminate H.
    + rewrite inst_step_let in H by exact Es. cbv zeta in H.
      destruct (op_arg_classes o k) as [cls|]; [|discriminate H]. simpl in H.
      destruct (map2_option _ cls args) as [xs|]; [|discriminate H]. simpl in H.
      destruct (op_res o k xs m) as [[rr m'|why|q0 kont]|] eqn:Eo; try discriminate H.
      unfold bind_res in H. destruct rr; try discriminate H. injection H as <-.
      exact (op_unchecked_source _ _ _ _ _ _ Eo).
  - exfalso. simpl in H. cases H.
  - right. left. do 4 eexists. reflexivity.
  - right. right. left. do 4 eexists. reflexivity.
  - do 4 right. simpl in H. destruct cl as [n | n | g]; try discriminate H.
    destruct (map_option _ args) as [xs|]; [|discriminate H]. simpl in H.
    destruct (find_fn ge g) as [[gf | g']|]; try discriminate H.
    unfold external_call in H. destruct (lookup g (ge_globals ge)); [discriminate H|].
    destruct (negb (is_free_name g)) eqn:En; [discriminate H|].
    apply negb_false_iff in En.
    cases H. injection H as <-. subst. do 5 eexists. split; [reflexivity | split; eassumption].
  - right. right. right. left. do 3 eexists. reflexivity.
  - exfalso. simpl in H. cases H.
  - exfalso. simpl in H. discriminate H.
  - exfalso. simpl in H. discriminate H.
Qed.

(** ## Raw accesses go through a temporary

    The evidence pass tracks bounds facts by temporary variable name, so
    it can only justify a raw memory access whose address operand is a
    [[temporary]]. This section verifies that static validation rejects
    any raw load, store, or compare-and-swap with a non-temporary
    address. *)

(** In any validated function, every raw load, store, or [[cas]] reads
    its base address from a [[temporary]] rather than a global or
    constant. As a result, [raw_access] recognizes every raw memory
    instruction in a checked module. *)
Lemma raw_tmp : forall md f b i,
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) -> In i (b_insts b) ->
  (exists q k t off args, i = Let q k (RawLoad t off) args) \/
  (exists q k off es args, i = Let q k (RawLoadPointer off es) args) \/
  (exists wd off v a, i = RawStore wd off v a) \/
  (exists off v a es, i = RawStorePointer off v a es) \/
  (exists q k t off args, i = Let q k (RawCas t off) args) ->
  raw_access i <> None.
Proof.
  intros md f b i Hmd Hin Hb Hi Hr. destruct (inst_valid _ _ _ _ Hmd Hin Hb Hi) as [cls Hvi].
  destruct Hr as [(q & k & t & off & args & ->) | [(q & k & off & es & args & ->) |
                  [(wd & off & v & a & ->) | [(off & v & a & es & ->) | (q & k & t & off & args & ->)]]]].
  - destruct k; destruct args as [|[n | n | g] [|v2 args]]; simpl in Hvi;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
      try discriminate; simpl; discriminate.
  - destruct k; destruct args as [|[n | n | g] [|v2 args]]; simpl in Hvi;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
      try discriminate; simpl; discriminate.
  - simpl in Hvi. destruct (width_value_ok wd); [|discriminate Hvi].
    apply andb_true_iff in Hvi as [_ Hvi]. destruct a as [n | n | g]; simpl in Hvi; try discriminate Hvi.
    simpl. discriminate.
  - simpl in Hvi. apply andb_true_iff in Hvi as [_ Hvi].
    destruct a as [n | n | g]; simpl in Hvi; try discriminate Hvi. simpl. discriminate.
  - destruct k; destruct args as [|[n | n | g] args]; simpl in Hvi;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
      try discriminate; simpl; discriminate.
Qed.

(** ## Undoomed execution steps

    When a frame has not been marked [[doomed]] by a failed
    [[check_ahead]], an [[unchecked]] error can only come from
    evaluating the next instruction in a block. The lemmas below rule
    out block entries, jumps, and returns as sources of unchecked
    outcomes. *)

(** In a frame fr that is not [[doomed]], `doomed_result/5` keeps an
    instruction's result out as it is, or goes on. *)
Lemma undoomed_result : forall ge fr m i out od,
  fr_doomed fr = None -> doomed_result ge fr m i out = Some od ->
  fst od = out \/ exists e locals m', fst od = IContinue e locals m'.
Proof.
  intros ge fr m i out od Hd H. unfold doomed_result in H. rewrite Hd in H.
  cases H; injection H as <-; simpl; first [left; reflexivity | right; do 3 eexists; reflexivity].
Qed.

(** When a function return finishes the entire program run, [return_step]
    propagates the callee's own return outcome unchanged. *)
Lemma return_step_done : forall c o o', return_step c o = Done o' -> o' = o.
Proof.
  unfold return_step, or_stuck. intros c o o' H. cases H.
  all: repeat match goal with
              | E : Some _ = Some _ |- _ => injection E as E
              | E : ?x = Done _ |- _ => is_var x; subst x
              | E : context [match _ with _ => _ end] |- _ => progress cases E
              end.
  all: congruence.
Qed.

(** When a C function fails an unchecked operation in a healthy frame,
    the failure must come from the instruction itself rather than
    control-flow glue. Lemma [step_unchecked_inst] confirms that block
    entries, jumps, and returns never produce [Unchecked], so only
    [inst_step] can fail that way. *)
Lemma step_unchecked_inst : forall ge c w,
  fr_doomed (c_frame c) = None -> step ge c = Done (Unchecked w) ->
  exists l i rest j, fr_at (c_frame c) = Exec l (i :: rest) j /\
    inst_step ge (c_frame c) (c_mem c) i = Some (IStop (Unchecked w)).
Proof.
  intros ge c w Hd H. unfold step in H.
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - destruct xs; [discriminate H|]. destruct (negb _); discriminate H.
  - destruct (c_fuel c =? 0); [discriminate H|]. unfold or_stuck in H.
    destruct (find_block l _); simpl in H; [|discriminate H].
    destruct (phis_env _ _ _ _); simpl in H; discriminate H.
  - exfalso. unfold jump_step, edge_step, or_stuck in H. rewrite Hd in H. cbv zeta in H. cases H.
    all: repeat match goal with
                | E : Some _ = Some _ |- _ => injection E as E
                | E : return_step _ _ = Done _ |- _ => apply return_step_done in E; discriminate E
                | E : ?x = Done _ |- _ => is_var x; subst x
                | E : context [match _ with _ => _ end] |- _ => progress cases E
                end.
  - rewrite Hd in H. cbv zeta in H.
    destruct (inst_step ge (c_frame c) (c_mem c) i) as [out0|] eqn:Ei; [|discriminate H]. simpl in H.
    destruct (doomed_result ge (c_frame c) (c_mem c) i out0) as [od|] eqn:Eo; [|discriminate H]. simpl in H.
    apply inst_next_done in H.
    destruct (undoomed_result _ _ _ _ _ _ Hd Eo) as [Ho | (e & locals & m' & Ho)]; rewrite H in Ho; [|discriminate Ho].
    exists l, i, rest, j. split; [reflexivity|]. rewrite Ei, Ho. reflexivity.
Qed.

(** ## Along a run

    With the sources of unchecked outcomes classified, we can prove the
    main safety theorem for any runtime R. The proof splits on whether
    the running frame is [[doomed]] or healthy and delegates each case
    to its dedicated run theorem. *)

(** Functor [Sound] proves [valid_no_unchecked] for any concrete
    [[runtime]] R satisfying the [Runtime] interface. *)
Module Sound (R : Runtime).

Module GD := Guards R.
Module D := Doom R.

(** Every transition in the [Guard](Guard.v) machine instance is also a
    valid transition in the [Doomed](Doomed.v) machine instance. *)
Lemma mstep_doom : forall ge st st', GD.G.H.P.I.RM.mstep ge st st' -> D.P.I.RM.mstep ge st st'.
Proof. intros ge st st' H. destruct H; econstructor; eassumption. Qed.

(** A program execution that starts in one machine instance must also be
    recognized by the doomed-frame theorem. By induction over the steps
    of a run, [mreachable_doom] translates multi-step reachability from
    [Guards] to [Doom]. *)
Lemma mreachable_doom : forall ge st st',
  GD.G.H.P.I.RM.mreachable ge st st' -> D.P.I.RM.mreachable ge st st'.
Proof.
  intros ge st st' H. induction H as [st st' H | st | st1 st2 st3 _ IH1 _ IH2].
  - apply rt_step. exact (mstep_doom _ _ _ H).
  - apply rt_refl.
  - exact (rt_trans _ _ _ _ _ IH1 IH2).
Qed.

(** If the [[validator]] accepts a module, no [[run]] starting from a
    [[ready]] runtime ever steps to an [[unchecked]] outcome. Doomed
    frames are discharged by [run_doomed_checked], while undoomed frames
    route each candidate instruction to [run_access_checked],
    [run_reuse_checked], [run_guard_checked], or [R.free_checked]. *)
Theorem valid_no_unchecked : forall ge md f xs fr m fuel s0 c s w,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  step ge c <> Done (Unchecked w).
Proof.
  intros ge md f xs fr m fuel s0 c s w Hmd Hge Hfree Hin Hcf H0 Hreach E.
  destruct (fr_doomed (c_frame c)) as [why|] eqn:Ed.
  - exact (D.run_doomed_checked ge md f xs fr m fuel s0 c s w Hmd Hge Hfree Hin Hcf H0
             (mreachable_doom _ _ _ Hreach) ltac:(rewrite Ed; discriminate) E).
  - destruct (step_unchecked_inst _ _ _ Ed E) as (l & i & rest & j & Ha & Hi).
    pose proof (GD.G.H.S.run_sinv _ _ _ _ _ _ _ _ _ Hmd Hge Hfree Hin Hcf H0 (GD.G.H.mreachable_same _ _ _ Hreach))
      as [[Hsh _] _].
    simpl in Hsh. unfold shaped in Hsh. cbv zeta in Hsh. destruct Hsh as [Hinf Hsh]. rewrite Ha in Hsh.
    destruct Hsh as (_ & b & k & Hb & _ & Hk & _).
    destruct (find_block_in _ _ _ Hb) as [Hbin _].
    assert (Hii : In i (b_insts b)).
    { rewrite <- (firstn_skipn k (b_insts b)). apply in_or_app. right. rewrite <- Hk. left. reflexivity. }
    pose proof (raw_tmp _ _ _ _ Hmd Hinf Hbin Hii) as Hraw.
    pose proof (GD.G.H.run_access_checked ge md f xs fr m fuel s0 c s l i rest j w
                  Hmd Hge Hfree Hin Hcf H0 Hreach Ed Ha) as Hacc.
    destruct (inst_unchecked_source _ _ _ _ _ Hi)
      as [(q & kc & o & args & -> & Ho) | [(wd & off & v & a & ->) | [(off & v & a & es & ->) |
          [(r & cl & args & ->) | (r & g & args & x & m' & -> & _ & Hf)]]]].
    + destruct o; try discriminate Ho.
      all: first
        [ exact (Hacc (or_introl (Hraw ltac:(left; do 5 eexists; reflexivity))) Hi)
        | exact (Hacc (or_introl (Hraw ltac:(right; left; do 5 eexists; reflexivity))) Hi)
        | exact (Hacc (or_introl (Hraw ltac:(do 4 right; do 5 eexists; reflexivity))) Hi)
        | exact (GD.G.run_reuse_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hin Hcf H0
                   Hreach Ed Ha ltac:(left; do 7 eexists; reflexivity) Hi)
        | exact (GD.G.run_reuse_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hin Hcf H0
                   Hreach Ed Ha ltac:(right; left; do 7 eexists; reflexivity) Hi)
        | exact (GD.G.run_reuse_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hin Hcf H0
                   Hreach Ed Ha ltac:(right; right; do 8 eexists; reflexivity) Hi)
        | exact (GD.run_guard_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hin Hcf H0
                   Hreach Ed Ha ltac:(left; do 7 eexists; reflexivity) Hi)
        | exact (GD.run_guard_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hin Hcf H0
                   Hreach Ed Ha ltac:(right; do 7 eexists; reflexivity) Hi) ].
    + exact (Hacc (or_introl (Hraw ltac:(right; right; left; do 4 eexists; reflexivity))) Hi).
    + exact (Hacc (or_introl (Hraw ltac:(right; right; right; left; do 4 eexists; reflexivity))) Hi).
    + exact (Hacc (or_intror (ex_intro _ r (ex_intro _ cl (ex_intro _ args eq_refl)))) Hi).
    + rewrite Hfree in Hf. exact (R.free_checked _ _ _ _ Hf).
Qed.

End Sound.

(** ## The interpreter's runtime

    Finally, we instantiate [Sound] with [InterpRuntime] to obtain a
    closed soundness theorem for the executable reference interpreter.
    No extra runtime hypotheses remain beyond starting from a ready
    memory state. *)

(** Module [InterpSound] instantiates the [Sound] functor with
    [InterpRuntime]. *)
Module InterpSound := Sound InterpRuntime.

(** For any validated module executed under [InterpRuntime] from a ready
    initial state, no reachable step ever produces an [[unchecked]]
    outcome. *)
Corollary interp_valid_no_unchecked : forall md globals f xs fr m fuel s0 c s w,
  let ge := mkGenv md globals InterpRuntime.free in
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpSound.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  step ge c <> Done (Unchecked w).
Proof.
  intros md globals f xs fr m fuel s0 c s w ge Hmd Hin Hcf H0 Hreach.
  exact (InterpSound.valid_no_unchecked ge md f xs fr m fuel s0 c s w
           Hmd eq_refl eq_refl Hin Hcf H0 Hreach).
Qed.
