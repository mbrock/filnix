(** Campaign 3's theorem, [valid_no_unchecked]: if the
    [[validator]] accepts a module, no [[run]] of it that starts
    [[ready]] ever steps to [[unchecked]]
    ([formal.md, Campaign 3](../../docs/formal.md#campaign-3-the-soundness-theorem);
    [rocq.md, No run is unchecked](../../docs/rocq.md#no-run-is-unchecked)).

    The [[interpreter]]'s `unchecked(Reason)` is the outcome a validated
    module must never reach: it marks a [[raw access]] or a
    [[reuse|reuse form]] the validator accepted but whose justification
    was false at run time. So the theorem says the validator's checks
    are sound: every access it lets go unchecked is in fact in bounds,
    or traps as a checked access would. It rests on the
    [[runtime|runtime axioms]] of Runtime.v, on one hypothesis about the
    runtime's [[poll|safepoints]] ([spares]), and on the run starting
    ready; for the interpreter's own runtime only the ready start is
    left ([interp_valid_no_unchecked]). The validator here is
    Validate.v's transcription, which the gates compare with
    `ir:valid_module/1`; external calls other than free are stuck in
    the model, so the theorem says nothing about a run past one. The
    proof is assembled from the run theorems, one per place an
    `unchecked` can come from:

    | Source | Run theorem |
    |---|---|
    | a raw load, store or call | Chain.v's [run_access_checked] |
    | a renew, a renew over a hull, a half check | Renew.v's [run_reuse_checked] |
    | a `renew_if`, a `check_limit` | Guard.v's [run_guard_checked] |
    | a frame a `check_ahead` doomed | Doomed.v's [run_doomed_checked] |
    | the runtime's free | Runtime.v's axiom [free_checked] |

    ## Decisions

    | Decision | Why |
    |---|---|
    | free never answering `unchecked` is the module type's axiom [free_checked] | mbrock's decision, with the native test axiom-free.c |
    | the theorem takes [spares] as the run theorems do | it is false natively at a pointer store's [[aux]] exit; mbrock's decision keeps it a hypothesis ([The runtime's safepoints](../../docs/rocq.md#the-evidence-invariant-over-runs)) |
    | a run is stated over Guard.v's machine instance | the doomed frame's run is carried over to Doomed.v's ([mreachable_doom]) | *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Dominance Walk Steps Invariant Persistence Identity Single Chain Renew Guard Doomed.
Import ListNotations.
Open Scope Z_scope.

(** ## Where unchecked comes from *)

(** The ops o whose result may be [[unchecked]]: a raw load, whose
    access the check before it covers (`raw_res/2`), or a
    [[reuse|reuse form]] (renew, renew over a hull, half check,
    `renew_if`, `check_limit`), whose source or limit may not be the
    one the pass took. *)
Definition unchecked_op (o : op) : bool :=
  match o with
  | RawLoad _ _ | RawLoadPointer _ _ | Renew _ _ _ _ | RenewHull _ _ _ _ | HalfCheck _ _ _ _ _
  | RenewIf _ _ _ _ | CheckLimit _ _ _ _ => true
  | _ => false
  end.

(** No op but an [unchecked_op] answers [[unchecked]] (`kind_res/8`):
    a check answers its access check, which traps or passes. *)
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

(** An instruction i's result is [[unchecked]] only as a `let` of an
    [unchecked_op], a raw store, a raw call, or a call of `free` that
    the runtime's free ([ge_free]) answered so (`inst_result/5`). *)
Lemma inst_unchecked_source : forall ge fr m i w,
  inst_step ge fr m i = Some (IStop (Unchecked w)) ->
  (exists q k o args, i = Let q k o args /\ unchecked_op o = true) \/
  (exists wd off v a, i = RawStore wd off v a) \/
  (exists off v a es, i = RawStorePointer off v a es) \/
  (exists r cl args, i = RawCall r cl args) \/
  (exists r args x m', i = Call r (Global free_name) args /\ ge_free ge x m = Some (RUnchecked w, m')).
Proof.
  intros ge fr m i w H.
  destruct i as [q k o args | d o args lw | wd off v a | off v a es | r cl args | r cl args | x size | file line].
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
    destruct (negb (name_eqb g free_name)) eqn:En; [discriminate H|].
    apply negb_false_iff, name_eqb_true in En. subst g.
    cases H. injection H as <-. subst. do 4 eexists. split; [reflexivity | eassumption].
  - right. right. right. left. do 3 eexists. reflexivity.
  - exfalso. simpl in H. cases H.
  - exfalso. simpl in H. discriminate H.
Qed.

(** ## Raw accesses go through a temporary *)

(** A raw load or store i of a function of a [checked_module] md reads
    its address from a [[temporary]], so the validator saw it as a
    [[raw access]] ([raw_access] is not None, `raw_access/5`):
    `valid_use/3` reads no global at the proof [[class]] `a` and no
    constant at a proof class. *)
Lemma raw_tmp : forall md f b i,
  checked_module md -> In (IFunc f) md -> In b (fn_blocks f) -> In i (b_insts b) ->
  (exists q k t off args, i = Let q k (RawLoad t off) args) \/
  (exists q k off es args, i = Let q k (RawLoadPointer off es) args) \/
  (exists wd off v a, i = RawStore wd off v a) \/
  (exists off v a es, i = RawStorePointer off v a es) ->
  raw_access i <> None.
Proof.
  intros md f b i Hmd Hin Hb Hi Hr. destruct (inst_valid _ _ _ _ Hmd Hin Hb Hi) as [cls Hvi].
  destruct Hr as [(q & k & t & off & args & ->) | [(q & k & off & es & args & ->) |
                  [(wd & off & v & a & ->) | (off & v & a & es & ->)]]].
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
Qed.

(** ## A step that is not doomed *)

(** In a frame fr that is not [[doomed]], `doomed_result/5` keeps an
    instruction's result out as it is, or goes on. *)
Lemma undoomed_result : forall ge fr m i out od,
  fr_doomed fr = None -> doomed_result ge fr m i out = Some od ->
  fst od = out \/ exists e locals m', fst od = IContinue e locals m'.
Proof.
  intros ge fr m i out od Hd H. unfold doomed_result in H. rewrite Hd in H.
  cases H; injection H as <-; simpl; first [left; reflexivity | right; do 3 eexists; reflexivity].
Qed.

(** A return that ends the run ends it with the outcome o it returns,
    not another (`call_outcome_result/5`). *)
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

(** A frame that is not [[doomed]] steps to [[unchecked]] only where its
    next instruction i's result is: a block's entry, a jump and a return
    give no such outcome (`block_outcome/7`, `jump_outcome/7`). *)
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

(** ## Along a run *)

(** The theorem for any [[runtime]] R that meets Runtime.v's module
    type. *)
Module Sound (R : Runtime).

Module GD := Guards R.
Module D := Doom R.

(** A step of Guard.v's [[machine]] instance, the one Chain.v's,
    Renew.v's and Guard.v's run theorems share, is a step of Doomed.v's. *)
Lemma mstep_doom : forall ge st st', GD.G.H.P.I.RM.mstep ge st st' -> D.P.I.RM.mstep ge st st'.
Proof. intros ge st st' H. destruct H; econstructor; eassumption. Qed.

(** A run of Guard.v's machine instance is a run of Doomed.v's, so
    [run_doomed_checked] applies to it. *)
Lemma mreachable_doom : forall ge st st',
  GD.G.H.P.I.RM.mreachable ge st st' -> D.P.I.RM.mreachable ge st st'.
Proof.
  intros ge st st' H. induction H as [st st' H | st | st1 st2 st3 _ IH1 _ IH2].
  - apply rt_step. exact (mstep_doom _ _ _ H).
  - apply rt_refl.
  - exact (rt_trans _ _ _ _ _ IH1 IH2).
Qed.

(** Soundness of checking. Take a module md the [[validator]] accepts
    ([checked_module]), a function f of it called with arguments xs,
    and a memory m where the [[runtime]] R is [[ready]]. In every state c
    a [[run]] reaches from that call, the next [[step]] is not
    [[unchecked]]: every access the checked code did not check was in
    bounds or trapped as a check would. It rests on Runtime.v's axioms
    (among them [free_checked]: free never answers unchecked) and on one
    hypothesis, that the runtime [spares] the pass's facts at
    [[poll|safepoints]] (see
    [The evidence invariant over runs](../../docs/rocq.md#the-evidence-invariant-over-runs)).
    The proof sends a doomed frame to [run_doomed_checked], and any
    other to the run theorem for its instruction. *)
Theorem valid_no_unchecked : forall ge md f xs fr m fuel s0 c s w,
  checked_module md -> ge_module ge = md -> ge_free ge = R.free ->
  GD.G.H.P.I.spares ge md ->
  In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
  GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  step ge c <> Done (Unchecked w).
Proof.
  intros ge md f xs fr m fuel s0 c s w Hmd Hge Hfree Hsp Hin Hcf H0 Hreach E.
  destruct (fr_doomed (c_frame c)) as [why|] eqn:Ed.
  - exact (D.run_doomed_checked ge md f xs fr m fuel s0 c s w Hmd Hge Hfree Hsp Hin Hcf H0
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
                  Hmd Hge Hfree Hsp Hin Hcf H0 Hreach Ed Ha) as Hacc.
    destruct (inst_unchecked_source _ _ _ _ _ Hi)
      as [(q & kc & o & args & -> & Ho) | [(wd & off & v & a & ->) | [(off & v & a & es & ->) |
          [(r & cl & args & ->) | (r & args & x & m' & -> & Hf)]]]].
    + destruct o; try discriminate Ho.
      all: first
        [ exact (Hacc (or_introl (Hraw ltac:(left; do 5 eexists; reflexivity))) Hi)
        | exact (Hacc (or_introl (Hraw ltac:(right; left; do 5 eexists; reflexivity))) Hi)
        | exact (GD.G.run_reuse_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hsp Hin Hcf H0
                   Hreach Ed Ha ltac:(left; do 7 eexists; reflexivity) Hi)
        | exact (GD.G.run_reuse_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hsp Hin Hcf H0
                   Hreach Ed Ha ltac:(right; left; do 7 eexists; reflexivity) Hi)
        | exact (GD.G.run_reuse_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hsp Hin Hcf H0
                   Hreach Ed Ha ltac:(right; right; do 8 eexists; reflexivity) Hi)
        | exact (GD.run_guard_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hsp Hin Hcf H0
                   Hreach Ed Ha ltac:(left; do 7 eexists; reflexivity) Hi)
        | exact (GD.run_guard_checked ge md f xs fr m fuel s0 c s l _ rest j w Hmd Hge Hfree Hsp Hin Hcf H0
                   Hreach Ed Ha ltac:(right; do 7 eexists; reflexivity) Hi) ].
    + exact (Hacc (or_introl (Hraw ltac:(right; right; left; do 4 eexists; reflexivity))) Hi).
    + exact (Hacc (or_introl (Hraw ltac:(right; right; right; do 4 eexists; reflexivity))) Hi).
    + exact (Hacc (or_intror (ex_intro _ r (ex_intro _ cl (ex_intro _ args eq_refl)))) Hi).
    + rewrite Hfree in Hf. exact (R.free_checked _ _ _ _ Hf).
Qed.

End Sound.

(** ## The interpreter's runtime *)

(** The theorem for the [[interpreter]]'s runtime. *)
Module InterpSound := Sound InterpRuntime.

(** [valid_no_unchecked] for the [[interpreter]]'s runtime, which
    changes nothing at a safepoint ([interp_spares]): in every state of
    a run of a checked module's function that starts ready, no step is
    [[unchecked]]. No hypothesis remains but the ready start;
    Print Assumptions reports it closed. *)
Corollary interp_valid_no_unchecked : forall md globals f xs fr m fuel s0 c s w,
  let ge := mkGenv md globals InterpRuntime.free in
  checked_module md -> In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpSound.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  step ge c <> Done (Unchecked w).
Proof.
  intros md globals f xs fr m fuel s0 c s w ge Hmd Hin Hcf H0 Hreach.
  exact (InterpSound.valid_no_unchecked ge md f xs fr m fuel s0 c s w
           Hmd eq_refl eq_refl (interp_spares ge md) Hin Hcf H0 Hreach).
Qed.
