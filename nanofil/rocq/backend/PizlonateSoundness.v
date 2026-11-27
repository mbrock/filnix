(** Proving that the Pizlonator passes static validation is only half of the
    safety story until that verdict connects to the operational semantics.
    [PizlonateProof](PizlonateProof.v) proves that every well-formed unchecked
    core-subset module transforms into a module accepted by [Validate.valid],
    while [Soundness](Soundness.v) proves that every validated checked module
    never reaches an [[unchecked]] runtime outcome under any [Runtime].

    This module joins those two developments into an unconditional end-to-end
    soundness theorem for [Pizlonate.pizlonate_module]. Checked outputs
    delegate directly to [Sound.valid_no_unchecked], while plain-mode outputs
    whose [Validate.module_checked] flag remains false never execute any
    checked instruction or enter a [[doomed]] frame. Instantiating the
    resulting functor with [InterpRuntime] produces closed, zero-axiom
    runtime soundness theorems for both Fil-C and plain modules. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine Validate
  Transport Walk Soundness.
From Backend Require Pizlonate.
From Backend Require Import PizlonateEvidenceProof PizlonateProof.
Import ListNotations.
Open Scope Z_scope.

(** ## Plain modules without checked instructions

    When a validated module leaves [Validate.module_checked] clear, no block
    in any of its functions contains a checked instruction, a raw memory
    access, a raw call, or an ahead check. Every reachable configuration in
    such a module stays undoomed and executes only non-checked instructions,
    leaving `c: free` as the only remaining candidate for an [[unchecked]]
    outcome. *)

(** Predicate [plain_frame] records that a call frame belongs to a defined
    function in module md, is not [[doomed]], and has only non-checked
    instructions left to execute in its current block. *)
Definition plain_frame (md : module) (fr : frame) : Prop :=
  In (IFunc (fr_fn fr)) md /\
  fr_doomed fr = None /\
  match fr_at fr with
  | Exec _ instructions _ => Forall (fun i => checked_inst i = false) instructions
  | _ => True
  end.

(** Predicate [plain_config] extends [plain_frame] across the active frame
    and every suspended caller on the stack. *)
Definition plain_config (md : module) (c : config) : Prop :=
  plain_frame md (c_frame c) /\
  Forall (fun cp => plain_frame md (fst cp)) (c_callers c).

(** When [existsb] returns false over a list, its predicate returns false on
    every member of that list. *)
Local Lemma existsb_false_in {A} (p : A -> bool) (xs : list A) (x : A) :
  existsb p xs = false -> In x xs -> p x = false.
Proof.
  intros H Hin. destruct (p x) eqn:E; [|reflexivity].
  exfalso. assert (Ht : existsb p xs = true) by (apply existsb_exists; eauto).
  congruence.
Qed.

(** Whenever [Validate.module_checked] returns false on module md, every
    instruction in every block of every defined function in md has
    [checked_inst] equal to false. *)
Local Lemma plain_module_no_checked : forall md f b,
  Validate.module_checked md = false -> In (IFunc f) md -> In b (fn_blocks f) ->
  Forall (fun i => checked_inst i = false) (b_insts b).
Proof.
  intros md f b Hmc Hin Hb. unfold Validate.module_checked in Hmc.
  pose proof (existsb_false_in _ _ (IFunc f) Hmc Hin) as Hf. simpl in Hf.
  pose proof (existsb_false_in _ _ b Hf Hb) as Hbi.
  apply orb_false_iff in Hbi as [His _].
  apply Forall_forall. intros i Hi. exact (existsb_false_in _ _ i His Hi).
Qed.

(** Every function returned as [Defined] by [find_direct] appears in the
    module's item list. *)
Local Lemma find_direct_defined : forall n items f,
  find_direct n items = Some (Defined f) -> In (IFunc f) items.
Proof.
  intros n items f. induction items as [|it items IH]; simpl; intros H; [discriminate H|].
  destruct it as [g | | |]; simpl in H; try (destruct (name_eqb _ n); [try discriminate H |]).
  - injection H as <-. left. reflexivity.
  - right. exact (IH H).
  - right. exact (IH H).
  - right. exact (IH H).
  - right. exact (IH H).
Qed.

(** Resolving a direct or aliased function symbol through [find_fn] yields a
    function defined in the global environment's module. *)
Local Lemma find_fn_defined : forall ge n f,
  find_fn ge n = Some (Defined f) -> In (IFunc f) (ge_module ge).
Proof.
  intros ge n f H. unfold find_fn in H.
  destruct (find_direct n (ge_module ge)) as [d|] eqn:Ed.
  - injection H as ->. exact (find_direct_defined _ _ _ Ed).
  - destruct (find_alias n (ge_module ge)) as [t|]; [|discriminate H].
    exact (find_direct_defined _ _ _ H).
Qed.

(** Building an initial callee frame with [call_frame] for a defined function
    produces a [plain_frame] positioned at block entry or argument snapshot
    with no doom reason. *)
Local Lemma plain_call_frame : forall md f xs fr,
  In (IFunc f) md -> call_frame f xs = Some fr -> plain_frame md fr.
Proof.
  intros md f xs fr Hin Hcf. unfold call_frame in Hcf.
  destruct (length xs <? length (fn_params f))%nat; [discriminate Hcf|].
  destruct (fn_blocks f) as [|b bs]; [discriminate Hcf|].
  injection Hcf as <-. unfold plain_frame. simpl.
  destruct (variadic_func f); repeat split; auto.
Qed.

(** An instruction whose [checked_inst] flag is false cannot be a
    [CheckAhead], so [doomed_result] preserves both the instruction outcome
    and the undoomed state. *)
Local Lemma plain_doomed_result : forall ge fr m i out od,
  fr_doomed fr = None -> checked_inst i = false ->
  doomed_result ge fr m i out = Some od -> od = (out, None).
Proof.
  intros ge fr m i out od Hd Hc H.
  assert (Ea : ahead_inst i = false).
  { destruct i as [d k o args | | | | | | | | ]; try reflexivity.
    destruct o; simpl in Hc; try discriminate; destruct k; reflexivity. }
  rewrite (doomed_result_other _ _ _ _ _ Ea), Hd in H.
  destruct out as [| o0 | | |]; try (destruct o0); injection H as <-; reflexivity.
Qed.

(** Any non-checked instruction that evaluates to [ICall] must be a direct
    call resolved inside [ge_module]. *)
Local Lemma plain_inst_step_call : forall ge fr m i g xs pd,
  checked_inst i = false -> inst_step ge fr m i = Some (ICall g xs pd) ->
  In (IFunc g) (ge_module ge).
Proof.
  intros ge fr m i g xs pd Hc H.
  destruct i as [q k o args | | | | r cl args | | x sz | file line | tq];
    simpl in Hc; try discriminate Hc.
  - exfalso.
    destruct (special_let o) eqn:Es.
    + destruct o; simpl in Hc, Es; try discriminate;
        cbn in H; cases H; unfold bind_res in H; cases H.
    + rewrite inst_step_let in H by exact Es. cbv zeta in H.
      destruct (op_arg_classes o k); [|discriminate H]. simpl in H.
      destruct (map2_option _ _ args); [|discriminate H]. simpl in H.
      destruct (op_res o k _ m) as [[rr m' | why | q0 kont] |]; try discriminate H.
      unfold bind_res in H. destruct rr; discriminate H.
  - simpl in H. destruct cl as [n | n | f]; [discriminate H | discriminate H |].
    destruct (map_option _ args) as [ys|]; [|discriminate H]. simpl in H.
    destruct (find_fn ge f) as [[gf | fn]|] eqn:Ef.
    + injection H as <- _ _. exact (find_fn_defined _ _ _ Ef).
    + discriminate H.
    + unfold external_call in H. cases H.
  - simpl in H. cases H.
  - simpl in H. discriminate H.
Qed.

(** Returning from a callee pops the suspended caller frame and preserves
    [plain_config]. *)
Local Lemma plain_return_step : forall md c o c',
  Forall (fun cp => plain_frame md (fst cp)) (c_callers c) ->
  return_step c o = Next c' -> plain_config md c'.
Proof.
  intros md c o c' Hcallers Hstep. unfold return_step, or_stuck in Hstep.
  destruct (invalidate_locals _ _); [|discriminate Hstep]. simpl in Hstep.
  destruct (c_callers c) as [|[caller pd] callers] eqn:Ec; [discriminate Hstep|].
  inversion Hcallers as [| ? ? Htop Hrest]; subst.
  destruct (pd_conv pd) as [[cw kw]|]; [destruct (converted_outcome _ _ _); [|discriminate Hstep] |];
    simpl in Hstep; (destruct (returned_env _ _ _); [|discriminate Hstep]);
    injection Hstep as <-; destruct Htop as (Hcfn & Hcd & Hcat); repeat split; auto.
Qed.

(** Every deterministic [Next] step in a module with [module_checked] false
    preserves [plain_config]. *)
Local Lemma plain_step_next : forall ge md c c',
  ge_module ge = md -> Validate.module_checked md = false ->
  plain_config md c -> step ge c = Next c' -> plain_config md c'.
Proof.
  intros ge md c c' Hge Hmc [[Hin [Hd Hat]] Hcallers] Hstep.
  unfold step in Hstep.
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - destruct xs as [|x xs'].
    + injection Hstep as <-. repeat split; auto.
    + destruct (negb _); discriminate Hstep.
  - destruct (c_fuel c =? 0); [discriminate Hstep|]. unfold or_stuck in Hstep.
    destruct (find_block l (fn_blocks (fr_fn (c_frame c)))) as [b|] eqn:Eb; [|discriminate Hstep].
    simpl in Hstep. destruct (phis_env ge (b_phis b) from (fr_env (c_frame c))) as [e|]; [|discriminate Hstep].
    injection Hstep as <-. repeat split; auto.
    exact (plain_module_no_checked md _ b Hmc Hin (proj1 (find_block_in _ _ _ Eb))).
  - unfold jump_step, edge_step, or_stuck in Hstep.
    rewrite Hd in Hstep. cbv zeta in Hstep.
    destruct j as [t | v t1 t2 | v | vs | | ].
    + destruct t; injection Hstep as <-; repeat split; auto.
    + destruct (value_x ge (fr_env (c_frame c)) W v) as [x|]; [|discriminate Hstep].
      simpl in Hstep. destruct x; [|discriminate Hstep | discriminate Hstep].
      destruct (if n =? 0 then t2 else t1); injection Hstep as <-; repeat split; auto.
    + destruct (fn_ret (fr_fn (c_frame c))); [|discriminate Hstep | discriminate Hstep].
      destruct (value_x _ _ _ v); [|discriminate Hstep]. simpl in Hstep.
      exact (plain_return_step _ _ _ _ Hcallers Hstep).
    + destruct (fn_ret (fr_fn (c_frame c))); [discriminate Hstep | discriminate Hstep |].
      destruct (map2_option _ _ vs); [|discriminate Hstep]. simpl in Hstep.
      exact (plain_return_step _ _ _ _ Hcallers Hstep).
    + exact (plain_return_step _ _ _ _ Hcallers Hstep).
    + discriminate Hstep.
  - rewrite Hd in Hstep. cbv zeta in Hstep.
    inversion Hat as [| ? ? Hi Hrest]; subst.
    destruct (inst_step ge (c_frame c) (c_mem c) i) as [out0|] eqn:Ei; [|discriminate Hstep].
    simpl in Hstep.
    destruct (doomed_result ge (c_frame c) (c_mem c) i out0) as [od|] eqn:Eo; [|discriminate Hstep].
    simpl in Hstep.
    rewrite (plain_doomed_result _ _ _ _ _ _ Hd Hi Eo) in Hstep.
    unfold inst_next in Hstep. simpl in Hstep.
    destruct out0 as [e locals m' | o0 | g xs pd | q k | fn]; try discriminate Hstep.
    + injection Hstep as <-. repeat split; auto.
    + destruct (call_frame g xs) as [callee|] eqn:Ecf; [|discriminate Hstep].
      injection Hstep as <-. split.
      * eapply plain_call_frame; [|exact Ecf].
        exact (plain_inst_step_call _ _ _ _ _ _ _ Hi Ei).
      * constructor; [repeat split; auto | exact Hcallers].
Qed.

(** Returning from a callee never issues a [Fresh] allocation request. *)
Local Lemma return_step_not_fresh : forall c o q k, return_step c o <> Fresh q k.
Proof.
  intros c o q k H. unfold return_step, or_stuck in H.
  destruct (invalidate_locals _ _); [|discriminate H]. simpl in H.
  destruct (c_callers c) as [|[caller pd] callers]; [discriminate H|].
  destruct (pd_conv pd) as [[cw kw]|]; [destruct (converted_outcome _ _ _); [|discriminate H] |];
    simpl in H; destruct (returned_env _ _ _); discriminate H.
Qed.

(** Every [Fresh] allocation continuation preserves [plain_config] for every
    chosen base address. *)
Local Lemma plain_step_fresh : forall ge md c q k base,
  plain_config md c -> step ge c = Fresh q k -> plain_config md (k base).
Proof.
  intros ge md c q k base [[Hin [Hd Hat]] Hcallers] Hstep.
  unfold step in Hstep.
  destruct (fr_at (c_frame c)) as [xs l | l from | l [|i rest] j] eqn:Ha.
  - destruct xs as [|x xs']; [discriminate Hstep|].
    destruct (negb _); [discriminate Hstep|].
    injection Hstep as _ <-. repeat split; auto.
  - destruct (c_fuel c =? 0); [discriminate Hstep|]. unfold or_stuck in Hstep.
    destruct (find_block _ _); [|discriminate Hstep]. simpl in Hstep.
    destruct (phis_env _ _ _ _); discriminate Hstep.
  - unfold jump_step, edge_step, or_stuck in Hstep.
    rewrite Hd in Hstep. cbv zeta in Hstep.
    destruct j as [t | v t1 t2 | v | vs | | ].
    + destruct t; discriminate Hstep.
    + destruct (value_x _ _ _ v) as [x|]; [|discriminate Hstep]. simpl in Hstep.
      destruct x; [|discriminate Hstep | discriminate Hstep].
      destruct (if n =? 0 then t2 else t1); discriminate Hstep.
    + destruct (fn_ret _); [|discriminate Hstep | discriminate Hstep].
      destruct (value_x _ _ _ v); [|discriminate Hstep]. simpl in Hstep.
      exfalso. exact (return_step_not_fresh _ _ _ _ Hstep).
    + destruct (fn_ret _); [discriminate Hstep | discriminate Hstep |].
      destruct (map2_option _ _ vs); [|discriminate Hstep]. simpl in Hstep.
      exfalso. exact (return_step_not_fresh _ _ _ _ Hstep).
    + exfalso. exact (return_step_not_fresh _ _ _ _ Hstep).
    + discriminate Hstep.
  - rewrite Hd in Hstep. cbv zeta in Hstep.
    inversion Hat as [| ? ? Hi Hrest]; subst.
    destruct (inst_step ge (c_frame c) (c_mem c) i) as [out0|] eqn:Ei; [|discriminate Hstep].
    simpl in Hstep.
    destruct (doomed_result ge (c_frame c) (c_mem c) i out0) as [od|] eqn:Eo; [|discriminate Hstep].
    simpl in Hstep.
    rewrite (plain_doomed_result _ _ _ _ _ _ Hd Hi Eo) in Hstep.
    unfold inst_next in Hstep. simpl in Hstep.
    destruct out0 as [e locals m' | o0 | g xs pd | q0 k0 | fn]; try discriminate Hstep.
    + destruct (call_frame g xs); discriminate Hstep.
    + injection Hstep as _ <-. destruct (k0 base) as [[e locals] m']. repeat split; auto.
Qed.

(** ## End-to-end runtime soundness

    The functor [PizlonateSound] combines [PizlonateProof.pizlonate_module_valid]
    with [Sound.valid_no_unchecked] for any runtime satisfying [Runtime].
    Checked outputs discharge directly through [Sound.valid_no_unchecked],
    while plain outputs rely on the [plain_config] invariant above. *)

(** Functor [PizlonateSound] establishes unconditional absence of
    [[unchecked]] runtime outcomes for every validated module and every
    pizlonated core-subset module over an arbitrary [Runtime] R. *)
Module PizlonateSound (R : Runtime).

  Module S := Sound R.

  (** A single machine transition in a plain module preserves [plain_config]. *)
  Local Lemma plain_mstep : forall ge md st st',
    ge_module ge = md -> Validate.module_checked md = false ->
    plain_config md (fst st) -> S.GD.G.H.P.I.RM.mstep ge st st' ->
    plain_config md (fst st').
  Proof.
    intros ge md st st' Hge Hmc Hp Hm.
    destruct Hm as [c c' s E | c q k s base s' E _ _ | c s s' m' _ _]; simpl in *.
    - exact (plain_step_next _ _ _ _ Hge Hmc Hp E).
    - exact (plain_step_fresh _ _ _ _ _ base Hp E).
    - exact Hp.
  Qed.

  (** Multi-step reachability in a plain module preserves [plain_config]. *)
  Local Lemma plain_mreachable : forall ge md st st',
    ge_module ge = md -> Validate.module_checked md = false ->
    plain_config md (fst st) -> S.GD.G.H.P.I.RM.mreachable ge st st' ->
    plain_config md (fst st').
  Proof.
    intros ge md st st' Hge Hmc Hp Hreach.
    induction Hreach as [st st' Hm | st | st1 st2 st3 _ IH1 _ IH2]; auto.
    exact (plain_mstep _ _ _ _ Hge Hmc Hp Hm).
  Qed.

  (** Any module accepted by [Validate.valid] never steps to an [[unchecked]]
      outcome under R, whether [Validate.module_checked] is true or false. *)
  Theorem valid_module_no_unchecked : forall ge md f xs fr m fuel s0 c s w,
    Validate.valid md = Some true -> ge_module ge = md -> ge_free ge = R.free ->
    In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
    S.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
    step ge c <> Done (Unchecked w).
  Proof.
    intros ge md f xs fr m fuel s0 c s w Hv Hge Hfree Hin Hcf H0 Hreach.
    destruct (Validate.module_checked md) eqn:Hmc.
    - exact (S.valid_no_unchecked ge md f xs fr m fuel s0 c s w
               (conj Hv Hmc) Hge Hfree Hin Hcf H0 Hreach).
    - assert (Hp0 : plain_config md (mkConfig fr [] m fuel)).
      { split; [exact (plain_call_frame _ _ _ _ Hin Hcf) | constructor]. }
      pose proof (plain_mreachable ge md (mkConfig fr [] m fuel, s0) (c, s) Hge Hmc Hp0 Hreach) as [[_ [Hd Hat]] _].
      intro E.
      destruct (step_unchecked_inst _ _ _ Hd E) as (l & i & rest & j & Ha & Hi).
      rewrite Ha in Hat. inversion Hat as [| ? ? Hic _]; subst.
      destruct (inst_unchecked_source _ _ _ _ _ Hi)
        as [(q & kc & o & args & -> & Ho) | [(wd & off & v & a & ->) | [(off & v & a & es & ->) |
            [(r & cl & args & ->) | (r & g & args & x & m' & -> & _ & Hf)]]]].
      + destruct o; simpl in Hic, Ho; discriminate.
      + discriminate Hic.
      + discriminate Hic.
      + discriminate Hic.
      + rewrite Hfree in Hf. exact (R.free_checked _ _ _ _ Hf).
  Qed.

  (** Every well-formed unchecked core-subset module that succeeds under
      [Pizlonate.pizlonate_module] decodes to a module whose reachable runs
      under R never step to an [[unchecked]] outcome. *)
  Theorem pizlonate_no_unchecked : forall m_in m_out md ge f xs fr m fuel s0 c s w,
    valid_unchecked_module m_in ->
    Pizlonate.pizlonate_module m_in = Some m_out ->
    Transport.decode_module m_out = Some md ->
    ge_module ge = md -> ge_free ge = R.free ->
    In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
    S.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
    step ge c <> Done (Unchecked w).
  Proof.
    intros m_in m_out md ge f xs fr m fuel s0 c s w Hin Run Dec Hge Hfree Hf Hcf H0 Hreach.
    destruct (pizlonate_module_valid _ _ Hin Run) as (md' & Dec' & Val).
    rewrite Dec in Dec'. injection Dec' as <-.
    exact (valid_module_no_unchecked ge md f xs fr m fuel s0 c s w Val Hge Hfree Hf Hcf H0 Hreach).
  Qed.

  (** Packaging decoding, validation, and runtime safety together, any
      well-formed unchecked module accepted by [Pizlonate.pizlonate_module]
      produces a decoded module that passes [Validate.valid] and never hits
      [[unchecked]] along any run under R. *)
  Theorem pizlonate_output_no_unchecked : forall m_in m_out,
    valid_unchecked_module m_in ->
    Pizlonate.pizlonate_module m_in = Some m_out ->
    exists md,
      Transport.decode_module m_out = Some md /\
      Validate.valid md = Some true /\
      forall ge f xs fr m fuel s0 c s w,
        ge_module ge = md -> ge_free ge = R.free ->
        In (IFunc f) md -> call_frame f xs = Some fr -> R.ready s0 m ->
        S.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
        step ge c <> Done (Unchecked w).
  Proof.
    intros m_in m_out Hin Run.
    destruct (pizlonate_module_valid _ _ Hin Run) as (md & Dec & Val).
    exists md. split; [exact Dec|]. split; [exact Val|].
    intros ge f xs fr m fuel s0 c s w Hge Hfree Hf Hcf H0 Hreach.
    exact (valid_module_no_unchecked ge md f xs fr m fuel s0 c s w Val Hge Hfree Hf Hcf H0 Hreach).
  Qed.

End PizlonateSound.

(** ## The reference interpreter runtime

    Instantiating [PizlonateSound] with [InterpRuntime] yields closed,
    zero-axiom end-to-end theorems for the executable reference interpreter. *)

(** Module [InterpPizlonateSound] instantiates [PizlonateSound] with
    [InterpRuntime]. *)
Module InterpPizlonateSound := PizlonateSound InterpRuntime.

(** Any validated module running under [InterpRuntime] from a ready initial
    memory never steps to an [[unchecked]] outcome. *)
Corollary interp_valid_module_no_unchecked : forall md globals f xs fr m fuel s0 c s w,
  let ge := mkGenv md globals InterpRuntime.free in
  Validate.valid md = Some true -> In (IFunc f) md -> call_frame f xs = Some fr ->
  InterpRuntime.ready s0 m ->
  InterpPizlonateSound.S.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  step ge c <> Done (Unchecked w).
Proof.
  intros md globals f xs fr m fuel s0 c s w ge Val Hf Hcf H0 Hreach.
  exact (InterpPizlonateSound.valid_module_no_unchecked ge md f xs fr m fuel s0 c s w
           Val eq_refl eq_refl Hf Hcf H0 Hreach).
Qed.

(** Any well-formed unchecked core-subset module transformed by
    [Pizlonate.pizlonate_module] decodes to a module that never steps to an
    [[unchecked]] outcome under [InterpRuntime]. *)
Corollary interp_pizlonate_no_unchecked : forall m_in m_out md globals f xs fr m fuel s0 c s w,
  let ge := mkGenv md globals InterpRuntime.free in
  valid_unchecked_module m_in ->
  Pizlonate.pizlonate_module m_in = Some m_out ->
  Transport.decode_module m_out = Some md ->
  In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpPizlonateSound.S.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  step ge c <> Done (Unchecked w).
Proof.
  intros m_in m_out md globals f xs fr m fuel s0 c s w ge Hin Run Dec Hf Hcf H0 Hreach.
  exact (InterpPizlonateSound.pizlonate_no_unchecked m_in m_out md ge f xs fr m fuel s0 c s w
           Hin Run Dec eq_refl eq_refl Hf Hcf H0 Hreach).
Qed.

(** Packaging the whole pipeline for [InterpRuntime], pizlonating a
    well-formed unchecked module yields a decoded module that passes
    [Validate.valid] and never reaches [[unchecked]]. *)
Corollary interp_pizlonate_output_no_unchecked : forall m_in m_out,
  valid_unchecked_module m_in ->
  Pizlonate.pizlonate_module m_in = Some m_out ->
  exists md,
    Transport.decode_module m_out = Some md /\
    Validate.valid md = Some true /\
    forall globals f xs fr m fuel s0 c s w,
      let ge := mkGenv md globals InterpRuntime.free in
      In (IFunc f) md -> call_frame f xs = Some fr -> InterpRuntime.ready s0 m ->
      InterpPizlonateSound.S.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
      step ge c <> Done (Unchecked w).
Proof.
  intros m_in m_out Hin Run.
  destruct (InterpPizlonateSound.pizlonate_output_no_unchecked _ _ Hin Run) as (md & Dec & Val & Safe).
  exists md. split; [exact Dec|]. split; [exact Val|].
  intros globals f xs fr m fuel s0 c s w ge Hf Hcf H0 Hreach.
  exact (Safe ge f xs fr m fuel s0 c s w eq_refl eq_refl Hf Hcf H0 Hreach).
Qed.

(** ## Concrete runtime soundness examples

    The two sanity modules from [PizlonateProof](PizlonateProof.v) exercise
    both branches of [valid_module_no_unchecked]: the Fil-C loop flows
    through [Sound.valid_no_unchecked] with [Validate.module_checked] true,
    and the plain integer function flows through the plain-mode invariant. *)

(** Executing the pizlonated Fil-C loop [example_filc_loop_checked] from any
    ready [InterpRuntime] state never steps to an [[unchecked]] outcome. *)
Example example_filc_loop_no_unchecked : forall globals xs fr m fuel s0 c s w,
  let md := [IFunc example_filc_loop_checked] in
  let ge := mkGenv md globals InterpRuntime.free in
  call_frame example_filc_loop_checked xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpPizlonateSound.S.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  step ge c <> Done (Unchecked w).
Proof.
  intros globals xs fr m fuel s0 c s w md ge Hcf H0 Hreach.
  destruct example_filc_loop_pizlonates_valid as (m_out & Run & Dec & _ & _).
  exact (interp_pizlonate_no_unchecked _ _ md globals example_filc_loop_checked xs fr m fuel s0 c s w
           example_filc_loop_valid_unchecked Run Dec (or_introl eq_refl) Hcf H0 Hreach).
Qed.

(** Executing the pizlonated plain integer function [example_plain_func] from
    any ready [InterpRuntime] state never steps to an [[unchecked]] outcome. *)
Example example_plain_no_unchecked : forall globals xs fr m fuel s0 c s w,
  let md := [IFunc example_plain_func] in
  let ge := mkGenv md globals InterpRuntime.free in
  call_frame example_plain_func xs = Some fr -> InterpRuntime.ready s0 m ->
  InterpPizlonateSound.S.GD.G.H.P.I.RM.mreachable ge (mkConfig fr [] m fuel, s0) (c, s) ->
  step ge c <> Done (Unchecked w).
Proof.
  intros globals xs fr m fuel s0 c s w md ge Hcf H0 Hreach.
  destruct example_plain_pizlonates_valid as (m_out & Run & Dec & _).
  exact (interp_pizlonate_no_unchecked _ _ md globals example_plain_func xs fr m fuel s0 c s w
           example_plain_valid_unchecked Run Dec (or_introl eq_refl) Hcf H0 Hreach).
Qed.
