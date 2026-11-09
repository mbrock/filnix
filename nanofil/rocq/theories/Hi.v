(** The source-shaped body of tests/c/prog/hi.c at the trusted libc
    boundary. Entry and libc realization are premises, not proofs of
    the native launcher or libc. The body ignores all launcher words. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine ExternalCalls Startup Stdio Shutdown ExternalMachine.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Main's one call has the exact checked IR result and argument syntax. *)
Definition hi_site : call_site :=
  mkCallSite (TAtom "start") (CResult (TAtom "v1") W) (TAtom "puts")
    [Arg P (Tmp (TAtom "v0"))] [] (JRet (Const 0)).

(** The two instructions emitted for hi.c: copy its literal, then call puts. *)
Definition hi_instructions : list inst :=
  [Let (TAtom "v0") P Copy [Global (TAtom "str.10")];
   Call (site_result hi_site) (Global (site_name hi_site)) (site_args hi_site)].

(** The source-shaped main returns an int and declares no parameters or locals. *)
Definition hi_function : func :=
  mkFunc (TAtom "main") (TAtom "export") (RClass W) []
    [mkBlock (TAtom "start") [] hi_instructions (JRet (Const 0))].

(** The module's read-only hello literal includes its NUL. *)
Definition hi_module : Syntax.module :=
  [IFunc hi_function; IData (TAtom "str.10") (LRo (TAtom "local")) 1
    (map (Item Wb) (hello_bytes ++ [0]))].

(** The pointer assigned to the literal by the model's actual module layout. *)
Definition hi_literal : ptr := mkPtr 65552 (Ro 65552).

(** The model's actual initialized module memory, before launcher/libc allocations. *)
Definition hi_memory : mem :=
  match initial_memory hi_module with Some (_, m) => m | None => empty_mem end.

(** Initializing the module succeeds and exposes the expected symbol pointers. *)
Example hi_initial_memory :
  initial_memory hi_module = Some
    ([(TAtom "str.10", hi_literal); (TAtom "main", mkPtr 65536 (Fn (TAtom "main")))], hi_memory).
Proof. reflexivity. Qed.

(** The initialized literal is a checked in-object C string, not an assumed address. *)
Example hi_initialized_literal : c_string hi_memory hi_literal hello_bytes.
Proof. vm_compute. repeat split; try reflexivity; lia. Qed.

(** A configuration in this main, with no caller/local objects or doom. *)
Definition hi_config (m : mem) (fuel : Z) (e : env) (at_ : point) : config :=
  mkConfig (mkFrame hi_function e [] None at_) [] m fuel.

(** Main begins at its actual entry block. *)
Definition hi_entry (m : mem) (fuel : Z) : config :=
  hi_config m fuel [] (Enter (TAtom "start") None).

(** Just before puts, its argument has been copied into v0. *)
Definition hi_call (m : mem) (fuel : Z) : config :=
  hi_config m fuel [(TAtom "v0", WPtr hi_literal)]
    (Exec (TAtom "start") (tl hi_instructions) (JRet (Const 0))).

(** Any launcher's argc/argv/environment produce the same main(void) frame. *)
Theorem hi_ignores_launcher_words : forall argc argv envp m fuel,
  call_frame hi_function (main_arguments argc argv envp) = Some (c_frame (hi_entry m fuel)).
Proof. reflexivity. Qed.

(** Bind this body's own symbols; libc remains unresolved and contract-dispatched. *)
Module Hi (R : Runtime).
Module M := ExternalMachine R.

(** The linked model environment: this module and its initialized global symbols. *)
Definition hi_genv : genv :=
  mkGenv hi_module
    [(TAtom "str.10", hi_literal); (TAtom "main", mkPtr 65536 (Fn (TAtom "main")))] R.free.

(** Main reaches the call by two ordinary core steps, preserving entry memory. *)
Lemma hi_reaches_call : forall (world : Type) m fuel s (w : world) registry,
  fuel <> 0 ->
  M.run registry hi_genv (M.Running (hi_entry m fuel, s) w) []
    (M.Running (hi_call m (fuel - 1), s) w).
Proof.
  intros world m fuel s w registry Hfuel.
  eapply M.run_cons with (trace := []) (tail := [])
    (mid := M.Running (hi_config m (fuel - 1) []
      (Exec (TAtom "start") hi_instructions (JRet (Const 0))), s) w).
  - apply M.step_core. apply M.P.I.RM.mstep_next.
    unfold Semantics.step, hi_entry, hi_config. simpl.
    assert ((fuel =? 0) = false) as E by (apply Z.eqb_neq; assumption).
    rewrite E. reflexivity.
  - eapply M.run_cons with (trace := []) (tail := []).
    + apply M.step_core. apply M.P.I.RM.mstep_next. reflexivity.
    + constructor.
Qed.

(** No native implementation is inferred from the registry: only puts is covered. *)
Definition hi_registry (rep : mem -> stdio_world -> Prop)
    (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop)
    (symbol : name) : option (contract stdio_world) :=
  if name_eqb symbol (TAtom "puts") then Some (puts_contract rep requests) else None.

(** This real call is unresolved, not free, not data, and not doomed. *)
Lemma hi_external_site : forall m fuel,
  external_site hi_genv (hi_call m fuel) hi_site.
Proof. intros m fuel. repeat split; reflexivity. Qed.

(** The caller's obligation is checked independently of any invocation's existence. *)
Theorem hi_call_admissible : forall rep requests m w fuel,
  rep m w -> stdio_ready m w -> c_string m hi_literal hello_bytes ->
  M.admissible (hi_registry rep requests) hi_genv (hi_call m fuel) w hi_site.
Proof.
  intros rep requests m w fuel Hr Hw Hstr.
  exists (puts_contract rep requests), [WPtr hi_literal].
  split; [reflexivity|]. split; [reflexivity|]. split.
  - split; [right; exists (TAtom "v1"); reflexivity|]. exists (Tmp (TAtom "v0")). reflexivity.
  - split; [exact Hr|]. split; [exact Hw|]. exists hi_literal, hello_bytes. auto.
Qed.

(** Every completed puts invocation either returns its W result or exhausts
    resources; it cannot terminate the process or yield a capability panic. *)
Theorem hi_puts_end : forall rep requests s m w trace ending s' m' w',
  M.E.invoke (puts_contract rep requests) (site_result hi_site) (site_args hi_site)
    [WPtr hi_literal] s m w trace ending s' m' w' ->
  (exists n, ending = CallReturn [WInt n]) \/
  (exists why, ending = CallResource why /\ resource_reason why /\ ~ puts_panic why).
Proof.
  intros rep requests s m w trace ending s' m' w' H. destruct H.
  - left. destruct H2 as (p & bytes & acc & tail & n & _ & _ & _ & _ & _ & Hend & _).
    exists n. exact Hend.
  - right. exists why. repeat split; auto. apply puts_no_capability_panic with (rep := rep) (requests := requests). assumption.
Qed.

(** Returned integers bind the source's v1 without consuming main's return. *)
Lemma hi_return_environment : forall rep requests n m fuel,
  external_env (puts_contract rep requests) hi_site [WInt n] (fr_env (c_frame (hi_call m fuel))) =
    Some [(TAtom "v1", WInt (n mod 2 ^ 32)); (TAtom "v0", WPtr hi_literal)].
Proof. reflexivity. Qed.

(** Whatever puts returns, main's next real core instruction returns zero,
    and the retained snapshot is exactly the invocation's final memory. *)
Theorem hi_after_puts_return : forall n m m' fuel,
  main_return_site hi_genv
    (resume_external (hi_call m fuel) hi_site
      [(TAtom "v1", WInt n); (TAtom "v0", WPtr hi_literal)] m') 0.
Proof.
  intros n m m' fuel. exists (TAtom "start"), (Const 0).
  repeat split; reflexivity.
Qed.

(** An actual returning contract call followed by main's return reaches the
    existing machine terminal. No exit observation is appended here. *)
Theorem hi_returning_run : forall rep requests s m w trace n s' m' w' fuel,
  M.E.invoke (puts_contract rep requests) (site_result hi_site) (site_args hi_site)
    [WPtr hi_literal] s m w trace (CallReturn [WInt n]) s' m' w' ->
  let c' := resume_external (hi_call m fuel) hi_site
    [(TAtom "v1", WInt (n mod 2 ^ 32)); (TAtom "v0", WPtr hi_literal)] m' in
  M.run (hi_registry rep requests) hi_genv (M.Running (hi_call m fuel, s) w) trace
    (M.Stopped (CoreEnd (Ret (WInt 0))) (c', s') w').
Proof.
  intros rep requests s m w trace n s' m' w' fuel H. cbv zeta.
  rewrite <- (app_nil_r trace).
  eapply M.run_cons with (trace := trace) (tail := []).
  - eapply M.step_return with (site := hi_site) (values := [WInt n]);
      [apply hi_external_site|reflexivity|reflexivity|exact H|reflexivity].
  - eapply M.run_cons with (trace := []) (tail := []).
    + apply M.step_core_end.
      * intros site Hsite. pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
        discriminate Hstuck.
      * exact (proj1 (main_return_step _ _ _ (hi_after_puts_return (n mod 2 ^ 32) m m' fuel))).
    + constructor.
Qed.

(** Before the call, the literal retains its actual global region and bytes. *)
Definition hi_literal_valid (m : mem) : Prop :=
  object_region 65552 (m_regions m) = Some (mkRegion 65552 65560 GlobalData Live) /\
  string_at m 65552 hello_bytes.

(** This invariant establishes the entire NUL-inclusive argument check. *)
Lemma hi_literal_checked : forall m,
  hi_literal_valid m -> c_string m hi_literal hello_bytes.
Proof.
  intros m [Hreg Hbytes]. split; [|exact Hbytes].
  unfold access_res, cap_access_res. simpl. rewrite Hreg. reflexivity.
Qed.

(** The initialized source module establishes the literal invariant. *)
Example hi_literal_initial : hi_literal_valid hi_memory.
Proof. vm_compute. repeat split; try reflexivity; lia. Qed.

(** A safepoint cannot free GlobalData as though it were a heap object;
    non-moving bytes preserve the first NUL and the literal's contents. *)
Lemma hi_literal_safepoint : forall s m s' m',
  R.safepoint s m s' m' -> hi_literal_valid m -> hi_literal_valid m'.
Proof.
  intros s m s' m' Hsp [Hreg Hbytes].
  assert (Hexists : object_region 65552 (m_regions m') <> None).
  { apply (R.rooting _ _ _ _ Hsp). rewrite Hreg. discriminate. }
  destruct (object_region 65552 (m_regions m')) as [reg'|] eqn:E; [|contradiction].
  destruct (R.safepoint_lifetime _ _ _ _ Hsp _ _ E) as (reg & Hr & [Heq|[Hheap _]]).
  - rewrite Hreg in Hr. injection Hr as <-. subst reg'. split; [exact E|].
    eapply string_at_agree; [|exact Hbytes]. intros a.
    rewrite (R.non_moving _ _ _ _ Hsp). reflexivity.
  - rewrite Hreg in Hr. injection Hr as <-. discriminate Hheap.
Qed.

(** The source's copy point, after its entry block has consumed fuel. *)
Definition hi_copy (m : mem) (fuel : Z) : config :=
  hi_config m fuel [] (Exec (TAtom "start") hi_instructions (JRet (Const 0))).

(** After the call, return zero reads no old literal or argument state. *)
Definition hi_return (m : mem) (fuel : Z) (e : env) : config :=
  hi_config m fuel e (Exec (TAtom "start") [] (JRet (Const 0))).

(** Entry consumes fuel or reports OutOfFuel; neither is a library transition. *)
Lemma hi_entry_step : forall m fuel,
  Semantics.step hi_genv (hi_entry m fuel) =
    if fuel =? 0 then Done OutOfFuel else Next (hi_copy m (fuel - 1)).
Proof. intros m fuel. reflexivity. Qed.

(** The literal copy has no memory effect or dynamic allocation. *)
Lemma hi_copy_step : forall m fuel,
  Semantics.step hi_genv (hi_copy m fuel) = Next (hi_call m fuel).
Proof. reflexivity. Qed.

(** The no-locals return ignores puts' result, even EOF. *)
Lemma hi_return_step : forall m fuel e,
  Semantics.step hi_genv (hi_return m fuel e) = Done (Ret (WInt 0)).
Proof. reflexivity. Qed.

(** There is exactly one external-call syntax at the reached call point. *)
Lemma hi_site_unique : forall m fuel site,
  external_site hi_genv (hi_call m fuel) site -> site = hi_site.
Proof.
  intros m fuel [l r n args rest j] (_ & Hat & _). simpl in Hat.
  inversion Hat. reflexivity.
Qed.

(** The four application phases and permitted terminals; none deletes a
    failed precondition or silently turns it into a native safety result. *)
Section BodySafety.
Variable rep : mem -> stdio_world -> Prop.
Variable requests : list word -> mem -> stdio_world -> Z -> Z -> Prop.

(** This environment/library premise requires the opaque representation and
    writable roots to survive collector safepoints, including permitted
    rewriting of capabilities to already-freed objects. It is not an extra
    Runtime axiom. The literal preservation is proved above. *)
Hypothesis stdio_stable : forall s m s' m' w,
  R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
  rep m' w /\ stdio_ready m' w.

(** Only the facts main still needs are retained before its call; argv is unused. *)
Definition hi_before_call (m : mem) (w : stdio_world) : Prop :=
  rep m w /\ stdio_ready m w /\ hi_literal_valid m.

(** Safepoints retain those facts under the explicit stdio-stability premise. *)
Lemma hi_before_safepoint : forall s m s' m' w,
  R.safepoint s m s' m' -> hi_before_call m w -> hi_before_call m' w.
Proof.
  intros s m s' m' w Hsp [Hr [Hw Hl]].
  destruct (stdio_stable _ _ _ _ _ Hsp Hr Hw) as [Hr' Hw'].
  split; [exact Hr'|]. split; [exact Hw'|]. eapply hi_literal_safepoint; eauto.
Qed.

(** Safe finite application outcomes include resource refusal and fuel exhaustion,
    not unreachable/stuck/unchecked/capability-panic or contract-violation endings. *)
Definition hi_ending (why : ending) : Prop :=
  why = CoreEnd (Ret (WInt 0)) \/ why = CoreEnd OutOfFuel \/
  exists resource, why = CoreEnd (Trap resource) /\ resource_reason resource.

(** The actual configuration shape and the caller obligations at every phase. *)
Inductive hi_body_state : M.state stdio_world -> Prop :=
| hi_body_entry : forall m fuel s w, hi_before_call m w ->
    hi_body_state (M.Running (hi_entry m fuel, s) w)
| hi_body_copy : forall m fuel s w, hi_before_call m w ->
    hi_body_state (M.Running (hi_copy m fuel, s) w)
| hi_body_call : forall m fuel s w, hi_before_call m w ->
    hi_body_state (M.Running (hi_call m fuel, s) w)
| hi_body_return : forall m fuel e s w,
    hi_body_state (M.Running (hi_return m fuel e, s) w)
| hi_body_end : forall why ms w, hi_ending why ->
    hi_body_state (M.Stopped why ms w).

(** Every external call in a body state is this puts, with its obligations proved. *)
Theorem hi_reached_call_admissible : forall c s w site,
  hi_body_state (M.Running (c, s) w) -> external_site hi_genv c site ->
  site = hi_site /\ M.admissible (hi_registry rep requests) hi_genv c w site.
Proof.
  intros c s w site Hinv Hsite. inversion Hinv; subst.
  - pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
    rewrite hi_entry_step in Hstuck. destruct (fuel =? 0); discriminate.
  - pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
    rewrite hi_copy_step in Hstuck. discriminate.
  - pose proof (hi_site_unique _ _ _ Hsite) as ->. split; [reflexivity|].
    match goal with Hpre : hi_before_call _ _ |- _ => destruct Hpre as [Hr [Hw Hl]] end.
    apply hi_call_admissible; auto using hi_literal_checked.
  - pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
    rewrite hi_return_step in Hstuck. discriminate.
Qed.

(** Ordinary core steps retain the exact source phase and its needed facts. *)
Lemma hi_body_core : forall c s c' s' w,
  hi_body_state (M.Running (c, s) w) ->
  M.P.I.RM.mstep hi_genv (c, s) (c', s') -> hi_body_state (M.Running (c', s') w).
Proof.
  intros c s c' s' w Hinv Hcore. inversion Hinv; subst.
  - inversion Hcore as [c0 c1 rt Hnext|c0 q k rt base rt' Hfresh Hsize Ha|c0 rt rt' m' Hdue Hsp]; subst.
    + rewrite hi_entry_step in Hnext. destruct (fuel =? 0); inversion Hnext; subst.
      apply hi_body_copy. assumption.
    + rewrite hi_entry_step in Hfresh. destruct (fuel =? 0); discriminate.
    + discriminate Hdue.
  - inversion Hcore as [c0 c1 rt Hnext|c0 q k rt base rt' Hfresh Hsize Ha|c0 rt rt' m' Hdue Hsp]; subst.
    + rewrite hi_copy_step in Hnext. inversion Hnext; subst. apply hi_body_call. assumption.
    + rewrite hi_copy_step in Hfresh. discriminate.
    + apply hi_body_copy. eapply hi_before_safepoint; eauto.
  - pose proof (external_site_stuck _ _ _ (hi_external_site m fuel)) as Hstuck.
    inversion Hcore as [c0 c1 rt Hnext|c0 q k rt base rt' Hfresh Hsize Ha|c0 rt rt' m' Hdue Hsp]; subst.
    + rewrite Hstuck in Hnext. discriminate.
    + rewrite Hstuck in Hfresh. discriminate.
    + apply hi_body_call. eapply hi_before_safepoint; eauto.
  - inversion Hcore as [c0 c1 rt Hnext|c0 q k rt base rt' Hfresh Hsize Ha|c0 rt rt' m' Hdue Hsp]; subst.
    + rewrite hi_return_step in Hnext. discriminate.
    + rewrite hi_return_step in Hfresh. discriminate.
    + discriminate Hdue.
Qed.

(** An actual core terminal at a body phase is return zero or OutOfFuel. *)
Lemma hi_body_core_end : forall c s w o,
  hi_body_state (M.Running (c, s) w) -> Semantics.step hi_genv c = Done o ->
  hi_ending (CoreEnd o).
Proof.
  intros c s w o Hinv Hdone. inversion Hinv; subst.
  - rewrite hi_entry_step in Hdone. destruct (fuel =? 0); inversion Hdone. right; left; reflexivity.
  - rewrite hi_copy_step in Hdone. discriminate.
  - rewrite (external_site_stuck _ _ _ (hi_external_site m fuel)) in Hdone. discriminate.
  - rewrite hi_return_step in Hdone. inversion Hdone. left; reflexivity.
Qed.

(** Core stuck at a body phase is exactly the external call, never an unhandled
    core error. Missing coverage is still detected by the external rules. *)
Lemma hi_body_stuck_external : forall c s w diagnostic,
  hi_body_state (M.Running (c, s) w) -> Semantics.step hi_genv c = Stuck diagnostic ->
  exists site, external_site hi_genv c site.
Proof.
  intros c s w diagnostic Hinv Hstuck. inversion Hinv; subst.
  - rewrite hi_entry_step in Hstuck. destruct (fuel =? 0); discriminate.
  - rewrite hi_copy_step in Hstuck. discriminate.
  - exists hi_site. apply hi_external_site.
  - rewrite hi_return_step in Hstuck. discriminate.
Qed.

(** No core allocation is hidden in this body. Puts' allocations remain in its contract. *)
Lemma hi_body_no_fresh : forall c s w q k,
  hi_body_state (M.Running (c, s) w) -> Semantics.step hi_genv c <> Fresh q k.
Proof.
  intros c s w q k Hinv Hfresh. inversion Hinv; subst.
  - rewrite hi_entry_step in Hfresh. destruct (fuel =? 0); discriminate.
  - rewrite hi_copy_step in Hfresh. discriminate.
  - rewrite (external_site_stuck _ _ _ (hi_external_site m fuel)) in Hfresh. discriminate.
  - rewrite hi_return_step in Hfresh. discriminate.
Qed.

(** Dispatch and argument evaluation select exactly this contract and literal. *)
Lemma hi_selected_call : forall c s w site spec xs,
  hi_body_state (M.Running (c, s) w) -> external_site hi_genv c site ->
  hi_registry rep requests (site_name site) = Some spec ->
  map_option (arg_x hi_genv (fr_env (c_frame c))) (site_args site) = Some xs ->
  exists m fuel, c = hi_call m fuel /\ site = hi_site /\
    spec = puts_contract rep requests /\ xs = [WPtr hi_literal].
Proof.
  intros c s w site spec xs Hinv Hsite Hreg Hargs.
  destruct (hi_reached_call_admissible _ _ _ _ Hinv Hsite) as [-> _].
  change (Some (puts_contract rep requests) = Some spec) in Hreg. injection Hreg as <-.
  inversion Hinv; subst.
  - pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
    rewrite hi_entry_step in Hstuck. destruct (fuel =? 0); discriminate.
  - pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
    rewrite hi_copy_step in Hstuck. discriminate.
  - change (Some [WPtr hi_literal] = Some xs) in Hargs. injection Hargs as <-.
    exists m, fuel. repeat split; reflexivity.
  - pose proof (external_site_stuck _ _ _ Hsite) as Hstuck.
    rewrite hi_return_step in Hstuck. discriminate.
Qed.

(** Every enabled labelled step retains the body invariant. Bad contracts are not
    filtered out: the concrete call's proved obligations contradict rejection. *)
Theorem hi_body_step : forall st trace st',
  M.step (hi_registry rep requests) hi_genv st trace st' ->
  hi_body_state st -> hi_body_state st'.
Proof.
  intros st trace st' Hstep Hinv.
  destruct Hstep as
    [ms ms' w Hcore
    |c s w o Hnone Hdone
    |c s w why Hnone Hstuck
    |c s w q k Hnone Hfresh Hsize Hrefuse
    |c s w site spec xs trace values s' m' w' e Hsite Hreg Hargs Hcall Henv
    |c s w site spec xs trace status s' m' w' Hsite Hreg Hargs Hcall
    |c s w site spec xs trace why s' m' w' Hsite Hreg Hargs Hcall
    |c s w site why Hsite Hreject
    |c s w site spec xs trace values s' m' w' Hsite Hreg Hargs Hcall Henv].
  - destruct ms as [c s], ms' as [c' s']. eapply hi_body_core; eauto.
  - apply hi_body_end. eapply hi_body_core_end; eauto.
  - destruct (hi_body_stuck_external _ _ _ _ Hinv Hstuck) as [site Hsite].
    exfalso. exact (Hnone site Hsite).
  - exfalso. exact (hi_body_no_fresh _ _ _ _ _ Hinv Hfresh).
  - destruct (hi_selected_call _ _ _ _ _ _ Hinv Hsite Hreg Hargs)
      as (m & fuel & -> & -> & -> & ->).
    destruct (hi_puts_end _ _ _ _ _ _ _ _ _ _ Hcall) as [(n & Hend)|(why & Hend & _)];
      inversion Hend; subst.
    rewrite hi_return_environment in Henv. injection Henv as <-. apply hi_body_return.
  - destruct (hi_selected_call _ _ _ _ _ _ Hinv Hsite Hreg Hargs)
      as (m & fuel & -> & -> & -> & ->).
    destruct (hi_puts_end _ _ _ _ _ _ _ _ _ _ Hcall) as [(n & Hend)|(why & Hend & _)]; discriminate Hend.
  - destruct (hi_selected_call _ _ _ _ _ _ Hinv Hsite Hreg Hargs)
      as (m & fuel & -> & -> & -> & ->).
    destruct (hi_puts_end _ _ _ _ _ _ _ _ _ _ Hcall) as [(n & Hend)|(resource & Hend & Hresource & _)];
      inversion Hend; subst.
    apply hi_body_end. right; right. exists resource. auto.
  - destruct (hi_reached_call_admissible _ _ _ _ Hinv Hsite) as [_ Hadmit].
    exfalso. exact (M.admissible_not_rejected _ _ _ _ _ _ _ Hadmit Hreject).
  - destruct (hi_selected_call _ _ _ _ _ _ Hinv Hsite Hreg Hargs)
      as (m & fuel & -> & -> & -> & ->).
    destruct (hi_puts_end _ _ _ _ _ _ _ _ _ _ Hcall) as [(n & Hend)|(why & Hend & _)];
      inversion Hend; subst.
    rewrite hi_return_environment in Henv. discriminate.
Qed.

(** Safety covers every represented finite run, including arbitrarily many
    permitted safepoints, not just the exhibited two-step path to puts. *)
Theorem hi_body_run : forall st trace st',
  M.run (hi_registry rep requests) hi_genv st trace st' ->
  hi_body_state st -> hi_body_state st'.
Proof.
  intros st trace st' H. induction H; [auto|]. intros Hinv.
  apply IHrun. eapply hi_body_step; eauto.
Qed.

(** Every reached external call meets its obligations, regardless of whether
    libc has a completed invocation there. No coverage-by-empty-relation claim. *)
Theorem hi_all_calls_admissible : forall m fuel s w trace c s' w' site,
  hi_before_call m w ->
  M.run (hi_registry rep requests) hi_genv (M.Running (hi_entry m fuel, s) w) trace
    (M.Running (c, s') w') -> external_site hi_genv c site ->
  M.admissible (hi_registry rep requests) hi_genv c w' site.
Proof.
  intros m fuel s w trace c s' w' site Hpre Hrun Hsite.
  assert (Hinv : hi_body_state (M.Running (c, s') w')).
  { eapply hi_body_run; [exact Hrun|]. apply hi_body_entry. exact Hpre. }
  exact (proj2 (hi_reached_call_admissible _ _ _ _ Hinv Hsite)).
Qed.

(** A stopped application can only have a declared resource/fuel ending or
    return zero, under the explicit entry and environment premises. *)
Theorem hi_finite_safety : forall m fuel s w trace why ms w',
  hi_before_call m w ->
  M.run (hi_registry rep requests) hi_genv (M.Running (hi_entry m fuel, s) w) trace
    (M.Stopped why ms w') -> hi_ending why.
Proof.
  intros m fuel s w trace why ms w' Hpre Hrun.
  assert (Hinv : hi_body_state (M.Stopped why ms w')).
  { eapply hi_body_run; [exact Hrun|]. apply hi_body_entry. exact Hpre. }
  inversion Hinv. assumption.
Qed.

End BodySafety.
End Hi.

(** ## Inhabited interpreter boundary checks
    These represent the selected contracts, not native libc implementations. *)
Module HiChecks.
Module H := Hi InterpRuntime.

(** Retain the actual initialized literal and give the fixture its existing libc root. *)
Definition memory : mem :=
  mkMem (m_bytes hi_memory) (mkRegion 2048 2064 Heap Live :: m_regions hi_memory)
    (m_aux hi_memory).

(** The fixture supplies the body invariant without assuming call admissibility. *)
Lemma entry_pre : H.hi_before_call fixture_rep memory hello_world.
Proof.
  split; [split; reflexivity|]. split.
  - split; [reflexivity|]. constructor; [|constructor].
    split; [simpl; lia|]. exists 2048, (mkRegion 2048 2064 Heap Live).
    repeat split; reflexivity.
  - vm_compute. repeat split; try reflexivity; lia.
Qed.

(** Identity safepoints supply the stability premise for any representation. *)
Lemma interpreter_stdio_stable : forall (rep : mem -> stdio_world -> Prop) s m s' m' w,
  InterpRuntime.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
  rep m' w /\ stdio_ready m' w.
Proof. intros rep s m s' m' w [_ ->]. auto. Qed.

(** EOF may accept any prefix and still lets this exact main return zero. *)
Lemma eof_invocation : forall acc tail,
  hello_bytes ++ [10] = acc ++ tail ->
  H.M.E.invoke (puts_contract fixture_rep fixture_requests)
    (site_result hi_site) (site_args hi_site) [WPtr hi_literal]
    InterpRuntime.start memory hello_world [StreamBytes 1 acc]
    (CallReturn [WInt (2 ^ 32 - 1)]) InterpRuntime.start memory hello_world.
Proof.
  intros acc tail Hb. destruct entry_pre as [Hr [Hw Hl]].
  pose proof (H.hi_literal_checked memory Hl) as Hstr.
  eapply H.M.E.invoke_normal with (born := []).
  - split; [right; exists (TAtom "v1"); reflexivity|]. exists (Tmp (TAtom "v0")). reflexivity.
  - split; [exact Hr|]. split; [exact Hw|]. exists hi_literal, hello_bytes. auto.
  - split; [constructor|]. split; [exact Hr|]. split; [exact Hw|]. split.
    + apply stdio_delegates_refl; [reflexivity|exact (proj2 Hw)].
    + right. exists hi_literal, hello_bytes, acc, tail. repeat split; auto.
  - exists hi_literal, hello_bytes, acc, tail, (2 ^ 32 - 1).
    split; [reflexivity|]. split; [exact Hstr|]. split; [exact Hb|].
    split; [right; reflexivity|]. split; [reflexivity|]. split; [reflexivity|exact Hw].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt (2 ^ 32 - 1)). split; reflexivity.
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** The actual return-zero run after EOF, parameterized by the accepted bytes. *)
Definition eof_main_returns_zero (acc : list Z) : Prop :=
  let c' := resume_external (hi_call memory 9) hi_site
    [(TAtom "v1", WInt (2 ^ 32 - 1)); (TAtom "v0", WPtr hi_literal)] memory in
  H.M.run (H.hi_registry fixture_rep fixture_requests) H.hi_genv
    (H.M.Running (hi_call memory 9, InterpRuntime.start) hello_world)
    [StreamBytes 1 acc]
    (H.M.Stopped (CoreEnd (Ret (WInt 0))) (c', InterpRuntime.start) hello_world).

(** Every allowed EOF prefix can resume the actual source-shaped main. *)
Lemma eof_run : forall acc tail,
  hello_bytes ++ [10] = acc ++ tail -> eof_main_returns_zero acc.
Proof.
  intros acc tail Hb. unfold eof_main_returns_zero.
  apply (H.hi_returning_run fixture_rep fixture_requests InterpRuntime.start memory hello_world
    [StreamBytes 1 acc] (2 ^ 32 - 1) InterpRuntime.start memory hello_world 9).
  exact (eof_invocation acc tail Hb).
Qed.

(** Empty acceptance is not mistaken for a successful full write. *)
Example eof_empty_returns_zero : eof_main_returns_zero [].
Proof. apply (eof_run _ (hello_bytes ++ [10])). reflexivity. Qed.

(** Partial acceptance does not change the C source's return value. *)
Example eof_partial_returns_zero : eof_main_returns_zero [104; 101].
Proof. apply (eof_run _ [108; 108; 111; 10]). reflexivity. Qed.

(** EOF after accepting the full string and newline is also permitted. *)
Example eof_full_returns_zero : eof_main_returns_zero (hello_bytes ++ [10]).
Proof. apply (eof_run _ []). reflexivity. Qed.

(** The safety premise is inhabited and the resulting theorem covers all finite runs. *)
Example interpreter_finite_safety : forall trace why ms w',
  H.M.run (H.hi_registry fixture_rep fixture_requests) H.hi_genv
    (H.M.Running (hi_entry memory 10, InterpRuntime.start) hello_world) trace
    (H.M.Stopped why ms w') -> H.hi_ending why.
Proof.
  intros trace why ms w' Hrun. eapply H.hi_finite_safety;
    [apply interpreter_stdio_stable|exact entry_pre|exact Hrun].
Qed.

(** Without registry coverage the machine rejects even though no invoke exists. *)
Example missing_puts_rejected :
  H.M.step (fun _ => None) H.hi_genv
    (H.M.Running (hi_call memory 9, InterpRuntime.start) hello_world) []
    (H.M.Stopped (ContractViolation (TAtom "puts") MissingContract)
      (hi_call memory 9, InterpRuntime.start) hello_world).
Proof. eapply H.M.step_rejected with (site := hi_site);
  [apply H.hi_external_site|]. constructor. reflexivity. Qed.

(** Freeing the protected fixture root destroys its representation. Such a
    program free is not a collector-safepoint action; the fixture still
    requires the root to be live at entry and throughout the puts contract. *)
Example protected_root_cannot_be_freed :
  let m' := mkMem (m_bytes memory)
    [mkRegion 2048 2048 Heap Freed; mkRegion 65552 65560 GlobalData Live] (m_aux memory) in
  ~ fixture_rep m' hello_world /\ ~ stdio_ready m' hello_world.
Proof.
  split.
  - intros [_ Hreg]. discriminate.
  - intros [_ Hroots]. inversion Hroots as [|root rest Hwrite Hrest]; subst.
    destruct Hwrite as [_ [base [reg [Hcap [Hreg [Hlive Haccess]]]]]].
    simpl in Hcap. injection Hcap as <-. simpl in Hreg. injection Hreg as <-. discriminate.
Qed.

End HiChecks.
