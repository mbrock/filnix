(** These retained fixtures check ExternalMachine with the earlier libc-contract
    examples. The live foundation does not depend on these fixtures. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Values Memory Runtime Ops Semantics Machine
  Validate Identity ExternalCalls LibcCalls LibcCallFixtures Walk Steps Invariant Persistence Single.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

From Nanofil Require Import ExternalMachine.

(** ## Public transition regressions

    These are abstract contract fixtures, not native libc instances.
    The argument is genuinely evaluated from a temporary; the separate
    caller, local object, remaining instruction and fuel expose accidental
    whole-frame replacement or return-from-the-caller behavior. *)

(** The regressions, over the interpreter's runtime. *)
Module ExternalMachineChecks.
Module M := ExternalMachine InterpRuntime.

(** The [[temporary]] holding the call's argument. *)
Definition arg_name : name := TAtom "input".
(** The temporary a scalar or tuple result binds. *)
Definition result_name : name := TAtom "answer".
(** The one [[block]]'s label. *)
Definition label : name := TAtom "entry".
(** The called name, unresolved in the test module. *)
Definition symbol : name := TAtom "puts".
(** The call's one argument: the temporary input as a pointer. *)
Definition args : list arg := [Arg P (Tmp arg_name)].
(** The instruction after the call, a source location. *)
Definition rest : list inst := [Loc (TAtom "hi.c") 3].
(** A main of one block: the call with result r, then [rest], then
    return. *)
Definition test_fn (r : call_result) : func :=
  mkFunc (TAtom "main") (TAtom "export") RVoid [(P, arg_name)]
    [mkBlock label [] (Call r (Global symbol) args :: rest) JRetVoid].
(** The environment at the call: input is [hello_ptr], and an unrelated
    temporary keep must survive the call. *)
Definition test_env : env := [(arg_name, WPtr hello_ptr); (TAtom "keep", WInt 91)].
(** One local object, at 3072. *)
Definition test_locals : list (name * option Z) := [(TAtom "local", Some 3072)].
(** A separate waiting caller frame. *)
Definition test_caller : frame := mkFrame (test_fn CVoid) [] [] None (Exec label [] JRetVoid).
(** The call stack: [test_caller], waiting for a void result. *)
Definition test_callers : list (frame * pending) := [(test_caller, mkPending CVoid None)].
(** The configuration at the call with result r, over [hello_mem], with
    41 units of [[fuel]]. *)
Definition test_config (r : call_result) : config :=
  mkConfig (mkFrame (test_fn r) test_env test_locals None
    (Exec label (Call r (Global symbol) args :: rest) JRetVoid)) test_callers hello_mem 41.
(** The [call_site] of [test_config] r. *)
Definition test_site (r : call_result) : call_site := mkCallSite label r symbol args rest JRetVoid.
(** A global environment with no functions or data, so symbol is
    unresolved. *)
Definition test_ge : genv := mkGenv [] [] InterpRuntime.free.
(** A registry giving every name the contract spec. *)
Definition registry {world : Type} (spec : contract world) : name -> option (contract world) := fun _ => Some spec.

(** The test configuration is at an [external_site], whatever the call's
    result. *)
Lemma test_external : forall r, external_site test_ge (test_config r) (test_site r).
Proof. intros r. repeat split; reflexivity. Qed.

(** The call of puts on hello from the test site completes like
    [hello_return], for a void or word result. *)
Lemma puts_invocation : forall r n accepted tail,
  (r = CVoid \/ exists d, r = CResult d W) ->
  hello_bytes ++ [10] = accepted ++ tail ->
  ((tail = [] /\ n = 0) \/ n = 2 ^ 32 - 1) ->
  M.E.invoke (puts_contract fixture_rep fixture_requests) r args [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world [StreamBytes 1 accepted] (CallReturn [WInt n])
    InterpRuntime.start hello_mem hello_world.
Proof.
  intros r n accepted tail Hr Hb Hn. eapply M.E.invoke_normal with (born := []).
  - split; [exact Hr|]. exists (Tmp arg_name). reflexivity.
  - exact hello_pre.
  - split; [constructor|]. split; [split; reflexivity|]. split; [exact hello_stdio|]. split.
    + apply stdio_delegates_refl; [reflexivity|exact (proj2 hello_stdio)].
    + right. exists hello_ptr, hello_bytes, accepted, tail. repeat split; auto using hello_string.
  - exists hello_ptr, hello_bytes, accepted, tail, n.
    split; [reflexivity|]. split; [exact hello_string|]. split; [exact Hb|]. split.
    + destruct Hn as [[Ht ->] | ->];
        [left; split; [exact Ht|change (0 <= 0 < 2147483648); lia] | right; reflexivity].
    + split; [reflexivity|]. split; [reflexivity|exact hello_stdio].
  - intros why H. discriminate H.
  - intros values H. injection H as <-. split.
    + exists (WInt n). split; [reflexivity|]. destruct Hn as [[_ ->] | ->]; reflexivity.
    + constructor; [exact I|constructor].
  - intros status H. discriminate H.
Qed.

(** A successful puts step emits its one event and resumes the same
    frame at [rest] with answer bound to 0, the same locals, callers,
    memory and fuel. *)
Example puts_resumes_exactly :
  M.step (registry (puts_contract fixture_rep fixture_requests)) test_ge
    (M.Running (test_config (CResult result_name W), InterpRuntime.start) hello_world)
    [StreamBytes 1 [104; 101; 108; 108; 111; 10]]
    (M.Running (mkConfig (mkFrame (test_fn (CResult result_name W))
      ((result_name, WInt 0) :: test_env) test_locals None (Exec label rest JRetVoid))
      test_callers hello_mem 41, InterpRuntime.start) hello_world).
Proof.
  eapply M.step_return with (site := test_site (CResult result_name W)) (values := [WInt 0]);
    [apply test_external | reflexivity | reflexivity | | reflexivity].
  apply (puts_invocation _ _ _ []); [right; eexists; reflexivity | reflexivity | left; auto].
Qed.

(** A partial EOF puts with a discarded result also resumes, with the
    environment unchanged. *)
Example puts_eof_resumes :
  M.step (registry (puts_contract fixture_rep fixture_requests)) test_ge
    (M.Running (test_config CVoid, InterpRuntime.start) hello_world)
    [StreamBytes 1 [104; 101]]
    (M.Running (resume_external (test_config CVoid) (test_site CVoid) test_env hello_mem,
      InterpRuntime.start) hello_world).
Proof.
  eapply M.step_return with (site := test_site CVoid) (values := [WInt (2 ^ 32 - 1)]);
    [apply test_external | reflexivity | reflexivity | | reflexivity].
  apply (puts_invocation _ _ _ [108; 108; 111; 10]); [left; reflexivity | reflexivity | right; reflexivity].
Qed.

(** A contract with return type ty whose ABI premise, precondition and
    postcondition are the given propositions abi, pre and behavior,
    which may write only [stdout_span], requests no allocation and
    accepts any prefix. Such deliberately independent propositions
    expose rejection even when no behavior exists. *)
Definition test_contract (ty : ret_type) (abi pre behavior : Prop) : contract unit :=
  mkContract unit ty (fun _ _ => abi) (fun _ _ _ => pre)
    (fun _ _ _ => []) (fun _ _ _ => [stdout_span]) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ => behavior) (fun _ => False) (fun _ => False).

(** An always-true test contract may return, changing nothing, any
    values of its [return_shape] whose capabilities need no source or
    born object ([word_authority]). *)
Lemma test_return : forall ty r values,
  return_shape ty values -> Forall (word_authority [] [] hello_mem) values ->
  M.E.invoke (test_contract ty True True True) r args [WPtr hello_ptr]
    InterpRuntime.start hello_mem tt [] (CallReturn values) InterpRuntime.start hello_mem tt.
Proof.
  intros ty r values Hshape Hauth. eapply M.E.invoke_normal with (born := []);
    try exact I; try (intros x H; discriminate H).
  - split; [constructor|exact I].
  - intros xs H. injection H as <-. auto.
Qed.

(** Such a return is a silent machine step to [resume_external] with the
    environment [external_env] gives. *)
Lemma return_channel : forall ty r values e,
  return_shape ty values -> Forall (word_authority [] [] hello_mem) values ->
  external_env (test_contract ty True True True) (test_site r) values test_env = Some e ->
  M.step (registry (test_contract ty True True True)) test_ge
    (M.Running (test_config r, InterpRuntime.start) tt) []
    (M.Running (resume_external (test_config r) (test_site r) e hello_mem, InterpRuntime.start) tt).
Proof.
  intros ty r values e Hs Ha He. eapply M.step_return with (site := test_site r) (values := values);
    [apply test_external | reflexivity | reflexivity | exact (test_return ty r values Hs Ha) | exact He].
Qed.

(** Void, empty-tuple and one-element-tuple returns each use their own
    channel. *)
Example void_and_tuple_channels :
  M.step (registry (test_contract RVoid True True True)) test_ge
    (M.Running (test_config CVoid, InterpRuntime.start) tt) []
    (M.Running (resume_external (test_config CVoid) (test_site CVoid) test_env hello_mem, InterpRuntime.start) tt) /\
  M.step (registry (test_contract (RTuple []) True True True)) test_ge
    (M.Running (test_config (CTuple []), InterpRuntime.start) tt) []
    (M.Running (resume_external (test_config (CTuple [])) (test_site (CTuple [])) test_env hello_mem, InterpRuntime.start) tt) /\
  M.step (registry (test_contract (RTuple [W]) True True True)) test_ge
    (M.Running (test_config (CTuple [(result_name, W)]), InterpRuntime.start) tt) []
    (M.Running (resume_external (test_config (CTuple [(result_name, W)])) (test_site (CTuple [(result_name, W)]))
      ((result_name, WInt 7) :: test_env) hello_mem, InterpRuntime.start) tt).
Proof.
  split; [eapply return_channel with (values := []); repeat constructor |].
  split; [eapply return_channel with (values := []); repeat constructor |].
  eapply return_channel with (values := [WInt 7]); repeat constructor.
Qed.

(** A call with no registered contract stops with [MissingContract]. *)
Example missing_contract_rejects :
  M.step (fun _ => @None (contract unit)) test_ge (M.Running (test_config CVoid, InterpRuntime.start) tt) []
    (M.Stopped (ContractViolation symbol MissingContract) (test_config CVoid, InterpRuntime.start) tt).
Proof. eapply M.step_rejected with (site := test_site CVoid); [apply test_external | constructor; reflexivity]. Qed.

(** A false precondition is rejected even when the contract has no
    behavior at all. *)
Example empty_behavior_bad_pre_rejects :
  M.step (registry (test_contract RVoid True False False)) test_ge
    (M.Running (test_config CVoid, InterpRuntime.start) tt) []
    (M.Stopped (ContractViolation symbol BadPrecondition) (test_config CVoid, InterpRuntime.start) tt).
Proof.
  eapply M.step_rejected with (site := test_site CVoid); [apply test_external|]. eapply M.reject_pre;
    [reflexivity | reflexivity | exact I | exact (fun H => H)].
Qed.

(** A call can be [admissible] yet have no completed invocation:
    admissibility does not promise behavior. *)
Example admitted_empty_behavior :
  M.admissible (registry (test_contract RVoid True True False)) test_ge (test_config CVoid) tt (test_site CVoid) /\
  ~ exists trace result s' m' w', M.E.invoke (test_contract RVoid True True False) CVoid args [WPtr hello_ptr]
    InterpRuntime.start hello_mem tt trace result s' m' w'.
Proof.
  split; [eexists; eexists; repeat split; reflexivity || exact I|].
  intros (trace & result & s' & m' & w' & H). inversion H; assumption.
Qed.

(** A one-word tuple returned to a scalar result stops with [BadReturn],
    keeping the call's memory. *)
Example incompatible_return_rejects :
  M.step (registry (test_contract (RTuple [W]) True True True)) test_ge
    (M.Running (test_config (CResult result_name W), InterpRuntime.start) tt) []
    (M.Stopped (ContractViolation symbol BadReturn)
      (M.P.I.RM.with_mem (test_config (CResult result_name W)) (store_bytes hello_mem 2048 1 1), InterpRuntime.start) tt).
Proof.
  eapply M.step_bad_return with (site := test_site (CResult result_name W)) (values := [WInt 7]);
    [apply test_external | reflexivity | reflexivity | | reflexivity].
  eapply M.E.invoke_normal with (born := []); try exact I; try (intros x H; discriminate H).
  - split; [|exact I]. eapply M.E.effects_local; [apply local_store_bytes|constructor].
    intros b Hb. left. exists stdout_span. split; [left; reflexivity|].
    split; [exact (Forall_inv (proj2 hello_stdio))|]. unfold span_contains. simpl. lia.
  - intros values H. injection H as <-. split; repeat constructor.
Qed.

(** A two-word tuple binds both names, and a void result discards it. *)
Example tuple_multiword_and_discard :
  M.step (registry (test_contract (RTuple [W; L]) True True True)) test_ge
    (M.Running (test_config (CTuple [(result_name, W); (TAtom "second", L)]), InterpRuntime.start) tt) []
    (M.Running (resume_external (test_config (CTuple [(result_name, W); (TAtom "second", L)]))
      (test_site (CTuple [(result_name, W); (TAtom "second", L)]))
      ((TAtom "second", WInt 11) :: (result_name, WInt 3) :: test_env) hello_mem, InterpRuntime.start) tt) /\
  M.step (registry (test_contract (RTuple [W; L]) True True True)) test_ge
    (M.Running (test_config CVoid, InterpRuntime.start) tt) []
    (M.Running (resume_external (test_config CVoid) (test_site CVoid) test_env hello_mem, InterpRuntime.start) tt).
Proof. split; eapply return_channel with (values := [WInt 3; WInt 11]); repeat constructor. Qed.

(** A false ABI premise is rejected as [BadABI], without behavior. *)
Example bad_abi_rejects_without_behavior :
  M.step (registry (test_contract RVoid False True False)) test_ge
    (M.Running (test_config CVoid, InterpRuntime.start) tt) []
    (M.Stopped (ContractViolation symbol BadABI) (test_config CVoid, InterpRuntime.start) tt).
Proof.
  eapply M.step_rejected with (site := test_site CVoid); [apply test_external|].
  eapply M.reject_abi; [reflexivity | reflexivity | exact (fun H => H)].
Qed.

(** The test configuration with an empty environment, so the argument
    input has no value. *)
Definition missing_arg_config : config :=
  mkConfig (mkFrame (test_fn CVoid) [] test_locals None (fr_at (c_frame (test_config CVoid))))
    test_callers hello_mem 41.

(** An argument that does not evaluate is rejected as [BadArguments]. *)
Example argument_evaluation_rejects :
  M.step (registry (puts_contract fixture_rep fixture_requests)) test_ge
    (M.Running (missing_arg_config, InterpRuntime.start) hello_world) []
    (M.Stopped (ContractViolation symbol BadArguments) (missing_arg_config, InterpRuntime.start) hello_world).
Proof.
  eapply M.step_rejected with (site := test_site CVoid); [repeat split; reflexivity|].
  eapply M.reject_arguments; reflexivity.
Qed.

(** Even at a call that would be rejected, the core machine may take a
    safepoint ([[poll]]) step first. *)
Example invalid_site_can_poll :
  M.step (registry (test_contract RVoid True False False)) test_ge
    (M.Running (test_config CVoid, InterpRuntime.start) tt) []
    (M.Running (test_config CVoid, InterpRuntime.start) tt).
Proof.
  apply M.step_core. change (M.P.I.RM.mstep test_ge (test_config CVoid, InterpRuntime.start)
    (M.P.I.RM.with_mem (test_config CVoid) hello_mem, InterpRuntime.start)).
  eapply M.P.I.RM.mstep_safepoint; [reflexivity|split; reflexivity].
Qed.

(** The test configuration with its frame [[doomed]] to trap out of
    bounds. *)
Definition doomed_config : config :=
  mkConfig (mkFrame (test_fn CVoid) test_env test_locals (Some OutOfBounds)
    (fr_at (c_frame (test_config CVoid)))) test_callers hello_mem 41.

(** A doomed frame's call is not external: the core ends it as
    [Unchecked] ([Ahead] out of bounds). *)
Example doomed_call_stays_core :
  M.step (registry (puts_contract fixture_rep fixture_requests)) test_ge
    (M.Running (doomed_config, InterpRuntime.start) hello_world) []
    (M.Stopped (CoreEnd (Unchecked (Ahead OutOfBounds))) (doomed_config, InterpRuntime.start) hello_world).
Proof.
  apply M.step_core_end; [intros site (Hd & _); discriminate Hd | reflexivity].
Qed.

(** A defined function named puts. *)
Definition callee : func := mkFunc symbol (TAtom "export") RVoid [] [mkBlock label [] [] JRetVoid].
(** An environment where puts is that defined function. *)
Definition defined_ge : genv := mkGenv [IFunc callee] [] InterpRuntime.free.
(** An environment where puts is a function outside the
    [[core subset]]. *)
Definition outside_ge : genv := mkGenv [IOutside symbol (TAtom "body")] [] InterpRuntime.free.
(** An environment where puts is global data. *)
Definition data_ge : genv := mkGenv [] [(symbol, hello_ptr)] InterpRuntime.free.
(** The test frame about to call free. *)
Definition free_config : config :=
  mkConfig (with_point (c_frame (test_config CVoid))
    (Exec label [Call CVoid (Global free_name) args] JRetVoid)) test_callers hello_mem 41.
(** The test frame about to call zgc_free. *)
Definition zgc_free_config : config :=
  mkConfig (with_point (c_frame (test_config CVoid))
    (Exec label [Call CVoid (Global zgc_free_name) args] JRetVoid)) test_callers hello_mem 41.

(** Calls of a defined, outside or data name, and of free or zgc_free,
    stay core calls: every step there is silent. *)
Example dispatch_stays_core : forall trace st,
  (M.step (registry (test_contract RVoid True True True)) defined_ge
      (M.Running (test_config CVoid, InterpRuntime.start) tt) trace st \/
   M.step (registry (test_contract RVoid True True True)) outside_ge
      (M.Running (test_config CVoid, InterpRuntime.start) tt) trace st \/
   M.step (registry (test_contract RVoid True True True)) data_ge
      (M.Running (test_config CVoid, InterpRuntime.start) tt) trace st \/
   M.step (registry (test_contract RVoid True True True)) test_ge
      (M.Running (free_config, InterpRuntime.start) tt) trace st \/
   M.step (registry (test_contract RVoid True True True)) test_ge
      (M.Running (zgc_free_config, InterpRuntime.start) tt) trace st) -> trace = [].
Proof.
  intros trace st [H | [H | [H | [H | H]]]]; eapply M.non_external_silent; try exact H;
    intros site Hsite; pose proof (external_site_stuck _ _ _ Hsite) as Hstuck; discriminate Hstuck.
Qed.

(** A call of zgc_free runs the runtime's free, as a call of free does:
    the core step there is not stuck. *)
Example zgc_free_runs : Semantics.step test_ge zgc_free_config <> Stuck "instruction".
Proof. discriminate. Qed.

(** A puts whose allocation is refused stops as [OutOfMemory] with its
    event and its write to the libc state retained. *)
Example puts_refusal_retains_prefix :
  M.step (registry (puts_contract fixture_rep fixture_requests)) test_ge
    (M.Running (test_config CVoid, InterpRuntime.address_end) hello_world) [StreamBytes 1 [104]]
    (M.Stopped (CoreEnd (Trap OutOfMemory))
      (M.P.I.RM.with_mem (test_config CVoid) (store_bytes hello_mem 2048 1 1), InterpRuntime.address_end) hello_world).
Proof.
  eapply M.step_resource with (site := test_site CVoid);
    [apply test_external | reflexivity | reflexivity |].
  eapply M.E.invoke_resource with (born := []).
  - split; [left; reflexivity|]. exists (Tmp arg_name). reflexivity.
  - exact hello_pre.
  - split.
    + eapply M.E.effects_local; [apply local_store_bytes|constructor].
      intros b Hb. left. exists stdout_span. split; [left; reflexivity|].
      split; [exact (Forall_inv (proj2 hello_stdio))|]. unfold span_contains. simpl. lia.
    + split; [split; reflexivity|]. split; [exact hello_stdio|]. split.
      * apply stdio_delegates_refl; [reflexivity|exact (proj2 hello_stdio)].
      * right. exists hello_ptr, hello_bytes, ([104]), ([101; 108; 108; 111; 10]).
        split; [reflexivity|]. split; [exact hello_string|]. split; reflexivity.
  - eapply M.E.failure_oom with (align := 16) (size := 32);
      [split; reflexivity | unfold max_allocation_size; simpl; lia | reflexivity].
  - left. reflexivity.
Qed.

(** An exiting call's trace already ends in its [ProcessExit]; the step
    adds no second one. *)
Example exit_trace_not_duplicated :
  M.step (registry (test_contract RVoid True True True)) test_ge
    (M.Running (test_config CVoid, InterpRuntime.start) tt) [StreamBytes 1 [65]; ProcessExit 7]
    (M.Stopped (ExternalExit 7) (test_config CVoid, InterpRuntime.start) tt).
Proof.
  eapply M.step_exit with (site := test_site CVoid);
    [apply test_external | reflexivity | reflexivity |].
  eapply M.E.invoke_normal with (born := []); try exact I; try (intros x H; discriminate H).
  - split; [constructor|exact I].
  - intros status H. injection H as <-. exists [StreamBytes 1 [65]]. reflexivity.
Qed.

(** A top-level test frame at point pt with the given fuel and no
    callers. *)
Definition core_config (pt : point) (fuel : Z) : config :=
  mkConfig (mkFrame (test_fn CVoid) test_env [(TAtom "local", None)] None pt) [] hello_mem fuel.

(** A top-level return and running out of [[fuel]] stop with the core's
    outcome. *)
Example core_return_and_fuel :
  M.step (registry (test_contract RVoid True True True)) test_ge
    (M.Running (core_config (Exec label [] JRetVoid) 41, InterpRuntime.start) tt) []
    (M.Stopped (CoreEnd RetVoid) (core_config (Exec label [] JRetVoid) 41, InterpRuntime.start) tt) /\
  M.step (registry (test_contract RVoid True True True)) test_ge
    (M.Running (core_config (Enter label None) 0, InterpRuntime.start) tt) []
    (M.Stopped (CoreEnd OutOfFuel) (core_config (Enter label None) 0, InterpRuntime.start) tt).
Proof.
  split; apply M.step_core_end;
    try reflexivity; intros site H; pose proof (external_site_stuck _ _ _ H) as Hs; discriminate Hs.
Qed.

(** A local allocation the runtime refuses stops as [OutOfMemory]. *)
Example core_refusal :
  let c := core_config (Exec label [LocalAlloc (TAtom "local") 32] JRetVoid) 41 in
  M.step (registry (test_contract RVoid True True True)) test_ge (M.Running (c, InterpRuntime.address_end) tt) []
    (M.Stopped (CoreEnd (Trap OutOfMemory)) (c, InterpRuntime.address_end) tt).
Proof.
  cbv zeta. eapply M.step_core_refusal;
    [intros site H; pose proof (external_site_stuck _ _ _ H) as Hs; discriminate Hs |
     reflexivity | simpl; lia | reflexivity].
Qed.

(** A call of a function outside the [[core subset]] stops stuck. *)
Example core_stuck_outside :
  M.step (registry (test_contract RVoid True True True)) outside_ge
    (M.Running (test_config CVoid, InterpRuntime.start) tt) []
    (M.Stopped (CoreStuck "outside the core subset") (test_config CVoid, InterpRuntime.start) tt).
Proof.
  apply M.step_core_stuck;
    [intros site H; pose proof (external_site_stuck _ _ _ H) as Hs; discriminate Hs | reflexivity].
Qed.

(** A main that calls puts twice in a row. *)
Definition double_fn : func :=
  mkFunc (TAtom "main") (TAtom "export") RVoid [(P, arg_name)]
    [mkBlock label [] [Call CVoid (Global symbol) args; Call CVoid (Global symbol) args] JRetVoid].
(** [double_fn]'s frame at its first call. *)
Definition double_config : config :=
  mkConfig (mkFrame double_fn test_env test_locals None
    (Exec label [Call CVoid (Global symbol) args; Call CVoid (Global symbol) args] JRetVoid))
    test_callers hello_mem 41.
(** The first call, followed by the second. *)
Definition first_site : call_site := mkCallSite label CVoid symbol args [Call CVoid (Global symbol) args] JRetVoid.
(** The second call, the block's last instruction. *)
Definition last_site : call_site := mkCallSite label CVoid symbol args [] JRetVoid.
(** The configuration after the first call returns. *)
Definition after_first : config := resume_external double_config first_site test_env hello_mem.

(** A run of the two calls observes the first call's event, then the
    second's. *)
Example two_call_event_order :
  M.run (registry (puts_contract fixture_rep fixture_requests)) test_ge
    (M.Running (double_config, InterpRuntime.start) hello_world)
    [StreamBytes 1 [104; 101; 108; 108; 111; 10]; StreamBytes 1 [104]]
    (M.Running (resume_external after_first last_site test_env hello_mem, InterpRuntime.start) hello_world).
Proof.
  eapply M.run_cons with (trace := [StreamBytes 1 (hello_bytes ++ [10])]) (tail := [StreamBytes 1 [104]])
    (mid := M.Running (after_first, InterpRuntime.start) hello_world).
  - eapply M.step_return with (site := first_site) (values := [WInt 0]);
      [repeat split; reflexivity | reflexivity | reflexivity | | reflexivity].
    apply (puts_invocation _ _ _ []); [left; reflexivity | reflexivity | left; auto].
  - eapply M.run_cons with (trace := [StreamBytes 1 [104]]) (tail := []).
    + eapply M.step_return with (site := last_site) (values := [WInt (2 ^ 32 - 1)]);
        [repeat split; reflexivity | reflexivity | reflexivity | | reflexivity].
      apply (puts_invocation _ _ _ [101; 108; 108; 111; 10]); [left; reflexivity | reflexivity | right; reflexivity].
    + constructor.
Qed.

End ExternalMachineChecks.
