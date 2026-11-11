(** In Fil-C, capability checks catch every out-of-bounds access,
    use-after-free, or type violation by trapping before an invalid memory
    operation can run. When we verify a C function or program in
    [[campaign|Campaign]] 7
    ([formal.md](../../../docs/formal.md#campaign-7-a-program-that-never-panics)),
    we prove a stronger guarantee: for every admissible input, the program
    never triggers a safety [[trap]] or undefined behavior at all.

    Not every way a run can stop is a bug in the program. A C program can
    return normally, exit the process, or run out of execution [[fuel]] in
    our step-indexed model. The allocator can also refuse an allocation
    because the machine is out of memory or because the requested size
    exceeds Fil-C's 48-bit allocation limit. Those resource refusals are
    normal outcomes that C's `c: malloc` reports by returning null, whereas
    a capability check failure, an [[unchecked]] memory access, undefined
    behavior, or reaching `unreachable` is a program failure.

    This module defines that distinction once for both the closed-module
    [[machine]] in [Machine](../core/Machine.v) and the contract-aware
    external machine in [ExternalMachine](../external/ExternalMachine.v).
    The predicate [failure] classifies core machine [[outcome|outcomes]],
    [failure_ending] classifies external-machine endings, and
    [never_panics] states the whole-program safety theorem for a closed
    module over any Fil-C [[runtime]].

    ## Decisions

    The theorem [never_panics] is parameterized over any implementation of
    the [Runtime] interface so that a program proof cannot depend on where
    the allocator places objects or when it refuses an allocation. It
    quantifies over every fuel supply and every reachable state rather than
    only final outcomes, so a diverging loop or a run that exhausts its
    fuel still satisfies the theorem as long as no reachable state fails.

    To prevent the property from holding vacuously when a module fails to
    initialize, [never_panics] requires that the module's initial memory
    and entry function exist and that every admissible input builds a valid
    initial call [[frame]]. By contrast, it requires no extra assumption
    about garbage-collection [[poll|safepoints]]. By the runtime interface
    in [Runtime](../core/Runtime.v), a safepoint never frees a live
    [[region]], and a module that tried to install an unmodeled signal
    handler or thread would call an external function with no contract and
    fail immediately. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine.
Import ListNotations.
Open Scope Z_scope.

(** ## Failures

    When a step of the machine stops, we must distinguish normal endings
    and resource refusals from genuine safety failures. This section
    classifies trap reasons, core outcomes, configurations, and
    external-machine endings, and defines what it means for a single step
    to preserve a configuration invariant without failing. *)

(** In Fil-C, an allocation can trap either because the runtime has no room
    for the object or because the requested size exceeds 2^48 - 1 bytes.
    The predicate [refusal] identifies these two resource-exhaustion trap
    reasons so that we can treat them as benign allocation refusals rather
    than program panics. *)
Definition refusal (why : reason) : Prop := why = OutOfMemory \/ why = TooBig.

(** A core machine [[outcome]] satisfies [failure] when the program hits a
    non-refusal [[trap]], performs an [[unchecked]] access, triggers
    undefined behavior, or executes `unreachable`. Every capability check
    and [[check_ahead]] failure is a non-refusal trap, whereas normal
    function returns and running out of [[fuel]] are not failures. *)
Definition failure (o : outcome) : Prop :=
  match o with
  | Trap why => ~ refusal why
  | Unchecked _ | UB _ | Unreachable => True
  | Ret _ | Rets _ | RetVoid | OutOfFuel => False
  end.

(** A machine configuration satisfies [fails] when its next [[step]]
    produces a [failure] outcome, gets stuck outside the [[core subset]]
    model, or requests a heap allocation with a negative byte size. If the
    runtime refuses a valid allocation request, the machine ends with an
    out-of-memory refusal rather than failing here. *)
Definition fails (ge : genv) (c : config) : Prop :=
  match step ge c with
  | Done o => failure o
  | Stuck _ => True
  | Fresh q _ => req_extent q < 0
  | Next _ => False
  end.

(** In the external machine of
    [ExternalMachine](../external/ExternalMachine.v), a run can also stop
    at an [[external call]]. An ending satisfies [failure_ending] when it
    comes from a core [failure], a stuck core step, or a contract violation
    at a call boundary, whereas a normal process exit is not a failure. *)
Definition failure_ending (why : ending) : Prop :=
  match why with
  | CoreEnd o => failure o
  | CoreStuck _ => True
  | ExternalExit _ => False
  | ContractViolation _ _ => True
  end.

(** In [ExternalCalls](../external/ExternalCalls.v), an external call that
    runs out of memory or exceeds the allocation limit stops with one of
    the same two trap reasons. Lemma [refusal_resource] records that
    [refusal] and [resource_reason] are equivalent. *)
Lemma refusal_resource : forall why, refusal why <-> resource_reason why.
Proof. intros why. unfold refusal, resource_reason. tauto. Qed.

(** Consequently, any trap caused by a resource refusal during an external
    call is never classified as a [failure]. *)
Lemma resource_not_failure : forall why, resource_reason why -> ~ failure (Trap why).
Proof. intros why H Hf. apply Hf, refusal_resource, H. Qed.

(** To prove that a program never fails by induction over its execution, we
    check one step at a time against a configuration invariant. A step
    result satisfies [safe_step] when it never gets stuck, avoids any
    [failure] outcome, preserves the invariant on a normal step, and
    preserves the invariant for every [[fresh]] base address on a
    non-negative allocation request. *)
Definition safe_step (inv : config -> Prop) (m : mem) (r : step_result) : Prop :=
  match r with
  | Next c' => inv c'
  | Done o => ~ failure o
  | Fresh q k => 0 <= req_extent q /\ forall base, fresh m q base -> inv (k base)
  | Stuck _ => False
  end.

(** ## The property

    A program proof should hold regardless of how the underlying allocator
    chooses addresses or schedules garbage collection. This section
    parameterizes the whole-program safety property [never_panics] over an
    arbitrary [Runtime] implementation and proves the invariant rule used
    to establish it. *)

(** The functor [Panics] defines [never_panics] and its invariant proof
    rule for any implementation of the Fil-C [Runtime] interface. *)
Module Panics (R : Runtime).
Module RM := Machine R.

(** Given a module and its initialized global variables, [program_genv]
    builds the [[genv|global environment]] that pairs the module's
    definitions with the runtime's deallocator. *)
Definition program_genv (md : module) (globals : list (name * ptr)) : genv :=
  mkGenv md globals R.free.

(** A closed C module satisfies [never_panics] at an entry function when
    its global memory initializes cleanly, the entry function is defined in
    the module, and every admissible argument list builds a valid initial
    call [[frame]]. Starting from that call in a [[ready]] runtime state, no
    state reachable across any number of instructions, [[fresh]] heap
    allocations, or garbage-collection [[poll|safepoints]] ever fails. *)
Definition never_panics (md : module) (entry : name) (input : list word -> Prop) : Prop :=
  exists globals m f,
    initial_memory md = Some (globals, m) /\
    find_fn (program_genv md globals) entry = Some (Defined f) /\
    forall xs, input xs ->
      exists fr, call_frame f xs = Some fr /\
        (R.ready R.start m ->
         forall fuel st,
           RM.mreachable (program_genv md globals) (mkConfig fr [] m fuel, R.start) st ->
           ~ fails (program_genv md globals) (fst st)).

(** Instead of reasoning about multi-step traces directly, a proof can
    establish [never_panics] by exhibiting a configuration invariant. Lemma
    [never_panics_by_invariant] shows that if the invariant holds at every
    admissible initial call frame, every single step from a [[ready]] state
    satisfies [safe_step], and every due [[poll|safepoint]] preserves the
    invariant, then the module never panics. *)
Lemma never_panics_by_invariant : forall md entry input globals m f (inv : config -> Prop),
  initial_memory md = Some (globals, m) ->
  find_fn (program_genv md globals) entry = Some (Defined f) ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\ forall fuel, inv (mkConfig fr [] m fuel)) ->
  (forall c s, inv c -> R.ready s (c_mem c) -> safe_step inv (c_mem c) (step (program_genv md globals) c)) ->
  (forall c s s' m', inv c -> R.ready s (c_mem c) -> RM.safepoint_due (program_genv md globals) c = true ->
     R.safepoint s (c_mem c) s' m' -> inv (RM.with_mem c m')) ->
  never_panics md entry input.
Proof.
  intros md entry input globals m f inv Hm Hf Hin Hstep Hsp.
  exists globals, m, f. split; [exact Hm|]. split; [exact Hf|].
  intros xs Hxs. destruct (Hin xs Hxs) as (fr & Hfr & Hinv). exists fr. split; [exact Hfr|].
  intros Hready fuel st Hreach.
  assert (Hgen : forall st1 st2, RM.mreachable (program_genv md globals) st1 st2 ->
                   inv (fst st1) /\ RM.ready_state st1 -> inv (fst st2) /\ RM.ready_state st2).
  { intros st1 st2 H. induction H as [st1 st2 Hs | st1 | st1 st2 st3 _ IH1 _ IH2]; auto.
    intros [H0 Hr0]. split; [|exact (RM.mstep_ready (program_genv md globals) _ _ eq_refl Hs Hr0)].
    destruct Hs as [c c' s E | c q k s base s' E He Hal | c s s' m' Hdue Hsp'];
      unfold RM.ready_state in Hr0; cbn [fst snd] in H0, Hr0 |- *;
      pose proof (Hstep _ _ H0 Hr0) as Hr.
    - rewrite E in Hr. exact Hr.
    - rewrite E in Hr. destruct (step_fresh_kept _ _ _ _ E) as [Ha _].
      destruct (R.fresh_allocation _ _ _ _ _ Hr0 Ha He Hal) as [Hfresh _].
      exact (proj2 Hr base Hfresh).
    - exact (Hsp c s s' m' H0 Hr0 Hdue Hsp'). }
  destruct (Hgen _ _ Hreach (conj (Hinv fuel) Hready)) as [Hst Hrs].
  unfold fails. pose proof (Hstep _ _ Hst Hrs) as Hr.
  destruct (step (program_genv md globals) (fst st)); cbn [safe_step] in Hr; try tauto. lia.
Qed.

End Panics.
