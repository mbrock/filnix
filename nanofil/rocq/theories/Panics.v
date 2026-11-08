(** Campaign 7's property, [never_panics]: no [[run]] of a program
    from any admissible input ever reaches a failure
    ([formal.md, Campaign 7](../../docs/formal.md#campaign-7-a-program-that-never-panics)).

    A failure is what formal.md's panic table rules out: a Fil-C
    [[trap]] that is a capability check failing (a panic, in Filip's
    meaning), an [[unchecked]] access, undefined behaviour, an
    `unreachable` reached, or a step that leaves the model. A refusal
    (`out_of_memory`, `too_big`), a return, running out of [[fuel]] and
    a process exit are not failures, and neither is a run that never
    ends: the property speaks of every state a run reaches, not of how
    it ends.

    This file owns the one classification of endings that both the core
    [[machine]] and Campaign 4's labelled machine use: [failure] for a
    core [[outcome]], [failure_ending] for an ExternalMachine.v ending.
    The program statement [never_panics] is over Machine.v's machine
    for a closed module, one with no external calls; a program that
    calls libc is stated over the labelled machine with the same
    [failure_ending].

    ## Decisions

    | Decision | Why |
    |---|---|
    | every runtime R, as a functor argument | the proof may not depend on where objects are placed or when the runtime refuses an allocation (formal.md's statement) |
    | the run starts ready, an antecedent | until the heap starts above the module's data ([rocq.md](../../docs/rocq.md)), as in Campaign 3 |
    | every fuel, and every state reached | divergence and `out_of_fuel` are allowed; fuel plays no part |
    | an allocation with a negative extent is a failure | the machine has no step there, so the run left the model |
    | the module's initial memory and its entry function must exist, and every admissible input must make a frame | otherwise there is no run to speak of, and the program would hold vacuously |
    | no premise about the runtime's safepoints | a safepoint may free any live heap object (Runtime.v's [safepoint_lifetime]); a program that relies on its heap objects staying live states that as a premise of its own theorem | *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine.
Import ListNotations.
Open Scope Z_scope.

(** ## Failures *)

(** A [[trap]] reason that is a refusal, not a panic: the runtime
    would not hold an allocation (`out_of_memory`), or the request is
    over 2^48 - 1 bytes (`too_big`), which C's `malloc` would answer
    with null. These are mbrock's decisions in formal.md's panic table,
    and ExternalCalls.v's [resource_reason] for a call ([refusal_resource]). *)
Definition refusal (why : reason) : Prop := why = OutOfMemory \/ why = TooBig.

(** The [[outcome]] o is a failure: a trap that is not a [refusal]
    (every capability check, [Early] traps of a [[check_ahead]]
    included), an [[unchecked]] access, undefined behaviour, or
    `unreachable` reached. Returns and [OutOfFuel] are not. *)
Definition failure (o : outcome) : Prop :=
  match o with
  | Trap why => ~ refusal why
  | Unchecked _ | UB _ | Unreachable => True
  | Ret _ | Rets _ | RetVoid | OutOfFuel => False
  end.

(** The configuration c fails in the genv ge: its [[step]] ends in a
    [failure], is stuck (the run left the model: an external call, code
    outside the [[core subset]], an ill-formed word), or asks for an
    allocation with a negative extent, which the machine cannot take.
    An allocation the runtime refuses is not a failure: it ends the run
    with `trap(out_of_memory)`, a refusal. *)
Definition fails (ge : genv) (c : config) : Prop :=
  match step ge c with
  | Done o => failure o
  | Stuck _ => True
  | Fresh q _ => req_extent q < 0
  | Next _ => False
  end.

(** The labelled machine's ending why is a failure: a core [failure], a
    stuck core step, or a contract violation at a call. A process exit
    is not. *)
Definition failure_ending (why : ending) : Prop :=
  match why with
  | CoreEnd o => failure o
  | CoreStuck _ => True
  | ExternalExit _ => False
  | ContractViolation _ _ => True
  end.

(** A refusal is a resource ending of a call, and back. *)
Lemma refusal_resource : forall why, refusal why <-> resource_reason why.
Proof. intros why. unfold refusal, resource_reason. tauto. Qed.

(** A trap that ends a call for lack of resources is not a failure. *)
Lemma resource_not_failure : forall why, resource_reason why -> ~ failure (Trap why).
Proof. intros why H Hf. apply Hf, refusal_resource, H. Qed.

(** The step result r is safe for the invariant inv: a next
    configuration in inv, an ending that is not a [failure], or an
    allocation with a nonnegative extent whose every base gives a
    configuration in inv. Never stuck. *)
Definition safe_result (inv : config -> Prop) (r : step_result) : Prop :=
  match r with
  | Next c' => inv c'
  | Done o => ~ failure o
  | Fresh q k => 0 <= req_extent q /\ forall base, inv (k base)
  | Stuck _ => False
  end.

(** ## The property *)

(** The property over any [[runtime]] R. *)
Module Panics (R : Runtime).
Module RM := Machine R.

(** The genv of the module md with its globals, whose free is R's. *)
Definition program_genv (md : module) (globals : list (name * ptr)) : genv :=
  mkGenv md globals R.free.

(** The closed module md never panics when its function entry is called
    with any arguments xs that input admits: its initial memory exists
    and the entry is a function of the [[core subset]]; every admissible
    xs makes the entry's [[frame]]; and, where R is [[ready]] in the
    initial memory at its start, no state a run reaches from that call,
    with any fuel, [fails]. A run is Machine.v's: any fresh base R
    grants, and anything R does at a [[poll|safepoint]]. This is
    `run/5`'s start ([Driver]'s [run]). *)
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

(** The proof rule for [never_panics]: an invariant inv of
    configurations that holds where every admissible call starts, whose
    every [step] is [safe_result], and that what R does at a due
    [[poll|safepoint]] keeps. Then no state a run reaches [fails]. The
    invariant is the program's own; Cycle.v's says what holds at each
    point of its function. *)
Lemma never_panics_by_invariant : forall md entry input globals m f (inv : config -> Prop),
  initial_memory md = Some (globals, m) ->
  find_fn (program_genv md globals) entry = Some (Defined f) ->
  (forall xs, input xs -> exists fr, call_frame f xs = Some fr /\ forall fuel, inv (mkConfig fr [] m fuel)) ->
  (forall c, inv c -> safe_result inv (step (program_genv md globals) c)) ->
  (forall c s s' m', inv c -> RM.safepoint_due (program_genv md globals) c = true ->
     R.safepoint s (c_mem c) s' m' -> inv (RM.with_mem c m')) ->
  never_panics md entry input.
Proof.
  intros md entry input globals m f inv Hm Hf Hin Hstep Hsp.
  exists globals, m, f. split; [exact Hm|]. split; [exact Hf|].
  intros xs Hxs. destruct (Hin xs Hxs) as (fr & Hfr & Hinv). exists fr. split; [exact Hfr|].
  intros _ fuel st Hreach.
  assert (Hgen : forall st1 st2, RM.mreachable (program_genv md globals) st1 st2 ->
                   inv (fst st1) -> inv (fst st2)).
  { intros st1 st2 H. induction H as [st1 st2 Hs | st1 | st1 st2 st3 _ IH1 _ IH2]; auto.
    intros H0. pose proof (Hstep _ H0) as Hr.
    destruct Hs as [c c' s E | c q k s base s' E _ _ | c s s' m' Hdue Hsp'];
      cbn [fst] in H0, Hr |- *.
    - rewrite E in Hr. exact Hr.
    - rewrite E in Hr. exact (proj2 Hr base).
    - exact (Hsp c s s' m' H0 Hdue Hsp'). }
  assert (Hst : inv (fst st)) by (apply (Hgen _ _ Hreach), Hinv).
  unfold fails. pose proof (Hstep _ Hst) as Hr.
  destruct (step (program_genv md globals) (fst st)); cbn [safe_result] in Hr; try tauto. lia.
Qed.

End Panics.
