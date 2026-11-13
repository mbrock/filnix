(** This module proves that the C function `c: sum` in `sum.c` never panics,
    no matter which runtime executes it or how much [[fuel]] the execution
    has. The function loops over a read-only global array of four longs and
    returns their sum, taking no arguments and making no external calls. It
    is the simplest closed-module example in [formal.md](../../../docs/formal.md#the-quest-in-steps).

    Because `c: sum` takes no input, it follows the exact same 59-point path
    on every run. We compute that trace once on the module's initial memory
    to get the list of visited points ([sum_points]), and then prove in
    [sum_progress] that each point steps to the next one in any memory that
    still holds the array's bytes and bounds ([mem_ok]).

    Between any two instructions, the garbage collector may pause the program
    at a [[poll|safepoint]] to inspect memory. Because the array is immutable
    global data, the collector never moves its bytes or frees its
    [[region]]. The function allocates no heap objects and takes no
    parameters, so allocator readiness and extra call arguments cannot cause
    a failure. *)

From Stdlib Require Import String ZArith List Bool Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Transport Panics SumCode.
Import ListNotations.
Open Scope Z_scope.

(** ## The program

    The proof operates on the checked IR that `nanofil -O` actually produces
    from `sum.c`, rather than a hand-written model. Decoding the saved
    compiler output gives us the function body, its global symbol table, and
    its initial memory layout. *)

(** Decoding [sum_term] extracts the compiled module so the operational
    semantics can step through its instructions. *)
Definition sum_module : module :=
  match decode_module sum_term with Some md => md | None => [] end.

(** The saved compiler fixture decodes cleanly into [sum_module]. *)
Lemma sum_decodes : decode_module sum_term = Some sum_module.
Proof. vm_compute. reflexivity. Qed.

(** The compiled function `sum` sits at the front of the module. *)
Definition sum_fn : func :=
  match sum_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "sum") (TAtom "export") (RClass L) [] []
  end.

(** The global table places the array `xs` at address 65552 and the function
    `sum` at address 65536. *)
Definition sum_globals : list (name * ptr) :=
  [(TAtom "xs", mkPtr 65552 (Ro 65552)); (TAtom "sum", mkPtr 65536 (Fn (TAtom "sum")))].

(** Laying out the module's globals builds the initial memory state before
    execution starts. *)
Definition sum_mem : mem :=
  match initial_memory sum_module with Some (_, m) => m | None => empty_mem end.

(** Memory layout succeeds and produces the expected global pointers and
    initial heap. *)
Lemma sum_initial : initial_memory sum_module = Some (sum_globals, sum_mem).
Proof.
  assert (H : option_map fst (initial_memory sum_module) = Some sum_globals)
    by (vm_compute; reflexivity).
  unfold sum_mem. destruct (initial_memory sum_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** Wrapping the module and its globals into a global environment lets the
    semantics resolve function calls under any `free` handler. *)
Definition sum_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv sum_module sum_globals free.

(** Looking up `sum` in the global environment finds the compiled function in
    the [[core subset]]. *)
Lemma sum_find : forall free, find_fn (sum_ge free) (TAtom "sum") = Some (Defined sum_fn).
Proof. intros free. vm_compute. reflexivity. Qed.

(** Calling `sum` with any argument list enters its start block with an
    empty local environment. *)
Lemma sum_call_frame : forall xs,
  call_frame sum_fn xs = Some (mkFrame sum_fn [] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** ## The path

    Because `c: sum` has no inputs and no branches that depend on outside
    state, it always executes the same sequence of instructions. We record
    that concrete sequence as a list of program points and environments so
    the progress proof can check each step against abstract memory. *)

(** Running the step function up to n times collects the program points and
    environments visited along a single execution path. *)
Fixpoint trace (ge : genv) (n : nat) (c : config) : list (point * env) :=
  (fr_at (c_frame c), fr_env (c_frame c)) ::
  match n with
  | O => []
  | S n' => match step ge c with Next c' => trace ge n' c' | _ => [] end
  end.

(** Executing `sum` from its initial memory yields 59 points ending with a
    return value of 10. The proof treats this list only as a witness and
    verifies every transition independently in [sum_progress]. *)
Definition sum_points : list (point * env) :=
  trace (sum_ge (fun _ _ => None)) 200 (mkConfig (mkFrame sum_fn [] [] None (Enter (TAtom "start") None)) [] sum_mem 1000).

(** ## What the program reads of memory

    A function that only reads a global array does not care about the rest
    of memory or about capability metadata in [[aux]] slots. As long as the
    raw bytes and the array's bounds remain intact, every load behaves the
    same way as on the initial memory. *)

(** The global array `xs` occupies 32 bytes of read-only data starting at
    address 65552. *)
Definition xs_region : region := mkRegion 65552 65584 GlobalData Live.

(** Two memory states agree for `sum` when they share the same raw bytes and
    keep the global array's [[region]] live. *)
Definition mem_ok (m0 m : mem) : Prop :=
  m_bytes m = m_bytes m0 /\ object_region 65552 (m_regions m) = Some xs_region.

(** The initial memory trivially agrees with itself. *)
Lemma mem_ok_initial : mem_ok sum_mem sum_mem.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

(** Two memories with identical bytes return the same value from any load. *)
Lemma load_bytes_same : forall m m', m_bytes m = m_bytes m' ->
  forall a n, load_bytes m a n = load_bytes m' a n.
Proof. intros m m' H a n. unfold load_bytes. rewrite H. reflexivity. Qed.

(** ## Each step of the path

    Checking all 59 program points by hand would repeat the same symbolic
    reduction 59 times. Instead, we record the four integer values stored in
    the array and automate each single-step check so every point reduces in
    a uniform way. *)

(** The four 8-byte elements of `xs` in initial memory hold the integers 1
    through 4. *)
Lemma xs0 : load_bytes sum_mem 65552 8 = 1. Proof. vm_compute. reflexivity. Qed.
Lemma xs1 : load_bytes sum_mem 65560 8 = 2. Proof. vm_compute. reflexivity. Qed.
Lemma xs2 : load_bytes sum_mem 65568 8 = 3. Proof. vm_compute. reflexivity. Qed.
Lemma xs3 : load_bytes sum_mem 65576 8 = 4. Proof. vm_compute. reflexivity. Qed.

(** This tactic reduces a single execution step under abstract memory
    hypotheses without unfolding the full memory map. At block entries, it
    case-splits on fuel availability first so arithmetic stays folded. *)
Ltac step_eq Hb Hr fuel :=
  match goal with |- context[step ?g ?c] =>
    remember (step g c) as r eqn:Estep;
    try (match type of Estep with context[Enter _ _] => case_eq (fuel =? 0); intro end);
    cbv beta iota zeta delta -[object_region m_regions load_bytes sum_mem sum_module Z.eqb] in Estep;
    try (match goal with Hf : (fuel =? 0) = _ |- _ => rewrite Hf in Estep end);
    repeat progress (cbv beta iota zeta delta -[object_region m_regions load_bytes sum_mem sum_module] in Estep;
                     rewrite ?Hr, ?(load_bytes_same _ _ Hb), ?xs0, ?xs1, ?xs2, ?xs3 in Estep);
    subst r
  end.

(** This tactic checks one point on the trace by unpacking its state and
    matching the resulting step against a transition, fuel exhaustion, or
    return. *)
Ltac point_step Hn Hb Hr fuel :=
  cbv in Hn; injection Hn as <- <-;
  step_eq Hb Hr fuel;
  first [ right; right; reflexivity
        | right; left; reflexivity
        | left; do 3 eexists; split; [|reflexivity]; reflexivity ].

(** From any point in [sum_points] and any agreeing memory, `sum` either
    advances to the next point, runs out of fuel, or returns 10. *)
Lemma sum_progress : forall free n pt e m fuel,
  nth_error sum_points n = Some (pt, e) -> mem_ok sum_mem m ->
  (exists pt' e' fuel', nth_error sum_points (S n) = Some (pt', e') /\
     step (sum_ge free) (mkConfig (mkFrame sum_fn e [] None pt) [] m fuel) =
     Next (mkConfig (mkFrame sum_fn e' [] None pt') [] m fuel')) \/
  step (sum_ge free) (mkConfig (mkFrame sum_fn e [] None pt) [] m fuel) = Done OutOfFuel \/
  step (sum_ge free) (mkConfig (mkFrame sum_fn e [] None pt) [] m fuel) = Done (Ret (WInt 10)).
Proof.
  intros free n pt e m fuel Hn [Hb Hr].
  set (pts := sum_points) in Hn |- *. vm_compute in pts.
  set (f := sum_fn). vm_compute in f.
  do 59 (destruct n as [|n]; [point_step Hn Hb Hr fuel|]).
  destruct n; discriminate.
Qed.

(** ## Over any runtime

    Single-step progress covers one instruction at a time, whereas a full
    run interleaves instructions with garbage-collector pauses. We lift the
    trace property to the full machine over any [[runtime]] R and show that
    neither instructions nor pauses can ever leave the safe set of states. *)

(** This functor packages the safety proof for any runtime implementation
    satisfying the [Runtime] interface. *)
Module SumSafe (R : Runtime).
Module P := Panics R.

(** A garbage-collector [[poll|safepoint]] preserves [mem_ok] because
    bytes never move and global data regions are never freed. *)
Lemma mem_ok_safepoint : forall m0 s m s' m',
  R.safepoint s m s' m' -> mem_ok m0 m -> mem_ok m0 m'.
Proof.
  intros m0 s m s' m' Hsp [Hb Hr]. split.
  - rewrite (R.non_moving _ _ _ _ Hsp). exact Hb.
  - assert (Hold : object_region 65552 (m_regions m) <> None) by (rewrite Hr; discriminate).
    pose proof (R.rooting _ _ _ _ Hsp 65552 Hold) as Hin.
    destruct (object_region 65552 (m_regions m')) as [reg'|] eqn:E'; [|contradiction].
    destruct (R.safepoint_lifetime _ _ _ _ Hsp _ _ E') as (reg & Hreg & [-> | (Hk & _)]);
      rewrite Hr in Hreg; injection Hreg as <-; [reflexivity | discriminate Hk].
Qed.

(** A machine state satisfies [sum_inv] when its frame sits at one of the
    59 recorded points with an agreeing memory and no callers. *)
Definition sum_inv (st : P.RM.mstate) : Prop :=
  exists n pt e, nth_error sum_points n = Some (pt, e) /\
    fst st = mkConfig (mkFrame sum_fn e [] None pt) [] (c_mem (fst st)) (c_fuel (fst st)) /\
    mem_ok sum_mem (c_mem (fst st)).

(** Every machine transition keeps the execution on the recorded path
    because instructions follow the trace, no heap allocations occur, and
    collector pauses preserve the array. *)
Lemma sum_mstep : forall st st', P.RM.mstep (P.program_genv sum_module sum_globals) st st' ->
  sum_inv st -> sum_inv st'.
Proof.
  intros st st' Hs (n & pt & e & Hn & Hc & Hm).
  destruct Hs as [c c' s E | c q k s base s' E _ _ | c s s' m' _ Hsp]; cbn [fst snd] in Hc, Hm |- *;
    change (P.program_genv sum_module sum_globals) with (sum_ge R.free) in *.
  - rewrite Hc in E. destruct (sum_progress R.free n pt e (c_mem c) (c_fuel c) Hn Hm)
      as [(pt' & e' & fuel' & Hn' & E') | [E' | E']]; rewrite E' in E; try discriminate.
    injection E as <-. exists (S n), pt', e'. cbn [c_mem c_fuel]. auto.
  - rewrite Hc in E. destruct (sum_progress R.free n pt e (c_mem c) (c_fuel c) Hn Hm)
      as [(pt' & e' & fuel' & Hn' & E') | [E' | E']]; rewrite E' in E; discriminate.
  - exists n, pt, e. rewrite Hc. unfold P.RM.with_mem; cbn [c_mem c_fuel c_frame c_callers]. split; [exact Hn|]. split; [reflexivity|].
    eapply mem_ok_safepoint; eauto.
Qed.

(** By induction on machine steps, every state reachable from [sum_inv]
    remains in [sum_inv]. *)
Lemma sum_reachable : forall st st',
  P.RM.mreachable (P.program_genv sum_module sum_globals) st st' -> sum_inv st -> sum_inv st'.
Proof.
  intros st st' H. induction H as [st st' Hs | st | st1 st2 st3 _ IH1 _ IH2]; auto.
  apply sum_mstep; assumption.
Qed.

(** No state satisfying [sum_inv] can fail, because [sum_progress] rules
    out every error and trap outcome. *)
Lemma sum_not_fails : forall st, sum_inv st ->
  ~ fails (P.program_genv sum_module sum_globals) (fst st).
Proof.
  intros st (n & pt & e & Hn & Hc & Hm). rewrite Hc. unfold fails.
  destruct (sum_progress R.free n pt e (c_mem (fst st)) (c_fuel (fst st)) Hn Hm)
    as [(pt' & e' & fuel' & _ & E) | [E | E]];
    change (P.program_genv sum_module sum_globals) with (sum_ge R.free); rewrite E; simpl; tauto.
Qed.

(** Calling `sum` with any arguments, any fuel, and any runtime satisfying
    [Runtime] never reaches a failing state. *)
Theorem sum_never_panics : P.never_panics sum_module (TAtom "sum") (fun _ => True).
Proof.
  exists sum_globals, sum_mem, sum_fn. split; [exact sum_initial|]. split; [apply sum_find|].
  intros xs _. eexists. split; [apply sum_call_frame|].
  intros _ fuel st Hreach. apply sum_not_fails. eapply sum_reachable; [exact Hreach|].
  exists O, (Enter (TAtom "start") None), []. split; [reflexivity|].
  split; [reflexivity|]. exact mem_ok_initial.
Qed.

End SumSafe.

(** Instantiating the safety functor with the [[interpreter]]'s runtime
    gives a concrete closed-module safety theorem. *)
Module InterpSum := SumSafe InterpRuntime.
