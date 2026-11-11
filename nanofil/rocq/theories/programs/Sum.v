(** The first program proved never to panic: rocq/theories/programs/sum.c, a
    loop that sums a read-only global array of four longs, as nanofil
    -O compiles it (SumCode.v, checked current by rocq/scripts/programs.sh).
    Step 1 of [formal.md's quest](../../../docs/formal.md#the-quest-in-steps):
    a closed module, with no input and no external call.

    The statement is Panics.v's [never_panics] over every [[runtime]]
    R, every argument list and every [[fuel]]: no state a [[run]]
    reaches [fails]. The proof is a symbolic execution of the one path
    the program has. The run on the module's initial memory is computed
    once by the model's own [step] ([sum_points], 59 states); then
    [sum_progress] shows that from each of those states, in any memory
    that agrees with the initial one on what the program reads ([mem_ok]),
    the step is the next state of the list, the last return, or the end
    of fuel. A [[poll|safepoint]] may change the memory, but
    [mem_ok_safepoint] shows it keeps [mem_ok], by Runtime.v's axioms:
    the array is global data, which no free empties, and no byte moves.

    ## Decisions

    | Decision | Why |
    |---|---|
    | the run is computed, then each step checked against abstract memory | the computed list is only a guess the proof checks; the memory and fuel stay universally quantified, so nothing about one runtime's placement is assumed |
    | [mem_ok] tracks the bytes and the array's [[region]], not the [[aux]] | the program loads no pointer, so it reads memory only through the array's bounds and bytes |
    | no use of [R.ready] | the program allocates nothing, so readiness, which only governs fresh allocations, plays no part |
    | the input is any argument list | `sum` takes no parameters, and [call_frame] ignores extra words | *)

From Stdlib Require Import String ZArith List Bool Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Transport Panics SumCode.
Import ListNotations.
Open Scope Z_scope.

(** ## The program *)

(** The checked module, decoded from the fixture [sum_term]
    ([sum_decodes]). *)
Definition sum_module : module :=
  match decode_module sum_term with Some md => md | None => [] end.

(** The fixture decodes to [sum_module]: the proof is about what nanofil
    makes of sum.c. *)
Lemma sum_decodes : decode_module sum_term = Some sum_module.
Proof. vm_compute. reflexivity. Qed.

(** The function `sum`, the module's first item. *)
Definition sum_fn : func :=
  match sum_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "sum") (TAtom "export") (RClass L) [] []
  end.

(** The module's globals, each name with its pointer: the array `xs`
    and the function `sum`. *)
Definition sum_globals : list (name * ptr) :=
  [(TAtom "xs", mkPtr 65552 (Ro 65552)); (TAtom "sum", mkPtr 65536 (Fn (TAtom "sum")))].

(** The module's initial memory, as `initial_memory/4` lays it out. *)
Definition sum_mem : mem :=
  match initial_memory sum_module with Some (_, m) => m | None => empty_mem end.

(** Laying out the module succeeds, with [sum_globals] and [sum_mem]. *)
Lemma sum_initial : initial_memory sum_module = Some (sum_globals, sum_mem).
Proof.
  assert (H : option_map fst (initial_memory sum_module) = Some sum_globals)
    by (vm_compute; reflexivity).
  unfold sum_mem. destruct (initial_memory sum_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The genv of the module with any free; the program calls none. *)
Definition sum_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv sum_module sum_globals free.

(** `sum` is a function of the [[core subset]] in the module. *)
Lemma sum_find : forall free, find_fn (sum_ge free) (TAtom "sum") = Some (Defined sum_fn).
Proof. intros free. vm_compute. reflexivity. Qed.

(** Any argument list starts `sum` at its entry block with no
    temporaries. *)
Lemma sum_call_frame : forall xs,
  call_frame sum_fn xs = Some (mkFrame sum_fn [] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** ## The path *)

(** The points and environments of the run in the genv ge from the
    configuration c, one per [step], for at most n steps, until a step
    is not [Next]. *)
Fixpoint trace (ge : genv) (n : nat) (c : config) : list (point * env) :=
  (fr_at (c_frame c), fr_env (c_frame c)) ::
  match n with
  | O => []
  | S n' => match step ge c with Next c' => trace ge n' c' | _ => [] end
  end.

(** The one path of `sum`, computed by running the model on the initial
    memory: 59 points, ending at the return of 10. The proof does not
    trust it; [sum_progress] checks every step. *)
Definition sum_points : list (point * env) :=
  trace (sum_ge (fun _ _ => None)) 200 (mkConfig (mkFrame sum_fn [] [] None (Enter (TAtom "start") None)) [] sum_mem 1000).

(** ## What the program reads of memory *)

(** The array `xs`: 32 bytes of read-only global data. *)
Definition xs_region : region := mkRegion 65552 65584 GlobalData Live.

(** The memory m agrees with the initial memory m0 on everything a
    program that only reads the array reads: the bytes, and the array's
    [[region]]. *)
Definition mem_ok (m0 m : mem) : Prop :=
  m_bytes m = m_bytes m0 /\ object_region 65552 (m_regions m) = Some xs_region.

(** The initial memory agrees with itself. *)
Lemma mem_ok_initial : mem_ok sum_mem sum_mem.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

(** A load reads only bytes: two memories with the same bytes load the
    same value. *)
Lemma load_bytes_same : forall m m', m_bytes m = m_bytes m' ->
  forall a n, load_bytes m a n = load_bytes m' a n.
Proof. intros m m' H a n. unfold load_bytes. rewrite H. reflexivity. Qed.

(** ## Each step of the path *)

(** The four longs of the array in the initial memory, 1 to 4. *)
Lemma xs0 : load_bytes sum_mem 65552 8 = 1. Proof. vm_compute. reflexivity. Qed.
Lemma xs1 : load_bytes sum_mem 65560 8 = 2. Proof. vm_compute. reflexivity. Qed.
Lemma xs2 : load_bytes sum_mem 65568 8 = 3. Proof. vm_compute. reflexivity. Qed.
Lemma xs3 : load_bytes sum_mem 65576 8 = 4. Proof. vm_compute. reflexivity. Qed.

(** Compute the [step] in the goal for a memory known only by Hb and Hr
    and the fuel: at a block's entry, which tests the fuel, split on
    whether fuel is left, and rewrite that test
    first, before the arithmetic it guards is unfolded; then reduce the
    step without unfolding the memory's regions, loads or the initial
    memory, and rewrite what the reduction is stuck on (the array's
    region, its loads), again until nothing changes. *)
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

(** One point of the path: take its point and environment from Hn,
    compute the step, and find it among the three outcomes
    [sum_progress] allows. *)
Ltac point_step Hn Hb Hr fuel :=
  cbv in Hn; injection Hn as <- <-;
  step_eq Hb Hr fuel;
  first [ right; right; reflexivity
        | right; left; reflexivity
        | left; do 3 eexists; split; [|reflexivity]; reflexivity ].

(** From the n-th point of the path, in any memory m that is [mem_ok]
    and with any fuel, `sum` steps to the next point with the same
    memory, ends for lack of fuel, or returns 10. *)
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

(** ## Over any runtime *)

(** `sum` never panics under the [[runtime]] R. *)
Module SumSafe (R : Runtime).
Module P := Panics R.

(** What R does at a [[poll|safepoint]] keeps [mem_ok]: no byte moves
    ([R.non_moving]), and the array is still an object ([R.rooting])
    whose bounds only a free of a heap object could empty
    ([R.safepoint_lifetime]); it is global data. *)
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

(** A machine state on the path: its configuration is `sum` at one of
    [sum_points], with no caller, in a [mem_ok] memory. *)
Definition sum_inv (st : P.RM.mstate) : Prop :=
  exists n pt e, nth_error sum_points n = Some (pt, e) /\
    fst st = mkConfig (mkFrame sum_fn e [] None pt) [] (c_mem (fst st)) (c_fuel (fst st)) /\
    mem_ok sum_mem (c_mem (fst st)).

(** Every machine step from a state on the path stays on it: a step is
    the next point ([sum_progress]), never an allocation, and a
    safepoint keeps the point and [mem_ok]. *)
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

(** Every state a run reaches from a state on the path is on it. *)
Lemma sum_reachable : forall st st',
  P.RM.mreachable (P.program_genv sum_module sum_globals) st st' -> sum_inv st -> sum_inv st'.
Proof.
  intros st st' H. induction H as [st st' Hs | st | st1 st2 st3 _ IH1 _ IH2]; auto.
  apply sum_mstep; assumption.
Qed.

(** No state on the path [fails]: its step is the next point, the end
    of fuel, or the return of 10. *)
Lemma sum_not_fails : forall st, sum_inv st ->
  ~ fails (P.program_genv sum_module sum_globals) (fst st).
Proof.
  intros st (n & pt & e & Hn & Hc & Hm). rewrite Hc. unfold fails.
  destruct (sum_progress R.free n pt e (c_mem (fst st)) (c_fuel (fst st)) Hn Hm)
    as [(pt' & e' & fuel' & _ & E) | [E | E]];
    change (P.program_genv sum_module sum_globals) with (sum_ge R.free); rewrite E; simpl; tauto.
Qed.

(** `sum` never panics: called with any arguments, under the runtime R,
    with any fuel, no state of its run [fails]. *)
Theorem sum_never_panics : P.never_panics sum_module (TAtom "sum") (fun _ => True).
Proof.
  exists sum_globals, sum_mem, sum_fn. split; [exact sum_initial|]. split; [apply sum_find|].
  intros xs _. eexists. split; [apply sum_call_frame|].
  intros _ fuel st Hreach. apply sum_not_fails. eapply sum_reachable; [exact Hreach|].
  exists O, (Enter (TAtom "start") None), []. split; [reflexivity|].
  split; [reflexivity|]. exact mem_ok_initial.
Qed.

End SumSafe.

(** The theorem for the [[interpreter]]'s runtime. *)
Module InterpSum := SumSafe InterpRuntime.
