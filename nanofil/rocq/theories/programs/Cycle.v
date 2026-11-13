(** This module proves that the C function `c: cycle` in `cycle.c` never
    panics for any integer input. The function sums n longs from a four-element
    read-only global array by indexing `c: xs[i % 4]` for i from 0 while
    i < n. Because n can be any signed 32-bit integer up to 2^31 - 1, no
    finite list of concrete runs can cover all trip counts.

    Instead of unrolling the loop, we use Floyd's invariant method. We attach
    an assertion ([cycle_assert]) to every program point in the function and
    prove in [cycle_safe] that taking one [[step]] from any state satisfying
    its point's assertion lands in another valid point or terminates cleanly.
    The key loop invariant is that the index i stays between 0 and 2^31 - 1,
    which guarantees that `i % 4` falls between 0 and 3 and that `i + 1` never
    overflows when the loop condition i < n holds.

    Execution can pause between any two instructions, so we attach facts to
    every program point rather than only to the loop header. Each point
    constrains only the [[temporary|temporaries]] that later instructions
    read, leaving the rest of the environment abstract across iterations.
    The global array's bytes and bounds never move, and `c: cycle` accepts
    any trailing arguments because it only inspects its first integer
    parameter. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Transport Panics Symbolic CycleCode Sum.
Import ListNotations.
Open Scope Z_scope.

(** Integer arithmetic on symbolic values stays folded during step
    reduction so bounds remain readable. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## The program

    The proof verifies the compiled IR fixture emitted by `nanofil -O` for
    `cycle.c`. Decoding that fixture gives us the function body, the global
    array layout, and the initial memory state. *)

(** Decoding [cycle_term] produces the compiled module for `cycle.c`. *)
Definition cycle_module : module :=
  match decode_module cycle_term with Some md => md | None => [] end.

(** The saved compiler fixture decodes cleanly into [cycle_module]. *)
Lemma cycle_decodes : decode_module cycle_term = Some cycle_module.
Proof. vm_compute. reflexivity. Qed.

(** The compiled function `cycle` is the first definition in the module. *)
Definition cycle_fn : func :=
  match cycle_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "cycle") (TAtom "export") (RClass L) [] []
  end.

(** The global table places the array `xs` at address 65552 and the function
    `cycle` at address 65536. *)
Definition cycle_globals : list (name * ptr) :=
  [(TAtom "xs", mkPtr 65552 (Ro 65552)); (TAtom "cycle", mkPtr 65536 (Fn (TAtom "cycle")))].

(** Laying out the module's globals builds the initial memory state before
    execution starts. *)
Definition cycle_mem : mem :=
  match initial_memory cycle_module with Some (_, m) => m | None => empty_mem end.

(** Memory layout succeeds and produces the expected global pointers and
    initial heap. *)
Lemma cycle_initial : initial_memory cycle_module = Some (cycle_globals, cycle_mem).
Proof.
  assert (H : option_map fst (initial_memory cycle_module) = Some cycle_globals)
    by (vm_compute; reflexivity).
  unfold cycle_mem. destruct (initial_memory cycle_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** Wrapping the module and its globals into a global environment lets the
    semantics resolve calls under any `free` handler. *)
Definition cycle_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv cycle_module cycle_globals free.

(** Looking up `cycle` in the global environment finds the compiled function
    in the [[core subset]]. *)
Lemma cycle_find : forall free,
  find_fn (cycle_ge free) (TAtom "cycle") = Some (Defined cycle_fn).
Proof. intros free. vm_compute. reflexivity. Qed.

(** Calling `cycle` with an integer first argument starts at its entry block
    with `v0` bound to that integer. *)
Lemma cycle_call_frame : forall n rest,
  call_frame cycle_fn (WInt n :: rest) =
  Some (mkFrame cycle_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** ## The points

    Because the invariant must hold at every intermediate machine state, we
    enumerate every program point in `cycle` in a fixed list. Each entry
    identifies either a block transition or a specific instruction suffix
    within a basic block. *)

(** Computing the suffix of block l after skipping j instructions builds a
    program point inside that block. *)
Definition block_at (l : string) (j : nat) : point :=
  match find_block (TAtom l) (fn_blocks cycle_fn) with
  | Some b => Exec (TAtom l) (skipn j (b_insts b)) (b_jump b)
  | None => Enter (TAtom l) None
  end.

(** The list [cycle_points] indexes all 19 reachable program points across
    the entry block `start`, the loop header `L4`, the loop body `L5`, and
    the exit block `L7`. *)
Definition cycle_points : list point :=
  [Enter (TAtom "start") None; block_at "start" 0;
   Enter (TAtom "L4") (Some (TAtom "start")); Enter (TAtom "L4") (Some (TAtom "L5"));
   block_at "L4" 0; block_at "L4" 1;
   Enter (TAtom "L5") (Some (TAtom "L4"))] ++ map (block_at "L5") (seq 0 10) ++
  [Enter (TAtom "L7") (Some (TAtom "L4")); block_at "L7" 0].

(** ## The assertions

    Each program point carries an assertion describing the integer bounds and
    pointer capabilities held in live temporaries. By tracking only the
    values needed by subsequent instructions, the assertions stay simple
    while still discharging every memory access check. *)

(** A temporary x satisfies [into_xs] when it holds a read-only pointer into
    the global array `xs` with at least 8 bytes remaining before the end. *)
Definition into_xs (e : env) (x : string) : Prop :=
  exists a, lookup (TAtom x) e = Some (WPtr (mkPtr a (Ro 65552))) /\ 65552 <= a <= 65576.

(** Inside the loop body, every instruction keeps the running sum and
    bounded loop index valid while building the [[check|checked]] array
    pointer up to index j. *)
Definition body_assert (j : nat) (e : env) : Prop :=
  int_at e (TAtom "pr.1") any /\ int_at e (TAtom "pr.2") (fun i => 0 <= i /\ i + 1 < 2 ^ 31) /\
  (if (1 <=? j)%nat then lookup (TAtom "v12") e = Some (WPtr (mkPtr 65552 (Ro 65552))) else True) /\
  (if (2 <=? j)%nat then int_at e (TAtom "v14") (fun r => 0 <= r < 4) else True) /\
  (if (3 <=? j)%nat then int_at e (TAtom "v15") (fun r => 0 <= r < 4) else True) /\
  (if (4 <=? j)%nat then int_at e (TAtom "v16") (fun o => 0 <= o <= 24) else True) /\
  (if (5 <=? j)%nat then into_xs e "v17" else True) /\
  (if (6 <=? j)%nat then into_xs e "chk0" else True) /\
  (if (7 <=? j)%nat then int_at e (TAtom "v18") any else True) /\
  (if (8 <=? j)%nat then int_at e (TAtom "v19") any else True) /\
  (if (9 <=? j)%nat then int_at e (TAtom "v21") (fun i => 0 <= i < 2 ^ 31) else True).

(** Depending on which of the 19 program points execution has reached, the
    point assertion records either the loop comparison outcome or the body
    state up to that instruction. *)
Definition cycle_assert (k : nat) (e : env) : Prop :=
  match k with
  | 3%nat => int_at e (TAtom "v21") (fun i => 0 <= i < 2 ^ 31) /\ int_at e (TAtom "v19") any
  | 4%nat => int_at e (TAtom "pr.1") any /\ int_at e (TAtom "pr.2") (fun i => 0 <= i < 2 ^ 31)
  | 5%nat => int_at e (TAtom "pr.1") any /\
         exists i, lookup (TAtom "pr.2") e = Some (WInt i) /\ 0 <= i < 2 ^ 31 /\
           (lookup (TAtom "v10") e = Some (WInt 0) \/
            (lookup (TAtom "v10") e = Some (WInt 1) /\ i + 1 < 2 ^ 31))
  | 6%nat => body_assert 0 e
  | 17%nat | 18%nat => int_at e (TAtom "pr.1") any
  | _ => if (7 <=? k)%nat && (k <=? 16)%nat then body_assert (k - 7) e else True
  end.

(** A machine state is valid when `cycle` is at one of the 19 recorded
    points, has no callers, holds an integer input, and matches the global
    array. *)
Definition cycle_inv (c : config) : Prop :=
  exists k pt e,
    c = mkConfig (mkFrame cycle_fn e [] None pt) [] (c_mem c) (c_fuel c) /\
    nth_error cycle_points k = Some pt /\
    mem_ok cycle_mem (c_mem c) /\ int_at e (TAtom "v0") any /\ cycle_assert k e.

(** ## Each step

    Rather than proving 19 separate lemmas by hand, we write small tactics
    that unpack the current point's assertion, apply the matching symbolic
    step rule, and discharge the resulting arithmetic obligations. *)

(** This tactic unfolds the point assertion in the goal so individual
    temporary bounds become visible. *)
Ltac assertion := cbn [cycle_assert Nat.leb andb Nat.sub]; try unfold body_assert; cbn [Nat.leb].

(** This tactic unfolds the point assertion inside a named hypothesis H. *)
Ltac assertion_in H :=
  cbn [cycle_assert Nat.leb andb Nat.sub] in H; try unfold body_assert in H; cbn [Nat.leb] in H.

(** This tactic locates the target program point pt in [cycle_points] by
    testing each index starting from n. *)
Ltac find_point pt n :=
  lazymatch n with
  | 19%nat => fail
  | _ => first [ assert (Hpt : nth_error cycle_points n = Some pt) by (vm_compute; reflexivity);
                 exists n, pt
               | find_point pt (S n) ]
  end.

(** This tactic proves that a stepped configuration satisfies [cycle_inv]
    by finding its new point index and discharging all temporary facts. *)
Ltac next_inv Hb Hr :=
  unfold cycle_inv;
  match goal with |- exists k pt e, mkConfig (mkFrame _ _ _ _ ?pt') _ _ _ = _ /\ _ =>
    find_point pt' 0%nat
  end;
  eexists; split; [subst; reflexivity|]; split; [assumption|]; cbn [c_mem]; split; [exact (conj Hb Hr)|];
  split; [show_facts | assertion; try unfold into_xs; show_facts].

(** This tactic proves safety for a single program point by unpacking its
    assertion, stepping through the instruction, and checking that the next
    state stays within the invariant or exits cleanly. *)
Ltac point_safe pts Hk Ha Hb Hr :=
  cbv in Hk; injection Hk as <-; clear pts;
  assertion_in Ha; unfold int_at, into_xs in *; facts;
  take_step; cbn [safe_step];
  solve [ intro; assumption | next_inv Hb Hr ].

(** Every configuration satisfying [cycle_inv] takes a safe step under any
    `free` handler, either preserving the invariant or terminating cleanly. *)
Lemma cycle_safe : forall free c, cycle_inv c -> safe_step cycle_inv (c_mem c) (step (cycle_ge free) c).
Proof.
  intros free c (k & pt & e & Ec & Hk & Hm & Hin & Ha).
  rewrite Ec. destruct Hm as [Hb Hr]. unfold xs_region in Hr. clear Ec.
  set (m := c_mem c) in *. set (fuel := c_fuel c) in *. clearbody m fuel.
  set (pts := cycle_points) in Hk. vm_compute in pts.
  remember cycle_fn as f eqn:Hf.
  block_fact f cycle_fn Hf (TAtom "start") b0 Hb0.
  block_fact f cycle_fn Hf (TAtom "L4") b4 Hb4.
  block_fact f cycle_fn Hf (TAtom "L5") b5 Hb5.
  block_fact f cycle_fn Hf (TAtom "L7") b7 Hb7.
  assert (Hret : fn_ret f = RClass L) by (rewrite Hf; reflexivity).
  do 19 (destruct k as [|k]; [point_safe pts Hk Ha Hb Hr|]).
  destruct k; discriminate Hk.
Qed.

(** Entering `cycle` with any integer argument and any fuel immediately
    satisfies [cycle_inv]. *)
Lemma cycle_start : forall n fuel,
  cycle_inv (mkConfig (mkFrame cycle_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
                      [] cycle_mem fuel).
Proof.
  intros n fuel. exists O, (Enter (TAtom "start") None), [(TAtom "v0", WInt n)].
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [split; [reflexivity | vm_compute; reflexivity]|].
  split; [exists n; split; [reflexivity | exact I] | exact I].
Qed.

(** ## Over any runtime

    Single-step safety covers individual instructions, while a full machine
    run also includes garbage-collector pauses at safepoints. We lift
    [cycle_safe] to any [[runtime]] R and show that safepoints preserve
    the invariant because they keep the global array intact. *)

(** This functor packages the safety proof for any runtime implementation
    satisfying the [Runtime] interface. *)
Module CycleSafe (R : Runtime).
Module P := Panics R.
Module S := SumSafe R.

(** A garbage-collector [[poll|safepoint]] preserves the machine invariant
    because it leaves the global array's bytes and bounds untouched. *)
Lemma cycle_safepoint : forall c s s' m',
  cycle_inv c -> R.safepoint s (c_mem c) s' m' -> cycle_inv (P.RM.with_mem c m').
Proof.
  intros c s s' m' (k & pt & e & Ec & Hk & Hm & Hin & Ha) Hsp.
  exists k, pt, e. rewrite Ec at 1. unfold P.RM.with_mem; cbn [c_frame c_callers c_mem c_fuel].
  split; [reflexivity|]. split; [exact Hk|]. split; [|split; assumption].
  eapply S.mem_ok_safepoint; eassumption.
Qed.

(** Calling `cycle` with any integer first argument, any fuel, and any
    runtime satisfying [Runtime] never reaches a failing state. *)
Theorem cycle_never_panics :
  P.never_panics cycle_module (TAtom "cycle") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply (P.never_panics_by_invariant _ _ _ cycle_globals cycle_mem cycle_fn cycle_inv).
  - exact cycle_initial.
  - apply cycle_find.
  - intros xs (n & rest & ->). eexists. split; [apply cycle_call_frame|]. intros fuel. apply cycle_start.
  - intros c s Hc _. apply cycle_safe, Hc.
  - intros c s s' m' Hc _ _ Hsp. eapply cycle_safepoint; eassumption.
Qed.

End CycleSafe.

(** Instantiating the safety functor with the [[interpreter]]'s runtime
    gives a concrete closed-module safety theorem. *)
Module InterpCycle := CycleSafe InterpRuntime.
