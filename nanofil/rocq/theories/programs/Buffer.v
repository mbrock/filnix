(** This module proves that the C function `c: buffer` in `buffer.c` never
    panics for any integer input. The function allocates a four-long buffer
    on the collected heap using `c: __builtin_alloca`, fills the buffer with
    values, and then sums `c: p[i % 4]` for i from 0 while i < n.

    Unlike `cycle.c`, this function creates a dynamic heap object whose base
    address b is chosen by the [[runtime]] at allocation time. From that
    point onward, the invariant tracks that `v4` holds a pointer with b's
    [[capability]] and that b's [[region]] is a live 32-byte heap object.
    Because every access in both loops falls within b plus 0 to 24 bytes,
    all bounds checks pass for any [[fresh]] address.

    While `c: buffer` runs, the garbage collector never frees a live
    allocation or shrinks its bounds, so the proof needs no extra runtime
    premise. In addition, the sum loop reads the buffer only as 64-bit
    integers, so every possible byte value is safe. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Transport Panics Symbolic BufferCode.
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
    `buffer.c`. Decoding that fixture gives us the function body and its
    initial global symbol table, which contains only the function itself. *)

(** Decoding [buffer_term] extracts the compiled module for `buffer.c`. *)
Definition buffer_module : module :=
  match decode_module buffer_term with Some md => md | None => [] end.

(** The saved compiler fixture decodes cleanly into [buffer_module]. *)
Lemma buffer_decodes : decode_module buffer_term = Some buffer_module.
Proof. vm_compute. reflexivity. Qed.

(** The compiled function `buffer` is the only definition in the module. *)
Definition buffer_fn : func :=
  match buffer_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "buffer") (TAtom "export") (RClass L) [] []
  end.

(** The global table contains a single entry for the function `buffer` at
    address 65536. *)
Definition buffer_globals : list (name * ptr) :=
  [(TAtom "buffer", mkPtr 65536 (Fn (TAtom "buffer")))].

(** Laying out the module builds the initial memory state with no
    pre-allocated heap objects. *)
Definition buffer_mem : mem :=
  match initial_memory buffer_module with Some (_, m) => m | None => empty_mem end.

(** Memory layout succeeds and produces the expected global pointer and
    empty initial heap. *)
Lemma buffer_initial : initial_memory buffer_module = Some (buffer_globals, buffer_mem).
Proof.
  assert (H : option_map fst (initial_memory buffer_module) = Some buffer_globals)
    by (vm_compute; reflexivity).
  unfold buffer_mem. destruct (initial_memory buffer_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** Wrapping the module and its globals into a global environment lets the
    semantics resolve calls under any `free` handler. *)
Definition buffer_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv buffer_module buffer_globals free.

(** Looking up `buffer` in the global environment finds the compiled function
    in the [[core subset]]. *)
Lemma buffer_find : forall free,
  find_fn (buffer_ge free) (TAtom "buffer") = Some (Defined buffer_fn).
Proof. intros free. vm_compute. reflexivity. Qed.

(** Calling `buffer` with an integer first argument starts at its entry
    block with `v0` bound to that integer. *)
Lemma buffer_call_frame : forall n rest,
  call_frame buffer_fn (WInt n :: rest) =
  Some (mkFrame buffer_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** ## The points

    Because the invariant must hold at every intermediate machine state, we
    enumerate all 32 program points of `buffer` in a fixed list. Each entry
    identifies either a block transition or a specific instruction suffix
    within one of the six basic blocks. *)

(** Computing the suffix of block l after skipping j instructions builds a
    program point inside that block. *)
Definition buffer_at (l : string) (j : nat) : point :=
  match find_block (TAtom l) (fn_blocks buffer_fn) with
  | Some b => Exec (TAtom l) (skipn j (b_insts b)) (b_jump b)
  | None => Enter (TAtom l) None
  end.

(** The list [buffer_points] indexes all 32 reachable program points across
    the entry block, the fill loop, the sum loop, and the exit block. *)
Definition buffer_points : list point :=
  [Enter (TAtom "start") None; buffer_at "start" 0; buffer_at "start" 1;
   Enter (TAtom "L6") (Some (TAtom "start")); Enter (TAtom "L6") (Some (TAtom "L7"));
   buffer_at "L6" 0; buffer_at "L6" 1;
   Enter (TAtom "L7") (Some (TAtom "L6"))] ++ map (buffer_at "L7") (seq 0 8) ++
  [Enter (TAtom "L24") (Some (TAtom "L6")); Enter (TAtom "L24") (Some (TAtom "L25"));
   buffer_at "L24" 0; buffer_at "L24" 1;
   Enter (TAtom "L25") (Some (TAtom "L24"))] ++ map (buffer_at "L25") (seq 0 9) ++
  [Enter (TAtom "L27") (Some (TAtom "L24")); buffer_at "L27" 0].

(** ## The assertions

    Each program point needs an assertion describing the live buffer and the
    current loop indices. Before the allocation runs, no buffer exists yet;
    afterward, every point checks that the 32-byte buffer at address b
    remains live and that both loop indices stay in bounds. *)

(** After allocation, the temporary `v4` holds a pointer to a positive,
    non-wrapping base b whose 32-byte heap region remains live. *)
Definition holds_buffer (e : env) (m : mem) (b : Z) : Prop :=
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b (Obj b))) /\ 0 < b /\ b + 32 <= 2 ^ 64 /\
  object_region b (m_regions m) = Some (mkRegion b (b + 32) Heap Live).

(** A temporary x satisfies [into_buf] when it holds a pointer into the
    buffer at b with at least 8 bytes remaining before the end. *)
Definition into_buf (e : env) (x : string) (b : Z) : Prop :=
  exists a, lookup (TAtom x) e = Some (WPtr (mkPtr a (Obj b))) /\ b <= a <= b + 24.

(** Inside the fill loop body, every instruction keeps the loop index below
    4 while computing the store offset and the [[check|checked]] pointer. *)
Definition fill_assert (j : nat) (b : Z) (e : env) : Prop :=
  int_at e (TAtom "pr.1") (fun i => 0 <= i < 4) /\
  (if (1 <=? j)%nat then int_at e (TAtom "v14") (fun i => 0 <= i < 4) else True) /\
  (if (2 <=? j)%nat then int_at e (TAtom "v15") (fun o => 0 <= o <= 24) else True) /\
  (if (3 <=? j)%nat then into_buf e "v16" b else True) /\
  (if (4 <=? j)%nat then int_at e (TAtom "v18") (fun i => 0 <= i <= 4) else True) /\
  (if (5 <=? j)%nat then int_at e (TAtom "v19") any else True) /\
  (if (6 <=? j)%nat then into_buf e "chk0" b else True).

(** Inside the sum loop body, every instruction keeps the running sum and
    bounded loop index valid while building the [[check|checked]] pointer. *)
Definition sum_assert (j : nat) (b : Z) (e : env) : Prop :=
  int_at e (TAtom "pr.2") any /\ int_at e (TAtom "pr.3") (fun i => 0 <= i /\ i + 1 < 2 ^ 31) /\
  (if (1 <=? j)%nat then int_at e (TAtom "v34") (fun r => 0 <= r < 4) else True) /\
  (if (2 <=? j)%nat then int_at e (TAtom "v35") (fun r => 0 <= r < 4) else True) /\
  (if (3 <=? j)%nat then int_at e (TAtom "v36") (fun o => 0 <= o <= 24) else True) /\
  (if (4 <=? j)%nat then into_buf e "v37" b else True) /\
  (if (5 <=? j)%nat then into_buf e "chk1" b else True) /\
  (if (6 <=? j)%nat then int_at e (TAtom "v38") any else True) /\
  (if (7 <=? j)%nat then int_at e (TAtom "v39") any else True) /\
  (if (8 <=? j)%nat then int_at e (TAtom "v41") (fun i => 0 <= i < 2 ^ 31) else True).

(** At point index k of [buffer_points], [point_assert] specifies the loop
    conditions, [fill_assert], or [sum_assert] for that location. *)
Definition point_assert (k : nat) (b : Z) (e : env) : Prop :=
  match k with
  | 4%nat => int_at e (TAtom "v18") (fun i => 0 <= i <= 4)
  | 5%nat => int_at e (TAtom "pr.1") (fun i => 0 <= i <= 4)
  | 6%nat => exists i, lookup (TAtom "pr.1") e = Some (WInt i) /\ 0 <= i <= 4 /\
               (lookup (TAtom "v11") e = Some (WInt 0) \/
                (lookup (TAtom "v11") e = Some (WInt 1) /\ i < 4))
  | 7%nat => int_at e (TAtom "pr.1") (fun i => 0 <= i < 4)
  | 17%nat => int_at e (TAtom "v41") (fun i => 0 <= i < 2 ^ 31) /\ int_at e (TAtom "v39") any
  | 18%nat => int_at e (TAtom "pr.2") any /\ int_at e (TAtom "pr.3") (fun i => 0 <= i < 2 ^ 31)
  | 19%nat => int_at e (TAtom "pr.2") any /\
              exists i, lookup (TAtom "pr.3") e = Some (WInt i) /\ 0 <= i < 2 ^ 31 /\
                (lookup (TAtom "v30") e = Some (WInt 0) \/
                 (lookup (TAtom "v30") e = Some (WInt 1) /\ i + 1 < 2 ^ 31))
  | 20%nat => sum_assert 0 b e
  | 30%nat | 31%nat => int_at e (TAtom "pr.2") any
  | _ => if (8 <=? k)%nat && (k <=? 15)%nat then fill_assert (k - 8) b e
         else if (21 <=? k)%nat && (k <=? 29)%nat then sum_assert (k - 21) b e
         else True
  end.

(** Before the allocation runs, no heap buffer exists yet. From the
    allocation onward, some heap address b holds the buffer and satisfies
    the current point's loop assertion. *)
Definition buffer_assert (k : nat) (e : env) (m : mem) : Prop :=
  match k with
  | 0%nat | 1%nat => True
  | _ => exists b, holds_buffer e m b /\ point_assert k b e
  end.

(** A machine configuration satisfies [buffer_inv] when it sits at a known
    point of `buffer` with no callers, an integer input `v0`, and the
    point's assertion. *)
Definition buffer_inv (c : config) : Prop :=
  exists k pt e,
    c = mkConfig (mkFrame buffer_fn e [] None pt) [] (c_mem c) (c_fuel c) /\
    nth_error buffer_points k = Some pt /\
    int_at e (TAtom "v0") any /\ buffer_assert k e (c_mem c).

(** ## Each step

    Checking all 32 points by hand would repeat the same symbolic step
    reduction across every block. Instead, we automate the step check with
    tactics that unpack the point's assertion, handle ordinary instructions,
    and verify that any [[fresh]] heap base satisfies the invariant. *)

(** This tactic unfolds the point assertion in the goal so individual
    temporary bounds become visible. *)
Ltac assertion :=
  cbn [buffer_assert point_assert Nat.leb andb Nat.sub];
  try unfold fill_assert; try unfold sum_assert; cbn [Nat.leb].

(** This tactic unfolds the point assertion inside a named hypothesis H. *)
Ltac assertion_in H :=
  cbn [buffer_assert point_assert Nat.leb andb Nat.sub] in H;
  try unfold fill_assert in H; try unfold sum_assert in H; cbn [Nat.leb] in H.

(** This tactic locates the target program point pt in [buffer_points] by
    testing each index starting from n. *)
Ltac find_point pt n :=
  lazymatch n with
  | 32%nat => fail
  | _ => first [ assert (Hpt : nth_error buffer_points n = Some pt) by (vm_compute; reflexivity);
                 exists n, pt
               | find_point pt (S n) ]
  end.

(** This tactic proves that a stepped configuration satisfies [buffer_inv]
    by finding its new point index and discharging all temporary facts. *)
Ltac next_inv :=
  cbv beta; unfold buffer_inv;
  match goal with |- exists k pt e, mkConfig (mkFrame _ _ _ _ ?pt') _ _ _ = _ /\ _ =>
    find_point pt' 0%nat
  end;
  eexists; split; [subst; reflexivity|]; split; [assumption|];
  split; [show_facts | assertion; unfold holds_buffer, into_buf; show_facts].

(** This tactic verifies the heap allocation step by showing that the
    requested extent is nonnegative and that every [fresh] base satisfies
    [buffer_inv]. *)
Ltac fresh_inv :=
  change (heap_req 16 32) with (mkReq 16 32 Heap) in *;
  split; [cbv; discriminate|]; intros ? Hfresh; unfold fresh in Hfresh;
  cbn [c_mem req_extent req_align] in Hfresh; facts; next_inv.

(** This tactic proves safety for a single program point by unpacking its
    assertion, stepping through the instruction, and checking that the next
    state stays within the invariant or exits cleanly. *)
Ltac point_safe pts Hk Ha :=
  cbv in Hk; injection Hk as <-; clear pts;
  assertion_in Ha; unfold int_at, holds_buffer, into_buf in *; facts;
  take_step; cbn [safe_step];
  solve [ intro; assumption | next_inv | fresh_inv ].

(** Every configuration satisfying [buffer_inv] takes a safe step under any
    `free` handler, either preserving the invariant or terminating cleanly. *)
Lemma buffer_safe : forall free c, buffer_inv c ->
  safe_step buffer_inv (c_mem c) (step (buffer_ge free) c).
Proof.
  intros free c (k & pt & e & Ec & Hk & Hin & Ha).
  rewrite Ec. clear Ec.
  set (m := c_mem c) in *. set (fuel := c_fuel c) in *. clearbody m fuel.
  set (pts := buffer_points) in Hk. vm_compute in pts.
  remember buffer_fn as f eqn:Hf.
  block_fact f buffer_fn Hf (TAtom "start") b0 Hb0.
  block_fact f buffer_fn Hf (TAtom "L6") b6 Hb6.
  block_fact f buffer_fn Hf (TAtom "L7") b7 Hb7.
  block_fact f buffer_fn Hf (TAtom "L24") b24 Hb24.
  block_fact f buffer_fn Hf (TAtom "L25") b25 Hb25.
  block_fact f buffer_fn Hf (TAtom "L27") b27 Hb27.
  assert (Hret : fn_ret f = RClass L) by (rewrite Hf; reflexivity).
  do 32 (destruct k as [|k]; [point_safe pts Hk Ha|]).
  destruct k; discriminate Hk.
Qed.

(** Entering `buffer` with any integer argument and any fuel immediately
    satisfies [buffer_inv]. *)
Lemma buffer_start : forall n fuel,
  buffer_inv (mkConfig (mkFrame buffer_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
                       [] buffer_mem fuel).
Proof.
  intros n fuel. exists O, (Enter (TAtom "start") None), [(TAtom "v0", WInt n)].
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [exists n; split; [reflexivity | exact I] | exact I].
Qed.

(** ## Over any runtime

    Single-step safety covers individual instructions, while a full machine
    run also includes garbage-collector pauses at safepoints. We lift
    [buffer_safe] to any [[runtime]] R and show that safepoints preserve
    the invariant because they leave every heap region intact. *)

(** This functor packages the safety proof for any runtime implementation
    satisfying the [Runtime] interface. *)
Module BufferSafe (R : Runtime).
Module P := Panics R.

(** A garbage-collector [[poll|safepoint]] preserves [buffer_inv] because
    the collector never frees or alters heap regions. *)
Lemma buffer_safepoint : forall c s s' m',
  buffer_inv c -> R.safepoint s (c_mem c) s' m' -> buffer_inv (P.RM.with_mem c m').
Proof.
  intros c s s' m' (k & pt & e & Ec & Hk & Hin & Ha) Hsp.
  exists k, pt, e. rewrite Ec at 1. unfold P.RM.with_mem; cbn [c_frame c_callers c_mem c_fuel].
  split; [reflexivity|]. split; [exact Hk|]. split; [exact Hin|].
  destruct k as [|[|k]]; [exact I | exact I|].
  destruct Ha as (b & (Hv & Hpos & Hle & Hr) & Hp). exists b. split; [|exact Hp].
  split; [exact Hv|]. split; [exact Hpos|]. split; [exact Hle|].
  rewrite (R.collector_live _ _ _ _ Hsp). exact Hr.
Qed.

(** Calling `buffer` with any integer first argument, any fuel, and any
    runtime satisfying [Runtime] never reaches a failing state. *)
Theorem buffer_never_panics :
  P.never_panics buffer_module (TAtom "buffer") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply (P.never_panics_by_invariant _ _ _ buffer_globals buffer_mem buffer_fn buffer_inv).
  - exact buffer_initial.
  - apply buffer_find.
  - intros xs (n & rest & ->). eexists. split; [apply buffer_call_frame|]. intros fuel. apply buffer_start.
  - intros c s Hc _. apply buffer_safe, Hc.
  - intros c s s' m' Hc _ _ Hsp. eapply buffer_safepoint; eassumption.
Qed.

End BufferSafe.

(** Instantiating the safety functor with the [[interpreter]]'s runtime
    gives a concrete closed-module safety theorem. *)
Module InterpBuffer := BufferSafe InterpRuntime.

(** The concrete theorem [interp_buffer_never_panics] applies
    [buffer_never_panics] to the interpreter runtime. *)
Theorem interp_buffer_never_panics :
  InterpBuffer.P.never_panics buffer_module (TAtom "buffer")
    (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply InterpBuffer.buffer_never_panics.
Qed.
