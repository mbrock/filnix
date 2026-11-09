(** A program with a heap object, proved never to panic:
    rocq/programs/buffer.c, which allocates a buffer of four longs
    (`__builtin_alloca`, which Fil-C places in the collected heap),
    fills it, then sums `p[i % 4]` for i from 0 while i < n, for every
    int n (BufferCode.v, checked current by rocq/programs.sh).

    The proof is Cycle.v's: an assertion at each of the function's 32
    points ([buffer_assert]), and one [[step]] from any configuration
    where it holds is safe and reaches a point where its assertion holds
    ([buffer_safe]). What is new is the object. The run chooses its
    base, so the assertions speak of any base b that the allocation
    could return ([fresh]): from the allocation on, the temporary `v4`
    holds a pointer to b with b's own [[capability]], and b's [[region]]
    is a live heap object of 32 bytes. The access checks then pass
    because each address is b plus 0 to 24.

    A heap object is the one thing a [[poll|safepoint]] may take away:
    Runtime.v lets the runtime free any live heap object there
    ([safepoint_lifetime]), as another thread's `free` would. So the
    theorem has a premise, [safepoint_keeps_live]: no safepoint frees a
    live object. It holds of the [[interpreter]]'s runtime
    ([interp_buffer_never_panics] has no assumption), and natively of a
    program with one thread, since Fil-C's collector frees nothing the
    program can still reach. It is the program's own premise, as
    Campaign 4's `stdio_stable` is hi.c's for its stdio objects.

    ## Decisions

    | Decision | Why |
    |---|---|
    | the premise is stated for every live object, not for the buffer alone | the buffer's base is chosen by the run, so a premise naming it would have to quantify over bases anyway; "frees nothing live" is the plain statement of a single-threaded program |
    | the premise is an antecedent of the theorem, not an axiom | it is true of some runtimes and not others; [Runtime] keeps the weaker axiom that only a heap object is ever freed |
    | the assertions say nothing of the buffer's bytes | the program reads them only as `long`s it adds; any value is safe, so neither the fill nor a safepoint's bytes matter |
    | an allocation's base is any [fresh] one | Panics.v's [never_panics_by_invariant] gives every base the runtime may return; the proof uses only that it is positive and that the object ends at or below 2^64 | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Transport Panics Symbolic BufferCode.
Import ListNotations.
Open Scope Z_scope.

(** Integer arithmetic on an unknown stays folded when a step is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## The program *)

(** The checked module, decoded from the fixture [buffer_term]
    ([buffer_decodes]). *)
Definition buffer_module : module :=
  match decode_module buffer_term with Some md => md | None => [] end.

(** The fixture decodes to [buffer_module]. *)
Lemma buffer_decodes : decode_module buffer_term = Some buffer_module.
Proof. vm_compute. reflexivity. Qed.

(** The function `buffer`, the module's only item. *)
Definition buffer_fn : func :=
  match buffer_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "buffer") (TAtom "export") (RClass L) [] []
  end.

(** The module's one global, the function `buffer`. *)
Definition buffer_globals : list (name * ptr) :=
  [(TAtom "buffer", mkPtr 65536 (Fn (TAtom "buffer")))].

(** The module's initial memory, which holds no object. *)
Definition buffer_mem : mem :=
  match initial_memory buffer_module with Some (_, m) => m | None => empty_mem end.

(** Laying out the module succeeds, with [buffer_globals] and
    [buffer_mem]. *)
Lemma buffer_initial : initial_memory buffer_module = Some (buffer_globals, buffer_mem).
Proof.
  assert (H : option_map fst (initial_memory buffer_module) = Some buffer_globals)
    by (vm_compute; reflexivity).
  unfold buffer_mem. destruct (initial_memory buffer_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The genv of the module with any free; the program calls none. *)
Definition buffer_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv buffer_module buffer_globals free.

(** `buffer` is a function of the [[core subset]] in the module. *)
Lemma buffer_find : forall free,
  find_fn (buffer_ge free) (TAtom "buffer") = Some (Defined buffer_fn).
Proof. intros free. vm_compute. reflexivity. Qed.

(** Any arguments whose first word is the integer n start `buffer` at
    its entry block with n as its parameter `v0`. *)
Lemma buffer_call_frame : forall n rest,
  call_frame buffer_fn (WInt n :: rest) =
  Some (mkFrame buffer_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** ## The points *)

(** Block l of `buffer` after its first j instructions. *)
Definition buffer_at (l : string) (j : nat) : point :=
  match find_block (TAtom l) (fn_blocks buffer_fn) with
  | Some b => Exec (TAtom l) (skipn j (b_insts b)) (b_jump b)
  | None => Enter (TAtom l) None
  end.

(** Every point of `buffer`, numbered: the entry block `start`, before
    and after its allocation (0 to 2); the fill loop's head `L6` (3 to
    6) and body `L7` (7 to 15); the sum loop's head `L24` (16 to 19)
    and body `L25` (20 to 29); and the exit `L27` (30, 31). *)
Definition buffer_points : list point :=
  [Enter (TAtom "start") None; buffer_at "start" 0; buffer_at "start" 1;
   Enter (TAtom "L6") (Some (TAtom "start")); Enter (TAtom "L6") (Some (TAtom "L7"));
   buffer_at "L6" 0; buffer_at "L6" 1;
   Enter (TAtom "L7") (Some (TAtom "L6"))] ++ map (buffer_at "L7") (seq 0 8) ++
  [Enter (TAtom "L24") (Some (TAtom "L6")); Enter (TAtom "L24") (Some (TAtom "L25"));
   buffer_at "L24" 0; buffer_at "L24" 1;
   Enter (TAtom "L25") (Some (TAtom "L24"))] ++ map (buffer_at "L25") (seq 0 9) ++
  [Enter (TAtom "L27") (Some (TAtom "L24")); buffer_at "L27" 0].

(** ## The assertions *)

(** The buffer at the base b, in the environment e and the memory m:
    `v4` holds a pointer to b with b's capability, b is positive, the
    object ends at or below 2^64, and its region is a live heap object
    of 32 bytes. *)
Definition holds_buffer (e : env) (m : mem) (b : Z) : Prop :=
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b (Obj b))) /\ 0 < b /\ b + 32 <= 2 ^ 64 /\
  object_region b (m_regions m) = Some (mkRegion b (b + 32) Heap Live).

(** The temporary x holds a pointer into the buffer at b with 8 bytes
    after it. *)
Definition into_buf (e : env) (x : string) (b : Z) : Prop :=
  exists a, lookup (TAtom x) e = Some (WPtr (mkPtr a (Obj b))) /\ b <= a <= b + 24.

(** What holds after the first j instructions of the fill loop's body,
    which stores i + 1 at `p[i]`: the index `pr.1` below 4, then `v14`
    and `v15`, the offset, the pointer `v16`, the next index `v18` and
    its long `v19`, and the [[check|checked]] proof `chk0`. *)
Definition fill_assert (j : nat) (b : Z) (e : env) : Prop :=
  int_at e (TAtom "pr.1") (fun i => 0 <= i < 4) /\
  (if (1 <=? j)%nat then int_at e (TAtom "v14") (fun i => 0 <= i < 4) else True) /\
  (if (2 <=? j)%nat then int_at e (TAtom "v15") (fun o => 0 <= o <= 24) else True) /\
  (if (3 <=? j)%nat then into_buf e "v16" b else True) /\
  (if (4 <=? j)%nat then int_at e (TAtom "v18") (fun i => 0 <= i <= 4) else True) /\
  (if (5 <=? j)%nat then int_at e (TAtom "v19") any else True) /\
  (if (6 <=? j)%nat then into_buf e "chk0" b else True).

(** What holds after the first j instructions of the sum loop's body,
    as Cycle.v's [body_assert] with the buffer for the array. *)
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

(** What holds at point k of [buffer_points] besides the buffer: at
    each loop's head and branch, its index and the comparison's
    answer; in each body, [fill_assert] or [sum_assert]; at the exit,
    the sum. *)
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

(** What holds at point k in the memory m: nothing before the
    allocation; from it on, the buffer at some base b and the point's
    own assertion. *)
Definition buffer_assert (k : nat) (e : env) (m : mem) : Prop :=
  match k with
  | 0%nat | 1%nat => True
  | _ => exists b, holds_buffer e m b /\ point_assert k b e
  end.

(** A configuration of `buffer` where the assertions hold: at point k,
    with no caller, the input `v0` an integer, and the assertion of k. *)
Definition buffer_inv (c : config) : Prop :=
  exists k pt e,
    c = mkConfig (mkFrame buffer_fn e [] None pt) [] (c_mem c) (c_fuel c) /\
    nth_error buffer_points k = Some pt /\
    int_at e (TAtom "v0") any /\ buffer_assert k e (c_mem c).

(** ## Each step *)

(** Unfold the assertion at a known point. *)
Ltac assertion :=
  cbn [buffer_assert point_assert Nat.leb andb Nat.sub];
  try unfold fill_assert; try unfold sum_assert; cbn [Nat.leb].

(** Unfold the assertion at a known point in the hypothesis H. *)
Ltac assertion_in H :=
  cbn [buffer_assert point_assert Nat.leb andb Nat.sub] in H;
  try unfold fill_assert in H; try unfold sum_assert in H; cbn [Nat.leb] in H.

(** The point of the next configuration is point n of
    [buffer_points] or a later one: find it by computing each in turn. *)
Ltac find_point pt n :=
  lazymatch n with
  | 32%nat => fail
  | _ => first [ assert (Hpt : nth_error buffer_points n = Some pt) by (vm_compute; reflexivity);
                 exists n, pt
               | find_point pt (S n) ]
  end.

(** The next configuration is in [buffer_inv]: at its point, with the
    facts shown. *)
Ltac next_inv :=
  cbv beta; unfold buffer_inv;
  match goal with |- exists k pt e, mkConfig (mkFrame _ _ _ _ ?pt') _ _ _ = _ /\ _ =>
    find_point pt' 0%nat
  end;
  eexists; split; [subst; reflexivity|]; split; [assumption|];
  split; [show_facts | assertion; unfold holds_buffer, into_buf; show_facts].

(** The allocation's result is safe: its extent is nonnegative, and
    every [fresh] base gives a configuration where the assertions
    hold. *)
Ltac fresh_inv :=
  change (heap_req 16 32) with (mkReq 16 32 Heap) in *;
  split; [cbv; discriminate|]; intros ? Hfresh; unfold fresh in Hfresh;
  cbn [c_mem req_extent req_align] in Hfresh; facts; next_inv.

(** One point of [buffer_safe]: the point from Hk, an index into the
    points pts, the assertion Ha taken apart, the step taken by its
    rule ([take_step]), and its result shown safe. *)
Ltac point_safe pts Hk Ha :=
  cbv in Hk; injection Hk as <-; clear pts;
  assertion_in Ha; unfold int_at, holds_buffer, into_buf in *; facts;
  take_step; cbn [safe_step];
  solve [ intro; assumption | next_inv | fresh_inv ].

(** One step from a configuration where the assertions hold is
    [safe_step] for them. *)
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

(** A call with an integer first argument starts where the assertions
    hold, with any fuel. *)
Lemma buffer_start : forall n fuel,
  buffer_inv (mkConfig (mkFrame buffer_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
                       [] buffer_mem fuel).
Proof.
  intros n fuel. exists O, (Enter (TAtom "start") None), [(TAtom "v0", WInt n)].
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [exists n; split; [reflexivity | exact I] | exact I].
Qed.

(** ## Over any runtime that frees nothing live at a safepoint *)

(** `buffer` never panics under the [[runtime]] R, if R frees no live
    object at a safepoint. *)
Module BufferSafe (R : Runtime).
Module P := Panics R.

(** The premise: what R does at a [[poll|safepoint]] leaves every live
    object's [[region]] as it was. Runtime.v allows a safepoint to
    free a live heap object, as another thread's `free` would; a
    program with one thread has no other thread to do it. *)
Definition safepoint_keeps_live : Prop :=
  forall s m s' m' b reg, R.safepoint s m s' m' ->
    object_region b (m_regions m) = Some reg -> r_life reg = Live ->
    object_region b (m_regions m') = Some reg.

(** Under the premise, what R does at a safepoint keeps the
    assertions: it changes only the memory, and keeps the buffer's
    region. *)
Lemma buffer_safepoint : safepoint_keeps_live -> forall c s s' m',
  buffer_inv c -> R.safepoint s (c_mem c) s' m' -> buffer_inv (P.RM.with_mem c m').
Proof.
  intros Hkeep c s s' m' (k & pt & e & Ec & Hk & Hin & Ha) Hsp.
  exists k, pt, e. rewrite Ec at 1. unfold P.RM.with_mem; cbn [c_frame c_callers c_mem c_fuel].
  split; [reflexivity|]. split; [exact Hk|]. split; [exact Hin|].
  destruct k as [|[|k]]; [exact I | exact I|].
  destruct Ha as (b & (Hv & Hpos & Hle & Hr) & Hp). exists b. split; [|exact Hp].
  split; [exact Hv|]. split; [exact Hpos|]. split; [exact Hle|].
  exact (Hkeep _ _ _ _ _ _ Hsp Hr eq_refl).
Qed.

(** `buffer` never panics: if R frees no live object at a safepoint,
    then for every input whose first word is an integer, with any fuel,
    no state of its run [fails], whatever base its buffer gets. *)
Theorem buffer_never_panics : safepoint_keeps_live ->
  P.never_panics buffer_module (TAtom "buffer") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  intros Hkeep.
  apply (P.never_panics_by_invariant _ _ _ buffer_globals buffer_mem buffer_fn buffer_inv).
  - exact buffer_initial.
  - apply buffer_find.
  - intros xs (n & rest & ->). eexists. split; [apply buffer_call_frame|]. intros fuel. apply buffer_start.
  - intros c s Hc _. apply buffer_safe, Hc.
  - intros c s s' m' Hc _ _ Hsp. eapply buffer_safepoint; eassumption.
Qed.

End BufferSafe.

(** The theorem for the [[interpreter]]'s runtime. *)
Module InterpBuffer := BufferSafe InterpRuntime.

(** The interpreter's runtime frees nothing at a safepoint, so `buffer`
    never panics under it, with no premise. *)
Theorem interp_buffer_never_panics :
  InterpBuffer.P.never_panics buffer_module (TAtom "buffer")
    (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply InterpBuffer.buffer_never_panics.
  intros s m s' m' b reg [_ ->] Hr _. exact Hr.
Qed.
