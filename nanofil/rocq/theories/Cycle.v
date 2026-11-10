(** A loop whose trip count is the input, proved never to panic:
    rocq/programs/cycle.c, the sum of n longs read in turn from a
    read-only global array of four, `xs[i % 4]` for i from 0 while
    i < n, for every int n (CycleCode.v, checked current by
    rocq/programs.sh). The loop runs up to 2^31 - 1 times, so no list
    of runs covers it.

    The proof is Floyd's: an assertion at each point of the function
    ([cycle_assert]) says what the [[temporary|temporaries]] hold
    there, and one [[step]] from any configuration where the assertion
    holds reaches a point where its assertion holds, or ends without a
    failure ([cycle_safe]). Each step is taken by its rule from
    StepRules.v (Symbolic.v's [take_step]): the rule of the instruction
    at the point, with its premises (a temporary's value, an op on
    words, an access check) proved one by one.
    The loop's assertion is that its index i is between 0 and 2^31 - 1:
    then `i % 4` is between 0 and 3, the access is in bounds, and
    `i + 1` does not wrap. The index stays below 2^31 because the loop
    continues only while i < n, and no int n is above 2^31 - 1.
    Panics.v's [never_panics_by_invariant] turns that into
    [never_panics].

    ## Decisions

    | Decision | Why |
    |---|---|
    | assertions at every point, not only at the loop's head | the machine's invariant must hold in every state a run reaches, and the safepoint at the poll edge may act in the middle of the loop |
    | an assertion names only the temporaries read later, each with a range | the environment stays abstract, so the proof holds whatever else it holds, in the first iteration and in every later one |
    | the input is any list whose first word is an integer | the model reads an `int` parameter modulo 2^32, so no range on the word is needed; a pointer there is outside the C type |
    | memory as in Sum.v's [mem_ok] | the array is laid out where sum.c's is, and the program only reads it | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Transport Panics Symbolic CycleCode Sum.
Import ListNotations.
Open Scope Z_scope.

(** Integer arithmetic on an unknown stays folded when a step is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## The program *)

(** The checked module, decoded from the fixture [cycle_term]
    ([cycle_decodes]). *)
Definition cycle_module : module :=
  match decode_module cycle_term with Some md => md | None => [] end.

(** The fixture decodes to [cycle_module]. *)
Lemma cycle_decodes : decode_module cycle_term = Some cycle_module.
Proof. vm_compute. reflexivity. Qed.

(** The function `cycle`, the module's first item. *)
Definition cycle_fn : func :=
  match cycle_module with
  | IFunc f :: _ => f
  | _ => mkFunc (TAtom "cycle") (TAtom "export") (RClass L) [] []
  end.

(** The module's globals: the array `xs`, laid out as in Sum.v, and the
    function `cycle`. *)
Definition cycle_globals : list (name * ptr) :=
  [(TAtom "xs", mkPtr 65552 (Ro 65552)); (TAtom "cycle", mkPtr 65536 (Fn (TAtom "cycle")))].

(** The module's initial memory. *)
Definition cycle_mem : mem :=
  match initial_memory cycle_module with Some (_, m) => m | None => empty_mem end.

(** Laying out the module succeeds, with [cycle_globals] and
    [cycle_mem]. *)
Lemma cycle_initial : initial_memory cycle_module = Some (cycle_globals, cycle_mem).
Proof.
  assert (H : option_map fst (initial_memory cycle_module) = Some cycle_globals)
    by (vm_compute; reflexivity).
  unfold cycle_mem. destruct (initial_memory cycle_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The genv of the module with any free; the program calls none. *)
Definition cycle_ge (free : word -> mem -> option (res unit * mem)) : genv :=
  mkGenv cycle_module cycle_globals free.

(** `cycle` is a function of the [[core subset]] in the module. *)
Lemma cycle_find : forall free,
  find_fn (cycle_ge free) (TAtom "cycle") = Some (Defined cycle_fn).
Proof. intros free. vm_compute. reflexivity. Qed.

(** Any arguments whose first word is the integer n start `cycle` at
    its entry block with n as its parameter `v0`. *)
Lemma cycle_call_frame : forall n rest,
  call_frame cycle_fn (WInt n :: rest) =
  Some (mkFrame cycle_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** ## The points *)

(** Block l of `cycle` after its first j instructions. *)
Definition block_at (l : string) (j : nat) : point :=
  match find_block (TAtom l) (fn_blocks cycle_fn) with
  | Some b => Exec (TAtom l) (skipn j (b_insts b)) (b_jump b)
  | None => Enter (TAtom l) None
  end.

(** Every point of `cycle`, numbered: the entry block `start`; the
    loop's head `L4` (entered from `start` or from the body, then its
    comparison of i with n, then its branch); the loop's body `L5`,
    before each of its nine instructions and before its jump back,
    which polls; and the exit `L7`, which returns the sum. *)
Definition cycle_points : list point :=
  [Enter (TAtom "start") None; block_at "start" 0;
   Enter (TAtom "L4") (Some (TAtom "start")); Enter (TAtom "L4") (Some (TAtom "L5"));
   block_at "L4" 0; block_at "L4" 1;
   Enter (TAtom "L5") (Some (TAtom "L4"))] ++ map (block_at "L5") (seq 0 10) ++
  [Enter (TAtom "L7") (Some (TAtom "L4")); block_at "L7" 0].

(** ## The assertions *)

(** The temporary x holds a pointer into `xs` with 8 bytes after it:
    an address from the array's start to its last long, with the
    array's read-only capability. *)
Definition into_xs (e : env) (x : string) : Prop :=
  exists a, lookup (TAtom x) e = Some (WPtr (mkPtr a (Ro 65552))) /\ 65552 <= a <= 65576.

(** What holds after the first j instructions of the body: the sum
    `pr.1`, the index `pr.2` with room to add one, and each temporary
    the body has assigned and reads later: the array's pointer `v12`,
    `i % 4` (`v14`, then `v15` as a long), the offset `v16`, the
    pointer `v17` and its [[check|checked]] proof `chk0`, the long
    loaded `v18`, the new sum `v19` and the next index `v21`. *)
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

(** What holds at point k of [cycle_points], besides the input. At the
    loop's head entered from the body, the next index and sum; before
    the comparison, the index i and the sum; at the branch, also the
    comparison's answer, and where it is true, that i + 1 does not
    reach 2^31, since i < n; in the body, [body_assert]; at the exit,
    the sum. *)
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

(** A configuration of `cycle` where the assertions hold: at point k,
    with no caller, the input `v0` an integer, the assertion of k, and
    a memory that is [mem_ok] for the array. *)
Definition cycle_inv (c : config) : Prop :=
  exists k pt e,
    c = mkConfig (mkFrame cycle_fn e [] None pt) [] (c_mem c) (c_fuel c) /\
    nth_error cycle_points k = Some pt /\
    mem_ok cycle_mem (c_mem c) /\ int_at e (TAtom "v0") any /\ cycle_assert k e.

(** ## Each step *)

(** Unfold the assertion at a known point. *)
Ltac assertion := cbn [cycle_assert Nat.leb andb Nat.sub]; try unfold body_assert; cbn [Nat.leb].

(** Unfold the assertion at a known point in the hypothesis H. *)
Ltac assertion_in H :=
  cbn [cycle_assert Nat.leb andb Nat.sub] in H; try unfold body_assert in H; cbn [Nat.leb] in H.

(** The point of the next configuration is point n of
    [cycle_points] or a later one: find it by computing each in turn. *)
Ltac find_point pt n :=
  lazymatch n with
  | 19%nat => fail
  | _ => first [ assert (Hpt : nth_error cycle_points n = Some pt) by (vm_compute; reflexivity);
                 exists n, pt
               | find_point pt (S n) ]
  end.

(** The next configuration is in [cycle_inv]: at its point, with the
    memory unchanged, and the facts shown. *)
Ltac next_inv Hb Hr :=
  unfold cycle_inv;
  match goal with |- exists k pt e, mkConfig (mkFrame _ _ _ _ ?pt') _ _ _ = _ /\ _ =>
    find_point pt' 0%nat
  end;
  eexists; split; [subst; reflexivity|]; split; [assumption|]; cbn [c_mem]; split; [exact (conj Hb Hr)|];
  split; [show_facts | assertion; try unfold into_xs; show_facts].

(** One point of [cycle_safe]: the point from Hk, an index into the
    points pts, the assertion Ha taken apart, the step taken by its
    rule ([take_step]), and its result shown safe. *)
Ltac point_safe pts Hk Ha Hb Hr :=
  cbv in Hk; injection Hk as <-; clear pts;
  assertion_in Ha; unfold int_at, into_xs in *; facts;
  take_step; cbn [safe_step];
  solve [ intro; assumption | next_inv Hb Hr ].

(** One step from a configuration where the assertions hold is
    [safe_step] for them. *)
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

(** A call with an integer first argument starts where the assertions
    hold, with any fuel. *)
Lemma cycle_start : forall n fuel,
  cycle_inv (mkConfig (mkFrame cycle_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
                      [] cycle_mem fuel).
Proof.
  intros n fuel. exists O, (Enter (TAtom "start") None), [(TAtom "v0", WInt n)].
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [split; [reflexivity | vm_compute; reflexivity]|].
  split; [exists n; split; [reflexivity | exact I] | exact I].
Qed.

(** ## Over any runtime *)

(** `cycle` never panics under the [[runtime]] R. *)
Module CycleSafe (R : Runtime).
Module P := Panics R.
Module S := SumSafe R.

(** What R does at a [[poll|safepoint]] keeps the assertions: it
    changes only the memory, and keeps [mem_ok] (Sum.v's
    [mem_ok_safepoint]). *)
Lemma cycle_safepoint : forall c s s' m',
  cycle_inv c -> R.safepoint s (c_mem c) s' m' -> cycle_inv (P.RM.with_mem c m').
Proof.
  intros c s s' m' (k & pt & e & Ec & Hk & Hm & Hin & Ha) Hsp.
  exists k, pt, e. rewrite Ec at 1. unfold P.RM.with_mem; cbn [c_frame c_callers c_mem c_fuel].
  split; [reflexivity|]. split; [exact Hk|]. split; [|split; assumption].
  eapply S.mem_ok_safepoint; eassumption.
Qed.

(** `cycle` never panics: for every input whose first word is an
    integer, under the runtime R, with any fuel, no state of its run
    [fails], however many times the loop runs. *)
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

(** The theorem for the [[interpreter]]'s runtime. *)
Module InterpCycle := CycleSafe InterpRuntime.
