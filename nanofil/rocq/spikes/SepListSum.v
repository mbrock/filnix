(** The listsum spike proved with the hand-rolled separation logic of
    Sep.v (docs/logic.md): spikes/listsum.c never panics, with no
    premise, under any runtime, the interpreter's among them.

    The proof is Buffer.v's: an assertion at each point of each
    function, one step from a configuration where it holds is
    [safe_step], and a safepoint keeps it; Panics.v's
    [never_panics_by_invariant] turns that into [never_panics]. What
    is new is the shape of the assertions. Each is facts about the
    temporaries and a separation-logic assertion on the
    memory, and `sum` has a specification of its own with a frame:
    from the list [lst] p xs and any frame F it walks the list,
    dropping each node it has passed into [htrue], and returns an
    integer with [htrue] and F still there ([sum_step]). `listsum`
    builds the list one fresh node at a time and calls `sum` with the
    empty frame, suspended on the callers' stack.

    The configuration invariant [ls_inv] adds the one fact about the
    whole memory, [live_disjoint]: either `listsum` runs with no
    caller, or `sum` runs with `listsum` suspended after its call. A
    safepoint ([R.at_safepoint] is abstract, so one may be due before
    any instruction that is not evidence-preserving, and at each poll
    edge) keeps every assertion: it changes no region
    ([collector_live]) and no byte, and changes an aux slot only where a freed
    object's capability is stored, which no list does
    ([sum_safepoint], [ls_safepoint]). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Transport Panics Symbolic.
From Spike Require Import Pieces Sep ListSum.
Import ListNotations.
Open Scope Z_scope.

(** Integer arithmetic on an unknown stays folded when a step is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## Computing a step over memory the assertions describe *)

(** A pointer is its two fields. *)
Lemma ptr_eta : forall p, p = mkPtr (ptr_addr p) (ptr_cap p).
Proof. intros [a c]. reflexivity. Qed.

(** Rewrite in E every alignment test of an address the context proves
    8-aligned to its answer, before [drop_wraps] would turn the
    remainder into an unknown. *)
Ltac aligned E :=
  repeat match type of E with
  | context[?x mod 8] =>
      assert_fails (has_if x);
      let H := fresh "Hal" in
      assert (H : x mod 8 = 0) by (clear E; arith); rewrite H in E; clear H
  end.

(** Rewrite in E the facts about memory and the module a step reads
    besides Symbolic.v's: a node's next slot, as bytes and as aux, a
    function found by name, a callee's frame, and a pointer rebuilt
    from its fields. *)
Ltac use_more_facts E :=
  repeat match goal with
  | H : load_bytes _ _ _ = _ |- _ => rewrite H in E
  | H : m_aux _ _ = _ |- _ => rewrite H in E
  | H : find_fn _ _ = _ |- _ => rewrite H in E
  | H : forall x rest, call_frame _ (x :: rest) = _ |- _ => rewrite H in E
  end;
  repeat match type of E with
  | context[mkPtr (ptr_addr ?p) (ptr_cap ?p)] => rewrite <- (ptr_eta p) in E
  end.

(** Compute E, an equation r = step g c, as Symbolic.v's
    [compute_step] does, with stores and aux kept folded, offsets of 0
    dropped, and the facts above. *)
Ltac step_reduce E :=
  repeat progress (
    cbn -[load_bytes store_bytes store_aux call_frame] in E; rewrite ?store_bytes_regions, ?Z.add_0_r in E;
    try unfold sign_extension in E; try unfold raw_address in E; try unfold aligned_res in E;
    try unfold continue_at in E; try unfold with_point in E;
    try unfold int_load_res in E; try unfold access_res in E; try unfold cap_access_res in E;
    try unfold aux_at in E;
    use_facts E; use_more_facts E; cbn [r_base r_end r_kind r_life ptr_addr ptr_cap] in E;
    aligned E; drop_wraps E; decide_compares E).

(** ## `sum` *)

(** The function `sum`. *)
Definition sum_fn : func := ls_fn "sum".

(** Every point of `sum`, numbered: the entry `start` (0, 1); the
    loop's head `L3`, entered from `start` or from the body (2, 3),
    before its two instructions and its branch (4 to 6); the body `L4`,
    entered (7), then before each of its six instructions and its jump
    back, which polls (8 to 14); and the exit `L5` (15, 16). *)
Definition sum_points : list point :=
  [Enter (TAtom "start") None; ls_at sum_fn "start" 0;
   Enter (TAtom "L3") (Some (TAtom "start")); Enter (TAtom "L3") (Some (TAtom "L4"));
   ls_at sum_fn "L3" 0; ls_at sum_fn "L3" 1; ls_at sum_fn "L3" 2;
   Enter (TAtom "L4") (Some (TAtom "L3"))] ++ map (ls_at sum_fn "L4") (seq 0 7) ++
  [Enter (TAtom "L5") (Some (TAtom "L3")); ls_at sum_fn "L5" 0].

(** At the loop's head, after its first j instructions: the list from
    `pr.1`, the sum `pr.2` an integer, the walked nodes in [htrue], and
    the frame F; then `v7`, the list's address, and `v8`, whether it is
    not null. *)
Definition sum_head (j : nat) (F : hprop) (e : env) (m : mem) : Prop :=
  exists p s xs, lookup (TAtom "pr.1") e = Some (WPtr p) /\ lookup (TAtom "pr.2") e = Some (WInt s) /\
    (if (j =? 1)%nat then lookup (TAtom "v7") e = Some (WInt (ptr_addr p)) else True) /\
    (if (j =? 2)%nat then
       (ptr_addr p <= 0 /\ lookup (TAtom "v8") e = Some (WInt 0)) \/
       (0 < ptr_addr p /\ lookup (TAtom "v8") e = Some (WInt 1)) else True) /\
    exists S, (lst p xs ** htrue ** F)%h S m.

(** In the body, after its first j instructions: the node at a, its
    value v and next pointer next, the rest xs; then the pointer `v11`
    to the value and its checked proof `chk0`, the value
    `v12`, the new sum `v13`, the half-checked node
    pointer `chk1`, and the next pointer `v15`. *)
Definition sum_body (j : nat) (F : hprop) (e : env) (m : mem) : Prop :=
  exists a s v next xs,
    lookup (TAtom "pr.1") e = Some (WPtr (mkPtr a (Obj a))) /\ lookup (TAtom "pr.2") e = Some (WInt s) /\
    (if (1 <=? j)%nat then lookup (TAtom "v11") e = Some (WPtr (mkPtr (a + 8) (Obj a))) else True) /\
    (if (2 <=? j)%nat then lookup (TAtom "chk0") e = Some (WPtr (mkPtr (a + 8) (Obj a))) else True) /\
    (if (3 <=? j)%nat then int_at e (TAtom "v12") any else True) /\
    (if (4 <=? j)%nat then int_at e (TAtom "v13") any else True) /\
    (if (5 <=? j)%nat then lookup (TAtom "chk1") e = Some (WPtr (mkPtr a (Obj a))) else True) /\
    (if (6 <=? j)%nat then lookup (TAtom "v15") e = Some (WPtr next) else True) /\
    exists S, (lst_cons (mkPtr a (Obj a)) v next xs ** htrue ** F)%h S m.

(** What holds at point k of [sum_points] with the frame F: at the
    entry, the precondition, the list from the parameter `v0` and F; on
    the edge back, the loop's state in `v15` and `v13`; at the head,
    [sum_head]; in the body, [sum_body]; at the exit, the
    postcondition, the sum an integer, and [htrue] and F. *)
Definition sum_assert (k : nat) (F : hprop) (e : env) (m : mem) : Prop :=
  match k with
  | 0%nat | 1%nat | 2%nat => exists p xs, lookup (TAtom "v0") e = Some (WPtr p) /\ exists S, (lst p xs ** F)%h S m
  | 3%nat => exists p s xs, lookup (TAtom "v15") e = Some (WPtr p) /\ lookup (TAtom "v13") e = Some (WInt s) /\
           exists S, (lst p xs ** htrue ** F)%h S m
  | 4%nat | 5%nat | 6%nat => sum_head (k - 4) F e m
  | 7%nat => sum_body 0 F e m
  | 15%nat | 16%nat => exists s, lookup (TAtom "pr.2") e = Some (WInt s) /\ exists S, (htrue ** F)%h S m
  | _ => sum_body (k - 8) F e m
  end.

(** A configuration running `sum` with the frame F and the callers
    callers below it: at point k, with no locals and no doom, where the
    assertion of k holds. *)
Definition sum_at (F : hprop) (callers : list (frame * pending)) (c : config) : Prop :=
  exists k pt e, c = mkConfig (mkFrame sum_fn e [] None pt) callers (c_mem c) (c_fuel c) /\
    nth_error sum_points k = Some pt /\ sum_assert k F e (c_mem c).

(** ## Facts the steps read from the assertions *)

(** A list's address is 0 or inside the address space. *)
Lemma lst_star_range : forall p xs R S m, objects_fit (m_regions m) -> (lst p xs ** R)%h S m ->
  0 <= ptr_addr p < 2 ^ 48.
Proof. intros p xs R S m Hfit H. destruct (star_elim_l _ _ _ _ H) as (S1 & H1). exact (lst_range _ _ _ _ Hfit H1). Qed.

(** What a node of the list at a gives the steps that read it. *)
Lemma cons_facts : forall a v next xs R S m, objects_fit (m_regions m) ->
  (lst_cons (mkPtr a (Obj a)) v next xs ** R)%h S m ->
  0 < a /\ a mod 8 = 0 /\ a + 16 <= 2 ^ 48 /\
  object_region a (m_regions m) = Some (mkRegion a (a + 16) Heap Live) /\
  load_bytes m a 8 = ptr_addr next /\ m_aux m a = ptr_cap next.
Proof.
  intros a v next xs R S m Hfit H. destruct (lst_cons_facts _ _ _ _ _ _ _ Hfit H) as (a' & E & Hr).
  injection E as <-. exact Hr.
Qed.

(** Add to the context what the separation-logic facts H give a step:
    a list's address range, and a node's region and next slot. *)
Ltac sep_facts Hfit :=
  try match goal with H : (lst ?p _ ** _)%h _ _ |- _ => pose proof (lst_star_range _ _ _ _ _ Hfit H) end;
  try match goal with H : (lst_cons (mkPtr ?a (Obj ?a)) _ _ _ ** _)%h _ _ |- _ =>
        destruct (cons_facts _ _ _ _ _ _ _ Hfit H) as (? & ? & ? & ? & ? & ?) end.

(** ## `sum`'s step *)

(** The point of the next configuration is point n of [sum_points] or
    a later one. *)
Ltac sum_find pt n :=
  lazymatch n with
  | 17%nat => fail
  | _ => first [ assert (Hpt : nth_error sum_points n = Some pt) by (vm_compute; reflexivity);
                 exists n, pt
               | sum_find pt (S n) ]
  end.

(** Turn the separation-logic hypotheses into what the next point's
    assertion needs: [htrue] added at the loop's entry; the list
    dropped into it at the exit; at a nonnull list, its first node, its
    pointer taken apart; after the body, the walked node dropped. *)
Ltac sum_prep Hfit :=
  try match goal with H : (lst ?p ?xs ** htrue ** ?G)%h ?S ?m |- _ =>
        pose proof (htrue_absorb _ _ _ _ (lst_registered _ _) H) end;
  try match goal with H : (lst ?p ?xs ** ?G)%h ?S ?m |- _ =>
        lazymatch G with (htrue ** _)%h => fail | _ => idtac end;
        pose proof (star_mono_r _ _ _ _ _ (htrue_intro _) H) end;
  try match goal with Hp : 0 < ptr_addr ?p, H : (lst ?p ?xs ** ?R)%h ?S ?m |- _ =>
        let Hc := fresh "Hc" in
        destruct (lst_nonnull xs p R S m ltac:(lia) H) as (? & ? & ? & Hc);
        destruct (lst_cons_facts _ _ _ _ _ _ _ Hfit Hc) as (? & ? & _); subst p end;
  try match goal with H : (lst_cons _ _ _ _ ** htrue ** _)%h _ _ |- _ =>
        pose proof (lst_cons_drop _ _ _ _ _ _ _ H) end.

(** The next configuration runs `sum` at its point, with the same
    callers and frame and the memory unchanged. *)
Ltac sum_next Hfit :=
  cbv beta; split; [|reflexivity]; unfold sum_at;
  match goal with |- exists k pt e, mkConfig (mkFrame _ _ _ _ ?pt') _ _ _ = _ /\ _ =>
    sum_find pt' 0%nat
  end;
  eexists; split; [subst; reflexivity|]; split; [assumption|]; cbn [c_mem];
  cbn [sum_assert Nat.sub]; try unfold sum_head; try unfold sum_body; cbn [Nat.leb Nat.eqb];
  sum_prep Hfit; show_facts; eassumption.

(** One point of [sum_step]: the point from Hk, the assertion Ha taken
    apart with what it gives about memory, the step computed, and its
    result shown safe. *)
Ltac sum_point pts Hk Ha Hfit :=
  cbv in Hk; injection Hk as <-; clear pts;
  cbn [sum_assert Nat.sub] in Ha; try unfold sum_head in Ha; try unfold sum_body in Ha;
  cbn [Nat.leb Nat.eqb] in Ha; unfold int_at in *; facts; sep_facts Hfit;
  remember (step _ _) as r eqn:E; step_reduce E; subst r; cbn [safe_step];
  solve [ intro; assumption | sum_next Hfit ].

(** `sum`'s specification, as one step: from any configuration running
    `sum` where its assertion holds with the frame F, under any callers,
    the step returns an integer to the caller with [htrue] and F
    holding, or is [safe_step] into such a configuration with the same
    callers and frame, the memory unchanged. Any frame: `sum` never
    writes, and a frame need survive only safepoints ([sum_safepoint]). *)
Lemma sum_step : forall ge F callers c, objects_fit (m_regions (c_mem c)) -> sum_at F callers c ->
  (exists x S, step ge c = return_step c (Ret (WInt x)) /\ (htrue ** F)%h S (c_mem c)) \/
  safe_step (fun c' => sum_at F callers c' /\ c_mem c' = c_mem c) (c_mem c) (step ge c).
Proof.
  intros ge F callers c Hfit (k & pt & e & Ec & Hk & Ha).
  rewrite Ec. clear Ec. cbn [c_mem] in Hfit |- *.
  set (m := c_mem c) in *. set (fuel := c_fuel c) in *. clearbody m fuel.
  set (pts := sum_points) in Hk. vm_compute in pts.
  remember sum_fn as f eqn:Hf.
  block_fact f sum_fn Hf (TAtom "start") b0 Hb0.
  block_fact f sum_fn Hf (TAtom "L3") b3 Hb3.
  block_fact f sum_fn Hf (TAtom "L4") b4 Hb4.
  block_fact f sum_fn Hf (TAtom "L5") b5 Hb5.
  assert (Hret : fn_ret f = RClass L) by (rewrite Hf; reflexivity).
  do 16 (destruct k as [|k]; [right; sum_point pts Hk Ha Hfit|]).
  destruct k as [|k]; [left|destruct k; discriminate Hk].
  cbv in Hk. injection Hk as <-. clear pts. cbn [sum_assert] in Ha.
  destruct Ha as (s & Hs & S & HS). exists (s mod 2 ^ 64), S. split; [|exact HS].
  cbn -[return_step]. rewrite Hret. cbn -[return_step]. rewrite Hs. reflexivity.
Qed.

(** ## Safepoints in `sum` *)

(** What survives a safepoint holds after it. *)
Lemma sp_apply : forall P S m m', sp_stable P -> P S m ->
  same_regions m m' -> m_bytes m' = m_bytes m -> aux_moves m m' -> P S m'.
Proof. intros P S m m' HP H Hr Hb Ha. exact (HP S m m' H Hr Hb Ha). Qed.

(** Prove that an assertion built from [star], the list, nodes, [emp]
    and [htrue], and the frame whose survival is HF, survives a
    safepoint. *)
Ltac sp_auto HF :=
  repeat first [ exact HF | apply lst_safepoint | apply htrue_sp_stable | apply node_sp_stable
               | apply pure_sp_stable | apply emp_sp_stable | apply star_sp_stable ].

(** Move every separation-logic hypothesis about the memory m to the
    memory m' after a safepoint. *)
Ltac sp_hyps m m' HF Hr Hb Hx :=
  repeat match goal with H : ?P ?S m |- _ =>
    lazymatch type of P with hprop => idtac end;
    let H' := fresh "Hsp" in
    pose proof (sp_apply P S m m' ltac:(sp_auto HF) H Hr Hb Hx) as H'; clear H
  end.

(** The poll on the back edge leaves the list alone: a safepoint keeps
    the assertion at every point of `sum`, for any frame that survives
    it. The environment and the point do not change; the memory changes
    only as [safepoint_shape] allows, which every assertion survives
    ([lst_safepoint]). *)
Lemma sum_safepoint : forall F callers c m', sp_stable F -> sum_at F callers c ->
  same_regions (c_mem c) m' -> m_bytes m' = m_bytes (c_mem c) -> aux_moves (c_mem c) m' ->
  sum_at F callers (mkConfig (c_frame c) (c_callers c) m' (c_fuel c)).
Proof.
  intros F callers c m' HF (k & pt & e & Ec & Hk & Ha) Hr Hb Hx.
  exists k, pt, e. split; [rewrite Ec; reflexivity|]. cbn [c_mem].
  split; [exact Hk|]. set (m := c_mem c) in *. clearbody m.
  assert (Hlt : (k < length sum_points)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
  vm_compute in Hlt.
  do 17 (destruct k as [|k];
    [cbn [sum_assert Nat.sub] in Ha |- *; try unfold sum_head in Ha |- *; try unfold sum_body in Ha |- *;
     cbn [Nat.leb Nat.eqb] in Ha |- *; unfold int_at in *; facts; sp_hyps m m' HF Hr Hb Hx;
     show_facts; eassumption|]).
  lia.
Qed.

(** ## `listsum` *)

(** The function `listsum`. *)
Definition listsum_fn : func := ls_fn "listsum".

(** Every point of `listsum`, numbered: the entry `start` (0, 1); the
    loop's head `L4`, entered from `start` or from the body (2, 3), its
    comparison and its branch (4, 5); the body `L5`, entered (6), then
    before each of its eight instructions and its jump back, which
    polls (7 to 15); the exit `L7`, entered (16), before its call of
    `sum` (17) and before its return (18). *)
Definition ls_points : list point :=
  [Enter (TAtom "start") None; ls_at listsum_fn "start" 0;
   Enter (TAtom "L4") (Some (TAtom "start")); Enter (TAtom "L4") (Some (TAtom "L5"));
   ls_at listsum_fn "L4" 0; ls_at listsum_fn "L4" 1;
   Enter (TAtom "L5") (Some (TAtom "L4"))] ++ map (ls_at listsum_fn "L5") (seq 0 9) ++
  [Enter (TAtom "L7") (Some (TAtom "L4")); ls_at listsum_fn "L7" 0; ls_at listsum_fn "L7" 1].

(** In the loop, after the first j instructions of the body: the list
    built so far from `pr.1`, the index `pr.2` an integer; then, from
    the allocation on, the new node at b, from `v12`, at first with a
    null next pointer and the value 0, its checked proof
    `chk0`, after the pointer store with the list for its next
    pointer, the pointer `v16` to its value and the long `v18` to
    store there, its half-checked proof `chk1`, after the store any
    value, and the next index `v21`. *)
Definition ls_body (j : nat) (e : env) (m : mem) : Prop :=
  exists h i xs, lookup (TAtom "pr.1") e = Some (WPtr h) /\ lookup (TAtom "pr.2") e = Some (WInt i) /\
  if (j =? 0)%nat then exists S, lst h xs S m else
  exists b, lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) /\ 0 < b /\ b mod 16 = 0 /\
    (if (2 <=? j)%nat then lookup (TAtom "chk0") e = Some (WPtr (mkPtr b (Obj b))) else True) /\
    (if (4 <=? j)%nat then lookup (TAtom "v16") e = Some (WPtr (mkPtr (b + 8) (Obj b))) else True) /\
    (if (5 <=? j)%nat then int_at e (TAtom "v18") any else True) /\
    (if (6 <=? j)%nat then lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 8) (Obj b))) else True) /\
    (if (8 <=? j)%nat then int_at e (TAtom "v21") any else True) /\
    exists v, (if (7 <=? j)%nat then True else v = 0) /\
    exists S, (node b (if (3 <=? j)%nat then h else null) v ** lst h xs)%h S m.

(** What holds at point k of [ls_points] besides the input: nothing
    before the loop; on the edge back, the list from `v12` and the next
    index `v21`; in the loop, [ls_body], with the comparison `v10` at
    the branch; at the exit and the call, the list from `pr.1`; after
    the call, `sum`'s result `v23` an integer. *)
Definition ls_assert (k : nat) (e : env) (m : mem) : Prop :=
  match k with
  | 0%nat | 1%nat | 2%nat => True
  | 3%nat => exists h i xs, lookup (TAtom "v12") e = Some (WPtr h) /\
               lookup (TAtom "v21") e = Some (WInt i) /\ exists S, lst h xs S m
  | 4%nat | 6%nat => ls_body 0 e m
  | 5%nat => int_at e (TAtom "v10") any /\ ls_body 0 e m
  | 16%nat | 17%nat => exists h xs, lookup (TAtom "pr.1") e = Some (WPtr h) /\ exists S, lst h xs S m
  | 18%nat => int_at e (TAtom "v23") any
  | _ => ls_body (k - 7) e m
  end.

(** A configuration running `listsum` with no caller: at point k, with
    no locals and no doom, the input `v0` an integer, and the
    assertion of k. *)
Definition ls_here (c : config) : Prop :=
  exists k pt e, c = mkConfig (mkFrame listsum_fn e [] None pt) [] (c_mem c) (c_fuel c) /\
    nth_error ls_points k = Some pt /\ int_at e (TAtom "v0") any /\ ls_assert k e (c_mem c).

(** `listsum` suspended in its call of `sum`, with the environment e:
    it resumes before its return, reading the result into `v23`. *)
Definition ls_caller (e : env) : frame * pending :=
  (mkFrame listsum_fn e [] None (Exec (TAtom "L7") [] (JRet (Tmp (TAtom "v23")))),
   mkPending (CResult (TAtom "v23") L) None).

(** The configuration invariant: live objects do not overlap, and
    either `listsum` runs with no caller, or `sum` runs, with the empty
    frame, above `listsum` suspended in its call. *)
Definition ls_inv (c : config) : Prop :=
  live_disjoint (c_mem c) /\
  (ls_here c \/ exists e, sum_at emp [ls_caller e] c /\ int_at e (TAtom "v0") any).

(** ## Facts `listsum`'s steps read *)

(** `sum` is the module's function of that name. *)
Lemma ls_find_direct_sum : find_direct (TAtom "sum") ls_module = Some (Defined sum_fn).
Proof. vm_compute. reflexivity. Qed.

(** The point `listsum` resumes at after its call. *)
Lemma ls_L7_1 : ls_at listsum_fn "L7" 1 = Exec (TAtom "L7") [] (JRet (Tmp (TAtom "v23"))).
Proof. vm_compute. reflexivity. Qed.

(** The initial memory holds no object. *)
Lemma ls_mem_regions : m_regions ls_mem = [].
Proof. vm_compute. reflexivity. Qed.

(** A node's region, inside the address space. *)
Lemma node_star_facts : forall b x v R S m, objects_fit (m_regions m) -> (node b x v ** R)%h S m ->
  object_region b (m_regions m) = Some (mkRegion b (b + 16) Heap Live) /\ b + 16 <= 2 ^ 48.
Proof.
  intros b x v R S m Hfit H. destruct (star_elim_l _ _ _ _ H) as (S1 & H1).
  pose proof (node_region _ _ _ _ _ H1) as Hr. split; [exact Hr|]. destruct (Hfit _ _ Hr). cbn in *. lia.
Qed.

(** The list after a node is 0 or inside the address space. *)
Lemma node_lst_range : forall b x v h xs S m, objects_fit (m_regions m) -> (node b x v ** lst h xs)%h S m ->
  0 <= ptr_addr h < 2 ^ 64.
Proof.
  intros b x v h xs S m Hfit H. destruct (star_elim_r _ _ _ _ H) as (S2 & H2).
  pose proof (lst_range _ _ _ _ Hfit H2). lia.
Qed.

(** A [fresh] node's base is positive, 16-aligned, and ends at or below
    2^64. *)
Lemma fresh_node : forall m b, fresh m (heap_req 16 16) b -> 0 < b /\ b mod 16 = 0 /\ b + 16 <= 2 ^ 64.
Proof. intros m b (H0 & H1 & H2 & _). cbn in *. auto. Qed.

(** A node at a 16-aligned address and the rest make a list. *)
Lemma lst_cons_intro16 : forall b h v xs S m, 0 < b -> b mod 16 = 0 ->
  (node b h v ** lst h xs)%h S m -> lst (mkPtr b (Obj b)) (v :: xs) S m.
Proof. intros b h v xs S m Hb Hm. apply lst_cons_intro; [exact Hb|]. Z.to_euclidean_division_equations. lia. Qed.

(** The step from `sum`'s return into `listsum`, resumed with the
    result in `v23`. *)
Lemma return_to_listsum : forall fr e x m fuel, fr_locals fr = [] ->
  return_step (mkConfig fr [ls_caller e] m fuel) (Ret (WInt x)) =
  Next (mkConfig (mkFrame listsum_fn (put (TAtom "v23") (WInt (x mod 2 ^ 64)) e) [] None
                          (Exec (TAtom "L7") [] (JRet (Tmp (TAtom "v23"))))) [] m fuel).
Proof. intros [f e0 l d p] e x m fuel H. cbn in H. subst l. reflexivity. Qed.

(** [safe_step] for an invariant is [safe_step] for a weaker one. *)
Lemma safe_step_mono : forall (I J : config -> Prop) m r, (forall c, I c -> J c) ->
  safe_step I m r -> safe_step J m r.
Proof.
  intros I J m r H Hs. destruct r as [c|o|q k|why]; cbn in *; auto. destruct Hs as [He Hk]. split; [exact He|]. intros base Hf. apply H, Hk, Hf.
Qed.

(** Add to the context the region of a node the assertion owns. *)
Ltac ls_facts Hfit :=
  try match goal with H : (node ?b _ _ ** _)%h _ _ |- _ =>
        destruct (node_star_facts _ _ _ _ _ _ Hfit H) as (? & ?) end.

(** The point of the next configuration is point n of [ls_points] or a
    later one. *)
Ltac ls_find pt n :=
  lazymatch n with
  | 19%nat => fail
  | _ => first [ assert (Hpt : nth_error ls_points n = Some pt) by (vm_compute; reflexivity);
                 exists n, pt
               | ls_find pt (S n) ]
  end.

(** Turn the separation-logic hypotheses into what the next point's
    assertion needs, from the memory the next configuration has: the
    empty list at the loop's entry; the new node beside the list after
    the allocation; the node's next slot after the pointer store, and
    its value after the store of the long; the list one longer on the
    edge back; the empty frame at the call. *)
Ltac ls_prep Hfit Hd :=
  try match goal with |- context[lst _ _ _ ?m] => pose proof (lst_nil m) end;
  try match goal with Hf : fresh ?m _ ?b, H : lst ?h ?xs ?S ?m |- _ =>
        pose proof (alloc_frame m b (lst h xs) S Hf (lst_stable _ _) (lst_registered _ _) H) end;
  try match goal with H : (node ?b null 0 ** lst ?h ?xs)%h ?S ?m |- context[store_aux ?m ?b _] =>
        pose proof (node_store_next m b null h 0 (lst h xs) S Hd (lst_stable _ _)
                      (node_lst_range _ _ _ _ _ _ _ Hfit H) H) end;
  try match goal with H : (node ?b ?h 0 ** lst ?h ?xs)%h ?S ?m, Hx : 0 <= ?x < _
             |- context[store_bytes ?m (?b + 8) 8 ?x] =>
        pose proof (node_store_value m b h 0 x (lst h xs) S Hd (lst_stable _ _) Hx H) end;
  try match goal with H : (node ?b ?h ?v ** lst ?h ?xs)%h ?S ?m, Hb : 0 < ?b, Hm : ?b mod 16 = 0 |- _ =>
        pose proof (lst_cons_intro16 b h v xs S m Hb Hm H) end;
  try match goal with H : lst ?h ?xs ?S ?m |- context[(_ ** emp)%h] => pose proof (star_emp_r _ _ _ H) end.

(** The memory after the step keeps live objects apart: it is the
    same, a store's, or an allocation's at a [fresh] base. *)
Ltac ls_disjoint Hd :=
  first [ exact Hd
        | exact (live_disjoint_same _ _ eq_refl Hd)
        | match goal with Hf : fresh _ _ _ |- _ => exact (live_disjoint_allocated _ _ _ Hd Hf ltac:(cbn; lia)) end ].

(** The next configuration is in [ls_inv]: `listsum` at its point, or,
    after the call, `sum` at its entry with `listsum` suspended. *)
Ltac ls_next Hfit Hd :=
  cbv beta iota; unfold ls_inv; cbn [c_mem]; split; [ls_disjoint Hd|];
  first
  [ left; unfold ls_here;
    match goal with |- exists k pt e, mkConfig (mkFrame _ _ _ _ ?pt') _ _ _ = _ /\ _ => ls_find pt' 0%nat end;
    eexists; split; [subst; reflexivity|]; split; [assumption|]; cbn [c_mem];
    split; [solve [show_facts]|];
    cbn [ls_assert Nat.sub]; try unfold ls_body; cbn [Nat.leb Nat.eqb];
    ls_prep Hfit Hd; solve [show_facts; eassumption]
  | right; eexists; split;
    [ unfold sum_at; exists 0%nat, (Enter (TAtom "start") None); eexists;
      split; [subst; reflexivity|]; split; [reflexivity|]; cbn [sum_assert c_mem lookup];
      rewrite ?term_eqb_refl; ls_prep Hfit Hd; solve [show_facts; eassumption]
    | solve [show_facts] ] ].

(** An allocation's result is safe: its extent is nonnegative, and
    every [fresh] base gives a configuration in [ls_inv]. *)
Ltac ls_fresh Hfit Hd :=
  split; [cbv; discriminate|]; intros ?base ?Hfresh;
  destruct (fresh_node _ _ Hfresh) as (? & ? & ?); ls_next Hfit Hd.

(** One point of [ls_here_safe]: as [sum_point]. *)
Ltac ls_point pts Hk Ha Hfit Hd :=
  cbv in Hk; injection Hk as <-; clear pts;
  cbn [ls_assert Nat.sub] in Ha; try unfold ls_body in Ha; cbn [Nat.leb Nat.eqb] in Ha;
  unfold int_at in *; facts; repeat match goal with H : ?v = 0 |- _ => is_var v; subst v end;
  ls_facts Hfit;
  remember (step _ _) as r eqn:E; step_reduce E; subst r; cbn [safe_step];
  solve [ intro; assumption | ls_next Hfit Hd | ls_fresh Hfit Hd ].

(** One step of `listsum` with no caller is [safe_step] for
    [ls_inv], in any genv whose `sum` is the module's. *)
Lemma ls_here_safe : forall ge c, find_direct (TAtom "sum") (ge_module ge) = Some (Defined sum_fn) ->
  live_disjoint (c_mem c) -> objects_fit (m_regions (c_mem c)) -> ls_here c ->
  safe_step ls_inv (c_mem c) (step ge c).
Proof.
  intros ge c Hfd Hd Hfit (k & pt & e & Ec & Hk & Hv0 & Ha).
  rewrite Ec. clear Ec. cbn [c_mem] in *.
  set (m := c_mem c) in *. set (fuel := c_fuel c) in *. clearbody m fuel.
  set (pts := ls_points) in Hk. vm_compute in pts.
  remember listsum_fn as f eqn:Hf. remember sum_fn as fs eqn:Hfs in Hfd |- *.
  assert (Hff : find_fn ge (TAtom "sum") = Some (Defined fs)) by (unfold find_fn; rewrite Hfd; reflexivity).
  clear Hfd.
  assert (Hcf : forall x rest, call_frame fs (x :: rest) =
            Some (mkFrame fs [(TAtom "v0", x)] [] None (Enter (TAtom "start") None)))
    by (subst fs; exact sum_call_frame).
  block_fact f listsum_fn Hf (TAtom "start") b0 Hb0.
  block_fact f listsum_fn Hf (TAtom "L4") b4 Hb4.
  block_fact f listsum_fn Hf (TAtom "L5") b5 Hb5.
  block_fact f listsum_fn Hf (TAtom "L7") b7 Hb7.
  assert (Hret : fn_ret f = RClass L) by (rewrite Hf; reflexivity).
  do 19 (destruct k as [|k]; [ls_point pts Hk Ha Hfit Hd|]).
  destruct k; discriminate Hk.
Qed.

(** One step from any configuration of [ls_inv] is [safe_step]:
    `listsum`'s own, or `sum`'s by its specification with the empty
    frame, where a return resumes `listsum` after its call. *)
Lemma ls_safe : forall ge c, find_direct (TAtom "sum") (ge_module ge) = Some (Defined sum_fn) ->
  ls_inv c -> objects_fit (m_regions (c_mem c)) -> safe_step ls_inv (c_mem c) (step ge c).
Proof.
  intros ge c Hfd [Hd [Hh | (e & Hs & Hv0)]] Hfit.
  - exact (ls_here_safe ge c Hfd Hd Hfit Hh).
  - destruct (sum_step ge emp _ c Hfit Hs) as [(x & S & E & _) | Hsafe].
    + rewrite E. destruct Hs as (k & pt & e' & Ec & _).
      rewrite Ec, return_to_listsum by reflexivity. cbn [safe_step].
      split; [exact Hd|]. left. unfold int_at in Hv0. destruct Hv0 as (n & Hn & _).
      exists 18%nat, (Exec (TAtom "L7") [] (JRet (Tmp (TAtom "v23")))),
        (put (TAtom "v23") (WInt (x mod 2 ^ 64)) e).
      split; [reflexivity|]. split; [vm_compute; reflexivity|].
      split; [show_facts | cbn [ls_assert]; show_facts].
    + revert Hsafe. apply safe_step_mono. intros c' [Hc' Em].
      split; [rewrite Em; exact Hd|]. right. exists e. split; assumption.
Qed.

(** The poll on the back edge leaves the list alone: a safepoint keeps
    [ls_inv], given that it keeps live objects apart, for `listsum`'s
    points as for `sum`'s ([sum_safepoint]). *)
Lemma ls_safepoint : forall c m', ls_inv c -> live_disjoint m' -> same_regions (c_mem c) m' ->
  m_bytes m' = m_bytes (c_mem c) -> aux_moves (c_mem c) m' ->
  ls_inv (mkConfig (c_frame c) (c_callers c) m' (c_fuel c)).
Proof.
  intros c m' [_ [Hh | (e & Hs & Hv0)]] Hd' Hr Hb Hx; split; [exact Hd'| |exact Hd'|].
  - left. destruct Hh as (k & pt & e & Ec & Hk & Hv0 & Ha). exists k, pt, e.
    split; [rewrite Ec; reflexivity|]. split; [exact Hk|]. split; [exact Hv0|]. cbn [c_mem].
    set (m := c_mem c) in *. clearbody m.
    assert (Hlt : (k < length ls_points)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
    vm_compute in Hlt.
    do 19 (destruct k as [|k];
      [cbn [ls_assert Nat.sub] in Ha |- *; try unfold ls_body in Ha |- *; cbn [Nat.leb Nat.eqb] in Ha |- *;
       unfold int_at in *; facts; repeat match goal with H : ?v = 0 |- _ => is_var v; subst v end;
       sp_hyps m m' emp_sp_stable Hr Hb Hx; show_facts; eassumption|]).
    lia.
  - right. exists e. split; [|exact Hv0]. exact (sum_safepoint emp _ c m' emp_sp_stable Hs Hr Hb Hx).
Qed.

(** A call with an integer first argument starts where [ls_inv] holds,
    with any fuel: the initial memory holds no object. *)
Lemma ls_start : forall n fuel,
  ls_inv (mkConfig (mkFrame listsum_fn [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None))
                   [] ls_mem fuel).
Proof.
  intros n fuel. split.
  - intros b1 r1 b2 r2 [E _]. cbn [c_mem] in E. rewrite ls_mem_regions in E. discriminate.
  - left. exists O, (Enter (TAtom "start") None), [(TAtom "v0", WInt n)].
    split; [reflexivity|]. split; [vm_compute; reflexivity|].
    split; [exists n; split; [reflexivity | exact I] | exact I].
Qed.

(** ## Over any runtime *)

(** listsum.c never panics under the runtime R. *)
Module SepListSum (R : Runtime).

(** Panics.v's property over R. *)
Module P := Panics R.

(** What a safepoint of R does (Pieces.v). *)
Module SS := SafepointShape R.

(** listsum.c never panics: for every input whose first word is an
    integer, with any fuel, no state of its run [fails], wherever its
    nodes are placed. *)
Theorem listsum_never_panics :
  P.never_panics ls_module (TAtom "listsum") (fun xs => exists n rest, xs = WInt n :: rest).
Proof.
  apply (P.never_panics_by_invariant _ _ _ ls_globals ls_mem listsum_fn ls_inv).
  - exact ls_initial.
  - apply ls_find_listsum.
  - intros xs (n & rest & ->). eexists. split; [apply listsum_call_frame|]. intros fuel. apply ls_start.
  - intros c s Hc Hr. apply ls_safe; [exact ls_find_direct_sum | exact Hc | exact (R.address_space _ _ Hr)].
  - intros c s s' m' Hc _ _ Hsp. destruct (SS.safepoint_shape _ _ _ _ Hsp) as (Hr & Hb & Ha).
    exact (ls_safepoint c m' Hc (SS.live_disjoint_safepoint _ _ _ _ Hsp (proj1 Hc)) Hr Hb Ha).
Qed.

End SepListSum.

(** The theorem for the interpreter's runtime. *)
Module InterpSepListSum := SepListSum InterpRuntime.

(** listsum.c never panics under the interpreter's runtime. *)
Theorem interp_listsum_never_panics :
  InterpSepListSum.P.never_panics ls_module (TAtom "listsum")
    (fun xs => exists n rest, xs = WInt n :: rest).
Proof. exact InterpSepListSum.listsum_never_panics. Qed.
