(** Glibc stores `c: atexit` handlers in a linked list of 32-slot
    blocks, beginning with a statically allocated `initial` block.
    This module proves [[hoare-triple|Hoare triples]] for
    `__new_exitfn`, `__internal_atexit`, `__cxa_atexit`, and `c: atexit`
    over any [[runtime]] registry, world, and
    [[genv|global environment]] that binds their symbols.

    To register a handler, `__internal_atexit` acquires
    `__exit_funcs_lock` with an atomic [[cas|compare-and-swap]],
    reserves the next slot through `__new_exitfn`, writes the function
    pointer, argument, and DSO handle, and releases the lock. Because
    our model is single-threaded, the lock is always free, so neither
    the contention wait path nor the wake path runs.

    When fewer than 32 exit handlers have been registered, glibc keeps
    all entries inside that single static buffer. In [exit_funcs_inv],
    we package the lock, shutdown flag, call counter, and static buffer
    together so [wp_glibc_cxa_atexit] and [wp_glibc_atexit] can append
    an entry and return 0. Because registration modifies the lock,
    counter, and static buffer, any external world must satisfy
    [wi_ignores] for those three objects. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic MemLogic.
From Glibc Require Import StdlibCode GlibcLogic LeavesLogic.
From Glibc Require GlibcLogic LeavesLogic.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** [new_exitfn_fn] is the decoded IR body of glibc's `__new_exitfn`. *)
Definition new_exitfn_fn : func := Eval vm_compute in stdlib_fn "__new_exitfn".
(** [internal_atexit_fn] is the decoded IR body of glibc's
    `__internal_atexit`. *)
Definition internal_atexit_fn : func := Eval vm_compute in stdlib_fn "__internal_atexit".
(** [cxa_atexit_fn] is the decoded IR body of glibc's
    `__GI___cxa_atexit`. *)
Definition cxa_atexit_fn : func := Eval vm_compute in stdlib_fn "__GI___cxa_atexit".
(** [atexit_fn] is the decoded IR body of glibc's `c: atexit`. *)
Definition atexit_fn : func := Eval vm_compute in stdlib_fn "atexit".

(** [new_exitfn_frame] states the initial call [[frame]] constructed
    when calling `__new_exitfn` with pointer p. *)
Lemma new_exitfn_frame p :
  call_frame new_exitfn_fn [WPtr p] =
  Some (mkFrame new_exitfn_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** [internal_atexit_frame] states the initial call [[frame]]
    constructed when calling `__internal_atexit` with f, a, d, and l. *)
Lemma internal_atexit_frame f a d l :
  call_frame internal_atexit_fn [WPtr f; WPtr a; WPtr d; WPtr l] =
  Some (mkFrame internal_atexit_fn [(TAtom "v6", WPtr l); (TAtom "v4", WPtr d); (TAtom "v2", WPtr a);
                                    (TAtom "v0", WPtr f)] [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** [cxa_atexit_frame] states the initial call [[frame]] constructed
    when calling `__cxa_atexit` with f, a, and d. *)
Lemma cxa_atexit_frame f a d :
  call_frame cxa_atexit_fn [WPtr f; WPtr a; WPtr d] =
  Some (mkFrame cxa_atexit_fn [(TAtom "v4", WPtr d); (TAtom "v2", WPtr a); (TAtom "v0", WPtr f)] [] None
          (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** Acquiring `__exit_funcs_lock` with an atomic compare-and-swap
    replaces four zero bytes with 1, as [lock_take] evaluates. *)
Lemma lock_take : (if of_bytes [0; 0; 0; 0] =? 0 mod 2 ^ 32 then le_bytes 1 4 else [0; 0; 0; 0]) = [1; 0; 0; 0].
Proof. reflexivity. Qed.

(** Releasing the mutex stores zero back into the four-byte lock word
    when its current value is 1. Lemma [lock_release] evaluates that
    conditional write to four zero bytes. *)
Lemma lock_release : (if of_bytes [1; 0; 0; 0] =? 1 mod 2 ^ 32 then le_bytes 0 4 else [1; 0; 0; 0]) = [0; 0; 0; 0].
Proof. reflexivity. Qed.

(** The global environment must resolve `__new_exitfn`,
    `__internal_atexit`, and the `__cxa_atexit` alias to the decoded
    functions above. Predicate [exit_fns] packages those three bindings. *)
Definition exit_fns (ge : genv) : Prop :=
  find_fn ge (TAtom "__new_exitfn") = Some (Defined new_exitfn_fn) /\
  find_fn ge (TAtom "__internal_atexit") = Some (Defined internal_atexit_fn) /\
  find_fn ge (TAtom "__cxa_atexit") = Some (Defined cxa_atexit_fn).

(** Exit handler registration touches five global or static objects: the
    lock, the shutdown flag, the call counter, the list head, and the
    `initial` block. Record [exit_objs] pairs each object's base address
    with its [[region]]. *)
Record exit_objs : Type := mkExitObjs {
  xo_lock : Z; xo_lock_reg : region;
  xo_done : Z; xo_done_reg : region;
  xo_called : Z; xo_called_reg : region;
  xo_funcs : Z; xo_funcs_reg : region;
  xo_init : Z; xo_init_reg : region
}.

(** Each exit-handler object must satisfy the alignment and address
    bounds checked by glibc's instructions. Predicate [exit_layout]
    requires every object to lie below 2^64, keeps the lock and
    `initial` below 2^63 for [[half_check|half checks]], and reserves
    1040 bytes for `initial`. *)
Definition exit_layout (x : exit_objs) : Prop :=
  0 <= xo_lock x /\ xo_lock x mod 4 = 0 /\ xo_lock x + 4 <= r_end (xo_lock_reg x) <= 2 ^ 63 /\
  0 <= xo_done x /\ xo_done x + 1 <= r_end (xo_done_reg x) <= 2 ^ 64 /\
  0 <= xo_called x /\ xo_called x + 8 <= r_end (xo_called_reg x) <= 2 ^ 64 /\
  0 <= xo_funcs x /\ xo_funcs x mod 8 = 0 /\ xo_funcs x + 8 <= r_end (xo_funcs_reg x) <= 2 ^ 64 /\
  0 < xo_init x /\ xo_init x mod 8 = 0 /\ xo_init x + 1040 <= r_end (xo_init_reg x) <= 2 ^ 63.

(** The compiled functions look up four global variables by symbol name
    in the global environment. Predicate [exit_globals] checks that
    those four symbols map to writable pointers for the objects in x. *)
Definition exit_globals (ge : genv) (x : exit_objs) : Prop :=
  lookup (TAtom "__exit_funcs_lock") (ge_globals ge) = Some (mkPtr (xo_lock x) (Obj (xo_lock x))) /\
  lookup (TAtom "__exit_funcs_done") (ge_globals ge) = Some (mkPtr (xo_done x) (Obj (xo_done x))) /\
  lookup (TAtom "__new_exitfn_called") (ge_globals ge) = Some (mkPtr (xo_called x) (Obj (xo_called x))) /\
  lookup (TAtom "__exit_funcs") (ge_globals ge) = Some (mkPtr (xo_funcs x) (Obj (xo_funcs x))).

(** When a proof writes only to a single object b, the world
    interpretation needs to know that every modified piece key belongs
    to b. Lemma [ids_of] turns a `Forall` check over the piece list ps
    into that universal property. *)
Lemma ids_of (b : Z) (ps : list (piece * pval)) :
  Forall (fun lv => piece_id lv.1 = b) ps -> forall l, l ∈ ps.*1 -> piece_id l = b.
Proof.
  intros H l Hl. destruct (list_elem_of_fmap_1 _ _ _ Hl) as [[l' v] [E Hin]]. subst l.
  rewrite Forall_forall in H. exact (H (l', v) Hin).
Qed.

(** The tactic [ids] proves that every key in a concrete piece list
    belongs to the same object by applying [ids_of]. *)
Ltac ids := apply ids_of; cbn; repeat constructor.


Module ML := MemLogicOn R LG0.
Module LG := LG0.
Module L := LG.L.
Import L LG GlibcLogic ML LeavesLogic.

Local Opaque new_exitfn_fn internal_atexit_fn cxa_atexit_fn atexit_fn.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** Every Iris proof needs a state interpretation linking memory and
    world state to the operational semantics. [atexit_irisGS] builds
    that instance from [registry], [wi], and [ge]. *)
Local Instance atexit_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** [gexpr] abbreviates the expression type of the parameterized
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Modifying glibc's internal exit-handler globals must not invalidate
    the caller's [[state-interpretation|world interpretation]]. Predicate
    [wi_ignores] states that [wi] is preserved by any byte or pointer
    store inside object b up to bound e. *)
Definition wi_ignores (b e : Z) : Prop :=
  forall m wd h ps a n x c, b <= a -> a + n <= e -> (forall l, l ∈ ps.*1 -> piece_id l = b) -> wi m wd h ->
    wi (store_bytes m a n x) wd (overwrite ps h) /\ wi (store_bytes (store_aux m a c) a n x) wd (overwrite ps h).

(** Registering an exit handler writes to three global objects: the
    lock, the call counter, and the static handler block. Predicate
    [exit_wi] ensures that the caller's world invariant ignores all
    three. *)
Definition exit_wi (x : exit_objs) : Prop :=
  wi_ignores (xo_lock x) (r_end (xo_lock_reg x)) /\ wi_ignores (xo_called x) (r_end (xo_called_reg x)) /\
  wi_ignores (xo_init x) (r_end (xo_init_reg x)).

(** Each store instruction in the proof must show that the world
    interpretation ignores the modified object. The tactic [ign]
    discharges that side condition from hypothesis H. *)
Ltac ign H :=
  let m := fresh "m" in let wd := fresh "wd" in let h := fresh "h" in let Hw := fresh "Hw" in
  intros m wd h ? Hw;
  first [ refine (proj1 (H m wd h _ _ _ _ CNone _ _ _ Hw)); [lia | lia | ids]
        | refine (proj2 (H m wd h _ _ _ _ _ _ _ _ Hw)); [lia | lia | ids] ].

(** Applying a step rule creates a side condition showing that the world
    stays valid across garbage-collection safepoints. The tactic [inst]
    closes that [SafepointStable] obligation by typeclass search. *)


(** The tactic [st] advances the proof by one symbolic IR step,
    dispatching on whether the frame sits at a let binding, a
    [[flight]], a block entry, or a jump. *)


(** Functions in this file load global addresses such as
    `__exit_funcs_lock` and `__new_exitfn_called`. The tactic
    [st_global] steps past a global pointer load using its binding
    hypothesis Hs. *)


(** The tactic [br] steps across a conditional branch and immediately
    simplifies its boolean condition. *)


(** Both branches of `__new_exitfn` finish by claiming the chosen slot
    and updating the global call counter. The tactic [tail58] steps
    through that shared tail block `L121`, marks slot k in use, and
    returns its pointer. *)
Ltac tail58 k c Hc Hgcl Hwib Hwcl :=
  step;
  rule1 "Hil" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]);
  rule2 "Hil" "Hfl0" ltac:(eapply wp_raw_store; inst;
    [reflexivity | reflexivity | reflexivity | arith | ign Hwib]);
  step_global Hgcl;
  rule1 "Hcl" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]);
  rule2 "Hcl" "Hcc" ltac:(eapply wp_raw_load; inst; [reflexivity | reflexivity | reflexivity | arith]);
  rewrite (Z.mod_small c (2 ^ 64)); [|lia]; step;
  rule1 "Hcl" ltac:(eapply wp_renew; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith]);
  rule2 "Hcl" "Hcc" ltac:(eapply wp_raw_store; inst; [reflexivity | reflexivity | reflexivity | arith | ign Hwcl]);
  step; step; iApply wp_ret; [reflexivity | reflexivity |]; nx; simp.

(** Each slot in an `exit_function_list` block holds a 32-byte record at
    offset o. Predicate [slot] owns the flavor integer v together with
    the function pointer x, argument pointer y, and DSO handle z. *)
Definition slot (b o v : Z) (x y z : ptr) : iProp Σ :=
  icell b o v ∗ pcell b (o + 8) x ∗ pcell b (o + 16) y ∗ pcell b (o + 24) z.

(** A registered C++ exit handler fills one 32-byte slot with flavor 4
    (`ef_cxa`). Predicate [entry] instantiates [slot] with that flavor
    and the handler tuple e. *)
Definition entry (b o : Z) (e : ptr * ptr * ptr) : iProp Σ := slot b o 4 e.1.1 e.1.2 e.2.

(** An unused slot in `initial` may contain arbitrary bytes and
    pointers before it is claimed. Predicate [spare] existentially
    quantifies over its four fields. *)
Definition spare (b o : Z) : iProp Σ := ∃ v x y z, slot b o v x y z.

(** A single static array holds up to 32 exit handlers before glibc
    needs to allocate another block on the heap. Predicate [exit_block]
    owns that static block, its null link pointer, its entry count, the
    registered entries, and the remaining spare slots. *)
Definition exit_block (b : Z) (reg : region) (ents : list (ptr * ptr * ptr)) : iProp Σ :=
  live b reg ∗ pcell b 0 null ∗ icell b 8 (Z.of_nat (List.length ents)) ∗
  ([∗ list] i ↦ e ∈ ents, entry b (16 + 32 * Z.of_nat i) e) ∗
  ([∗ list] i ∈ seqZ (Z.of_nat (List.length ents)) (32 - Z.of_nat (List.length ents)), spare b (16 + 32 * i)).

(** Claiming the next free handler slot requires peeling off the head of
    the remaining spare-slot list. Lemma [spares_cons] splits slot k
    from the spare slots starting at k + 1 whenever k is below 32. *)
Lemma spares_cons b k :
  0 <= k < 32 ->
  ([∗ list] i ∈ seqZ k (32 - k), spare b (16 + 32 * i)) ⊣⊢
  spare b (16 + 32 * k) ∗ [∗ list] i ∈ seqZ (k + 1) (32 - (k + 1)), spare b (16 + 32 * i).
Proof.
  intros Hk. rewrite (seqZ_cons k (32 - k)); [|lia]. rewrite big_sepL_cons.
  replace (Z.succ k) with (k + 1) by lia. replace (Z.pred (32 - k)) with (32 - (k + 1)) by lia. done.
Qed.

(** Calling `__new_exitfn` reserves the next slot in `initial` whenever
    fewer than 32 entries are registered and shutdown has not begun.
    Lemma [wp_new_exitfn] marks slot k with flavor `ef_us` (1),
    increments `idx` and `__new_exitfn_called`, and returns a pointer to
    slot k. *)
Lemma wp_new_exitfn x ents c Φ :
  exit_layout x -> exit_globals ge x -> exit_wi x -> (List.length ents < 32)%nat -> 0 <= c < 2 ^ 64 ->
  live (xo_done x) (xo_done_reg x) ∗ ibyte (xo_done x) 0 0 ∗
  live (xo_called x) (xo_called_reg x) ∗ icell (xo_called x) 0 c ∗
  live (xo_funcs x) (xo_funcs_reg x) ∗ pcell (xo_funcs x) 0 (mkPtr (xo_init x) (Obj (xo_init x))) ∗
  exit_block (xo_init x) (xo_init_reg x) ents -∗
  (live (xo_done x) (xo_done_reg x) ∗ ibyte (xo_done x) 0 0 ∗
   live (xo_called x) (xo_called_reg x) ∗ icell (xo_called x) 0 ((c + 1) mod 2 ^ 64) ∗
   live (xo_funcs x) (xo_funcs_reg x) ∗ pcell (xo_funcs x) 0 (mkPtr (xo_init x) (Obj (xo_init x))) ∗
   live (xo_init x) (xo_init_reg x) ∗ pcell (xo_init x) 0 null ∗
   icell (xo_init x) 8 (Z.of_nat (List.length ents) + 1) ∗
   ([∗ list] i ↦ e ∈ ents, entry (xo_init x) (16 + 32 * Z.of_nat i) e) ∗
   ([∗ list] i ∈ seqZ (Z.of_nat (List.length ents) + 1) (32 - (Z.of_nat (List.length ents) + 1)),
      spare (xo_init x) (16 + 32 * i)) ∗
   (∃ y z w, slot (xo_init x) (16 + 32 * Z.of_nat (List.length ents)) 1 y z w) -∗
   Φ (Ret (WPtr (mkPtr (xo_init x + 16 + 32 * Z.of_nat (List.length ents)) (Obj (xo_init x)))))) -∗
  WP (ERun (mkFrame new_exitfn_fn [(TAtom "v0", WPtr (mkPtr (xo_funcs x) (Obj (xo_funcs x))))] [] None
              (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct x as [lk lkr dn dnr cl clr fs fsr ib ibr]. unfold exit_layout, exit_globals, exit_wi.
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg].
  intros (Hl0 & Hl4 & Hle & Hd0 & Hde & Hc0 & Hce & Hf0 & Hf8 & Hfe & Hi0 & Hi8 & Hie)
    (Hglk & Hgdn & Hgcl & Hgfs) (Hwlk & Hwcl & Hwib) Hk Hc.
  unfold exit_block. remember (Z.of_nat (List.length ents)) as k eqn:Ek. assert (Hk' : 0 <= k < 32) by lia.
  iIntros "(Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hil & Hnext & Hidx & Hents & Hspares) HΦ".
  rewrite (spares_cons ib k Hk'). iDestruct "Hspares" as "[(%v0 & %y & %z & %w & Hfl0 & Hy & Hz & Hw) Hspares]".
  step. step_global Hgdn.
  rule1 "Hdl" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  rule2 "Hdl" "Hdb" ltac:(eapply wp_raw_load_byte; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | left; reflexivity | arith]). (branch_symbolic; LeavesLogic.decide_branch). step.
  rule1 "Hfl" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Hfl Hfc Hil");
    [reflexivity | reflexivity | reflexivity | arith | arith | arith |].
  nx. iIntros "Hfl Hfc Hil". cbn [live_cap]. step. step. step. step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step.
  rule1 "Hil" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hidx" ltac:(eapply wp_raw_load; inst;
    [reflexivity | reflexivity | reflexivity | arith]). step. step. step. (branch_symbolic; LeavesLogic.decide_branch).
  destruct (Z.ltb_spec 0 k) as [Hpos|Hzero]; simp.
  - destruct (lookup_lt_is_Some_2 ents (Z.to_nat (k - 1))) as [e He]; [lia|].
    iDestruct (big_sepL_lookup_acc _ ents _ e He with "Hents") as "[(Hef & Hex) Hents]".
    rewrite Z2Nat.id; [|lia].
    step. step. step. step. step. simp.
    rule1 "Hil" ltac:(eapply wp_check_read; inst;
      [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
    rule2 "Hil" "Hef" ltac:(eapply wp_raw_load; inst;
      [reflexivity | reflexivity | reflexivity | arith]). iDestruct ("Hents" with "[$Hef $Hex]") as "Hents".
    step. (branch_symbolic; LeavesLogic.decide_branch). step. (branch_symbolic; LeavesLogic.decide_branch). step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step. step. step. (branch_symbolic; LeavesLogic.decide_branch).
    step. step. step. step. step. step. simp.
    rule1 "Hil" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
    rule2 "Hil" "Hidx" ltac:(eapply wp_raw_store; inst;
      [reflexivity | reflexivity | reflexivity | arith | ign Hwib]). step. step. step. step. (branch_symbolic; LeavesLogic.decide_branch).
    tail58 k c Hc Hgcl Hwib Hwcl. rewrite Zmod_mod.
    replace (ib + 16 + k * 32) with (ib + 16 + 32 * k) by lia.
    iApply "HΦ". iFrame "Hdl Hdb Hcl Hcc Hfl Hfc Hil Hnext Hidx Hents Hspares". iExists y, z, w.
    iFrame "Hfl0 Hy Hz Hw".
  - assert (k = 0) as -> by lia. step. (branch_symbolic; LeavesLogic.decide_branch). step. step.
    rule1 "Hil" ltac:(eapply wp_renew; inst;
      [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith]).
    rule2 "Hil" "Hidx" ltac:(eapply wp_raw_store; inst;
      [reflexivity | reflexivity | reflexivity | arith | ign Hwib]).
    rule1 "Hil" ltac:(eapply wp_half_check_read; inst;
      [reflexivity | reflexivity | reflexivity | left; reflexivity | arith | arith | arith | arith | arith]).
    iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 null ibr with "Hil Hnext []");
      [reflexivity | reflexivity | reflexivity | arith | arith | arith | done |]. nx. iIntros "Hil Hnext _".
    step. step. step. step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step. (branch_symbolic; LeavesLogic.decide_branch). step. (branch_symbolic; LeavesLogic.decide_branch). step. step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step. step.
    rule1 "Hil" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
    rule2 "Hil" "Hidx" ltac:(eapply wp_raw_store; inst;
      [reflexivity | reflexivity | reflexivity | arith | ign Hwib]).
    step. step. step. step. (branch_symbolic; LeavesLogic.decide_branch). tail58 0 c Hc Hgcl Hwib Hwcl. rewrite Zmod_mod Z.mul_0_r !Z.add_0_r.
    iApply "HΦ". iFrame "Hdl Hdb Hcl Hcc Hfl Hfc Hil Hnext Hidx Hents Hspares". iExists y, z, w.
    iFrame "Hfl0 Hy Hz Hw".
Qed.

(** Callers of `c: atexit` need a single invariant that tracks all
    global and static exit-handler state between calls. Predicate
    [exit_funcs_inv] owns the free lock, the shutdown flag, the call
    counter, the list head, and `initial`. *)
Definition exit_funcs_inv (x : exit_objs) (ents : list (ptr * ptr * ptr)) (c : Z) : iProp Σ :=
  ⌜(List.length ents <= 32)%nat /\ 0 <= c < 2 ^ 64⌝ ∗
  live (xo_lock x) (xo_lock_reg x) ∗ bytes (xo_lock x) 0 [0; 0; 0; 0] ∗
  live (xo_done x) (xo_done_reg x) ∗ ibyte (xo_done x) 0 0 ∗
  live (xo_called x) (xo_called_reg x) ∗ icell (xo_called x) 0 c ∗
  live (xo_funcs x) (xo_funcs_reg x) ∗ pcell (xo_funcs x) 0 (mkPtr (xo_init x) (Obj (xo_init x))) ∗
  exit_block (xo_init x) (xo_init_reg x) ents.

(** Once `__internal_atexit` fills in the newly claimed slot, we must
    fold that slot back into the list of registered entries. Lemma
    [exit_block_snoc] reassembles [exit_block] for `ents ++ [e]`. *)
Lemma exit_block_snoc b reg ents e :
  live b reg ∗ pcell b 0 null ∗ icell b 8 (Z.of_nat (List.length ents) + 1) ∗
  ([∗ list] i ↦ e' ∈ ents, entry b (16 + 32 * Z.of_nat i) e') ∗ entry b (16 + 32 * Z.of_nat (List.length ents)) e ∗
  ([∗ list] i ∈ seqZ (Z.of_nat (List.length ents) + 1) (32 - (Z.of_nat (List.length ents) + 1)),
     spare b (16 + 32 * i)) ⊢
  exit_block b reg (ents ++ [e]).
Proof.
  rewrite /exit_block length_app big_sepL_snoc. cbn [List.length].
  replace (Z.of_nat (List.length ents + 1)) with (Z.of_nat (List.length ents) + 1) by lia.
  iIntros "($ & $ & $ & $ & $ & $)".
Qed.

(** Acquiring or releasing the mutex updates the lock word in memory, so
    the step rule asks why the caller's world invariant stays valid. The
    tactic [cas_ign] discharges that obligation from hypothesis H. *)
Ltac cas_ign H := intros _; ign H.

(** Calling `__internal_atexit` with a non-null function pointer fnp,
    argument argp, and DSO handle dsop acquires the lock, claims a slot
    from `__new_exitfn`, writes the entry, releases the lock, and
    returns 0. Theorem [wp_internal_atexit] proves this specification
    and updates [exit_funcs_inv] with the new entry. *)
Lemma wp_internal_atexit x ents c fnp argp dsop Φ :
  exit_layout x -> exit_globals ge x -> exit_wi x -> (List.length ents < 32)%nat ->
  0 < ptr_addr fnp < 2 ^ 64 -> find_fn ge (TAtom "__new_exitfn") = Some (Defined new_exitfn_fn) ->
  exit_funcs_inv x ents c -∗
  (exit_funcs_inv x (ents ++ [(fnp, argp, dsop)]) ((c + 1) mod 2 ^ 64) -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (mkFrame internal_atexit_fn [(TAtom "v6", WPtr (mkPtr (xo_funcs x) (Obj (xo_funcs x))));
       (TAtom "v4", WPtr dsop); (TAtom "v2", WPtr argp); (TAtom "v0", WPtr fnp)] [] None
       (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct x as [lk lkr dn dnr cl clr fs fsr ib ibr]. intros Hlay Hgl Hwi Hk Hfp Hnf.
  pose proof Hlay as Hl_. destruct Hl_ as (Hl0 & Hl4 & Hle & _ & _ & _ & _ & _ & _ & _ & Hi0 & Hi8 & Hie).
  pose proof Hgl as Hg_. destruct Hg_ as (Hglk & _). pose proof Hwi as Hw_. destruct Hw_ as (Hwlk & _ & Hwib).
  iIntros "((%Hk32 & %Hc) & Hll & Hlb & Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hblk) HΦ".
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg]
    in *.
  step. step. step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step_global Hglk.
  rule1 "Hll" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hll" "Hlb" ltac:(eapply wp_raw_cas_w; inst;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwlk]). rewrite lock_take.
  step. (branch_symbolic; LeavesLogic.decide_branch). step. step. (branch_symbolic; LeavesLogic.decide_branch). step.
  eapply step_wand; [eapply wp_call_bind; inst; [reflexivity | exact Hnf | apply new_exitfn_frame] |].
  iApply (wp_new_exitfn (mkExitObjs lk lkr dn dnr cl clr fs fsr ib ibr) ents c
            with "[$Hdl $Hdb $Hcl $Hcc $Hfl $Hfc $Hblk]");
    [exact Hlay | exact Hgl | exact Hwi | exact Hk | exact Hc |].
  iIntros "(Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hil & Hnext & Hidx & Hents & Hspares &
            (%y & %z & %w & Hf & Hy & Hz & Hw))".
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg].
  remember (Z.of_nat (List.length ents)) as k eqn:Ek. assert (Hk' : 0 <= k < 32) by lia.
  iExists _. iSplit; [iPureIntro; reflexivity|]. nx. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step. step. (branch_symbolic; LeavesLogic.decide_branch). step. step.
  rule1 "Hil" ltac:(eapply wp_check; inst; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hy" ltac:(eapply wp_raw_store_pointer; inst;
    [reflexivity | reflexivity | reflexivity | arith | arith | ign Hwib]).
  step.
  rule1 "Hil" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hil" "Hz" ltac:(eapply wp_raw_store_pointer; inst;
    [reflexivity | reflexivity | reflexivity | arith | arith | ign Hwib]).
  step.
  rule1 "Hil" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hil" "Hw" ltac:(eapply wp_raw_store_pointer; inst;
    [reflexivity | reflexivity | reflexivity | arith | arith | ign Hwib]).
  rule1 "Hil" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hil" "Hf" ltac:(eapply wp_raw_store; inst; [reflexivity | reflexivity | reflexivity | arith | ign Hwib]).
  step_global Hglk.
  rule1 "Hll" ltac:(eapply wp_check_read; inst;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_sub_bytes_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 [1; 0; 0; 0] (WInt 1)
            (DfracOwn 1) (DfracOwn 1) with "Hll Hlb");
    [reflexivity | reflexivity | reflexivity | reflexivity | left; reflexivity | arith |]. nx. iIntros "Hll Hlb".
  step. step.
  rule1 "Hll" ltac:(eapply wp_half_check; inst;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hll" "Hlb" ltac:(eapply wp_raw_cas_w; inst;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwlk]). rewrite lock_release.
  step. (branch_symbolic; LeavesLogic.decide_branch). step. step. (branch_symbolic; LeavesLogic.decide_branch). step.
  iApply wp_ret; [reflexivity | reflexivity |]. nx.
  rewrite (Z.mod_small 4 (2 ^ 64)); [|lia].
  iApply "HΦ". rewrite /exit_funcs_inv.
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg].
  iSplit. { iPureIntro. rewrite length_app /=. split; [lia | apply Z.mod_pos_bound; lia]. }
  iFrame "Hll Hlb Hdl Hdb Hcl Hcc Hfl Hfc". iApply exit_block_snoc. subst k.
  iFrame "Hil Hnext Hidx Hents Hspares". iFrame "Hf Hy Hz Hw".
Qed.

(** Calling `__cxa_atexit` supplies `&__exit_funcs` implicitly and
    delegates to `__internal_atexit`. Theorem [wp_glibc_cxa_atexit]
    proves that registering a non-null handler appends the entry
    `(fnp, argp, dsop)` to [exit_funcs_inv] and returns 0. *)
Lemma wp_glibc_cxa_atexit x ents c fnp argp dsop Φ :
  exit_layout x -> exit_globals ge x -> exit_wi x -> exit_fns ge -> (List.length ents < 32)%nat ->
  0 < ptr_addr fnp < 2 ^ 64 ->
  exit_funcs_inv x ents c -∗
  (exit_funcs_inv x (ents ++ [(fnp, argp, dsop)]) ((c + 1) mod 2 ^ 64) -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (mkFrame cxa_atexit_fn [(TAtom "v4", WPtr dsop); (TAtom "v2", WPtr argp); (TAtom "v0", WPtr fnp)]
       [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hlay Hgl Hwi (Hnf & Hia & _) Hk Hfp. pose proof Hgl as Hg_. destruct Hg_ as (_ & _ & _ & Hgfs).
  iIntros "Hinv HΦ". step. step_global Hgfs.
  eapply step_wand; [eapply wp_call_bind; inst; [reflexivity | exact Hia | apply internal_atexit_frame] |].
  iApply (wp_internal_atexit with "Hinv");
    [exact Hlay | exact Hgl | exact Hwi | exact Hk | exact Hfp | exact Hnf |].
  iIntros "Hinv". iExists _. iSplit; [iPureIntro; reflexivity|]. nx. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iApply ("HΦ" with "Hinv").
Qed.

(** Calling `c: atexit` is a thin wrapper that calls `__cxa_atexit`
    with null argument and DSO pointers. Theorem [wp_glibc_atexit]
    proves that registering a non-null handler fnp appends
    `(fnp, null, null)` to [exit_funcs_inv] and returns 0. *)
Lemma wp_glibc_atexit x ents c fnp Φ :
  exit_layout x -> exit_globals ge x -> exit_wi x -> exit_fns ge -> (List.length ents < 32)%nat ->
  0 < ptr_addr fnp < 2 ^ 64 ->
  exit_funcs_inv x ents c -∗
  (exit_funcs_inv x (ents ++ [(fnp, null, null)]) ((c + 1) mod 2 ^ 64) -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun (mkFrame atexit_fn [(TAtom "v0", WPtr fnp)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hlay Hgl Hwi Hfns Hk Hfp. pose proof Hfns as Hf_. destruct Hf_ as (_ & _ & Hca).
  iIntros "Hinv HΦ". step.
  eapply step_wand; [eapply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ [WPtr fnp; WPtr null; WPtr null]); inst;
    [reflexivity | exact Hca | apply cxa_atexit_frame] |].
  iApply (wp_glibc_cxa_atexit with "Hinv");
    [exact Hlay | exact Hgl | exact Hwi | exact Hfns | exact Hk | exact Hfp |].
  iIntros "Hinv". iExists _. iSplit; [iPureIntro; reflexivity|]. nx. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iApply ("HΦ" with "Hinv").
Qed.

End rules.
