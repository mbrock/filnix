(** OpenSSL compares secret unsigned integers without branching on them.
    This module verifies [constant_time_lt] directly on the typed checked IR
    emitted by `nanofil -O` in [CtLtCode], with C source-hint temporary names
    from [CtLtNames]. The returned mask may reveal which integer is smaller,
    but the execution trace must reveal neither input before the caller
    chooses to disclose that result.

    We use the two function bodies from OpenSSL 3.6.0's
    [constant_time.h](https://github.com/openssl/openssl/blob/openssl-3.6.0/include/internal/constant_time.h).
    The fixture removes only their static inline qualifiers so the helper
    becomes a direct call that both the reflective taint checker and the
    [[iris|Iris]] proof check separately.

    ```c
    unsigned int constant_time_msb(unsigned int a) {
        return 0 - (a >> (sizeof(a) * 8 - 1));
    }
    unsigned int constant_time_lt(unsigned int a, unsigned int b) {
        return constant_time_msb(a ^ ((a ^ b) | ((a - b) ^ b)));
    }
    ```

    Subtraction alone cannot decide unsigned order from its high bit because
    it wraps when the operands straddle the unsigned range. The bitwise XOR
    and OR operations account for the operands' high bits before the helper
    expands the answer into an all-zero or all-one mask. This small call graph
    exercises arithmetic [[poison]] propagation, direct helper calls, and
    reflective taint checking without a buffer-loop invariant. *)

From Stdlib Require Import String ZArith List Bool Lia.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Term Maps Syntax Values Validate Memory Runtime Ops Semantics
  Run Machine Panics Pieces Heap Language Logic PoisonModel PoisonLogic
  TaintCheck FrameNotation CtLtCode CtLtNames.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The compiler supplies the program

    The proof operates directly on the typed [IRNotation] functions generated
    by `nanofil -O` in [CtLtCode] rather than decoding raw terms or copying
    instructions by hand. Running `rocq/scripts/programs.sh` recompiles
    `ct_lt.c` and rejects any drift in the functions, including the leaky
    control. *)

(** Campaign 1's [[validator]] accepts both helpers and the leaky control. *)
Theorem ctlt_valid : valid ctlt_module = Some true.
Proof. vm_compute. reflexivity. Qed.

(** Direct calls resolve against the same module that supplied the functions. *)
Definition ctlt_ge : genv := mkGenv ctlt_module [] free_res.

(** ## Reflective taint check across the call graph

    Before running any interactive proof, [TaintCheck] checks the whole two-function
    call graph by computation. Both arguments of `constant_time_lt` carry every
    [[poison]] restriction, the helper call preserves those restrictions across
    the call boundary, and the branching control `leaky_lt` is rejected
    statically against the exact same specification. *)

(** Taint specification for `constant_time_msb`: one secret word in, one secret
    word out, no memory writes. *)
Definition msb_tspec : tspec :=
  mkTSpec [WTInt taint_all] (Some (WTInt taint_all)) taint_bot taint_bot false.

(** Taint specification for `constant_time_lt`: two secret words in, one secret
    word out, no memory writes. *)
Definition lt_tspec : tspec :=
  mkTSpec [WTInt taint_all; WTInt taint_all] (Some (WTInt taint_all)) taint_bot taint_bot false.

(** Call-graph specification table pairing both constant-time functions. *)
Definition ctlt_tspecs : list (name * tspec) :=
  [(TAtom "constant_time_msb", msb_tspec);
   (TAtom "constant_time_lt", lt_tspec)].

(** The reflective taint checker accepts the full two-function call graph under
    [pol_strict] by `vm_compute`. *)
Theorem ctlt_taint_ok :
  taint_check_program pol_strict ctlt_module ctlt_tspecs = true.
Proof. vm_compute. reflexivity. Qed.

(** The reflective checker rejects the branching control `leaky_lt` against
    [lt_tspec] without running a concrete trace. *)
Theorem leaky_taint_rejected :
  taint_check_fn pol_strict ctlt_module ctlt_tspecs fn_leaky_lt lt_tspec = false.
Proof. vm_compute. reflexivity. Qed.

(** ## Tracking the secret arguments

    Both inputs carry every restriction, so neither integer may influence a
    branch, a memory address, or a variable-time operation. Pure bitwise and
    additive operations join their operands' restrictions, keeping the returned
    mask secret while allowing the computation to proceed. *)

Import CtLtNames.fn_constant_time_msb.

(** Entry frame for `constant_time_msb` with one secret integer parameter. *)
Definition msb_entry (x : Z) : frame :=
  frame{ fn_constant_time_msb env: [(‹a›, WInt x)] | enter: @"start" }.

(** Entry taint environment for `constant_time_msb`. *)
Definition msb_te : tenv :=
  [(‹a›, WTInt taint_all)].

Import CtLtNames.fn_constant_time_lt.

(** Entry frame for `constant_time_lt` using C source-hint parameter names. *)
Definition lt_entry (a b : Z) : frame :=
  frame{ fn_constant_time_lt env: [(‹b›, WInt b); (‹a›, WInt a)] | enter: @"start" }.

(** Entry taint environment tagging both `a` and `b` with [taint_all]. *)
Definition lt_te : tenv :=
  [(‹b›, WTInt taint_all); (‹a›, WTInt taint_all)].

(** Any two input pairs satisfy [ct_rel] because both integer parameters carry
    [taint_all] while memory and fuel stay identical. *)
Lemma lt_inputs_related a b a' b' m pm paux fuel :
  ct_rel cfg{ (lt_entry a b); mem: m; fuel: fuel }
    cfg{ (lt_entry a' b'); mem: m; fuel: fuel } (mkPState lt_te [] pm paux).
Proof.
  unfold ct_rel; cbn; repeat split; try congruence.
  intros x. unfold lt_te. cbn [lookup]. unfold name_eqb.
  destruct (term_eqb x ‹b›);
    [right; eexists _, _, _; repeat split; reflexivity|].
  destruct (term_eqb x ‹a›);
    [right; eexists _, _, _; repeat split; reflexivity|].
  left; split; reflexivity.
Qed.

Module CtLt (R : Runtime).
Module PL := PoisonLogic R.
Import PL.
Section proof.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ, !gen_heapGS ppiece ppval Σ}.
Local Instance ctlt_iris : irisGS_gen hlc (poison_lang pol_strict ctlt_ge) Σ :=
  poison_irisGS pol_strict ctlt_ge.
Local Abbreviation pexprL := (language.expr (poison_lang pol_strict ctlt_ge)).

(** ## Reading the one-run proof

    A weakest-precondition assertion, written WP, states that execution avoids
    every panic and [[poison]] fault and that any returned value satisfies the
    postcondition. Here the postcondition records that the returned word is an
    integer carrying [taint_all], without asserting that two runs return the
    same integer.

    Every arithmetic intermediate stays secret while the shift count 31 and
    the direct call target remain public. Returning from `constant_time_msb`
    uses [wp_pcall_bind] so the caller receives both the mask value and the
    full taint carried by the helper's postcondition. *)

(** The helper returns a secret integer without faulting or panicking. *)
Lemma msb_spec x :
  ⊢ WP (PRun (msb_entry x) msb_te : pexprL)
      {{ v, ∃ n, ⌜v = (Ret (WInt n), [WTInt taint_all])⌝ }}.
Proof using Type.
  iApply wp_penter; [reflexivity|reflexivity|reflexivity|]; iNext.
  iApply wp_plet; [reflexivity|reflexivity|reflexivity|intros; reflexivity|intros; reflexivity|]; iNext.
  iApply wp_plet; [reflexivity|reflexivity|reflexivity|intros; reflexivity|intros; reflexivity|]; iNext.
  iApply wp_pret; [reflexivity|reflexivity|reflexivity|]; iNext.
  iExists _. done.
Qed.

(** The comparison computes its five bitwise steps, calls `constant_time_msb`,
    and returns the helper's secret mask unchanged. *)
Lemma lt_spec a b :
  ⊢ WP (PRun (lt_entry a b) lt_te : pexprL)
      {{ v, ∃ n, ⌜v = (Ret (WInt n), [WTInt taint_all])⌝ }}.
Proof using Type.
  iApply wp_penter; [reflexivity|reflexivity|reflexivity|]; iNext.
  do 5 (iApply wp_plet;
    [reflexivity|reflexivity|reflexivity|intros; reflexivity|intros; reflexivity|]; iNext).
  iApply wp_pcall_bind;
    [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|]; iNext.
  iApply (wp_wand with "[]"); [iApply msb_spec|].
  iIntros (v) "H"; iDestruct "H" as (n) "->".
  iExists _, _; iSplit; [iPureIntro; reflexivity|]; iNext.
  iApply wp_pret; [reflexivity|reflexivity|reflexivity|]; iNext.
  iExists _. done.
Qed.
End proof.

(** ## From one-run safety to two-run plain traces

    The Iris proof establishes that no reachable state panics or violates the
    poison rules. Adequacy then transfers that single-run guarantee to any pair
    of secret inputs, yielding equal finite plain operational leakage traces
    under the deterministic runtime driver. *)

(** Instantiating Iris's heap functors discharges all logic parameters from the
    final theorems. *)
Definition ctltΣ : gFunctors := #[invΣ; gen_heapΣ piece pval; gen_heapΣ ppiece ppval].
Local Instance ctltΣ_inv : invGpreS ctltΣ.
Proof. apply subG_invΣ. apply _. Qed.
Local Instance ctltΣ_heap : gen_heapGpreS piece pval ctltΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.
Local Instance ctltΣ_poison : gen_heapGpreS ppiece ppval ctltΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** Every input pair avoids poison faults and ordinary machine panics. *)
Theorem lt_safe a b m pm paux s fuel :
  R.ready s m -> live_disjoint m ->
  poison_safe pol_strict ctlt_ge (lt_entry a b) lt_te m pm paux s fuel.
Proof.
  intros Hr Hd.
  apply (wp_poison_safe _ _ _ _ _ _ _ _ _ (fun v _ =>
    exists n, v = (Ret (WInt n), [WTInt taint_all]))).
  apply (poison_pieces_adequate ctltΣ pol_strict ctlt_ge _ _ _ _ _ _ fuel [] []
    (fun v => exists n, v = (Ret (WInt n), [WTInt taint_all])));
    try assumption; try (constructor; fail).
  intros Hinv Hheap Hpoison. simpl. iIntros "_ _".
  iApply (wp_wand with "[]"); [iApply lt_spec|].
  iIntros (v) "H"; iDestruct "H" as (n) "%H". eauto.
Qed.

(** All input pairs produce identical finite plain IR leakage traces under
    [pol_strict]. *)
Theorem lt_constant_time a b a' b' m (pm : Z -> poison_byte) (paux : Z -> taint) s fuel :
  R.ready s m -> live_disjoint m ->
  forall steps, exists tr,
    PD.driver_trace pol_strict ctlt_ge steps cfg{ (lt_entry a b); mem: m; fuel: fuel } s = Some tr /\
    PD.driver_trace pol_strict ctlt_ge steps cfg{ (lt_entry a' b'); mem: m; fuel: fuel } s = Some tr.
Proof.
  intros Hr Hd. apply (wp_ct_driver_plain pol_strict ctlt_ge
    (lt_entry a b) (lt_entry a' b') lt_te m m pm paux s fuel);
    try reflexivity; try assumption.
  - apply lt_inputs_related.
  - apply lt_safe; assumption.
Qed.
End CtLt.

(** ## A branch with the same answer still leaks

    Replacing the bit trick by an if statement preserves the returned mask
    while exposing the comparison in control flow. Concrete runs confirm the
    exact fault reported statically by [leaky_taint_rejected]: every input pair
    traps with [CannotBranch] on the branch instruction. *)

(** Entry frame for the branching control `leaky_lt`. *)
Definition leaky_entry (a b : Z) : frame :=
  frame{ fn_leaky_lt env: [(‹b›, WInt b); (‹a›, WInt a)] | enter: @"start" }.

(** Three steps enter `start`, compare the secret inputs, and trap on the
    branch. *)
Theorem leaky_rejected m pm paux :
  let run a b := prun pol_strict ctlt_ge 3 cfg{ (leaky_entry a b); mem: m; fuel: 100 }
    (mkPState lt_te [] pm paux) in
  run 0 1 = PTrap CannotBranch /\
  run 1 0 = PTrap CannotBranch /\
  run 0 0 = PTrap CannotBranch.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The constant-time routine returns the expected masks across zero, equality,
    and unsigned high-bit boundary cases while keeping every result tagged
    with [taint_all]. *)
Example lt_masks :
  let m := mkMem (fun _ => 0) [] (fun _ => CNone) in
  let run a b := prun pol_strict ctlt_ge 20 cfg{ (lt_entry a b); mem: m; fuel: 100 }
    (mkPState lt_te [] (fun _ => pb_clean) (fun _ => taint_bot)) in
  run 0 0 = PDone (Ret (WInt 0)) [WTInt taint_all] /\
  run 0 4294967295 = PDone (Ret (WInt 4294967295)) [WTInt taint_all] /\
  run 4294967295 0 = PDone (Ret (WInt 0)) [WTInt taint_all] /\
  run 2147483647 2147483648 = PDone (Ret (WInt 4294967295)) [WTInt taint_all].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ## What the theorem covers

    The theorem covers every pair of secret 32-bit unsigned words in the
    compiled IR, including unsigned wraparound, and excludes every modeled
    [[poison]] fault and panic. It does not prove functional correctness of
    the bit trick, preservation from C to IR, or hardware timing of emitted
    machine code.

    The returned mask remains secret, so a caller cannot branch on it while
    retaining the same noninterference claim. Because this routine performs no
    memory accesses, syscalls, variadic calls, or indirect calls, those
    features are verified separately in [PoisonHeap] and [CtTableScan]. *)

Module InterpCtLt := CtLt InterpRuntime.
Print Assumptions InterpCtLt.lt_spec.
Print Assumptions InterpCtLt.lt_safe.
Print Assumptions InterpCtLt.lt_constant_time.
Print Assumptions ctlt_taint_ok.
Print Assumptions leaky_rejected.
