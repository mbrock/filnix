(** OpenSSL compares secret unsigned integers without branching on them.
    This page follows [constant_time_lt] from C through nanofil's optimized
    [[stage|checked IR]] to an [[iris|Iris]] proof with [[poison]] restrictions.
    The result may reveal which integer is smaller; the execution trace must
    not reveal either input before the caller chooses to disclose that result.

    We use the two function bodies from OpenSSL 3.6.0's
    [constant_time.h](https://github.com/openssl/openssl/blob/openssl-3.6.0/include/internal/constant_time.h).
    The fixture removes only their static inline qualifiers, so the helper
    becomes a direct call that the proof checks separately.

    ```c
    unsigned int constant_time_msb(unsigned int a) {
        return 0 - (a >> (sizeof(a) * 8 - 1));
    }
    unsigned int constant_time_lt(unsigned int a, unsigned int b) {
        return constant_time_msb(a ^ ((a ^ b) | ((a - b) ^ b)));
    }
    ```

    Subtraction alone cannot decide unsigned order from its high bit: it
    wraps when the operands straddle the unsigned range. The XOR and OR
    operations account for the operands' high bits before the helper expands
    the answer into an all-zero or all-one mask. This small routine lets us
    examine arithmetic taint and a helper call without a buffer-loop invariant. *)

From Stdlib Require Import String ZArith List Bool Lia.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Term Maps Syntax Values Validate Memory Runtime Ops Semantics
  Run Machine Panics Transport Pieces Heap Language Logic PoisonModel PoisonLogic CtLtCode.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The compiler supplies the program

    The proof reads the generated fixture rather than reconstructing the C
    algorithm by hand. The fixture check recompiles ct_lt.c with nanofil -O
    and rejects any difference, including changes to the leaky control. *)

(** Decoding makes the compiler's term available to the operational semantics. *)
Definition ctlt_module : module :=
  match decode_module ctlt_term with Some md => md | None => [] end.

(** Validation checks the whole fixture, including both helpers and the control. *)
Theorem ctlt_valid : valid ctlt_module = Some true.
Proof. vm_compute. reflexivity. Qed.

(** Selecting a function from the fixture keeps its instructions tied to C. *)
Definition ctlt_nth (i : nat) : func :=
  match nth_error ctlt_module i with
  | Some (IFunc f) => f
  | _ => mkFunc (TAtom "missing") (TAtom "local") RVoid [] []
  end.

(** The helper shifts by the public constant 31 and subtracts from zero. *)
Definition msb_fn : func := Eval vm_compute in ctlt_nth 0.
(** The comparison computes five arithmetic temporaries before calling the helper. *)
Definition lt_fn : func := Eval vm_compute in ctlt_nth 1.
(** The control compares the same inputs and branches on the answer. *)
Definition leaky_fn : func := Eval vm_compute in ctlt_nth 2.

(** Direct calls resolve against the same module that supplied the instructions. *)
Definition ctlt_ge : genv := mkGenv ctlt_module [] free_res.

(** ## Tracking the secret arguments

    Both arguments carry every restriction: they cannot control a branch,
    an address, or an operation classified as variable-time by the policy.
    Arithmetic joins its operands' restrictions, so the mask remains secret
    even though computing it is permitted. *)

(** The helper starts with one secret integer and needs no memory ownership. *)
Definition msb_entry x := mkFrame msb_fn [(TAtom "v0", WInt x)] [] None
  (Enter (TAtom "start") None).
(** The helper's argument keeps all three restrictions. *)
Definition msb_te : tenv := [(TAtom "v0", WTInt taint_all)].
(** The comparison starts with the two temporaries named by the compiler. *)
Definition lt_entry a b := mkFrame lt_fn
  [(TAtom "v2", WInt b); (TAtom "v0", WInt a)] [] None
  (Enter (TAtom "start") None).
(** Neither argument may become observable through control flow or addressing. *)
Definition lt_te : tenv := [(TAtom "v2", WTInt taint_all); (TAtom "v0", WTInt taint_all)].

(** Any two input pairs are related because both integer temporaries are secret.
    The memory, runtime state, and initial fuel stay the same in both runs. *)
Lemma lt_inputs_related a b a' b' m pm paux fuel :
  ct_rel (mkConfig (lt_entry a b) [] m fuel)
    (mkConfig (lt_entry a' b') [] m fuel) (mkPState lt_te [] pm paux).
Proof.
  unfold ct_rel; cbn; repeat split; try congruence.
  intros x. unfold lt_te. cbn [lookup]. unfold name_eqb.
  destruct (term_eqb x (TAtom "v2"));
    [right; eexists _, _, _; repeat split; reflexivity|].
  destruct (term_eqb x (TAtom "v0"));
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
Local Notation pexprL := (language.expr (poison_lang pol_strict ctlt_ge)).

(** ## Reading the one-run proof

    A weakest-precondition assertion, written WP, says that execution is safe
    and that any returned result satisfies the assertion inside braces.
    Here that assertion says the result is an integer with every secret
    restriction; it does not say that two calls return the same integer.

    Every arithmetic result remains secret, while the shift count and call
    target are public. The proof checks this at each instruction with
    [wp_plet], which accounts for both the computed value and its restrictions.

    Returning from the helper must not erase the mask's restrictions.
    The caller uses [wp_pcall_bind] to receive both the helper's result
    and the restrictions established by its specification. *)

(** The helper returns a secret integer without a poison fault or panic.
    The postcondition deliberately does not make that integer public. *)
Lemma msb_spec x :
  ⊢ WP (PRun (msb_entry x) msb_te : pexprL)
      {{ v, ∃ n, ⌜v = (Ret (WInt n), [WTInt taint_all])⌝ }}.
Proof.
  iApply wp_penter; [reflexivity|reflexivity|reflexivity|]; iNext.
  iApply wp_plet; [reflexivity|reflexivity|reflexivity|intros; reflexivity|intros; reflexivity|]; iNext.
  iApply wp_plet; [reflexivity|reflexivity|reflexivity|intros; reflexivity|intros; reflexivity|]; iNext.
  iApply wp_pret; [reflexivity|reflexivity|reflexivity|]; iNext.
  iExists _. done.
Qed.

(** The helper returns a secret mask to its caller. The comparison can return
    that mask, but cannot remove its restrictions by passing it through a call. *)
Lemma lt_spec a b :
  ⊢ WP (PRun (lt_entry a b) lt_te : pexprL)
      {{ v, ∃ n, ⌜v = (Ret (WInt n), [WTInt taint_all])⌝ }}.
Proof.
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

(** ## From one-run safety to two-run traces

    The Iris proof establishes that no reachable state can panic or misuse
    poison. Adequacy then relates two executions with arbitrary secret inputs,
    under the same runtime driver and with the same step budget. *)

(** The routine needs no memory from its caller. We instantiate the logic's
    memory bookkeeping here so the final theorem has no Iris parameters. *)
Definition ctltΣ : gFunctors := #[invΣ; gen_heapΣ piece pval; gen_heapΣ ppiece ppval].
Local Instance ctltΣ_inv : invGpreS ctltΣ.
Proof. apply subG_invΣ. apply _. Qed.
Local Instance ctltΣ_heap : gen_heapGpreS piece pval ctltΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.
Local Instance ctltΣ_poison : gen_heapGpreS ppiece ppval ctltΣ.
Proof. apply subG_gen_heapGpreS. apply _. Qed.

(** Every input pair avoids poison faults and ordinary machine panics.
    The memory need only satisfy the runtime's usual readiness conditions. *)
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

(** All input pairs produce equal finite IR leakage traces. There is no
    premise that assumes a successful run or assumes the desired relation. *)
Theorem lt_constant_time a b a' b' m pm paux s fuel :
  R.ready s m -> live_disjoint m ->
  forall steps, exists tr,
    PD.pdriver_trace pol_strict ctlt_ge steps (mkConfig (lt_entry a b) [] m fuel)
      (mkPState lt_te [] pm paux) s = Some tr /\
    PD.pdriver_trace pol_strict ctlt_ge steps (mkConfig (lt_entry a' b') [] m fuel)
      (mkPState lt_te [] pm paux) s = Some tr.
Proof.
  intros Hr Hd. apply wp_ct_driver; try reflexivity; try assumption.
  - apply lt_inputs_related.
  - apply lt_safe; assumption.
Qed.
End CtLt.

(** ## A branch with the same answer still leaks

    Replacing the bit trick by an if statement preserves the intended mask
    but makes the comparison observable. The examples below reach a forbidden
    branch on either side of the comparison and when the inputs are equal. *)

(** The control uses the same argument environment as the verified comparison. *)
Definition leaky_entry a b := mkFrame leaky_fn
  [(TAtom "v2", WInt b); (TAtom "v0", WInt a)] [] None
  (Enter (TAtom "start") None).

(** Three steps enter the block, compare the arguments, and reject the branch. *)
Theorem leaky_rejected m pm paux :
  let run a b := prun pol_strict ctlt_ge 3 (mkConfig (leaky_entry a b) [] m 100)
    (mkPState lt_te [] pm paux) in
  run 0 1 = PTrap CannotBranch /\
  run 1 0 = PTrap CannotBranch /\
  run 0 0 = PTrap CannotBranch.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The good program may return different masks without changing its trace.
    These boundary cases check zero, equality, and the unsigned high bit;
    they do not replace a functional correctness theorem for all words. *)
Example lt_masks :
  let m := mkMem (fun _ => 0) [] (fun _ => CNone) in
  let run a b := prun pol_strict ctlt_ge 20 (mkConfig (lt_entry a b) [] m 100)
    (mkPState lt_te [] (fun _ => pb_clean) (fun _ => taint_bot)) in
  run 0 0 = PDone (Ret (WInt 0)) [WTInt taint_all] /\
  run 0 4294967295 = PDone (Ret (WInt 4294967295)) [WTInt taint_all] /\
  run 4294967295 0 = PDone (Ret (WInt 0)) [WTInt taint_all] /\
  run 2147483647 2147483648 = PDone (Ret (WInt 4294967295)) [WTInt taint_all].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ## What the theorem covers

    The theorem covers every pair of secret words in the generated IR,
    including unsigned wraparound, and excludes every modeled poison fault
    and panic. It does not prove the bit trick's functional specification,
    preservation from C to IR, or timing of the emitted machine code.

    The return value is still secret: a caller cannot branch on it while
    claiming the same guarantee. This routine makes no memory accesses,
    syscalls, variadic calls, or indirect calls; the proof makes no claim
    about those unsupported call forms or about a larger OpenSSL operation. *)

Module InterpCtLt := CtLt InterpRuntime.
Print Assumptions InterpCtLt.lt_spec.
Print Assumptions InterpCtLt.lt_safe.
Print Assumptions InterpCtLt.lt_constant_time.
Print Assumptions leaky_rejected.
