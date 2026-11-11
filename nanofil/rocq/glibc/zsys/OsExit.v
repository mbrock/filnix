(** When userland glibc terminates the current process, it calls
    libpizlo's `c: void zsys_exit_soft(int code)` or
    `c: void zsys_exit_hard(int code)` wrapper. Those wrappers sit at the
    [[external call|contract]] boundary between compiled C code and the
    Fil-C [[runtime]]. This module defines the shared contract
    [os_exit_contract] for both exit functions over the world [os_world]
    from [OsWorld](OsWorld.v), and derives their
    [[separation-logic|separation-logic]] call rules. Their runtime
    behavior is tested against native Fil-C in [zsys-exit.c](zsys-exit.c).

    ## What libpizlo runs

    At the pinned revision of `libpas/src/libpas/filc_runtime.c`,
    `c: zsys_exit_soft` runs the following native wrapper:

    ```c
    void filc_native_zsys_exit_soft(filc_thread* my_thread, int return_code)
    {
        ...
        filc_sampling_profiler_report();
        filc_exit(my_thread);
        exit(return_code);
        PAS_ASSERT(!"Should not be reached");
    }
    ```

    The companion wrapper `c: zsys_exit_hard` runs the same sequence but
    calls `c: _Exit(return_code)` in place of `c: exit(return_code)`.
    Neither function returns to its caller, and both end the process with
    exit status `return_code & 0xff`.

    Although `c: zsys_exit_soft` runs the host C library's exit handlers,
    userland glibc's own exit handlers and `c: FILE` stream buffers live
    in Fil-C memory that the host C library does not see. Userland glibc
    therefore flushes its streams and runs its handlers before calling
    `c: zsys_exit_soft`, and any stream buffer left unflushed at this
    boundary is discarded by both wrappers. Accordingly, both functions
    share the exact same contract: they write and allocate no memory, emit
    a single [ProcessExit] event carrying the low byte of the status code,
    and terminate the call with [CallExit]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
From Glibc Require Import OsBlocks OsWorld.
Import ListNotations.
Open Scope Z_scope.

(** ## The contract

    Before proving separation-logic rules, this first section defines the
    exit status masking, ABI, execution trace, and postcondition of
    [os_exit_contract]. *)

(** From the 32-bit integer passed to `c: exit`, [exit_status] extracts
    the low 8 bits `bits mod 256` that Linux reports as the process exit
    status. *)
Definition exit_status (bits : Z) : Z := bits mod 256.

(** A call site satisfies [os_exit_abi] when it passes a single 32-bit
    status code and discards the void return value. *)
Definition os_exit_abi (r : call_result) (args : list arg) : Prop :=
  r = CVoid /\ exists code, args = [Arg W code].

(** At call entry, [os_exit_pre] requires only a single integer word and
    places no requirements on memory or on the OS world. *)
Definition os_exit_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists bits, xs = [WInt bits].

(** During a call, [os_exit_prefix] states that the wrapper allocates no
    objects, leaves memory and the OS world unchanged, and has either
    emitted no event yet or emitted a single [ProcessExit] event with the
    masked status code. *)
Definition os_exit_prefix (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ m' = m /\ w' = w /\
  (trace = [] \/ exists bits, xs = [WInt bits] /\ trace = [ProcessExit (exit_status bits)]).

(** When an exit call finishes, [os_exit_post] states that it emitted a
    single [ProcessExit] event and ended the process via [CallExit] with
    the masked status code rather than returning to the caller. *)
Definition os_exit_post (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ m' = m /\ w' = w /\ exists bits, xs = [WInt bits] /\
    trace = [ProcessExit (exit_status bits)] /\ ending = CallExit (exit_status bits).

(** The contract [os_exit_contract] packages these predicates for a void
    call that never writes, allocates, or frees memory and terminates the
    process with [CallExit]. *)
Definition os_exit_contract : contract os_world :=
  mkContract os_world RVoid os_exit_abi os_exit_pre
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) os_exit_prefix os_exit_post
    (fun _ => False) (fun why => In why [ArgumentSize]).

(** Soft process termination through `c: zsys_exit_soft` uses the shared
    contract [os_exit_contract]. *)
Definition os_exit_soft_contract : contract os_world := os_exit_contract.

(** Hard process termination through `c: zsys_exit_hard` uses the same
    contract [os_exit_contract]. *)
Definition os_exit_hard_contract : contract os_world := os_exit_contract.

(** Because [exit_status] keeps only the low byte of the argument, passing
    `256 + 7` yields exit status `7` and passing `c: -1` as `2 ^ 32 - 1`
    yields exit status `255`. *)
Example exit_status_low_byte : exit_status (256 + 7) = 7 /\ exit_status (2 ^ 32 - 1) = 255.
Proof. split; reflexivity. Qed.

(** ## Over a Logic instance

    The contract above describes `c: zsys_exit_soft` and
    `c: zsys_exit_hard` as relations on physical memory and the OS world.
    The functor below connects that contract to a Fil-C [[runtime]] and
    the program logic of [Logic](../../theories/logic/Logic.v), deriving
    the [[weakest-precondition|weakest-precondition]] rules that callers
    use in proofs. *)

(** To verify C functions that call `c: zsys_exit_soft` or
    `c: zsys_exit_hard`, [OsExitOn] lifts the contract above into
    separation-logic proof rules for a given [[runtime]] and program
    logic. *)
Module OsExitOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** No invocation of [os_exit_contract] can end with [CallReturn] and
    return control to its caller. *)
Lemma os_exit_no_return r args xs s m w trace values s' m' w' :
  ~ M.E.invoke os_exit_contract r args xs s m w trace (CallReturn values) s' m' w'.
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & _ & _ & bits & _ & _ & He). discriminate He.
Qed.

(** Every completed invocation of [os_exit_contract] leaves memory
    unchanged, emits a single [ProcessExit] event, and terminates the
    machine with [CallExit]. *)
Lemma os_exit_ends r args s m w trace ending s' m' w' bits :
  M.E.invoke os_exit_contract r args [WInt bits] s m w trace ending s' m' w' ->
  trace = [ProcessExit (exit_status bits)] /\ ending = CallExit (exit_status bits) /\ m' = m.
Proof.
  intros Hi. inversion Hi as [? ? ? ? ? born _ _ _ Hpost | ? ? ? ? ? ? _ _ _ _ Hres]; subst;
    [|contradiction].
  destruct Hpost as (_ & -> & _ & bits' & [= <-] & -> & ->). auto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The instance [os_exit_irisGS] configures Iris for the language with
    the OS contract registry and the world interpretation [os_wi]. *)
Local Instance os_exit_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** Because `c: zsys_exit_soft` terminates the process and never continues
    to the instructions after the call, [wp_zsys_exit_soft] proves the
    call for any postcondition without requiring the caller to lend any
    memory. *)
Lemma wp_zsys_exit_soft f e ls lab a0 rest j bits Φ :
  registry (TAtom "zsys_exit_soft") = Some os_exit_soft_contract ->
  find_fn ge (TAtom "zsys_exit_soft") = None -> lookup (TAtom "zsys_exit_soft") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0] = Some [WInt bits] ->
  ⊢ WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zsys_exit_soft")) [Arg W a0] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx.
  iApply (wp_os_noreturn w0 _ _ _ _ _ _ _ _ _ _ _ _ _ True%I with "[//]");
    [done | done | done | exact Hreg | exact Hx | split; [done | eexists; reflexivity] | |].
  - iIntros (σ) "_ _". iPureIntro. eexists. reflexivity.
  - intros. apply os_exit_no_return.
Qed.

(** Because `c: zsys_exit_hard` also terminates the process without
    returning, [wp_zsys_exit_hard] proves the call for any postcondition
    without requiring the caller to lend any memory. *)
Lemma wp_zsys_exit_hard f e ls lab a0 rest j bits Φ :
  registry (TAtom "zsys_exit_hard") = Some os_exit_hard_contract ->
  find_fn ge (TAtom "zsys_exit_hard") = None -> lookup (TAtom "zsys_exit_hard") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0] = Some [WInt bits] ->
  ⊢ WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zsys_exit_hard")) [Arg W a0] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx.
  iApply (wp_os_noreturn w0 _ _ _ _ _ _ _ _ _ _ _ _ _ True%I with "[//]");
    [done | done | done | exact Hreg | exact Hx | split; [done | eexists; reflexivity] | |].
  - iIntros (σ) "_ _". iPureIntro. eexists. reflexivity.
  - intros. apply os_exit_no_return.
Qed.

End rule.
End OsExitOn.
