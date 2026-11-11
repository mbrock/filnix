(** Trusted [[external call|contracts]] at libpizlo's boundary:
    `c: void zsys_exit_soft(int code)` and `c: void zsys_exit_hard(int
    code)`, over the [os_world] of [OsWorld](OsWorld.v). Their native
    counterexample probe is [zsys-exit.c](zsys-exit.c).

    ## What libpizlo runs

    At the pin (libpas/src/libpas/filc_runtime.c:8831 and 8844):

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

    `c: zsys_exit_hard` is the same with `c: _Exit(return_code)`. Neither
    returns: the process ends with status `c: return_code & 0xff`. Soft
    exit runs the native libc's exit handlers, hard exit does not; user
    glibc's own handlers and its stdio buffers are Fil-C memory that
    neither native exit sees, so user glibc runs them (or not) before
    calling here, and an unflushed user `c: FILE` buffer is lost either
    way (the probe checks this). So both contracts are the same: no
    writable root, nothing allocated or released, and one observation,
    [ProcessExit] with the status, ending the call ([CallExit]). They
    check no argument, and so have no capability panic. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
From Glibc Require Import OsBlocks OsWorld.
Import ListNotations.
Open Scope Z_scope.

(** ## The contract *)

(** The process status of an exit with the `c: int` bits:
    `c: code & 0xff`. *)
Definition exit_status (bits : Z) : Z := bits mod 256.

(** `c: void zsys_exit_*(int code)`: one [W], a void call. *)
Definition os_exit_abi (r : call_result) (args : list arg) : Prop :=
  r = CVoid /\ exists code, args = [Arg W code].

(** Precondition: one `c: int`. Nothing about memory or the world. *)
Definition os_exit_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists bits, xs = [WInt bits].

(** A finite prefix: nothing written, allocated or changed; nothing
    observed yet, or the process ended with the status. *)
Definition os_exit_prefix (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ m' = m /\ w' = w /\
  (trace = [] \/ exists bits, xs = [WInt bits] /\ trace = [ProcessExit (exit_status bits)]).

(** Postcondition: the process ended with the status of the code. No
    ending is a return. *)
Definition os_exit_post (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ m' = m /\ w' = w /\ exists bits, xs = [WInt bits] /\
    trace = [ProcessExit (exit_status bits)] /\ ending = CallExit (exit_status bits).

(** The contract of both exits: [RVoid]; no sources, roots, releases,
    allocations or resource endings. *)
Definition os_exit_contract : contract os_world :=
  mkContract os_world RVoid os_exit_abi os_exit_pre
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) os_exit_prefix os_exit_post
    (fun _ => False) (fun why => In why [ArgumentSize]).

(** `c: zsys_exit_soft`'s contract. *)
Definition os_exit_soft_contract : contract os_world := os_exit_contract.

(** `c: zsys_exit_hard`'s contract. *)
Definition os_exit_hard_contract : contract os_world := os_exit_contract.

(** The status is the low byte: `c: exit(256 + 7)` ends with 7 and
    `c: exit(-1)` (bits [2 ^ 32 - 1]) with 255, as the probe sees. *)
Example exit_status_low_byte : exit_status (256 + 7) = 7 /\ exit_status (2 ^ 32 - 1) = 255.
Proof. split; reflexivity. Qed.

(** ## Over a Logic instance *)

(** The rule for the exits over the [[runtime]] R and [LogicSig] LG0. *)
Module OsExitOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** No call of an exit returns. *)
Lemma os_exit_no_return r args xs s m w trace values s' m' w' :
  ~ M.E.invoke os_exit_contract r args xs s m w trace (CallReturn values) s' m' w'.
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & _ & _ & bits & _ & _ & He). discriminate He.
Qed.

(** A completed call ends the process with the status of its code,
    and observes exactly that. *)
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

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_exit_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** `c: zsys_exit_soft(code)`: any postcondition, since the call never
    goes on; it asks for nothing. *)
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

(** `c: zsys_exit_hard(code)`: the same. *)
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
