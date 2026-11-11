(** When userland glibc accesses thread-local state such as the current
    thread's `c: struct pthread` descriptor, it calls libpizlo's
    `c: void *zthread_self_cookie(void)` function. That function sits at
    the [[external call|contract]] boundary between compiled C code and
    the Fil-C [[runtime]]. This module defines the contract
    [os_self_contract] for `c: zthread_self_cookie` over the shared state
    [os_world] from [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rule. Its runtime behavior
    is tested against native Fil-C in [zsys-thread.c](zsys-thread.c).

    ## What libpizlo runs

    The runtime keeps a cookie that identifies the calling thread to
    userland glibc. The following function returns that saved pointer
    in the pinned `filc/src/runtime.c`.

    ```c
    void* zthread_self_cookie(void)
    {
        return zthread_get_cookie(zthread_self());
    }
    ```

    During thread startup, userland glibc stores the address of the
    calling thread's `c: struct pthread` descriptor into the runtime's
    thread structure. When the program later calls
    `c: zthread_self_cookie`, `c: zthread_get_cookie` reads that stored
    pointer back from the runtime.

    The wrapper takes no arguments, writes and allocates no memory, and
    emits no trace events. It simply returns the thread cookie pointer
    recorded in [ow_self] together with its [[capability]]. Once userland
    glibc's startup has completed, that cookie is non-null, and the world
    interpretation [os_wi] keeps its object identity registered in memory
    across every program step. *)

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

    Reading the thread cookie returns a pointer without changing memory
    or the OS world. The following definitions collect that promise and
    the argument-free calling convention into [os_self_contract]. *)

(** A call site satisfies [os_self_abi] when it passes no arguments and
    either discards the result or binds it to a pointer destination
    register. *)
Definition os_self_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ args = [].

(** A call to `c: zthread_self_cookie` reads the thread cookie from the
    OS world without modifying memory or allocating objects. The contract
    [os_self_contract] requires that the cookie is non-null, exposes its
    [[capability]] through a zero-length source span, and returns the
    cookie pointer to the caller. *)
Definition os_self_contract : contract os_world :=
  mkContract os_world (RClass P) os_self_abi
    (fun xs _ w => xs = [] /\ ptr_addr (ow_self w) <> 0)
    (fun _ _ w => [mkSpan (ow_self w) 0]) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun _ m w born trace ending m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w /\
       ending = CallReturn [WPtr (ow_self w)])
    (fun _ => False) (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Over a Logic instance

    A function that reads its thread cookie must receive the saved
    pointer without losing ownership of its other memory. The following
    [[weakest-precondition|weakest precondition]] rule lets its proof
    continue with that pointer under the same OS world. *)

(** To verify C functions that call `c: zthread_self_cookie`,
    [OsThreadOn] lifts the contract above into a separation-logic proof
    rule for a given [[runtime]] and program logic. *)
Module OsThreadOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** When an invocation of [os_self_contract] returns to its caller, it
    leaves the OS world unchanged and yields the thread cookie [ow_self]. *)
Lemma os_self_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_self_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ values = [WPtr (ow_self w)].
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & _ & _ & -> & He). injection He as ->. auto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The instance [os_self_irisGS] configures Iris for the language with
    the OS contract registry and the world interpretation [os_wi]. *)
Local Instance os_self_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** When a C function calls `c: zthread_self_cookie()` in an OS world
    whose thread cookie is non-null, [wp_zthread_self_cookie] binds the
    destination register to [ow_self] without requiring or modifying any
    caller-owned memory. *)
Lemma wp_zthread_self_cookie f e ls lab d rest j Φ :
  registry (TAtom "zthread_self_cookie") = Some os_self_contract ->
  find_fn ge (TAtom "zthread_self_cookie") = None ->
  lookup (TAtom "zthread_self_cookie") (ge_globals ge) = None ->
  ptr_addr (ow_self w0) <> 0 ->
  ▷ WP (ERun (mkFrame f (put d (WPtr (ow_self w0)) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "zthread_self_cookie")) [] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hz. iIntros "HK".
  iApply (wp_os_call w0 _ _ _ _ _ _ _ _ _ _ _ _ [] [] True%I (fun vs => vs = [WPtr (ow_self w0)])
            with "[//] [] [HK]"); [done | done | done | exact Hreg | done | | | done | | |].
  - split; [right; eexists; reflexivity | reflexivity].
  - iIntros (σ) "Hσ _". iDestruct (os_heap_world with "Hσ") as %[-> _]. iPureIntro.
    split; [split; [reflexivity | exact Hz]|]. split; [constructor | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_self_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_nil.
  - iNext. iIntros (vs ->) "_ _". iExists _. iSplit; [done|]. iExact "HK".
Qed.

End rule.
End OsThreadOn.
