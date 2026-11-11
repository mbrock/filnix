(** A trusted [[external call|contract]] at libpizlo's boundary:
    `c: void *zthread_self_cookie(void)`, over the [os_world] of
    [OsWorld](OsWorld.v). Its native counterexample probe is
    [zsys-thread.c](zsys-thread.c).

    ## What libpizlo runs

    It is pizlonated code of libpizlo's user runtime
    (filc/src/runtime.c:711):

    ```c
    void* zthread_self_cookie(void)
    {
        return zthread_get_cookie(zthread_self());
    }
    ```

    `c: zthread_get_cookie` (libpas/src/libpas/filc_runtime.c) loads the
    thread's `c: cookie_ptr`, which user glibc's thread setup stored
    with `c: zthread_set_self_cookie`: the thread's `c: struct pthread`,
    with its capability. The call writes, allocates and observes
    nothing, and returns that pointer ([ow_self]). The world is trusted
    to hold the cookie user glibc stored, nonnull once its startup has
    run (the precondition asks for a nonnull one); [os_wi] keeps it a
    registered object. *)

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

(** `c: void *zthread_self_cookie(void)`: no arguments, [P], or a
    discarded result. *)
Definition os_self_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ args = [].

(** The contract: [RClass] [P]; precondition no arguments and a
    nonnull cookie; the cookie's own capability as the only source (a
    zero-length span, as ExternalCalls.v's [errno_location_contract]);
    no roots, releases, allocations, observations or resource endings;
    memory and world unchanged, returning the cookie. *)
Definition os_self_contract : contract os_world :=
  mkContract os_world (RClass P) os_self_abi
    (fun xs _ w => xs = [] /\ ptr_addr (ow_self w) <> 0)
    (fun _ _ w => [mkSpan (ow_self w) 0]) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun _ m w born trace ending m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w /\
       ending = CallReturn [WPtr (ow_self w)])
    (fun _ => False) (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Over a Logic instance *)

(** The rule for `c: zthread_self_cookie()` over the [[runtime]] R and
    [LogicSig] LG0. *)
Module OsThreadOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** A returning call keeps the world and returns its cookie. *)
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

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_self_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** `c: zthread_self_cookie()` with w0's cookie nonnull: d is bound to
    the cookie, and nothing is owned or changed. *)
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
