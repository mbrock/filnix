(** When userland glibc closes a file descriptor, it calls libpizlo's
    `c: int zsys_close(int fd)` wrapper. That wrapper sits at the
    [[external call|contract]] boundary between compiled C code and the
    Fil-C [[runtime]]. This module defines the contract
    [os_close_contract] for `c: zsys_close` over the shared state
    [os_world] from [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rules. Its runtime checks
    and corner cases are tested against native Fil-C in
    [zsys-close.c](zsys-close.c).

    ## What libpizlo runs

    At the pinned revision, `c: zsys_close` combines user-runtime C code
    in `filc/src/runtime.c` with the native helper `c: zsys_close_impl`
    in `libpas/src/libpas/filc_runtime.c`:

    ```c
    int zsys_close(int fd)
    {
        struct fd_holder* holder;
        if (fd >= 0)
            holder = get_locked_existing_fd_holder(fd);
        else
            holder = 0;
        int result = zsys_close_impl(fd);
        if (holder) {
            if (!result)
                holder->backer = 0;
            lock_unlock(&holder->lock);
        }
        return result;
    }

    int filc_native_zsys_close_impl(filc_thread* my_thread, int fd)
    {
        if (is_reserved_fd(fd))
            return 0;
        filc_exit(my_thread);
        int result = close(fd);
        int my_errno = errno;
        filc_enter(my_thread);
        if (result < 0)
            filc_set_errno(my_errno);
        return result;
    }
    ```

    Unlike `c: zsys_write` or `c: zsys_fstat`, `c: zsys_close` does not
    call `c: check_fd(fd)`. Instead, if the caller passes libpizlo's
    reserved log descriptor, `c: is_reserved_fd(fd)` returns true and
    `c: zsys_close_impl` silently returns `0` without closing the file.
    The contract therefore admits any 32-bit integer descriptor without
    panicking.

    In `filc/src/runtime.c`, `c: get_locked_existing_fd_holder` consults
    an internal `c: fd_table` that is allocated only when a program calls
    `c: zsys_fcntl` with `c: F_DUPFD`, duplicates descriptors, or uses
    `c: epoll` tracking. Because the verified userland glibc paths never
    call those operations, the contract assumes that `c: fd_table` remains
    null, so `c: holder` is null and `c: zsys_close` touches no
    runtime-internal Fil-C objects.

    When the underlying host `c: close` call fails, `c: filc_set_errno`
    stores the error number into userland glibc's `c: errno` cell. The
    wrapper returns `0` on success or `c: -1` as `2 ^ 32 - 1` on failure. *)

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
    ABI, precondition, and postcondition of [os_close_contract]. *)

(** A call site satisfies [os_close_abi] when it passes a single 32-bit
    descriptor and either discards the result or binds it to a 32-bit
    destination register. *)
Definition os_close_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists fd, args = [Arg W fd].

(** At call entry, [os_close_pre] requires only a 32-bit integer argument
    and a writable 4-byte `c: int` cell for `c: errno`. Every file
    descriptor is accepted, including libpizlo's log descriptor. *)
Definition os_close_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd e, xs = [WInt fd] /\ ow_errno w = Some e /\ errno_cell m e.

(** The contract [os_close_contract] packages these predicates for a call
    returning a 32-bit integer. It lists `c: errno` as the only writable
    memory span, emits no trace events, allocates and frees no objects,
    and returns either `0` or `c: -1` as `2 ^ 32 - 1`. *)
Definition os_close_contract : contract os_world :=
  mkContract os_world (RClass W) os_close_abi os_close_pre
    (fun _ _ _ => []) (fun _ _ w => errno_spans w) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       (ending = CallReturn [WInt 0] \/ ending = CallReturn [WInt (2 ^ 32 - 1)]))
    (fun _ => False) (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Over a Logic instance

    The contract above describes `c: zsys_close` as a relation on physical
    memory and the OS world. The functor below connects that contract to a
    Fil-C [[runtime]] and the program logic of
    [Logic](../../theories/logic/Logic.v), deriving the
    [[weakest-precondition|weakest-precondition]] rules that callers use
    in proofs. *)

(** To verify C functions that call `c: zsys_close`, [OsCloseOn] lifts the
    contract above into separation-logic proof rules for a given
    [[runtime]] and program logic. *)
Module OsCloseOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** When an invocation of [os_close_contract] returns to its caller, it
    leaves the OS world unchanged and yields either `0` or `c: -1`. *)
Lemma os_close_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_close_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ (values = [WInt 0] \/ values = [WInt (2 ^ 32 - 1)]).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & _ & [He|He]); injection He as ->; auto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The instance [os_close_irisGS] configures Iris for the language with
    the OS contract registry and the world interpretation [os_wi]. *)
Local Instance os_close_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** When a C function calls `c: zsys_close` while lending the thread's
    `c: errno` cell, [wp_zsys_close] hands `c: errno` back to the caller
    and binds the destination register to `0` or `c: -1`. *)
Lemma wp_zsys_close f e ls lab d a0 rest j fd eb Φ :
  registry (TAtom "zsys_close") = Some os_close_contract ->
  find_fn ge (TAtom "zsys_close") = None -> lookup (TAtom "zsys_close") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0] = Some [WInt fd] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_close")) [Arg W a0] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He. iIntros "Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [] True%I
            (fun vs => vs = [WInt 0] \/ vs = [WInt (2 ^ 32 - 1)])
            with "[//] Herr [] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ _". iDestruct (os_heap_errno with "Hσ") as %[Hc _]; [exact He|].
    iDestruct (os_heap_world with "Hσ") as %[-> _].
    iPureIntro. split; [exists fd, (mkPtr eb (Obj eb)); auto|]. split; [constructor|].
    exists []. split; [reflexivity | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_close_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_nil.
  - iNext. iIntros (vs Hv) "_ Herr _".
    destruct Hv as [-> | ->]; iExists _; (iSplit; [done|]); iApply ("HK" with "[%] Herr"); auto.
Qed.

(** A caller that tracks the exact four bytes stored in `c: errno` before
    calling `c: zsys_close` can lend that cell directly through
    [wp_zsys_close_lend] and receive the updated cell back after the call. *)
Lemma wp_zsys_close_lend f e ls lab d a0 rest j fd eb bs Φ :
  registry (TAtom "zsys_close") = Some os_close_contract ->
  find_fn ge (TAtom "zsys_close") = None -> lookup (TAtom "zsys_close") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0] = Some [WInt fd] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  errno_own eb bs -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_close")) [Arg W a0] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof. intros. iIntros "Herr HK". iApply (wp_zsys_close with "[Herr] HK"); try eassumption. by iExists bs. Qed.

End rule.
End OsCloseOn.
