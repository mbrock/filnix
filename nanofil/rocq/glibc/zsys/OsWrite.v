(** When userland glibc writes bytes to an open file descriptor, it calls
    libpizlo's `c: long zsys_write(int fd, const void *buf, size_t size)`
    wrapper. That wrapper sits at the [[external call|contract]] boundary
    between compiled C code and the Fil-C [[runtime]]. This module defines
    the contract [os_write_contract] for `c: zsys_write` over the shared
    state [os_world] from [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rules. Its runtime checks
    and corner cases are tested against native Fil-C in
    [zsys-write.c](../zsys-write.c).

    ## What libpizlo runs

    Writing a buffer lends its bytes to the kernel after the runtime
    checks read permission. The following wrapper implements that
    boundary in the pinned `libpas/src/libpas/filc_runtime.c`.

    ```c
    ssize_t filc_native_zsys_write(filc_thread* my_thread, int fd, filc_ptr buf, size_t size)
    {
        check_fd(fd);
        filc_check_read(buf, size);
        return FILC_SYSCALL(my_thread, write(fd, filc_ptr_ptr(buf), size));
    }
    ```

    Before entering the kernel, `c: check_fd` asserts that the descriptor
    is not libpizlo's internal log descriptor. Next, `c: filc_check_read`
    returns immediately when the requested byte count is zero, and
    otherwise panics unless the caller's pointer carries read authority
    for the full byte count, as captured by [os_readable].

    Finally, `c: FILC_SYSCALL` clears the host thread's `c: errno`,
    invokes the host `c: write` system call on the raw buffer address, and
    copies any nonzero error number into userland glibc's thread-local
    `c: errno` cell. That 4-byte `c: errno` cell is the only caller memory
    the wrapper can overwrite. On Linux, a single `c: write` transfers at
    most `c: MAX_RW_COUNT` bytes, which is always strictly below `2 ^ 31`. *)

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
    ABI, precondition, execution trace, and postcondition of
    [os_write_contract]. Together they state what `c: zsys_write` checks
    at entry, what output events it records, and what return value it
    delivers to the caller. *)

(** A call site satisfies [os_write_abi] when it passes a 32-bit
    descriptor, a pointer buffer, and a 64-bit byte count, and either
    discards the result or binds it to a 64-bit destination register. *)
Definition os_write_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists fd p n, args = [Arg W fd; Arg P p; Arg L n].

(** At call entry, [os_write_pre] requires that the buffer satisfies
    [os_readable] for the requested length, the file descriptor is not
    libpizlo's log descriptor, and the thread's `c: errno` pointer names a
    writable 4-byte `c: int` cell. *)
Definition os_write_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd p n e, xs = [WInt fd; WPtr p; WInt n] /\ os_readable m p n /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** During a call, [os_write_prefix] states that `c: zsys_write` allocates
    no heap objects, leaves the OS world unchanged, and has either emitted
    no output event yet or emitted a single [StreamBytes] event carrying a
    leading prefix of the caller's buffer. *)
Definition os_write_prefix (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ w' = w /\
  (trace = [] \/ exists fd p n k, xs = [WInt fd; WPtr p; WInt n] /\ 0 <= k <= n /\
     trace = [StreamBytes fd (os_bytes m p k)]).

(** When `c: zsys_write` finishes, [os_write_post] states that the kernel
    either accepted a prefix of the buffer of length below `2 ^ 31` and
    returned that byte count, or accepted nothing and returned `c: -1` as
    `2 ^ 64 - 1`. *)
Definition os_write_post (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ w' = w /\ exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\
    ((exists k, 0 <= k <= n /\ k < 2 ^ 31 /\ trace = [StreamBytes fd (os_bytes m p k)] /\
                ending = CallReturn [WInt k]) \/
     (trace = [] /\ ending = CallReturn [WInt (2 ^ 64 - 1)])).

(** The contract [os_write_contract] packages these predicates for a call
    returning a 64-bit integer. It lists `c: errno` as the only writable
    memory span, allocates and frees no objects, and allows capability
    panics when the buffer pointer is null or out of bounds. *)
Definition os_write_contract : contract os_world :=
  mkContract os_world (RClass L) os_write_abi os_write_pre
    (fun _ _ _ => []) (fun _ _ w => errno_spans w) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) os_write_prefix os_write_post
    (fun _ => False) (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** Whenever `c: zsys_write` returns a value other than `c: -1`, the
    returned number is the length of the leading buffer prefix that the
    kernel accepted. *)
Lemma os_write_success_bytes xs m w born trace m' w' k :
  os_write_post xs m w born trace (CallReturn [WInt k]) m' w' -> k <> 2 ^ 64 - 1 ->
  exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\ 0 <= k <= n /\
    trace = [StreamBytes fd (os_bytes m p k)].
Proof.
  intros (_ & _ & fd & p & n & Hx & [(k' & Hk & _ & Ht & He) | (_ & He)]) Hn;
    injection He as ->; [exists fd, p, n; auto | contradiction].
Qed.

(** ## Over a Logic instance

    The contract above describes `c: zsys_write` as a relation on physical
    memory and the OS world. The functor below connects that contract to a
    Fil-C [[runtime]] and the program logic of
    [Logic](../../theories/logic/Logic.v), deriving the
    [[weakest-precondition|weakest-precondition]] rules that callers use
    in proofs. *)

(** To verify C functions that call `c: zsys_write`, [OsWriteOn] lifts the
    contract above into separation-logic proof rules for a given
    [[runtime]] and program logic. *)
Module OsWriteOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** When an invocation of [os_write_contract] returns to its caller, it
    leaves the OS world unchanged and yields either a written byte count
    below `2 ^ 31` or `c: -1`. *)
Lemma os_write_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_write_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ exists fd p n k, xs = [WInt fd; WPtr p; WInt n] /\ values = [WInt k] /\
    ((0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & fd & p & n & Hx & [(k & Hk & H31 & _ & He) | (_ & He)]);
    injection He as ->; split; auto; exists fd, p, n; eexists; auto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The instance [os_write_irisGS] configures Iris for the language with the
    OS contract registry and the world interpretation [os_wi]. *)
Local Instance os_write_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** When a C function calls `c: zsys_write`, the caller lends the thread's
    `c: errno` cell and presents owned memory pieces that make the input
    buffer readable for the requested byte count. When the call returns,
    [wp_zsys_write] hands back those pieces and `c: errno` and binds the
    destination register to a written byte count or `c: -1`. *)
Lemma wp_zsys_write f e ls lab d a0 a1 a2 rest j fd p n eb ps Φ :
  registry (TAtom "zsys_write") = Some os_write_contract ->
  find_fn ge (TAtom "zsys_write") = None -> lookup (TAtom "zsys_write") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1; Arg L a2] = Some [WInt fd; WPtr p; WInt n] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (forall m, all_agree m ps -> os_readable m p n) ->
  pts ps -∗ errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ pts ps -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt (k mod 2 ^ 64)) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zsys_write")) [Arg W a0; Arg P a1; Arg L a2]
                        :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He Hin Hrd. iIntros "Hps Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [] (pts ps)
            (fun vs => exists k, vs = [WInt k] /\ ((0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1))
            with "Hps Herr [] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hps". iDestruct (pts_facts with "Hσ Hps") as %(Ha & _).
    iDestruct (os_heap_ready with "Hσ") as %(-> & Hfd & Hc); [exact He | exact Hin|].
    iPureIntro. split; [exists fd, p, n, (mkPtr eb (Obj eb)); auto|]. split; [constructor|].
    exists []. split; [reflexivity | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro.
    destruct (os_write_returns _ _ _ _ _ _ _ _ _ _ _ Hi) as (-> & fd' & p' & n' & k & Hx' & -> & Hk).
    injection Hx' as <- <- <-. split; [reflexivity|]. eauto.
  - iApply blks_nil.
  - iNext. iIntros (vs (k & -> & Hk)) "Hps Herr _". iExists _. iSplit; [done|].
    iApply ("HK" with "[%] Hps Herr"). exact Hk.
Qed.

(** A caller that tracks the exact four bytes stored in `c: errno` before
    calling `c: zsys_write` can lend that cell directly through
    [wp_zsys_write_lend] and receive the updated cell back after the call. *)
Lemma wp_zsys_write_lend f e ls lab d a0 a1 a2 rest j fd p n eb bs ps Φ :
  registry (TAtom "zsys_write") = Some os_write_contract ->
  find_fn ge (TAtom "zsys_write") = None -> lookup (TAtom "zsys_write") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1; Arg L a2] = Some [WInt fd; WPtr p; WInt n] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (forall m, all_agree m ps -> os_readable m p n) ->
  pts ps -∗ errno_own eb bs -∗
  ▷ (∀ k, ⌜(0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ pts ps -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt (k mod 2 ^ 64)) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zsys_write")) [Arg W a0; Arg P a1; Arg L a2]
                        :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros. iIntros "Hps Herr HK". iApply (wp_zsys_write with "Hps [Herr] HK"); try eassumption.
  by iExists bs.
Qed.

End rule.
End OsWriteOn.
