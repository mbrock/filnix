From Glibc Require Import GlibcProgram.
(** When userland glibc repositions the file offset of an open descriptor,
    it calls libpizlo's `c: long zsys_lseek(int fd, long offset, int whence)`
    wrapper. That wrapper sits at the [[external call|contract]] boundary
    between compiled C code and the Fil-C [[runtime]]. This module defines
    the contract [os_lseek_contract] for `c: zsys_lseek` over the shared
    state [os_world] from [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rules. Its runtime checks
    and corner cases are tested against native Fil-C in
    [zsys-lseek.c](zsys-lseek.c).

    ## What libpizlo runs

    Seeking changes a kernel file offset without reading or writing a
    caller buffer. The following wrapper passes that request to the
    host in the pinned `libpas/src/libpas/filc_runtime.c`.

    ```c
    long filc_native_zsys_lseek(filc_thread* my_thread, int fd, long offset, int whence)
    {
        check_fd(fd);
        filc_exit(my_thread);
        long result = lseek(fd, offset, whence);
        int my_errno = errno;
        filc_enter(my_thread);
        if (result < 0)
            filc_set_errno(my_errno);
        return result;
    }
    ```

    Because `c: zsys_lseek` takes no pointer arguments, it performs no
    capability checks on caller buffers. Instead, `c: check_fd(fd)`
    asserts that the descriptor is not libpizlo's internal log descriptor
    [ow_log_fd], and the wrapper passes the descriptor, offset, and
    `c: whence` value directly to the host `c: lseek` system call.

    If the kernel returns a negative result, `c: filc_set_errno` stores
    the host error number into userland glibc's thread-local `c: errno`
    cell, which is the only caller memory the wrapper can overwrite. On
    Linux, a resulting file offset is a non-negative 64-bit signed integer
    below `2 ^ 63`, and failure returns `c: -1` as `2 ^ 64 - 1`. Because
    our trace model records written stream bytes rather than file offsets,
    `c: zsys_lseek` emits no trace events. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
From Glibc Require Import OsBlocks OsWorld.
From Glibc Require OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The contract

    A seek call may update the thread's error cell but cannot overwrite
    other caller memory. The following definitions collect its calling
    convention and possible results into [os_lseek_contract]. *)

(** A call site satisfies [os_lseek_abi] when it passes a 32-bit
    descriptor, a 64-bit byte offset, and a 32-bit `c: whence` flag, and
    either discards the result or binds it to a 64-bit destination
    register. *)
Definition os_lseek_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists fd off wh, args = [Arg W fd; Arg L off; Arg W wh].

(** At call entry, [os_lseek_pre] requires that the file descriptor is not
    libpizlo's log descriptor and that the thread's `c: errno` pointer
    names a writable 4-byte `c: int` cell. Any offset and `c: whence`
    integer are allowed, because the kernel rejects invalid values cleanly
    with `c: EINVAL`. *)
Definition os_lseek_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd off wh e, xs = [WInt fd; WInt off; WInt wh] /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** The contract [os_lseek_contract] packages these predicates for a call
    returning a 64-bit integer. It lists `c: errno` as the only writable
    memory span, emits no trace events, allocates and frees no objects,
    and returns either a new file offset below `2 ^ 63` or `c: -1` as
    `2 ^ 64 - 1`. *)
Definition os_lseek_contract : contract os_world :=
  mkContract os_world (RClass L) os_lseek_abi os_lseek_pre
    (fun _ _ _ => []) (fun _ _ w => errno_spans w) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       exists k, ((0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1) /\ ending = CallReturn [WInt k])
    (fun _ => False) (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Over a Logic instance

    The contract above describes `c: zsys_lseek` as a relation on physical
    memory and the OS world. The functor below connects that contract to a
    Fil-C [[runtime]] and the program logic of
    [Logic](../../theories/logic/Logic.v), deriving the
    [[weakest-precondition|weakest-precondition]] rules that callers use
    in proofs. *)

(** The rules below lift the contract above into separation-logic proof rules
    for C functions that call `c: zsys_lseek`. *)
Import OsWorld OsWorld.L OsWorld.LG.

(** When an invocation of [os_lseek_contract] returns to its caller, it
    leaves the OS world unchanged and yields either a non-negative file
    offset below `2 ^ 63` or `c: -1`. *)
Lemma os_lseek_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_lseek_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ exists k, values = [WInt k] /\ ((0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & _ & k & Hk & He). injection He as ->. eauto.
Qed.

Import ProgramAbbreviations.
Section rule.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** Seeking on a tracked file descriptor borrows the thread's errno
    cell and returns it with either a file offset or a failure result.
    The rule [wp_zsys_lseek] binds an offset below the signed 64-bit
    limit on success, or the all-ones bit pattern representing negative one on failure. *)
Lemma wp_zsys_lseek f e ls lab d a0 a1 a2 rest j fd off wh eb Φ :
  registry (TAtom "zsys_lseek") = Some os_lseek_contract ->
  find_fn ge (TAtom "zsys_lseek") = None -> lookup (TAtom "zsys_lseek") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg L a1; Arg W a2] = Some [WInt fd; WInt off; WInt wh] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1⌝ -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt (k mod 2 ^ 64)) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zsys_lseek")) [Arg W a0; Arg L a1; Arg W a2]
                        :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He Hin. iIntros "Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [] True%I
            (fun vs => exists k, vs = [WInt k] /\ ((0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1))
            with "[//] Herr [] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ _". iDestruct (os_heap_ready with "Hσ") as %(-> & Hfd & Hc); [exact He | exact Hin|].
    iPureIntro. split; [exists fd, off, wh, (mkPtr eb (Obj eb)); auto|]. split; [constructor|].
    exists []. split; [reflexivity | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_lseek_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_nil.
  - iNext. iIntros (vs (k & -> & Hk)) "_ Herr _". iExists _. iSplit; [done|].
    iApply ("HK" with "[%] Herr"). exact Hk.
Qed.

(** A caller that tracks the exact four bytes stored in `c: errno` before
    calling `c: zsys_lseek` can lend that cell directly through
    [wp_zsys_lseek_lend] and receive the updated cell back after the call. *)
Lemma wp_zsys_lseek_lend f e ls lab d a0 a1 a2 rest j fd off wh eb bs Φ :
  registry (TAtom "zsys_lseek") = Some os_lseek_contract ->
  find_fn ge (TAtom "zsys_lseek") = None -> lookup (TAtom "zsys_lseek") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg L a1; Arg W a2] = Some [WInt fd; WInt off; WInt wh] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  errno_own eb bs -∗
  ▷ (∀ k, ⌜(0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1⌝ -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt (k mod 2 ^ 64)) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zsys_lseek")) [Arg W a0; Arg L a1; Arg W a2]
                        :: rest) j)) : zexpr)
    {{ Φ }}.
Proof. intros. iIntros "Herr HK". iApply (wp_zsys_lseek with "[Herr] HK"); try eassumption. by iExists bs. Qed.

End rule.
