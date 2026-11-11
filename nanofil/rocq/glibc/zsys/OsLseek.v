(** A trusted [[external call|contract]] at libpizlo's boundary:
    `c: long zsys_lseek(int fd, long offset, int whence)`, over the
    [os_world] of [OsWorld](OsWorld.v). Its native counterexample probe
    is [zsys-lseek.c](zsys-lseek.c).

    ## What libpizlo runs

    At the pin (libpas/src/libpas/filc_runtime.c:8819):

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

    No pointer argument: `c: check_fd(fd)` asserts `c: fd` is not the log
    descriptor, and a failing call stores native errno through user
    glibc's errno handler ([errno_spans], the only writable root). A
    Linux offset is a nonnegative `c: off_t`, so a success is below 2^63;
    a failure is `c: -1`. Nothing is observed ([StreamBytes] records
    bytes, not file positions). *)

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

(** `c: long zsys_lseek(int fd, long offset, int whence)`: [W], [L],
    [W] to [L], or a discarded result. *)
Definition os_lseek_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists fd off wh, args = [Arg W fd; Arg L off; Arg W wh].

(** Precondition: `c: fd` is not the log descriptor, and errno is a
    writable `c: int`. Any offset and whence are admitted: the kernel
    rejects bad ones with `c: EINVAL`. *)
Definition os_lseek_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd off wh e, xs = [WInt fd; WInt off; WInt wh] /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** The contract: [RClass] [L], errno as the only writable root; no
    sources, releases, allocations, observations or resource endings;
    the new offset (below 2^63) or `c: -1`. Its only check,
    `c: check_fd`, is an assertion, not a capability panic. *)
Definition os_lseek_contract : contract os_world :=
  mkContract os_world (RClass L) os_lseek_abi os_lseek_pre
    (fun _ _ _ => []) (fun _ _ w => errno_spans w) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       exists k, ((0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1) /\ ending = CallReturn [WInt k])
    (fun _ => False) (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Over a Logic instance *)

(** The rule for `c: zsys_lseek(fd, offset, whence)` over the
    [[runtime]] R and [LogicSig] LG0. *)
Module OsLseekOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** A returning call keeps the world and yields an offset below 2^63
    or `c: -1`. *)
Lemma os_lseek_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_lseek_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ exists k, values = [WInt k] /\ ((0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & _ & k & Hk & He). injection He as ->. eauto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_lseek_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** `c: zsys_lseek(fd, off, wh)` with `c: fd` among w0's descriptors and
    errno owned: errno comes back holding whatever the call left, and
    d is bound to an offset below 2^63 or `c: -1`. *)
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

(** The same, lending errno holding bs: it comes back holding whatever
    the call left. *)
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
End OsLseekOn.
