(** A trusted [[external call|contract]] at libpizlo's boundary:
    `c: long zsys_write(int fd, const void *buf, size_t size)`, over the
    [os_world] of [OsWorld](OsWorld.v). Its native counterexample probe
    is [zsys-write.c](../zsys-write.c).

    ## What libpizlo runs

    At the pin (libpas/src/libpas/filc_runtime.c:8799):

    ```c
    ssize_t filc_native_zsys_write(filc_thread* my_thread, int fd, filc_ptr buf, size_t size)
    {
        check_fd(fd);
        filc_check_read(buf, size);
        return FILC_SYSCALL(my_thread, write(fd, filc_ptr_ptr(buf), size));
    }
    ```

    - `c: check_fd(fd)` asserts `c: fd` is not libpizlo's log
      descriptor ([ow_log_fd]).
    - `c: filc_check_read(buf, size)` returns at once for size 0, and
      otherwise panics unless `c: buf` is readable for size bytes
      ([os_readable]).
    - `c: FILC_SYSCALL` clears native errno, calls `c: write`, and on a
      nonzero native errno calls user glibc's errno handler, which
      stores it in the thread's `c: errno` ([errno_spans], the only
      writable root). Linux writes at most `c: MAX_RW_COUNT`, below
      2^31, at once. *)

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

(** `c: long zsys_write(int fd, const void *buf, size_t size)`: [W],
    [P], [L] to [L], or a discarded result. *)
Definition os_write_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists fd p n, args = [Arg W fd; Arg P p; Arg L n].

(** Precondition: the buffer passes `c: filc_check_read` ([os_readable]),
    `c: fd` is not the log descriptor, and errno is a writable `c: int`. *)
Definition os_write_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd p n e, xs = [WInt fd; WPtr p; WInt n] /\ os_readable m p n /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** A finite prefix: nothing allocated, the world kept, and nothing
    observed yet or the kernel accepted the buffer's first k bytes. *)
Definition os_write_prefix (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ w' = w /\
  (trace = [] \/ exists fd p n k, xs = [WInt fd; WPtr p; WInt n] /\ 0 <= k <= n /\
     trace = [StreamBytes fd (os_bytes m p k)]).

(** Postcondition: the kernel accepted the first k bytes, k below
    2^31, and the call returns k; or it accepted none and the call
    returns `c: -1` ([2 ^ 64 - 1]). *)
Definition os_write_post (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ w' = w /\ exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\
    ((exists k, 0 <= k <= n /\ k < 2 ^ 31 /\ trace = [StreamBytes fd (os_bytes m p k)] /\
                ending = CallReturn [WInt k]) \/
     (trace = [] /\ ending = CallReturn [WInt (2 ^ 64 - 1)])).

(** The contract: [RClass] [L], errno as the only writable root, no
    sources, releases, allocations or resource endings. A null or
    out-of-bounds buffer panics in `c: filc_check_read`; the log
    descriptor trips `c: check_fd`'s assertion, not a capability panic. *)
Definition os_write_contract : contract os_world :=
  mkContract os_world (RClass L) os_write_abi os_write_pre
    (fun _ _ _ => []) (fun _ _ w => errno_spans w) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) os_write_prefix os_write_post
    (fun _ => False) (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** A return other than `c: -1` is a count of leading buffer bytes the
    kernel accepted. *)
Lemma os_write_success_bytes xs m w born trace m' w' k :
  os_write_post xs m w born trace (CallReturn [WInt k]) m' w' -> k <> 2 ^ 64 - 1 ->
  exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\ 0 <= k <= n /\
    trace = [StreamBytes fd (os_bytes m p k)].
Proof.
  intros (_ & _ & fd & p & n & Hx & [(k' & Hk & _ & Ht & He) | (_ & He)]) Hn;
    injection He as ->; [exists fd, p, n; auto | contradiction].
Qed.

(** ## Over a Logic instance *)

(** The rule for `c: zsys_write(fd, buf, size)` over the [[runtime]] R
    and [LogicSig] LG0. *)
Module OsWriteOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** A returning call yields one `c: long`: a count k, [0 <= k <= n]
    and [k < 2 ^ 31], or `c: -1`; it keeps the world. *)
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

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_write_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** `c: zsys_write(fd, p, n)` with `c: fd` among w0's descriptors, the
    owned pieces ps making `c: p` pass `c: filc_check_read(p, n)`
    ([os_readable]) and errno owned ([errno_any]): ps and errno come
    back, errno holding whatever the call left, and d is bound to a
    count ([0 <= k <= n], [k < 2 ^ 31]) or `c: -1`. *)
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

(** The same, lending errno holding bs: it comes back holding whatever
    the call left. *)
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
