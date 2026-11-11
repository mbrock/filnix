(** A trusted [[external call|contract]] at libpizlo's boundary:
    `c: long zsys_writev(int fd, const struct iovec *iov, int iovcnt)`,
    over the [os_world] of [OsWorld](OsWorld.v). Its native
    counterexample probe is [zsys-writev.c](zsys-writev.c).

    ## What libpizlo runs

    At the pin (libpas/src/libpas/filc_runtime.c:8764):

    ```c
    ssize_t filc_native_zsys_writev(filc_thread* my_thread, int fd, filc_ptr user_iov, int iovcnt)
    {
        check_fd(fd);
        ssize_t result;
        struct iovec* iov = filc_prepare_iovec(my_thread, user_iov, iovcnt, filc_extended_read_access);
        filc_exit(my_thread);
        result = writev(fd, iov, iovcnt);
        int my_errno = errno;
        filc_enter(my_thread);
        if (result < 0)
            filc_set_errno(my_errno);
        return result;
    }
    ```

    `c: filc_prepare_iovec` allocates `c: filc_mul_size(16, iovcnt)`
    bytes of runtime scratch (a negative `c: iovcnt`, cast to
    `c: size_t`, overflows the multiplication and panics), then for
    each entry i checks `c: filc_check_read(iov + 16 i, 16)`, loads its
    `c: iov_base` as a pointer (an 8-aligned native pointer load, which
    takes the capability from the [[aux]] slot) and its `c: iov_len`,
    and checks `c: filc_check_access(iov_base, iov_len, read)`, which
    skips a zero length. The kernel then gathers the entries in order
    ([iov_gather]). A failure stores errno ([errno_spans]); Linux
    writes at most `c: MAX_RW_COUNT`, below 2^31, at once. *)

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

(** The i-th `c: struct iovec` of the array at iov in memory m: its
    `c: iov_base`, the address in its first 8 bytes with the
    capability in that slot's [[aux]], and its `c: iov_len`. *)
Definition iov_entry (m : mem) (iov : ptr) (i : nat) : ptr * Z :=
  let a := ptr_addr iov + 16 * Z.of_nat i in
  (mkPtr (load_bytes m a 8) (m_aux m a), load_bytes m (a + 8) 8).

(** The first cnt entries. *)
Definition iov_entries (m : mem) (iov : ptr) (cnt : Z) : list (ptr * Z) :=
  map (iov_entry m iov) (seq 0 (Z.to_nat cnt)).

(** The bytes the entries name, in order: what `c: writev` gathers. *)
Definition iov_gather (m : mem) (iov : ptr) (cnt : Z) : list Z :=
  concat (map (fun pe => os_bytes m (fst pe) (snd pe)) (iov_entries m iov cnt)).

(** `c: filc_prepare_iovec(iov, cnt, read)` passes: cnt is a nonnegative
    `c: int`; for cnt above 0 the array is 8-aligned and readable for
    16 cnt bytes; and every entry's buffer passes its read check
    ([os_readable]). *)
Definition iov_readable (m : mem) (iov : ptr) (cnt : Z) : Prop :=
  0 <= cnt < 2 ^ 31 /\
  (cnt = 0 \/ (ptr_addr iov mod 8 = 0 /\ readable_bytes m iov (16 * cnt))) /\
  Forall (fun pe => os_readable m (fst pe) (snd pe)) (iov_entries m iov cnt).

(** `c: long zsys_writev(int fd, const void *iov, int iovcnt)`: [W],
    [P], [W] to [L], or a discarded result. *)
Definition os_writev_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists fd p n, args = [Arg W fd; Arg P p; Arg W n].

(** Precondition: the array and buffers pass ([iov_readable]), `c: fd`
    is not the log descriptor, and errno is a writable `c: int`. *)
Definition os_writev_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd iov cnt e, xs = [WInt fd; WPtr iov; WInt cnt] /\ iov_readable m iov cnt /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** A finite prefix: nothing allocated, the world kept, and nothing
    observed yet or the kernel accepted the first k gathered bytes. *)
Definition os_writev_prefix (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ w' = w /\
  (trace = [] \/ exists fd iov cnt k, xs = [WInt fd; WPtr iov; WInt cnt] /\
     0 <= k <= Z.of_nat (length (iov_gather m iov cnt)) /\
     trace = [StreamBytes fd (firstn (Z.to_nat k) (iov_gather m iov cnt))]).

(** Postcondition: the kernel accepted the first k gathered bytes, k
    below 2^31, and the call returns k; or none and it returns `c: -1`. *)
Definition os_writev_post (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ w' = w /\ exists fd iov cnt, xs = [WInt fd; WPtr iov; WInt cnt] /\
    ((exists k, 0 <= k <= Z.of_nat (length (iov_gather m iov cnt)) /\ k < 2 ^ 31 /\
                trace = [StreamBytes fd (firstn (Z.to_nat k) (iov_gather m iov cnt))] /\
                ending = CallReturn [WInt k]) \/
     (trace = [] /\ ending = CallReturn [WInt (2 ^ 64 - 1)])).

(** The contract: [RClass] [L], errno as the only writable root; no
    capability sources (the call stores none), releases, application
    allocations (the scratch array is the runtime's) or resource
    endings. A bad array or buffer panics in the read checks; a
    negative count overflows `c: filc_mul_size`. *)
Definition os_writev_contract : contract os_world :=
  mkContract os_world (RClass L) os_writev_abi os_writev_pre
    (fun _ _ _ => []) (fun _ _ w => errno_spans w) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) os_writev_prefix os_writev_post
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Misaligned; ArgumentSize; ReturnSize]).

(** A zero count reads nothing: no entry, no byte. *)
Lemma iov_gather_zero m iov : iov_gather m iov 0 = [].
Proof. reflexivity. Qed.

(** ## Over a Logic instance *)

(** The rule for `c: zsys_writev(fd, iov, iovcnt)` over the [[runtime]]
    R and [LogicSig] LG0. *)
Module OsWritevOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** A returning call keeps the world and yields a count below 2^31 of
    at most the gathered bytes, or `c: -1`. *)
Lemma os_writev_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_writev_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ exists fd iov cnt k, xs = [WInt fd; WPtr iov; WInt cnt] /\ values = [WInt k] /\
    ((0 <= k <= Z.of_nat (length (iov_gather m iov cnt)) /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & fd & iov & cnt & Hx & [(k & Hk & H31 & _ & He) | (_ & He)]);
    injection He as ->; split; auto; exists fd, iov, cnt; eexists; auto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_writev_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** `c: zsys_writev(fd, iov, cnt)` with `c: fd` among w0's descriptors,
    the owned pieces ps making the array and buffers pass
    ([iov_readable]) and fixing the total length tot of the gathered
    bytes, and errno owned: ps and errno come back, and d is bound to a
    count ([0 <= k <= tot], [k < 2 ^ 31]) or `c: -1`. *)
Lemma wp_zsys_writev f e ls lab d a0 a1 a2 rest j fd iov cnt tot eb ps Φ :
  registry (TAtom "zsys_writev") = Some os_writev_contract ->
  find_fn ge (TAtom "zsys_writev") = None -> lookup (TAtom "zsys_writev") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1; Arg W a2] = Some [WInt fd; WPtr iov; WInt cnt] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (forall m, all_agree m ps -> iov_readable m iov cnt /\ Z.of_nat (length (iov_gather m iov cnt)) = tot) ->
  pts ps -∗ errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k <= tot /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ pts ps -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt (k mod 2 ^ 64)) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zsys_writev")) [Arg W a0; Arg P a1; Arg W a2]
                        :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He Hin Hrd. iIntros "Hps Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [] (pts ps)
            (fun vs => exists k, vs = [WInt k] /\ ((0 <= k <= tot /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1))
            with "Hps Herr [] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hps". iDestruct (pts_facts with "Hσ Hps") as %(Ha & _).
    iDestruct (os_heap_ready with "Hσ") as %(-> & Hfd & Hc); [exact He | exact Hin|].
    destruct (Hrd _ Ha) as [Hr _].
    iPureIntro. split; [exists fd, iov, cnt, (mkPtr eb (Obj eb)); auto|].
    split; [constructor|]. exists []. split; [reflexivity | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "Hσ Hps". iDestruct (pts_facts with "Hσ Hps") as %(Ha & _).
    destruct (Hrd _ Ha) as [_ Htot].
    destruct (os_writev_returns _ _ _ _ _ _ _ _ _ _ _ Hi) as (-> & fd' & iov' & cnt' & k & Hx' & -> & Hk).
    injection Hx' as <- <- <-. iPureIntro. split; [reflexivity|]. exists k. rewrite <- Htot. auto.
  - iApply blks_nil.
  - iNext. iIntros (vs (k & -> & Hk)) "Hps Herr _". iExists _. iSplit; [done|].
    iApply ("HK" with "[%] Hps Herr"). exact Hk.
Qed.

End rule.
End OsWritevOn.
