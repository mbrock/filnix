(** When userland glibc writes several buffers in one system call, such as
    when flushing a buffered stream alongside a caller string, it calls
    libpizlo's `c: long zsys_writev(int fd, const struct iovec *iov, int iovcnt)`
    wrapper. That wrapper sits at the [[external call|contract]] boundary
    between compiled C code and the Fil-C [[runtime]]. This module defines
    the contract [os_writev_contract] for `c: zsys_writev` over the shared
    state [os_world] from [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rule. Its runtime checks
    and corner cases are tested against native Fil-C in
    [zsys-writev.c](zsys-writev.c).

    ## What libpizlo runs

    At the pinned revision of `libpas/src/libpas/filc_runtime.c`,
    `c: zsys_writev` runs the following native wrapper:

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

    First, `c: check_fd(fd)` asserts that the descriptor is not libpizlo's
    internal log descriptor [ow_log_fd]. Next, `c: filc_prepare_iovec`
    allocates a scratch array of `c: filc_mul_size(16, iovcnt)` bytes
    inside the runtime. A negative vector count, when converted to
    `c: size_t`, overflows that multiplication and triggers a runtime
    panic.

    For each entry in the caller's vector, `c: filc_prepare_iovec` checks
    that the 16-byte `c: struct iovec` slot is readable, loads its 8-byte
    aligned `c: iov_base` pointer together with the [[capability]] from its
    [[aux]] slot, loads its 8-byte `c: iov_len` field, and checks read
    authority over the buffer when the length is nonzero. The kernel then
    gathers the bytes from all entries in order, as defined by
    [iov_gather], and writes at most `c: MAX_RW_COUNT` bytes, which is
    below `2 ^ 31`. If the kernel returns a negative result,
    `c: filc_set_errno` stores the error number into userland glibc's
    `c: errno` cell. *)

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

    Before proving separation-logic rules, this first section reads an
    array of `c: struct iovec` entries from memory, concatenates the bytes
    they name, and defines the contract [os_writev_contract]. *)

(** For the entry at index i of the vector at `iov`, [iov_entry] reads the
    8-byte `c: iov_base` address, pairs it with the [[capability]] stored
    in that slot's [[aux]] entry, and reads the 8-byte `c: iov_len` length
    that follows. *)
Definition iov_entry (m : mem) (iov : ptr) (i : nat) : ptr * Z :=
  let a := ptr_addr iov + 16 * Z.of_nat i in
  (mkPtr (load_bytes m a 8) (m_aux m a), load_bytes m (a + 8) 8).

(** For a vector count `cnt`, [iov_entries] collects the first `cnt`
    vector entries from memory in order. *)
Definition iov_entries (m : mem) (iov : ptr) (cnt : Z) : list (ptr * Z) :=
  map (iov_entry m iov) (seq 0 (Z.to_nat cnt)).

(** By concatenating the byte slice of each entry in [iov_entries],
    [iov_gather] forms the complete sequence of bytes that `c: writev`
    hands to the kernel. *)
Definition iov_gather (m : mem) (iov : ptr) (cnt : Z) : list Z :=
  concat (map (fun pe => os_bytes m (fst pe) (snd pe)) (iov_entries m iov cnt)).

(** A vector pointer and count satisfy [iov_readable] when
    `c: filc_prepare_iovec` succeeds without panicking. The count must be
    a non-negative 32-bit integer, a positive count requires an
    8-byte-aligned readable array of `16 * cnt` bytes, and each entry's
    buffer must satisfy [os_readable]. *)
Definition iov_readable (m : mem) (iov : ptr) (cnt : Z) : Prop :=
  0 <= cnt < 2 ^ 31 /\
  (cnt = 0 \/ (ptr_addr iov mod 8 = 0 /\ readable_bytes m iov (16 * cnt))) /\
  Forall (fun pe => os_readable m (fst pe) (snd pe)) (iov_entries m iov cnt).

(** A call site satisfies [os_writev_abi] when it passes a 32-bit
    descriptor, a vector pointer, and a 32-bit entry count, and either
    discards the result or binds it to a 64-bit destination register. *)
Definition os_writev_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists fd p n, args = [Arg W fd; Arg P p; Arg W n].

(** At call entry, [os_writev_pre] requires that the vector and its
    buffers satisfy [iov_readable], the file descriptor is not libpizlo's
    log descriptor, and the thread's `c: errno` pointer names a writable
    4-byte `c: int` cell. *)
Definition os_writev_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd iov cnt e, xs = [WInt fd; WPtr iov; WInt cnt] /\ iov_readable m iov cnt /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** During a call, [os_writev_prefix] states that `c: zsys_writev`
    allocates no caller-visible heap objects, leaves the OS world
    unchanged, and has either emitted no output event yet or emitted a
    single [StreamBytes] event carrying a leading prefix of the gathered
    bytes. *)
Definition os_writev_prefix (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ w' = w /\
  (trace = [] \/ exists fd iov cnt k, xs = [WInt fd; WPtr iov; WInt cnt] /\
     0 <= k <= Z.of_nat (length (iov_gather m iov cnt)) /\
     trace = [StreamBytes fd (firstn (Z.to_nat k) (iov_gather m iov cnt))]).

(** When `c: zsys_writev` finishes, [os_writev_post] states that the
    kernel either accepted a prefix of the gathered bytes of length below
    `2 ^ 31` and returned that byte count, or accepted nothing and
    returned `c: -1` as `2 ^ 64 - 1`. *)
Definition os_writev_post (xs : list word) (m : mem) (w : os_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : os_world) : Prop :=
  born = [] /\ w' = w /\ exists fd iov cnt, xs = [WInt fd; WPtr iov; WInt cnt] /\
    ((exists k, 0 <= k <= Z.of_nat (length (iov_gather m iov cnt)) /\ k < 2 ^ 31 /\
                trace = [StreamBytes fd (firstn (Z.to_nat k) (iov_gather m iov cnt))] /\
                ending = CallReturn [WInt k]) \/
     (trace = [] /\ ending = CallReturn [WInt (2 ^ 64 - 1)])).

(** The contract [os_writev_contract] packages these predicates for a call
    returning a 64-bit integer. It lists `c: errno` as the only writable
    memory span, allocates and frees no caller-visible objects, and allows
    capability panics when the vector or any buffer is null, misaligned,
    or out of bounds. *)
Definition os_writev_contract : contract os_world :=
  mkContract os_world (RClass L) os_writev_abi os_writev_pre
    (fun _ _ _ => []) (fun _ _ w => errno_spans w) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) os_writev_prefix os_writev_post
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Misaligned; ArgumentSize; ReturnSize]).

(** When the entry count is zero, [iov_gather] reads no entries and
    returns the empty byte list. *)
Lemma iov_gather_zero m iov : iov_gather m iov 0 = [].
Proof. reflexivity. Qed.

(** ## Over a Logic instance

    The contract above describes `c: zsys_writev` as a relation on
    physical memory and the OS world. The functor below connects that
    contract to a Fil-C [[runtime]] and the program logic of
    [Logic](../../theories/logic/Logic.v), deriving the
    [[weakest-precondition|weakest-precondition]] rule that callers use
    in proofs. *)

(** To verify C functions that call `c: zsys_writev`, [OsWritevOn] lifts
    the contract above into a separation-logic proof rule for a given
    [[runtime]] and program logic. *)
Module OsWritevOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** When an invocation of [os_writev_contract] returns to its caller, it
    leaves the OS world unchanged and yields either a written byte count
    below `2 ^ 31` that does not exceed the gathered byte length, or
    `c: -1`. *)
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

(** The instance [os_writev_irisGS] configures Iris for the language with
    the OS contract registry and the world interpretation [os_wi]. *)
Local Instance os_writev_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** When a C function calls `c: zsys_writev`, the caller lends the
    thread's `c: errno` cell and presents owned memory pieces that make
    the vector and its buffers readable with a known total byte length.
    When the call returns, [wp_zsys_writev] hands back those pieces and
    `c: errno` and binds the destination register to a written byte count
    or `c: -1`. *)
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
