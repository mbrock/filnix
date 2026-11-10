(** A trusted [[external call|contract]], [zsys_write_contract], at
    libpizlo's boundary: `c: long zsys_write(int fd, const void *buf, size_t size)`,
    the pizlonated write(2) that user glibc's `c: write(fd, buf, size)`
    calls ([zsys.md](../../docs/zsys.md),
    [glibc-ir.md](../../docs/glibc-ir.md)). Its native counterexample
    probe is [zsys-write.c](zsys-write.c).

    ## What libpizlo runs

    At the pin (libpas/src/libpas/filc_runtime.c), libpizlo's native
    entry point is three steps:

    ```c
    ssize_t filc_native_zsys_write(int fd, filc_ptr buf, size_t size)
    {
        check_fd(fd);
        filc_check_read(buf, size);
        return FILC_SYSCALL(write(fd, filc_ptr_ptr(buf), size));
    }
    ```

    - `c: check_fd(fd)` asserts that `c: fd` is not libpizlo's own log
      descriptor, which exists only when libpizlo logs to a file.
    - `c: filc_check_read(buf, size)` checks the buffer's capability and
      panics if `c: buf` cannot be read for `c: size` bytes.
    - `c: FILC_SYSCALL` leaves the Fil-C world, calls native
      `c: write(fd, ptr, size)`, re-enters, and on failure passes native
      `c: errno` to `c: filc_set_errno(my_errno)`, which calls user
      glibc's `c: errno_handler(errno_value)` to store the error number
      in the thread's `c: errno`.

    ## World and trust assumptions

    The contract's world, [fd_world], keeps what no Fil-C code in the
    module owns: the thread's [errno_ptr] and libpizlo's [log_fd]. User
    glibc's `c: errno_handler(errno_value)` is not proved here; instead,
    the contract names the 4-byte [errno_span] as the call's only
    writable root, so every other byte of memory is preserved by the
    machine's [effects] rule.

    The world is trusted to match the native runtime after startup:

    - [errno_ptr] is the calling thread's user glibc `c: errno`
      (`c: __thread int errno` in csu/errno.c), already allocated
      (Fil-C allocates a thread-local on first use, and the contract
      allows no allocation).
    - User glibc's `c: errno_handler(errno_value)` is registered by
      `c: __libc_start_main` (`c: filc_set_errno(my_errno)` panics
      without one).
    - `c: FILC_DUMP_ERRNOS` is unset, so a failing call logs nothing.
    - [log_fd] is libpizlo's log descriptor, and [StreamBytes] (from
      [ExternalCalls.v](../theories/ExternalCalls.v)) records bytes the
      kernel accepted for `c: fd`, not bytes buffered by stdio.

    Over a [Logic](../theories/Logic.v) instance, [fd_wi] ties
    [fd_world] to the ghost heap and [wp_zsys_write] gives the rule for
    a caller owning the buffer's pieces. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
Import ListNotations.
Open Scope Z_scope.

(** ## The world *)

(** State outside the module's Fil-C code that a descriptor call
    reaches: *)
Record fd_world : Type := mkFdWorld {
  errno_ptr : ptr;   (* the calling thread's `c: int errno` cell *)
  log_fd : option Z  (* libpizlo's log descriptor, if it logs to a file *)
}.

(** The 4-byte span of the thread's `c: int errno` cell. *)
Definition errno_span (w : fd_world) : span := mkSpan (errno_ptr w) 4.

(** The first [k] bytes of memory [m] starting at [p]'s address. *)
Definition bytes_at (m : mem) (p : ptr) (k : Z) : list Z :=
  map (fun i => m_bytes m (ptr_addr p + Z.of_nat i)) (seq 0 (Z.to_nat k)).

(** ## The contract *)

(** `c: long zsys_write(int fd, const void *buf, size_t size)`: takes
    `c: int` ([W]), a pointer ([P]) and `c: size_t` ([L]), and returns
    `c: long` ([L]) or discards its result ([CVoid]). *)
Definition zsys_write_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists fd p n, args = [Arg W fd; Arg P p; Arg L n].

(** Precondition for `c: zsys_write(fd, p, n)`:
    - [readable_bytes]: `c: p` is readable for `c: n` bytes through a
      live capability (`c: filc_check_read(buf, size)`);
    - `c: fd` is not libpizlo's [log_fd] (`c: check_fd(fd)`);
    - [errno_cell]: [errno_ptr] is a live, writable, aligned `c: int`. *)
Definition zsys_write_pre (xs : list word) (m : mem) (w : fd_world) : Prop :=
  exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\ readable_bytes m p n /\
    log_fd w <> Some fd /\ errno_cell m (errno_ptr w).

(** Any finite prefix of a call: nothing is allocated, the world is
    unchanged, `c: errno` stays a writable `c: int` ([errno_cell]), and
    either nothing was observed or the buffer's first `c: k` bytes
    ([0 <= k <= n]) were accepted for `c: fd`. *)
Definition zsys_write_prefix (xs : list word) (m : mem) (w : fd_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : fd_world) : Prop :=
  born = [] /\ w' = w /\ errno_cell m' (errno_ptr w) /\
  (trace = [] \/ exists fd p n k, xs = [WInt fd; WPtr p; WInt n] /\ 0 <= k <= n /\
     trace = [StreamBytes fd (bytes_at m p k)]).

(** Postcondition: as in [zsys_write_prefix], and either:
    - the kernel accepted the first `c: k` bytes ([0 <= k <= n] and
      [k < 2 ^ 31], since Linux writes at most `c: MAX_RW_COUNT` at
      once) and the call returns `c: k`; or
    - it accepted none and the call returns `c: (long)-1` ([2 ^ 64 - 1]
      in 64-bit unsigned bits).

    `c: FILC_SYSCALL` calls the handler only on a nonzero native
    `c: errno`; the contract permits writing [errno_span] either way. *)
Definition zsys_write_post (xs : list word) (m : mem) (w : fd_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : fd_world) : Prop :=
  born = [] /\ w' = w /\ errno_cell m' (errno_ptr w) /\
  exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\
    ((exists k, 0 <= k <= n /\ k < 2 ^ 31 /\ trace = [StreamBytes fd (bytes_at m p k)] /\
                ending = CallReturn [WInt k]) \/
     (trace = [] /\ ending = CallReturn [WInt (2 ^ 64 - 1)])).

(** Capability panics a call outside [zsys_write_pre] can reach: a null
    ([NullCapability]) or out-of-bounds ([OutOfBounds]) buffer in
    `c: filc_check_read(buf, size)`, or an ABI size mismatch
    ([ArgumentSize], [ReturnSize]). Passing [log_fd] trips
    `c: check_fd(fd)`'s own assertion, which is not a capability
    panic. *)
Definition zsys_write_panic (why : reason) : Prop :=
  In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize].

(** The trusted [[external call|contract]] of `c: zsys_write(fd, buf, size)`:
    returns `c: long` ([RClass] [L]), with [zsys_write_abi],
    [zsys_write_pre], [errno_span] as its sole writable root, no
    capability sources, releases, allocations or resource endings,
    [zsys_write_prefix], [zsys_write_post] and [zsys_write_panic]. *)
Definition zsys_write_contract : contract fd_world :=
  mkContract fd_world (RClass L) zsys_write_abi zsys_write_pre
    (fun _ _ _ => []) (fun _ _ w => [errno_span w]) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) zsys_write_prefix zsys_write_post
    (fun _ => False) zsys_write_panic.

(** ## Boundary checks *)

(** Any return value other than `c: -1` ([2 ^ 64 - 1]) means the kernel
    accepted that many leading bytes of the buffer for `c: fd`. *)
Lemma zsys_write_success_bytes : forall xs m w born trace m' w' k,
  zsys_write_post xs m w born trace (CallReturn [WInt k]) m' w' -> k <> 2 ^ 64 - 1 ->
  exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\ 0 <= k <= n /\
    trace = [StreamBytes fd (bytes_at m p k)].
Proof.
  intros xs m w born trace m' w' k (_ & _ & _ & fd & p & n & Hx & [(k' & Hk & _ & Ht & He) | (_ & He)]) Hn.
  - injection He as ->. exists fd, p, n. auto.
  - injection He as ->. contradiction.
Qed.

(** A call returning `c: -1` ([2 ^ 64 - 1]) observed no bytes. *)
Lemma zsys_write_failure_silent : forall xs m w born trace m' w',
  zsys_write_post xs m w born trace (CallReturn [WInt (2 ^ 64 - 1)]) m' w' -> trace = [].
Proof.
  intros xs m w born trace m' w' (_ & _ & _ & fd & p & n & _ & [(k & Hk & Hb & _ & He) | (Ht & _)]).
  - injection He as <-. lia.
  - exact Ht.
Qed.

(** ## Over a Logic instance *)

(** World interpretation and weakest-precondition rule for
    `c: zsys_write(fd, buf, size)` over the [[runtime]] R and
    [LogicSig] LG0. *)
Module ZsysWriteOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

(** World invariant for a program writing to descriptors [fds]:
    `c: errno` is a writable `c: int` ([errno_cell]) apart from every
    live object in the ghost heap [h] ([roots_apart]), and no descriptor
    in [fds] is libpizlo's [log_fd]. *)
Definition fd_wi (fds : list Z) (m : mem) (w : fd_world) (h : gmap piece pval) : Prop :=
  errno_cell m (errno_ptr w) /\ roots_apart [errno_span w] h m /\
  Forall (fun fd => log_fd w <> Some fd) fds.

(** A safepoint preserves [fd_wi]: no region changes ([collector_live]),
    and writability and apartness read only regions. *)
Instance fd_wi_safepoint fds : SafepointStable (fd_wi fds).
Proof.
  split. intros s m s' m' w h Hsp (Hw & Ha & Hf). pose proof (R.collector_live _ _ _ _ Hsp) as E.
  split; [|split; [|exact Hf]].
  - destruct Hw as (Hz & (Hs & base & reg & Hc & Hr & Hl & Hacc) & Hal). split; [exact Hz|].
    split; [|exact Hal]. split; [exact Hs|].
    exists base, reg. unfold access_res in *. rewrite E. auto.
  - intros sp a Hin Hs (l & v & reg & Hl & Hm & [E' Hlive] & Hb). apply (Ha sp a Hin Hs).
    rewrite E in E'. exists l, v, reg. split; [exact Hl|]. split; [exact Hm|]. split; [|exact Hb].
    split; [exact E' | exact Hlive].
Qed.

(** A returning `c: zsys_write(fd, p, n)` call yields one `c: long`: a
    count `c: k` with [0 <= k <= n] and [k < 2 ^ 31], or `c: -1`
    ([2 ^ 64 - 1]). *)
Lemma zsys_write_returns r args xs s m w trace values s' m' w' :
  M.E.invoke zsys_write_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  exists fd p n k, xs = [WInt fd; WPtr p; WInt n] /\ values = [WInt k] /\
    ((0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1).
Proof.
  intros Hi. remember (CallReturn values) as en eqn:Een.
  destruct Hi as [? ? ? ? ? ? _ _ _ Hp | ? ? ? ? ? ? _ _ _ _ _]; [|discriminate Een].
  subst. destruct Hp as (_ & _ & _ & fd & p & n & Hx & [(k & Hk & Hb & _ & He) | (_ & He)]);
    injection He as ->; exists fd, p, n; eexists; auto.
Qed.

(** A returning `c: zsys_write(fd, p, n)` call preserves the state
    interpretation against ghost heap [h]: its prefix keeps the runtime
    [[ready]], [prefix_agrees] preserves [h] because the only writable
    root (`c: errno`) is apart from [h], and the postcondition keeps
    [fd_wi]. *)
Lemma zsys_write_return_frame fds r args xs s m w trace values s' m' w' h :
  M.E.invoke zsys_write_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> fd_wi fds m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ fd_wi fds m' w' h.
Proof.
  intros Hi Ha Hd Hr (Hw & Hapart & Hfds).
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  destruct (prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hp Hr Hd Ha Hapart ltac:(intros ? ? ? []))
    as (Ha' & Hd' & _ & Hapart').
  destruct Hp as [_ (_ & -> & Hw' & _)].
  split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|]. split; [exact Hw'|].
  split; [exact Hapart' | exact Hfds].
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (fds : list Z) (registry : name -> option (contract fd_world)) (ge : genv).

(** The Iris instance for [registry] and [fd_wi]. *)
Local Instance zsys_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (fd_wi fds) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** Weakest-precondition rule for `c: zsys_write(fd, p, n)`, derived
    from [zsys_write_contract] via [wp_external]: when `c: fd` is in
    [fds] and the owned pieces [ps] make `c: p` readable for `c: n`
    bytes ([readable_bytes]), the call keeps [ps] and binds [d] to a
    count `c: k` ([0 <= k <= n], [k < 2 ^ 31]) or `c: -1`
    ([2 ^ 64 - 1]). *)
Lemma wp_zsys_write f e ls lab d a0 a1 a2 rest j fd p n ps Φ :
  registry (TAtom "zsys_write") = Some zsys_write_contract ->
  find_fn ge (TAtom "zsys_write") = None -> lookup (TAtom "zsys_write") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1; Arg L a2] = Some [WInt fd; WPtr p; WInt n] ->
  In fd fds -> (forall m, all_agree m ps -> readable_bytes m p n) ->
  pts ps -∗
  ▷ (∀ k, ⌜(0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ pts ps -∗
     WP (ERun (mkFrame f (put d (WInt (k mod 2 ^ 64)) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zsys_write")) [Arg W a0; Arg P a1; Arg L a2]
                        :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx Hin Hrd. iIntros "Hps HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ zsys_write_contract [WInt fd; WPtr p; WInt n]
            (pts ps) with "Hps [HK]");
    [done | done | done | done | exact Hx | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hps". iDestruct (pts_facts with "Hσ Hps") as %(Ha & _).
    iDestruct "Hσ" as (h) "[_ %Hf]". destruct Hf as (_ & _ & _ & Hw & _ & Hfd).
    iPureIntro. exists fd, p, n. split; [reflexivity|]. split; [exact (Hrd _ Ha)|].
    split; [|exact Hw]. rewrite Forall_forall in Hfd. exact (Hfd fd Hin).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hps".
    destruct Hf as (Ha & Hd & Hr & Hwi).
    destruct (zsys_write_return_frame _ _ _ _ _ _ _ _ _ _ _ _ h Hinv Ha Hd Hr Hwi)
      as (Ha' & Hd' & Hr' & Hwi').
    destruct (zsys_write_returns _ _ _ _ _ _ _ _ _ _ _ Hinv) as (fd' & p' & n' & k & Hx' & -> & Hk).
    injection Hx' as <- <- <-.
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh"; [iExists h; iFrame "Hh"; iPureIntro; auto|].
    iApply ("HK" with "[%] Hps"). exact Hk.
Qed.

End rule.
End ZsysWriteOn.
