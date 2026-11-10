(** A contract at libpizlo's boundary: `zsys_write`, the pizlonated
    write(2) that user glibc's `write` calls (docs/zsys.md,
    docs/glibc-ir.md). The contract [zsys_write_contract] is trusted;
    its native counterexample probe is rocq/glibc/zsys-write.c.

    At the pin, libpizlo's `filc_native_zsys_write(fd, buf, size)`
    (libpas/src/libpas/filc_runtime.c) is three steps:

    - `check_fd(fd)`: a Fil-C assertion that fd is not libpizlo's own
      log descriptor, which exists only when libpizlo logs to a file;
    - `filc_check_read(buf, size)`: the capability check, a Fil-C panic
      when buf cannot be read for size bytes;
    - `FILC_SYSCALL(write(fd, ptr, size))`: leave the Fil-C world, make
      the system call, come back, and on failure hand errno to
      `filc_set_errno`, which calls user glibc's errno handler, Fil-C
      code that stores the number in the thread's errno.

    The contract's world, [fd_world], keeps what no Fil-C code of the
    module owns: where that errno store lands and which descriptor is
    libpizlo's log. The errno handler is not proved here; the contract
    names its effect, a store into the 4-byte [errno_span], as the
    call's only writable root, so every other byte of memory is kept by
    the machine's [effects] rule.

    The world is trusted to be the real one: [errno_ptr] is the calling
    thread's user glibc `errno` (`__thread int errno`, csu/errno.c),
    already allocated (Fil-C allocates a thread-local on first use, and
    the contract allows no allocation); glibc's `errno_handler` is
    registered (`__libc_start_main` does it; `filc_set_errno` panics
    without one); `FILC_DUMP_ERRNOS` is unset, so a failure logs
    nothing; and [log_fd] is libpizlo's log descriptor. The observation reuses
    ExternalCalls.v's [StreamBytes] event, read at this layer as bytes
    the kernel accepted for the descriptor, not bytes stdio buffered.

    Over a Logic instance, [fd_wi] interprets the world: the errno cell
    writable and apart from every object the program owns, and the
    program's descriptors not the log's. [wp_zsys_write] is the
    contract's rule for a caller owning the buffer's pieces. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
Import ListNotations.
Open Scope Z_scope.

(** ## The world *)

(** What a descriptor call needs that no Fil-C code of the module
    owns: the thread's errno, where user glibc's errno handler stores a
    failure's number, and libpizlo's log descriptor, if it logs to a
    file. *)
Record fd_world : Type := mkFdWorld {
  errno_ptr : ptr;
  log_fd : option Z
}.

(** The 4 bytes of the world's errno. *)
Definition errno_span (w : fd_world) : span := mkSpan (errno_ptr w) 4.

(** The k bytes of memory m from p's address. *)
Definition bytes_at (m : mem) (p : ptr) (k : Z) : list Z :=
  map (fun i => m_bytes m (ptr_addr p + Z.of_nat i)) (seq 0 (Z.to_nat k)).

(** ## The contract *)

(** zsys_write returns a long (class L), or its result is discarded,
    and takes an int, a pointer and a size_t. *)
Definition zsys_write_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists fd p n, args = [Arg W fd; Arg P p; Arg L n].

(** The precondition: the buffer is readable for its n bytes through a
    live object's capability ([readable_bytes], the check
    `filc_check_read` makes), fd is not libpizlo's log descriptor (the
    check `check_fd` makes), and errno is a live, writable, aligned
    int ([errno_cell]). *)
Definition zsys_write_pre (xs : list word) (m : mem) (w : fd_world) : Prop :=
  exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\ readable_bytes m p n /\
    log_fd w <> Some fd /\ errno_cell m (errno_ptr w).

(** A finite prefix: nothing born, the world kept, errno still a
    writable int, and either nothing observed or the first k bytes
    of the buffer, k at most n, accepted for fd. *)
Definition zsys_write_prefix (xs : list word) (m : mem) (w : fd_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : fd_world) : Prop :=
  born = [] /\ w' = w /\ errno_cell m' (errno_ptr w) /\
  (trace = [] \/ exists fd p n k, xs = [WInt fd; WPtr p; WInt n] /\ 0 <= k <= n /\
     trace = [StreamBytes fd (bytes_at m p k)]).

(** The postcondition: as the prefix, and either the kernel accepted
    the first k bytes, k at most n and below 2^31 (Linux writes at most
    MAX_RW_COUNT at once), and the call returns k; or it accepted none
    and the call returns -1, 2^64 - 1 as a long's bits. Only a failure
    stores errno (FILC_SYSCALL calls the handler only on a nonzero
    native errno); the contract allows the store either way. *)
Definition zsys_write_post (xs : list word) (m : mem) (w : fd_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : fd_world) : Prop :=
  born = [] /\ w' = w /\ errno_cell m' (errno_ptr w) /\
  exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\
    ((exists k, 0 <= k <= n /\ k < 2 ^ 31 /\ trace = [StreamBytes fd (bytes_at m p k)] /\
                ending = CallReturn [WInt k]) \/
     (trace = [] /\ ending = CallReturn [WInt (2 ^ 64 - 1)])).

(** The capability checks a call outside the precondition reaches: the
    buffer's null or out-of-bounds capability, and argument or return
    size mismatch. A log descriptor fails libpizlo's own assertion,
    which is no capability reason. *)
Definition zsys_write_panic (why : reason) : Prop :=
  In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize].

(** The trusted [[external call|contract]] of zsys_write: a long,
    [zsys_write_abi], [zsys_write_pre], no capability sources (it
    returns an integer), errno's 4 bytes as its one writable root, no
    releases, no allocation, [zsys_write_prefix], [zsys_write_post], no
    resource ending, and [zsys_write_panic]. *)
Definition zsys_write_contract : contract fd_world :=
  mkContract fd_world (RClass L) zsys_write_abi zsys_write_pre
    (fun _ _ _ => []) (fun _ _ w => [errno_span w]) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False) zsys_write_prefix zsys_write_post
    (fun _ => False) zsys_write_panic.

(** ## Boundary checks *)

(** A call that returns anything but -1 accepted exactly that many of
    the buffer's first bytes for fd. *)
Lemma zsys_write_success_bytes : forall xs m w born trace m' w' k,
  zsys_write_post xs m w born trace (CallReturn [WInt k]) m' w' -> k <> 2 ^ 64 - 1 ->
  exists fd p n, xs = [WInt fd; WPtr p; WInt n] /\ 0 <= k <= n /\
    trace = [StreamBytes fd (bytes_at m p k)].
Proof.
  intros xs m w born trace m' w' k (_ & _ & _ & fd & p & n & Hx & [(k' & Hk & _ & Ht & He) | (_ & He)]) Hn.
  - injection He as ->. exists fd, p, n. auto.
  - injection He as ->. contradiction.
Qed.

(** A failed call observed nothing. *)
Lemma zsys_write_failure_silent : forall xs m w born trace m' w',
  zsys_write_post xs m w born trace (CallReturn [WInt (2 ^ 64 - 1)]) m' w' -> trace = [].
Proof.
  intros xs m w born trace m' w' (_ & _ & _ & fd & p & n & _ & [(k & Hk & Hb & _ & He) | (Ht & _)]).
  - injection He as <-. lia.
  - exact Ht.
Qed.

(** ## Over a Logic instance *)

(** The world interpretation, the rule and its lemmas over the
    [[runtime]] R and the Logic instance LG. *)
Module ZsysWriteOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

(** The world interpretation of a program that writes to the
    descriptors fds: errno is a writable int apart from every live
    object owning a piece of h, and no descriptor of fds is
    libpizlo's log. *)
Definition fd_wi (fds : list Z) (m : mem) (w : fd_world) (h : gmap piece pval) : Prop :=
  errno_cell m (errno_ptr w) /\ roots_apart [errno_span w] h m /\
  Forall (fun fd => log_fd w <> Some fd) fds.

(** A safepoint keeps [fd_wi]: no region changes ([collector_live]),
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

(** A zsys_write call that returns returns one long: a count no more
    than its size, or -1. *)
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

(** After a zsys_write call that returns, from a state interpreted with
    the ghost heap h, the state is interpreted with h again: the
    prefix keeps the runtime ready, the frame keeps h agreeing and live
    objects apart, since the one writable root, errno, is apart from
    h, and the world and errno's writability are kept. *)
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

(** The Iris instance of the registry and [fd_wi]. *)
Local Instance zsys_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (fd_wi fds) ge.

(** The expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** zsys_write's triple, from [zsys_write_contract]: a call whose
    arguments read as fd, one of fds, the pointer p and the size n,
    owning pieces ps that show p readable for n bytes, binds d to a
    count no more than n, or -1, and the pieces are still owned. *)
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
