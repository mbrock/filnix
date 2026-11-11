(** When userland glibc queries metadata for an open file descriptor, it
    calls libpizlo's `c: int zsys_fstat(int fd, struct stat *st)` wrapper.
    That wrapper sits at the [[external call|contract]] boundary between
    compiled C code and the Fil-C [[runtime]]. This module defines the
    contract [os_fstat_contract] for `c: zsys_fstat` over the shared state
    [os_world] from [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rules. Its runtime checks
    and corner cases are tested against native Fil-C in
    [zsys-fstat.c](zsys-fstat.c).

    ## What libpizlo runs

    A metadata query lends the kernel a writable buffer after the
    runtime checks its capability. The following wrapper implements
    that boundary in the pinned `libpas/src/libpas/filc_runtime.c`.

    ```c
    int filc_native_zsys_fstat(filc_thread* my_thread, int fd, filc_ptr stat_ptr)
    {
        check_fd(fd);
        filc_check_write(stat_ptr, sizeof(struct stat));
        return FILC_SYSCALL(my_thread, fstat(fd, (struct stat* )filc_ptr_ptr(stat_ptr)));
    }
    ```

    Before entering the kernel, `c: check_fd` asserts that the descriptor
    is not libpizlo's internal log descriptor. Next, `c: filc_check_write`
    verifies that the destination pointer carries a live, writable object
    [[capability]] covering all 144 bytes of `c: struct stat` on x86-64
    Linux.

    The kernel then writes the 144-byte `c: struct stat` record directly
    to the raw buffer address without updating the buffer's [[aux]]
    capability slots, and `c: FILC_SYSCALL` copies any nonzero error
    number into userland glibc's `c: errno` cell. Both the 144-byte buffer
    and the 4-byte `c: errno` cell are therefore writable spans of the
    call, and the caller lends both blocks before calling `c: zsys_fstat`.
    On success the wrapper returns `0`, and on failure it returns `c: -1`
    as `2 ^ 32 - 1`. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic.
From Glibc Require Import OsBlocks OsWorld.
Import ListNotations.
Open Scope Z_scope.

(** ## The contract

    A metadata query may overwrite both the destination record and the
    calling thread's error cell. The following definitions describe
    those spans and collect the call's requirements into [os_fstat_contract]. *)

(** On x86-64 Linux, `c: sizeof(struct stat)` is 144 bytes, which we name
    [stat_size]. *)
Definition stat_size : Z := 144.

(** A call site satisfies [os_fstat_abi] when it passes a 32-bit
    descriptor and a pointer to a `c: struct stat` buffer, and either
    discards the result or binds it to a 32-bit destination register. *)
Definition os_fstat_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists fd p, args = [Arg W fd; Arg P p].

(** At call entry, [os_fstat_pre] requires that the destination pointer
    covers a writable 144-byte span, the file descriptor is not libpizlo's
    log descriptor, and the thread's `c: errno` pointer names a writable
    4-byte `c: int` cell. *)
Definition os_fstat_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd p e, xs = [WInt fd; WPtr p] /\ writable_span m (mkSpan p stat_size) /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** A call to `c: zsys_fstat` can overwrite two memory spans: the 144-byte
    `c: struct stat` buffer at the caller's pointer and the thread's
    4-byte `c: errno` cell. *)
Definition os_fstat_writes (xs : list word) (m : mem) (w : os_world) : list span :=
  match xs with [WInt _; WPtr p] => [mkSpan p stat_size] | _ => [] end ++ errno_spans w.

(** The contract [os_fstat_contract] packages these predicates for a call
    returning a 32-bit integer. It emits no trace events, allocates and
    frees no objects, returns either `0` or `c: -1` as `2 ^ 32 - 1`, and
    allows capability panics when the buffer pointer is null, read-only,
    or out of bounds. *)
Definition os_fstat_contract : contract os_world :=
  mkContract os_world (RClass W) os_fstat_abi os_fstat_pre
    (fun _ _ _ => []) os_fstat_writes (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       (ending = CallReturn [WInt 0] \/ ending = CallReturn [WInt (2 ^ 32 - 1)]))
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** When a 144-byte block at offset o lies within the bounds of a live
    object, a pointer to that offset carrying the object's writable
    capability satisfies `c: filc_check_write`. *)
Lemma stat_block_writable m b reg o :
  live_at m b reg -> 0 <= o -> b + o + stat_size <= r_end reg ->
  writable_span m (mkSpan (mkPtr (b + o) (Obj b)) stat_size).
Proof.
  intros [E L] Ho He. split; [cbn; unfold stat_size; lia|]. exists b, reg.
  split; [reflexivity|]. split; [exact E|]. split; [exact L|].
  cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** ## Over a Logic instance

    The contract above describes `c: zsys_fstat` as a relation on physical
    memory and the OS world. The functor below connects that contract to a
    Fil-C [[runtime]] and the program logic of
    [Logic](../../theories/logic/Logic.v), deriving the
    [[weakest-precondition|weakest-precondition]] rules that callers use
    in proofs. *)

(** To verify C functions that call `c: zsys_fstat`, [OsFstatOn] lifts the
    contract above into separation-logic proof rules for a given
    [[runtime]] and program logic. *)
Module OsFstatOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** When an invocation of [os_fstat_contract] returns to its caller, it
    leaves the OS world unchanged and yields either `0` or `c: -1`. *)
Lemma os_fstat_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_fstat_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ (values = [WInt 0] \/ values = [WInt (2 ^ 32 - 1)]).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & _ & [He|He]); injection He as ->; auto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The instance [os_fstat_irisGS] configures Iris for the language with
    the OS contract registry and the world interpretation [os_wi]. *)
Local Instance os_fstat_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** When a C function calls `c: zsys_fstat`, the caller lends a 144-byte
    output buffer inside a live object together with the thread's
    `c: errno` cell. When the call returns, [wp_zsys_fstat] hands back the
    live object token, the updated 144-byte buffer, and `c: errno`, and
    binds the destination register to `0` or `c: -1`. *)
Lemma wp_zsys_fstat f e ls lab d a0 a1 rest j fd b reg o eb Φ :
  registry (TAtom "zsys_fstat") = Some os_fstat_contract ->
  find_fn ge (TAtom "zsys_fstat") = None -> lookup (TAtom "zsys_fstat") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1] = Some [WInt fd; WPtr (mkPtr (b + o) (Obj b))] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> b + o + stat_size <= r_end reg ->
  live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_fstat")) [Arg W a0; Arg P a1] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He Hin Ho Hend. iIntros "Hl Hb Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [(b, o, stat_size)] (live b reg)
            (fun vs => vs = [WInt 0] \/ vs = [WInt (2 ^ 32 - 1)])
            with "Hl Herr [Hb] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ Hl". iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    cbn [agree_piece fst snd] in Hlv.
    iDestruct (os_heap_ready with "Hσ") as %(-> & Hfd & Hc); [exact He | exact Hin|].
    pose proof (stat_block_writable _ _ _ _ Hlv Ho Hend) as Hwr.
    iPureIntro. split; [exists fd, (mkPtr (b + o) (Obj b)), (mkPtr eb (Obj eb)); auto|].
    split; [constructor; [exists reg; cbn; unfold stat_size in *; split; [exact Hlv|lia] | constructor]|].
    exists [mkSpan (mkPtr (b + o) (Obj b)) stat_size]. split; [reflexivity|].
    intros sp a [<- | []] Hs. exists b, o, stat_size. unfold span_contains in Hs. cbn in Hs.
    split; [left; reflexivity | lia].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_fstat_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_cons. iFrame "Hb". iApply blks_nil.
  - iNext. iIntros (vs Hv) "Hl Herr Hb". iDestruct (blks_cons with "Hb") as "[Hb _]".
    destruct Hv as [-> | ->]; iExists _; (iSplit; [done|]); iApply ("HK" with "[%] Hl Hb Herr"); auto.
Qed.

(** A caller that tracks the exact four bytes stored in `c: errno` before
    calling `c: zsys_fstat` can lend that cell directly through
    [wp_zsys_fstat_lend] and receive the updated cell back after the call. *)
Lemma wp_zsys_fstat_lend f e ls lab d a0 a1 rest j fd b reg o eb bs Φ :
  registry (TAtom "zsys_fstat") = Some os_fstat_contract ->
  find_fn ge (TAtom "zsys_fstat") = None -> lookup (TAtom "zsys_fstat") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1] = Some [WInt fd; WPtr (mkPtr (b + o) (Obj b))] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> b + o + stat_size <= r_end reg ->
  live b reg -∗ blk_any b o stat_size -∗ errno_own eb bs -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_fstat")) [Arg W a0; Arg P a1] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros. iIntros "Hl Hb Herr HK". iApply (wp_zsys_fstat with "Hl Hb [Herr] HK"); try eassumption.
  by iExists bs.
Qed.

End rule.
End OsFstatOn.
