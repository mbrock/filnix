From Glibc Require Import GlibcProgram.
(** When `c: __ptmalloc_init` gets no random bytes for its thread-cache
    key, it builds a key from the clock instead. It reads the clock
    through libpizlo's `c: int zsys_clock_gettime(int clock, void *ts)`
    wrapper. This module defines the [[external call|contract]]
    [os_clock_gettime_contract] for it over [os_world] from
    [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rule. Its checks and
    corner cases are tested against native Fil-C in
    [zsys-clock.c](zsys-clock.c).

    ## What libpizlo runs

    The wrapper checks the caller's buffer and lends it to the kernel,
    as the pinned `libpas/src/libpas/filc_runtime.c` shows.

    ```c
    int filc_native_zsys_clock_gettime(filc_thread* my_thread, int clock_id, filc_ptr timespec_ptr)
    {
        filc_check_write(timespec_ptr, sizeof(struct timespec));
        return FILC_SYSCALL(
            my_thread, clock_gettime(clock_id, (struct timespec* )filc_ptr_ptr(timespec_ptr)));
    }
    ```

    The kernel fills in the 16 bytes of `c: struct timespec` with any
    time, so the contract leaves those bytes arbitrary. The caller must
    own them and may write them, which the write check demands. When the
    system call fails, `c: FILC_SYSCALL` stores the error number through
    the registered errno handler, and it panics when no handler is
    registered yet. For that reason the contract requires [ow_errno] to
    name a cell, and the call may write both the buffer and that cell. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic.
From Glibc Require Import OsBlocks OsWorld.
From Glibc Require OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The contract

    A clock query may overwrite both the destination record and the
    calling thread's error cell. The following definitions describe
    those spans and collect the call's requirements into [os_clock_gettime_contract]. *)

(** On x86-64 Linux, `c: sizeof(struct timespec)` is 16 bytes, which we
    name [timespec_size]. *)
Definition timespec_size : Z := 16.

(** A call site satisfies [os_clock_gettime_abi] when it passes a 32-bit
    clock number and a pointer to a `c: struct timespec` buffer, and either
    discards the result or binds it to a 32-bit destination register. *)
Definition os_clock_gettime_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists a p, args = [Arg W a; Arg P p].

(** At call entry, [os_clock_gettime_pre] requires that the destination pointer
    covers a writable 16-byte span and that the errno handler is
    registered with a writable 4-byte `c: int` cell. *)
Definition os_clock_gettime_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists clk p e, xs = [WInt clk; WPtr p] /\ writable_span m (mkSpan p timespec_size) /\
    ow_errno w = Some e /\ errno_cell m e.

(** A call to `c: zsys_clock_gettime` can overwrite the 16-byte buffer at the
    caller's pointer and the thread's 4-byte `c: errno` cell. *)
Definition os_clock_gettime_writes (xs : list word) (m : mem) (w : os_world) : list span :=
  match xs with [WInt _; WPtr p] => [mkSpan p timespec_size] | _ => [] end ++ errno_spans w.

(** The contract [os_clock_gettime_contract] packages these predicates for a
    call returning a 32-bit integer. It emits no trace events, allocates
    and frees no objects, returns either `0` or `c: -1` as `2 ^ 32 - 1`,
    and allows capability panics when the buffer pointer is null,
    read-only, or out of bounds. *)
Definition os_clock_gettime_contract : contract os_world :=
  mkContract os_world (RClass W) os_clock_gettime_abi os_clock_gettime_pre
    (fun _ _ _ => []) os_clock_gettime_writes (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       (ending = CallReturn [WInt 0] \/ ending = CallReturn [WInt (2 ^ 32 - 1)]))
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** When a 16-byte block at offset o lies within the bounds of a live
    object, a pointer to that offset carrying the object's writable
    capability satisfies `c: filc_check_write`. *)
Lemma timespec_block_writable m b reg o :
  live_at m b reg -> 0 <= o -> b + o + timespec_size <= r_end reg ->
  writable_span m (mkSpan (mkPtr (b + o) (Obj b)) timespec_size).
Proof.
  intros [E L] Ho He. split; [cbn; unfold timespec_size; lia|]. exists b, reg.
  split; [reflexivity|]. split; [exact E|]. split; [exact L|].
  cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** ## Over a Logic instance

    The contract above describes `c: zsys_clock_gettime` as a relation on physical
    memory and the OS world. The functor below connects that contract to a
    Fil-C [[runtime]] and the program logic of
    [Logic](../../theories/logic/Logic.v), deriving the
    [[weakest-precondition|weakest-precondition]] rules that callers use
    in proofs. *)

(** The rules below lift the contract above into separation-logic proof rules
    for C functions that call `c: zsys_clock_gettime`. *)
Import OsWorld OsWorld.L OsWorld.LG.

(** When an invocation of [os_clock_gettime_contract] returns to its caller, it
    leaves the OS world unchanged and yields either `0` or `c: -1`. *)
Lemma os_clock_gettime_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_clock_gettime_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ (values = [WInt 0] \/ values = [WInt (2 ^ 32 - 1)]).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & _ & [He|He]); injection He as ->; auto.
Qed.

Import ProgramAbbreviations.
Section rule.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** When a C function calls `c: zsys_clock_gettime`, the caller lends a 16-byte
    output buffer inside a live object together with the thread's
    `c: errno` cell. When the call returns, [wp_zsys_clock_gettime] hands back the
    live object token, the updated 16-byte buffer, and `c: errno`, and
    binds the destination register to `0` or `c: -1`. The
    buffer holds any time. *)
Lemma wp_zsys_clock_gettime f e ls lab d a0 a1 rest j clk b reg o eb Φ :
  registry (TAtom "zsys_clock_gettime") = Some os_clock_gettime_contract ->
  find_fn ge (TAtom "zsys_clock_gettime") = None -> lookup (TAtom "zsys_clock_gettime") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1] = Some [WInt clk; WPtr (mkPtr (b + o) (Obj b))] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 <= o -> b + o + timespec_size <= r_end reg ->
  live b reg -∗ blk_any b o timespec_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live b reg -∗ blk_any b o timespec_size -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_clock_gettime")) [Arg W a0; Arg P a1] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He Ho Hend. iIntros "Hl Hb Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [(b, o, timespec_size)] (live b reg)
            (fun vs => vs = [WInt 0] \/ vs = [WInt (2 ^ 32 - 1)])
            with "Hl Herr [Hb] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ Hl". iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    cbn [agree_piece fst snd] in Hlv.
    iDestruct (os_heap_world with "Hσ") as %[-> _].
    iDestruct (os_heap_errno with "Hσ") as %[Hc _]; [exact He|].
    pose proof (timespec_block_writable _ _ _ _ Hlv Ho Hend) as Hwr.
    iPureIntro. split; [exists clk, (mkPtr (b + o) (Obj b)), (mkPtr eb (Obj eb)); auto|].
    split; [constructor; [exists reg; cbn; unfold timespec_size in *; split; [exact Hlv|lia] | constructor]|].
    exists [mkSpan (mkPtr (b + o) (Obj b)) timespec_size]. split; [reflexivity|].
    intros sp a [<- | []] Hs. exists b, o, timespec_size. unfold span_contains in Hs. cbn in Hs.
    split; [left; reflexivity | lia].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_clock_gettime_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_cons. iFrame "Hb". iApply blks_nil.
  - iNext. iIntros (vs Hv) "Hl Herr Hb". iDestruct (blks_cons with "Hb") as "[Hb _]".
    destruct Hv as [-> | ->]; iExists _; (iSplit; [done|]); iApply ("HK" with "[%] Hl Hb Herr"); auto.
Qed.

End rule.
