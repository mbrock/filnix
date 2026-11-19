From Glibc Require Import GlibcProgram.
(** Before the allocator hands out its first block, `c: __ptmalloc_init`
    picks a random key that protects the thread cache's free lists. It
    asks libpizlo's `c: long zsys_getrandom(void *buf, size_t len,
    unsigned flags)` wrapper for eight random bytes. This module defines
    the [[external call|contract]] [os_getrandom_contract] for that
    wrapper over [os_world] from [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rule. Its checks and
    corner cases are tested against native Fil-C in
    [zsys-getrandom.c](zsys-getrandom.c).

    ## What libpizlo runs

    The wrapper checks the caller's buffer and lends it to the kernel,
    as the pinned `libpas/src/libpas/filc_runtime.c` shows.

    ```c
    long filc_native_zsys_getrandom(filc_thread* my_thread, filc_ptr buf_ptr, size_t buflen,
                                    unsigned flags)
    {
        filc_check_write(buf_ptr, buflen);
        return FILC_SYSCALL(my_thread, getrandom(filc_ptr_ptr(buf_ptr), buflen, flags));
    }
    ```

    The kernel may fill any prefix of the buffer with any bytes, so the
    contract leaves both the bytes and the count arbitrary. The caller
    must own the buffer and may write it, which the write check demands.
    When the system call fails, `c: FILC_SYSCALL` stores the error number
    through the registered errno handler, and it panics when no handler
    is registered yet. For that reason the contract requires [ow_errno]
    to name a cell, and the call may write both the buffer and that
    cell. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic.
From Glibc Require Import OsBlocks OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The contract

    A random-bytes request may overwrite the caller's buffer and the
    calling thread's error cell. The following definitions describe
    those spans and collect the call's requirements into
    [os_getrandom_contract]. *)

(** A call site satisfies [os_getrandom_abi] when it passes a buffer
    pointer, a 64-bit length and a 32-bit flag word, and either discards
    the result or binds it to a 64-bit destination register. *)
Definition os_getrandom_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists p a f, args = [Arg P p; Arg L a; Arg W f].

(** At call entry, [os_getrandom_pre] requires that the buffer pointer
    covers a writable span of the requested length and that the errno
    handler is registered with a writable 4-byte `c: int` cell. *)
Definition os_getrandom_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists p n fl e, xs = [WPtr p; WInt n; WInt fl] /\ writable_span m (mkSpan p n) /\
    ow_errno w = Some e /\ errno_cell m e.

(** A call to `c: zsys_getrandom` can overwrite the requested bytes at
    the caller's pointer and the thread's 4-byte `c: errno` cell. *)
Definition os_getrandom_writes (xs : list word) (m : mem) (w : os_world) : list span :=
  match xs with [WPtr p; WInt n; WInt _] => [mkSpan p n] | _ => [] end ++ errno_spans w.

(** A returned count is either at most the requested length or `c: -1`,
    which the 64-bit result register holds as `2 ^ 64 - 1`. *)
Definition getrandom_count (xs : list word) (k : Z) : Prop :=
  k = 2 ^ 64 - 1 \/ exists p n fl, xs = [WPtr p; WInt n; WInt fl] /\ 0 <= k <= n.

(** The contract [os_getrandom_contract] packages these predicates for a
    call returning a 64-bit integer. It emits no trace events, allocates
    and frees no objects, returns any count that [getrandom_count]
    allows, and allows capability panics when the buffer pointer is
    null, read-only, or out of bounds. *)
Definition os_getrandom_contract : contract os_world :=
  mkContract os_world (RClass L) os_getrandom_abi os_getrandom_pre
    (fun _ _ _ => []) os_getrandom_writes (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun xs _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       exists k, ending = CallReturn [WInt k] /\ getrandom_count xs k)
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** When an n-byte block at offset o lies within the bounds of a live
    object, a pointer to that offset carrying the object's writable
    capability satisfies `c: filc_check_write`. *)
Lemma getrandom_block_writable m b reg o n :
  live_at m b reg -> 0 <= o -> 0 <= n -> b + o + n <= r_end reg ->
  writable_span m (mkSpan (mkPtr (b + o) (Obj b)) n).
Proof.
  intros [E L] Ho Hn He. split; [cbn; lia|]. exists b, reg.
  split; [reflexivity|]. split; [exact E|]. split; [exact L|].
  cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** ## Over a Logic instance

    The contract above describes `c: zsys_getrandom` as a relation on
    physical memory and the OS world. The rule below lifts it into a
    [[weakest-precondition|weakest-precondition]] rule that callers use
    in proofs. *)

Import OsWorld OsWorld.L OsWorld.LG.

(** When an invocation of [os_getrandom_contract] returns to its caller,
    it leaves the OS world unchanged and yields a count that
    [getrandom_count] allows. *)
Lemma os_getrandom_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_getrandom_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ exists k, values = [WInt k] /\ getrandom_count xs k.
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & _ & k & He & Hk); injection He as ->. eauto.
Qed.

Import ProgramAbbreviations.
Section rule.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** When a C function calls `c: zsys_getrandom`, the caller lends an
    n-byte buffer inside a live object together with the thread's
    `c: errno` cell. When the call returns, [wp_zsys_getrandom] hands
    them back with any contents and binds the destination register to
    any count from zero to n, or to `c: -1`. *)
Lemma wp_zsys_getrandom f e ls lab d a0 a1 a2 rest j b reg o n fl eb Φ :
  registry (TAtom "zsys_getrandom") = Some os_getrandom_contract ->
  find_fn ge (TAtom "zsys_getrandom") = None -> lookup (TAtom "zsys_getrandom") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg P a0; Arg L a1; Arg W a2] = Some [WPtr (mkPtr (b + o) (Obj b)); WInt n; WInt fl] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 <= o -> 0 <= n < 2 ^ 63 -> b + o + n <= r_end reg ->
  live b reg -∗ blk_any b o n -∗ errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k <= n \/ k = 2 ^ 64 - 1)⌝ -∗ live b reg -∗ blk_any b o n -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zsys_getrandom")) [Arg P a0; Arg L a1; Arg W a2] :: rest) j))
          : zexpr) {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hdata Hx He Ho Hn Hend. iIntros "Hl Hb Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [(b, o, n)] (live b reg)
            (fun vs => exists k, vs = [WInt k] /\ (0 <= k <= n \/ k = 2 ^ 64 - 1))
            with "Hl Herr [Hb] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hl". iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    cbn [agree_piece fst snd] in Hlv.
    iDestruct (os_heap_world with "Hσ") as %[-> _].
    iDestruct (os_heap_errno with "Hσ") as %[Hc _]; [exact He|].
    pose proof (getrandom_block_writable _ _ _ _ n Hlv Ho (proj1 Hn) Hend) as Hwr.
    iPureIntro. split; [exists (mkPtr (b + o) (Obj b)), n, fl, (mkPtr eb (Obj eb)); auto|].
    split; [constructor; [exists reg; cbn; split; [exact Hlv|lia] | constructor]|].
    exists [mkSpan (mkPtr (b + o) (Obj b)) n]. split; [reflexivity|].
    intros sp a [<- | []] Hs. exists b, o, n. unfold span_contains in Hs. cbn in Hs.
    split; [left; reflexivity | lia].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro.
    destruct (os_getrandom_returns _ _ _ _ _ _ _ _ _ _ _ Hi) as (-> & k & -> & [-> | (p & n' & fl' & Exs & Hk)]).
    + split; [reflexivity|]. exists (2 ^ 64 - 1). auto.
    + injection Exs as _ <- _. split; [reflexivity|]. exists k. auto.
  - iApply blks_cons. iFrame "Hb". iApply blks_nil.
  - iNext. iIntros (vs (k & -> & Hk)) "Hl Herr Hb". iDestruct (blks_cons with "Hb") as "[Hb _]".
    iExists _. iSplit.
    + iPureIntro. cbn. rewrite Z.mod_small; [reflexivity|lia].
    + iApply ("HK" with "[%] Hl Hb Herr"). exact Hk.
Qed.

End rule.
