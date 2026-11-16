From Glibc Require Import GlibcProgram.
(** During startup, `c: __pthread_early_init` asks for the stack size
    limit by calling libpizlo's `c: int zsys_getrlimit(int resource, void *rlim)`
    wrapper. This module defines the [[external call|contract]]
    [os_getrlimit_contract] for it over [os_world] from
    [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rule. Its checks and
    corner cases are tested against native Fil-C in
    [zsys-getrlimit.c](zsys-getrlimit.c).

    ## What libpizlo runs

    The wrapper checks the caller's buffer and lends it to the kernel,
    as the pinned `libpas/src/libpas/filc_runtime.c` shows.

    ```c
    int filc_native_zsys_getrlimit(filc_thread* my_thread, int resource, filc_ptr rlim_ptr)
    {
        filc_check_write(rlim_ptr, sizeof(struct rlimit));
        return FILC_SYSCALL(my_thread, getrlimit(resource, (struct rlimit* )filc_ptr_ptr(rlim_ptr)));
    }
    ```

    The kernel fills in 16 bytes of the caller's memory, so the wrapper
    first makes sure that the caller owns those bytes and may write them.
    The check requires a live, writable object [[capability]] covering
    the 16 bytes of `c: struct rlimit`. The kernel then writes those bytes
    without updating their [[aux]] capability slots. When the system call
    fails, `c: FILC_SYSCALL` stores the error number through the
    registered errno handler, and it panics when no handler is registered
    yet. For that reason the contract requires [ow_errno] to name a cell,
    and the call may write both the buffer and that cell. The wrapper
    takes no file descriptor, so the log descriptor plays no part. *)

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

    A limit query may overwrite both the destination record and the
    calling thread's error cell. The following definitions describe
    those spans and collect the call's requirements into [os_getrlimit_contract]. *)

(** On x86-64 Linux, `c: sizeof(struct rlimit)` is 16 bytes, which we name
    [rlimit_size]. *)
Definition rlimit_size : Z := 16.

(** A call site satisfies [os_getrlimit_abi] when it passes a 32-bit
    resource number and a pointer to a `c: struct rlimit` buffer, and either
    discards the result or binds it to a 32-bit destination register. *)
Definition os_getrlimit_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists a p, args = [Arg W a; Arg P p].

(** At call entry, [os_getrlimit_pre] requires that the destination pointer
    covers a writable 16-byte span and that the errno handler is
    registered with a writable 4-byte `c: int` cell. *)
Definition os_getrlimit_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists res p e, xs = [WInt res; WPtr p] /\ writable_span m (mkSpan p rlimit_size) /\
    ow_errno w = Some e /\ errno_cell m e.

(** A call to `c: zsys_getrlimit` can overwrite the 16-byte buffer at the
    caller's pointer and the thread's 4-byte `c: errno` cell. *)
Definition os_getrlimit_writes (xs : list word) (m : mem) (w : os_world) : list span :=
  match xs with [WInt _; WPtr p] => [mkSpan p rlimit_size] | _ => [] end ++ errno_spans w.

(** The contract [os_getrlimit_contract] packages these predicates for a
    call returning a 32-bit integer. It emits no trace events, allocates
    and frees no objects, returns either `0` or `c: -1` as `2 ^ 32 - 1`,
    and allows capability panics when the buffer pointer is null,
    read-only, or out of bounds. *)
Definition os_getrlimit_contract : contract os_world :=
  mkContract os_world (RClass W) os_getrlimit_abi os_getrlimit_pre
    (fun _ _ _ => []) os_getrlimit_writes (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       (ending = CallReturn [WInt 0] \/ ending = CallReturn [WInt (2 ^ 32 - 1)]))
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** When a 16-byte block at offset o lies within the bounds of a live
    object, a pointer to that offset carrying the object's writable
    capability satisfies `c: filc_check_write`. *)
Lemma rlimit_block_writable m b reg o :
  live_at m b reg -> 0 <= o -> b + o + rlimit_size <= r_end reg ->
  writable_span m (mkSpan (mkPtr (b + o) (Obj b)) rlimit_size).
Proof.
  intros [E L] Ho He. split; [cbn; unfold rlimit_size; lia|]. exists b, reg.
  split; [reflexivity|]. split; [exact E|]. split; [exact L|].
  cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** ## Over a Logic instance

    The contract above describes `c: zsys_getrlimit` as a relation on physical
    memory and the OS world. The functor below connects that contract to a
    Fil-C [[runtime]] and the program logic of
    [Logic](../../theories/logic/Logic.v), deriving the
    [[weakest-precondition|weakest-precondition]] rules that callers use
    in proofs. *)

(** The rules below lift the contract above into separation-logic proof rules
    for C functions that call `c: zsys_getrlimit`. *)
Import OsWorld OsWorld.L OsWorld.LG.

(** When an invocation of [os_getrlimit_contract] returns to its caller, it
    leaves the OS world unchanged and yields either `0` or `c: -1`. *)
Lemma os_getrlimit_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_getrlimit_contract r args xs s m w trace (CallReturn values) s' m' w' ->
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

(** When a C function calls `c: zsys_getrlimit`, the caller lends a 16-byte
    output buffer inside a live object together with the thread's
    `c: errno` cell. When the call returns, [wp_zsys_getrlimit] hands back the
    live object token, the updated 16-byte buffer, and `c: errno`, and
    binds the destination register to `0` or `c: -1`. *)
Lemma wp_zsys_getrlimit f e ls lab d a0 a1 rest j res b reg o eb Φ :
  registry (TAtom "zsys_getrlimit") = Some os_getrlimit_contract ->
  find_fn ge (TAtom "zsys_getrlimit") = None -> lookup (TAtom "zsys_getrlimit") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg P a1] = Some [WInt res; WPtr (mkPtr (b + o) (Obj b))] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 <= o -> b + o + rlimit_size <= r_end reg ->
  live b reg -∗ blk_any b o rlimit_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live b reg -∗ blk_any b o rlimit_size -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_getrlimit")) [Arg W a0; Arg P a1] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He Ho Hend. iIntros "Hl Hb Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [(b, o, rlimit_size)] (live b reg)
            (fun vs => vs = [WInt 0] \/ vs = [WInt (2 ^ 32 - 1)])
            with "Hl Herr [Hb] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ Hl". iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    cbn [agree_piece fst snd] in Hlv.
    iDestruct (os_heap_world with "Hσ") as %[-> _].
    iDestruct (os_heap_errno with "Hσ") as %[Hc _]; [exact He|].
    pose proof (rlimit_block_writable _ _ _ _ Hlv Ho Hend) as Hwr.
    iPureIntro. split; [exists res, (mkPtr (b + o) (Obj b)), (mkPtr eb (Obj eb)); auto|].
    split; [constructor; [exists reg; cbn; unfold rlimit_size in *; split; [exact Hlv|lia] | constructor]|].
    exists [mkSpan (mkPtr (b + o) (Obj b)) rlimit_size]. split; [reflexivity|].
    intros sp a [<- | []] Hs. exists b, o, rlimit_size. unfold span_contains in Hs. cbn in Hs.
    split; [left; reflexivity | lia].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_getrlimit_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_cons. iFrame "Hb". iApply blks_nil.
  - iNext. iIntros (vs Hv) "Hl Herr Hb". iDestruct (blks_cons with "Hb") as "[Hb _]".
    destruct Hv as [-> | ->]; iExists _; (iSplit; [done|]); iApply ("HK" with "[%] Hl Hb Herr"); auto.
Qed.

End rule.
