(** A trusted [[external call|contract]] at libpizlo's boundary:
    `c: int zsys_close(int fd)`, over the [os_world] of
    [OsWorld](OsWorld.v). Its native counterexample probe is
    [zsys-close.c](zsys-close.c).

    ## What libpizlo runs

    `c: zsys_close` is pizlonated code of libpizlo's user runtime
    (filc/src/runtime.c:296) around the native
    `c: zsys_close_impl` (libpas/src/libpas/filc_runtime.c:8806):

    ```c
    int zsys_close(int fd)
    {
        struct fd_holder* holder;
        if (fd >= 0)
            holder = get_locked_existing_fd_holder(fd);
        else
            holder = 0;
        int result = zsys_close_impl(fd);
        if (holder) {
            if (!result)
                holder->backer = 0;
            lock_unlock(&holder->lock);
        }
        return result;
    }

    int filc_native_zsys_close_impl(filc_thread* my_thread, int fd)
    {
        if (is_reserved_fd(fd))
            return 0;
        filc_exit(my_thread);
        int result = close(fd);
        int my_errno = errno;
        filc_enter(my_thread);
        if (result < 0)
            filc_set_errno(my_errno);
        return result;
    }
    ```

    - There is no `c: check_fd(fd)`: closing libpizlo's log descriptor
      returns 0 and closes nothing. So any `c: fd` is admitted.
    - Trust assumption: runtime.c's `c: fd_table` is null, so
      `c: get_locked_existing_fd_holder` returns 0 and the call writes
      no Fil-C memory of the runtime's own (the holder's lock and
      backer). The table is created only by `c: zsys_fcntl`'s
      `c: F_DUPFD`, `c: dup`-like calls and epoll tracking, none of
      which user glibc's Hello path makes. With a table the call would
      also write it, which [errno_spans] does not allow.
    - A failing native `c: close` stores errno ([errno_spans]); the call
      returns 0 or `c: (int)-1`, [2 ^ 32 - 1] at class [W]. *)

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

(** `c: int zsys_close(int fd)`: [W] to [W], or a discarded result. *)
Definition os_close_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists fd, args = [Arg W fd].

(** Precondition: one `c: int` and a writable errno. No descriptor is
    refused, the log descriptor included. *)
Definition os_close_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd e, xs = [WInt fd] /\ ow_errno w = Some e /\ errno_cell m e.

(** The contract: [RClass] [W], errno as the only writable root; no
    sources, releases, allocations, observations or resource endings;
    0 or `c: -1` ([2 ^ 32 - 1]). *)
Definition os_close_contract : contract os_world :=
  mkContract os_world (RClass W) os_close_abi os_close_pre
    (fun _ _ _ => []) (fun _ _ w => errno_spans w) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       (ending = CallReturn [WInt 0] \/ ending = CallReturn [WInt (2 ^ 32 - 1)]))
    (fun _ => False) (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Over a Logic instance *)

(** The rule for `c: zsys_close(fd)` over the [[runtime]] R and
    [LogicSig] LG0. *)
Module OsCloseOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** A returning call keeps the world and yields 0 or `c: -1`. *)
Lemma os_close_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_close_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ (values = [WInt 0] \/ values = [WInt (2 ^ 32 - 1)]).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & _ & [He|He]); injection He as ->; auto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_close_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** `c: zsys_close(fd)` with errno owned: errno comes back holding
    whatever the call left, and d is bound to 0 or `c: -1`. *)
Lemma wp_zsys_close f e ls lab d a0 rest j fd eb Φ :
  registry (TAtom "zsys_close") = Some os_close_contract ->
  find_fn ge (TAtom "zsys_close") = None -> lookup (TAtom "zsys_close") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0] = Some [WInt fd] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_close")) [Arg W a0] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He. iIntros "Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [] True%I
            (fun vs => vs = [WInt 0] \/ vs = [WInt (2 ^ 32 - 1)])
            with "[//] Herr [] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ _". iDestruct (os_heap_errno with "Hσ") as %[Hc _]; [exact He|].
    iDestruct (os_heap_world with "Hσ") as %[-> _].
    iPureIntro. split; [exists fd, (mkPtr eb (Obj eb)); auto|]. split; [constructor|].
    exists []. split; [reflexivity | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_close_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_nil.
  - iNext. iIntros (vs Hv) "_ Herr _".
    destruct Hv as [-> | ->]; iExists _; (iSplit; [done|]); iApply ("HK" with "[%] Herr"); auto.
Qed.

(** The same, lending errno holding bs. *)
Lemma wp_zsys_close_lend f e ls lab d a0 rest j fd eb bs Φ :
  registry (TAtom "zsys_close") = Some os_close_contract ->
  find_fn ge (TAtom "zsys_close") = None -> lookup (TAtom "zsys_close") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0] = Some [WInt fd] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  errno_own eb bs -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt k) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_close")) [Arg W a0] :: rest) j)) : zexpr)
    {{ Φ }}.
Proof. intros. iIntros "Herr HK". iApply (wp_zsys_close with "[Herr] HK"); try eassumption. by iExists bs. Qed.

End rule.
End OsCloseOn.
