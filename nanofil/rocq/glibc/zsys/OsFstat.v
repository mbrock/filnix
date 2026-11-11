(** A trusted [[external call|contract]] at libpizlo's boundary:
    `c: int zsys_fstat(int fd, struct stat *st)`, over the [os_world]
    of [OsWorld](OsWorld.v). Its native counterexample probe is
    [zsys-fstat.c](zsys-fstat.c).

    ## What libpizlo runs

    At the pin (libpas/src/libpas/filc_runtime.c:8979):

    ```c
    int filc_native_zsys_fstat(filc_thread* my_thread, int fd, filc_ptr stat_ptr)
    {
        check_fd(fd);
        filc_check_write(stat_ptr, sizeof(struct stat));
        return FILC_SYSCALL(my_thread, fstat(fd, (struct stat* )filc_ptr_ptr(stat_ptr)));
    }
    ```

    - `c: check_fd(fd)` asserts `c: fd` is not the log descriptor.
    - `c: filc_check_write(st, 144)` (`c: sizeof(struct stat)` is 144
      on x86-64, which the probe checks) panics unless `c: st` carries a
      live, writable [Obj] capability for 144 bytes ([writable_span]).
    - The kernel writes the 144 bytes natively, through the raw
      address: the bytes may change and the [[aux]] slots there are
      not updated by the kernel, so the contract's roots are the 144
      bytes and errno ([os_fstat_writes]), and the caller's block comes
      back holding whatever the call left ([blk_any]). A success
      returns 0, a failure `c: (int)-1`, [2 ^ 32 - 1] at class [W]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic.
From Glibc Require Import OsBlocks OsWorld.
Import ListNotations.
Open Scope Z_scope.

(** ## The contract *)

(** `c: sizeof(struct stat)` on x86-64. *)
Definition stat_size : Z := 144.

(** `c: int zsys_fstat(int fd, void *st)`: [W], [P] to [W], or a
    discarded result. *)
Definition os_fstat_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists fd p, args = [Arg W fd; Arg P p].

(** Precondition: `c: st` passes `c: filc_check_write(st, 144)`, `c: fd`
    is not the log descriptor, and errno is a writable `c: int`. *)
Definition os_fstat_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd p e, xs = [WInt fd; WPtr p] /\ writable_span m (mkSpan p stat_size) /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** The writable roots: the 144 bytes at `c: st`, then errno. *)
Definition os_fstat_writes (xs : list word) (m : mem) (w : os_world) : list span :=
  match xs with [WInt _; WPtr p] => [mkSpan p stat_size] | _ => [] end ++ errno_spans w.

(** The contract: [RClass] [W]; no sources, releases, allocations,
    observations or resource endings; 0 or `c: -1` ([2 ^ 32 - 1]). A
    null, out-of-bounds or read-only buffer panics in
    `c: filc_check_write`. *)
Definition os_fstat_contract : contract os_world :=
  mkContract os_world (RClass W) os_fstat_abi os_fstat_pre
    (fun _ _ _ => []) os_fstat_writes (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       (ending = CallReturn [WInt 0] \/ ending = CallReturn [WInt (2 ^ 32 - 1)]))
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** A live object's block of 144 bytes at an offset in its bounds,
    through its [Obj] capability, passes the write check. *)
Lemma stat_block_writable m b reg o :
  live_at m b reg -> 0 <= o -> b + o + stat_size <= r_end reg ->
  writable_span m (mkSpan (mkPtr (b + o) (Obj b)) stat_size).
Proof.
  intros [E L] Ho He. split; [cbn; unfold stat_size; lia|]. exists b, reg.
  split; [reflexivity|]. split; [exact E|]. split; [exact L|].
  cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** ## Over a Logic instance *)

(** The rule for `c: zsys_fstat(fd, st)` over the [[runtime]] R and
    [LogicSig] LG0. *)
Module OsFstatOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** A returning call keeps the world and yields 0 or `c: -1`. *)
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

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_fstat_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** `c: zsys_fstat(fd, st)` with `c: fd` among w0's descriptors,
    `c: st` the address of the 144-byte block at offset o of the live
    object b, owned with its aux slots, and errno owned: the block and
    errno come back holding whatever the call left (on success, the
    `c: struct stat`), and d is bound to 0 or `c: -1`. *)
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

(** The same, lending errno holding bs. *)
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
