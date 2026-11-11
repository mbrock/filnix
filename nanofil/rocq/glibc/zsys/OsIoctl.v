(** When userland glibc issues a device control request, such as probing
    whether a file descriptor refers to a terminal in `c: isatty`, it
    calls libpizlo's `c: int zsys_ioctl(int fd, int request, ...)` wrapper
    with one variadic argument. That wrapper sits at the
    [[external call|contract]] boundary between compiled C code and the
    Fil-C [[runtime]]. This module defines the contract
    [os_ioctl_contract] for `c: zsys_ioctl` over the shared state
    [os_world] from [OsWorld](OsWorld.v), and derives its
    [[separation-logic|separation-logic]] call rules. Its runtime checks
    and corner cases are tested against native Fil-C in
    [zsys-ioctl.c](zsys-ioctl.c).

    ## What libpizlo runs

    At the pinned revision of `libpas/src/libpas/filc_runtime.c`,
    `c: zsys_ioctl` first calls `c: check_fd(fd)` to assert that the
    descriptor is not libpizlo's internal log descriptor [ow_log_fd]. It
    then reads its first variadic argument as a pointer, defaulting to
    null when none was passed, and hands that value to
    `c: filc_call_syscall_with_guarded_ptr`.

    When the argument's raw address lies below `2 ^ 32`, the runtime
    asserts that the value is not an in-bounds object pointer and passes
    the integer directly to the kernel. Because every native Fil-C object
    lives above `2 ^ 32`, this integer path handles arguments that carry
    no [[capability]].

    When the argument points into a live object, the runtime computes the
    byte count available from the pointer to the object's upper bound and
    verifies read authority across that range with `c: filc_check_read`.
    It copies at most the first 128 available bytes to a scratch page
    placed just before an unmapped guard page, and runs the kernel
    `c: ioctl` on that copy. If the kernel succeeds, the runtime verifies
    write authority over the copied range with `c: filc_check_write` and
    copies any modified bytes back to the caller's object; if the kernel
    fails with `c: EFAULT`, the runtime either panics when the object was
    smaller than the copy limit or doubles the limit and retries. Any
    nonzero error number is stored into userland glibc's `c: errno` cell.

    To bound the bytes that the wrapper can overwrite, [os_ioctl_contract]
    admits pointer arguments only for requests whose kernel byte footprint
    is recorded in [ioctl_footprint] and fits inside the caller's object.
    For those requests, the kernel never faults on the 128-byte scratch
    copy and the runtime never retries with a larger limit. The call
    therefore overwrites at most the first 128 available bytes of the
    caller's object, which we name [ioctl_root].

    In native Fil-C, every allocated object lives above `2 ^ 32`, whereas
    our formal model places global objects starting at address `65536`.
    Accordingly, the contract dispatches on whether the argument carries
    an object [[capability]] rather than on whether its numeric address
    lies above `2 ^ 32`. *)

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

    A terminal query may copy bytes back through the supplied pointer,
    with a size that depends on the request. The following definitions
    describe that copy-back span with [ioctl_root] and collect the
    call's requirements into [os_ioctl_contract]. *)

(** For the `c: ioctl` request codes that the contract models,
    [ioctl_footprint] gives the number of bytes that the kernel reads or
    writes through the argument pointer: 44 bytes for `c: TCGETS2` and 36
    bytes for `c: TCGETS`. *)
Definition ioctl_footprint (req : Z) : option Z :=
  if req =? 2150388778 then Some 44          (* 0x802C542A *)
  else if req =? 21505 then Some 36          (* 0x5401 *)
  else None.

(** Given a pointer into an object with region `reg`, [ioctl_avail]
    computes the number of bytes from the pointer's address to the upper
    bound of `reg`, matching `c: filc_ptr_available`. *)
Definition ioctl_avail (reg : region) (p : ptr) : Z := r_end reg - ptr_addr p.

(** When the argument carries a writable capability for a registered
    object, [ioctl_root] returns the span of at most 128 available bytes
    that `c: filc_call_syscall_with_guarded_ptr` may copy back into the
    caller's object. *)
Definition ioctl_root (m : mem) (p : ptr) : list span :=
  match ptr_cap p with
  | Obj b => match object_region b (m_regions m) with
             | Some reg => [mkSpan p (Z.min (ioctl_avail reg p) 128)]
             | None => []
             end
  | _ => []
  end.

(** An argument pointer and request code satisfy [ioctl_arg] when
    `c: zsys_ioctl` can run without panicking. Either the argument is a
    capability-free integer below `2 ^ 32`, or it points into a live
    object whose remaining bytes are readable, whose copy-back span is
    writable, and whose remaining room covers the request's known
    [ioctl_footprint]. *)
Definition ioctl_arg (m : mem) (req : Z) (p : ptr) : Prop :=
  (ptr_cap p = CNone /\ 0 <= ptr_addr p < 2 ^ 32) \/
  (exists b reg k, ptr_cap p = Obj b /\ live_at m b reg /\ b <= ptr_addr p /\
     ioctl_footprint req = Some k /\ k <= ioctl_avail reg p /\
     access_res m (ptr_addr p) (Obj b) (ioctl_avail reg p) Read 1 = Some ok /\
     writable_span m (mkSpan p (Z.min (ioctl_avail reg p) 128))).

(** A call site satisfies [os_ioctl_abi] when it passes a 32-bit
    descriptor, a 32-bit request code, and a pointer argument, and either
    discards the result or binds it to a 32-bit destination register. *)
Definition os_ioctl_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists fd req p, args = [Arg W fd; Arg W req; Arg P p].

(** At call entry, [os_ioctl_pre] requires that the request and argument
    satisfy [ioctl_arg], the file descriptor is not libpizlo's log
    descriptor, and the thread's `c: errno` pointer names a writable
    4-byte `c: int` cell. *)
Definition os_ioctl_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd req p e, xs = [WInt fd; WInt req; WPtr p] /\ ioctl_arg m req p /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** A call to `c: zsys_ioctl` can overwrite the copy-back span
    [ioctl_root] of its pointer argument together with the thread's 4-byte
    `c: errno` cell. *)
Definition os_ioctl_writes (xs : list word) (m : mem) (w : os_world) : list span :=
  match xs with [WInt _; WInt _; WPtr p] => ioctl_root m p | _ => [] end ++ errno_spans w.

(** The contract [os_ioctl_contract] packages these predicates for a call
    returning a 32-bit integer. It emits no trace events, allocates and
    frees no objects, returns a non-negative 32-bit integer or `c: -1` as
    `2 ^ 32 - 1`, and allows capability panics when a pointer argument is
    null, read-only, or out of bounds. *)
Definition os_ioctl_contract : contract os_world :=
  mkContract os_world (RClass W) os_ioctl_abi os_ioctl_pre
    (fun _ _ _ => []) os_ioctl_writes (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       exists k, ((0 <= k < 2 ^ 31) \/ k = 2 ^ 32 - 1) /\ ending = CallReturn [WInt k])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** Userland glibc's `c: __isatty_nostatus` passes the `c: TCGETS2`
    request code, which has a 44-byte footprint in [ioctl_footprint],
    while an unmodeled request code has none. *)
Example tcgets2_footprint : ioctl_footprint 2150388778 = Some 44 /\ ioctl_footprint 2150389802 = None.
Proof. split; reflexivity. Qed.

(** When a pointer addresses offset o of a live object through its
    writable capability and the request's known footprint fits in the
    remaining bytes of that object, the pointer satisfies [ioctl_arg]. *)
Lemma ioctl_block_arg m b reg o req k :
  live_at m b reg -> 0 <= o -> ioctl_footprint req = Some k -> k <= r_end reg - (b + o) ->
  ioctl_arg m req (mkPtr (b + o) (Obj b)).
Proof.
  intros [E L] Ho Hk Hfit. right. unfold ioctl_avail. cbn [ptr_addr ptr_cap].
  assert (Hk0 : 0 < k) by (unfold ioctl_footprint in Hk; destruct (req =? 2150388778);
                            [|destruct (req =? 21505)]; try discriminate Hk; injection Hk as <-; lia).
  exists b, reg, k. split; [reflexivity|]. split; [split; assumption|]. split; [lia|].
  split; [exact Hk|]. split; [exact Hfit|]. split.
  - apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
  - split; [cbn; lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
    cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** ## Over a Logic instance

    The contract above describes `c: zsys_ioctl` as a relation on physical
    memory and the OS world. The functor below connects that contract to a
    Fil-C [[runtime]] and the program logic of
    [Logic](../../theories/logic/Logic.v), deriving the
    [[weakest-precondition|weakest-precondition]] rules that callers use
    in proofs. *)

(** To verify C functions that call `c: zsys_ioctl`, [OsIoctlOn] lifts the
    contract above into separation-logic proof rules for a given
    [[runtime]] and program logic. *)
Module OsIoctlOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** When an invocation of [os_ioctl_contract] returns to its caller, it
    leaves the OS world unchanged and yields either a non-negative 32-bit
    integer or `c: -1`. *)
Lemma os_ioctl_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_ioctl_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ exists k, values = [WInt k] /\ ((0 <= k < 2 ^ 31) \/ k = 2 ^ 32 - 1).
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & Hw & _ & k & Hk & He). injection He as ->. eauto.
Qed.

Section rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The instance [os_ioctl_irisGS] configures Iris for the language with
    the OS contract registry and the world interpretation [os_wi]. *)
Local Instance os_ioctl_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** For a pointer at offset o of an object with region `reg`, [ioctl_n]
    computes the byte length of the copy-back block that the caller lends
    to `c: zsys_ioctl`, capped at 128 bytes. *)
Definition ioctl_n (reg : region) (b o : Z) : Z := Z.min (r_end reg - (b + o)) 128.

(** When a C function calls `c: zsys_ioctl` with a known request whose
    footprint fits at offset o of a live object, the caller lends the
    copy-back block of length [ioctl_n] together with the thread's
    `c: errno` cell. When the call returns, [wp_zsys_ioctl] hands back the
    live object token, the updated copy-back block, and `c: errno`, and
    binds the destination register to a non-negative 32-bit integer or
    `c: -1`. *)
Lemma wp_zsys_ioctl f e ls lab d a0 a1 a2 rest j fd req k b reg o eb Φ :
  registry (TAtom "zsys_ioctl") = Some os_ioctl_contract ->
  find_fn ge (TAtom "zsys_ioctl") = None -> lookup (TAtom "zsys_ioctl") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg W a1; Arg P a2] = Some [WInt fd; WInt req; WPtr (mkPtr (b + o) (Obj b))] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> ioctl_footprint req = Some k -> k <= r_end reg - (b + o) ->
  live b reg -∗ blk_any b o (ioctl_n reg b o) -∗ errno_any eb -∗
  ▷ (∀ x, ⌜(0 <= x < 2 ^ 31) \/ x = 2 ^ 32 - 1⌝ -∗ live b reg -∗ blk_any b o (ioctl_n reg b o) -∗
       errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_ioctl")) [Arg W a0; Arg W a1; Arg P a2]
                        :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hx He Hin Ho Hk Hfit. iIntros "Hl Hb Herr HK".
  iApply (wp_os_errno_call w0 _ _ _ _ _ _ _ _ _ _ _ _ _ eb [(b, o, ioctl_n reg b o)] (live b reg)
            (fun vs => exists x, vs = [WInt x] /\ ((0 <= x < 2 ^ 31) \/ x = 2 ^ 32 - 1))
            with "Hl Herr [Hb] [HK]"); [done | done | done | exact Hreg | exact Hx | | exact He | | done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hl". iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    cbn [agree_piece fst snd] in Hlv.
    iDestruct (os_heap_ready with "Hσ") as %(-> & Hfd & Hc); [exact He | exact Hin|].
    pose proof (ioctl_block_arg _ _ _ _ _ _ Hlv Ho Hk Hfit) as Harg.
    assert (Hk0 : 0 < k) by (unfold ioctl_footprint in Hk; destruct (req =? 2150388778);
                              [|destruct (req =? 21505)]; try discriminate Hk; injection Hk as <-; lia).
    iPureIntro. split; [exists fd, req, (mkPtr (b + o) (Obj b)), (mkPtr eb (Obj eb)); auto|].
    split; [constructor; [exists reg; cbn; unfold ioctl_n; split; [exact Hlv|lia] | constructor]|].
    exists [mkSpan (mkPtr (b + o) (Obj b)) (ioctl_n reg b o)]. split.
    + cbn [os_ioctl_contract contract_writes os_ioctl_writes]. unfold ioctl_root. cbn [ptr_cap].
      destruct Hlv as [E _]. unfold os_ioctl_writes, ioctl_root. cbn [ptr_cap]. rewrite E.
      unfold ioctl_avail, ioctl_n. reflexivity.
    + intros sp a [<- | []] Hs. exists b, o, (ioctl_n reg b o). unfold span_contains in Hs. cbn in Hs.
      split; [left; reflexivity | lia].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_ioctl_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_cons. iFrame "Hb". iApply blks_nil.
  - iNext. iIntros (vs (x & -> & Hv)) "Hl Herr Hb". iDestruct (blks_cons with "Hb") as "[Hb _]".
    assert (Hm : x mod 2 ^ 32 = x) by (apply Z.mod_small; lia).
    iExists _. iSplit; [done|]. rewrite Hm. iApply ("HK" with "[%] Hl Hb Herr"). exact Hv.
Qed.

(** A caller that tracks the exact four bytes stored in `c: errno` before
    calling `c: zsys_ioctl` can lend that cell directly through
    [wp_zsys_ioctl_lend] and receive the updated cell back after the call. *)
Lemma wp_zsys_ioctl_lend f e ls lab d a0 a1 a2 rest j fd req k b reg o eb bs Φ :
  registry (TAtom "zsys_ioctl") = Some os_ioctl_contract ->
  find_fn ge (TAtom "zsys_ioctl") = None -> lookup (TAtom "zsys_ioctl") (ge_globals ge) = None ->
  map_option (arg_x ge e) [Arg W a0; Arg W a1; Arg P a2] = Some [WInt fd; WInt req; WPtr (mkPtr (b + o) (Obj b))] ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> ioctl_footprint req = Some k -> k <= r_end reg - (b + o) ->
  live b reg -∗ blk_any b o (ioctl_n reg b o) -∗ errno_own eb bs -∗
  ▷ (∀ x, ⌜(0 <= x < 2 ^ 31) \/ x = 2 ^ 32 - 1⌝ -∗ live b reg -∗ blk_any b o (ioctl_n reg b o) -∗
       errno_any eb -∗
     WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "zsys_ioctl")) [Arg W a0; Arg W a1; Arg P a2]
                        :: rest) j)) : zexpr)
    {{ Φ }}.
Proof.
  intros. iIntros "Hl Hb Herr HK". iApply (wp_zsys_ioctl with "Hl Hb [Herr] HK"); try eassumption.
  by iExists bs.
Qed.

End rule.
End OsIoctlOn.
