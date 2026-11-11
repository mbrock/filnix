(** A trusted [[external call|contract]] at libpizlo's boundary:
    `c: int zsys_ioctl(int fd, int request, ...)` with one variadic
    argument, over the [os_world] of [OsWorld](OsWorld.v). Its native
    counterexample probe is [zsys-ioctl.c](zsys-ioctl.c).

    ## What libpizlo runs

    At the pin (libpas/src/libpas/filc_runtime.c:10445), after
    `c: check_fd(fd)`, the call takes its first variadic argument as a
    pointer (a null one if there is none) and hands it to
    `c: filc_call_syscall_with_guarded_ptr` (filc_runtime.c:15466):

    - An address below 2^32 (`c: min_address`) is passed to the kernel
      as an integer, after asserting it is no in-bounds pointer of an
      object. Every Fil-C object lives above 2^32 natively, so this is
      the path of an argument with no capability ([CNone]).
    - Otherwise `c: maximum_extent` is the bytes available from the
      pointer to its object's upper bound, `c: filc_check_read(arg,
      maximum_extent)` checks them, and the first `c: limited =
      min(maximum_extent, 128)` are copied to a scratch page ending at
      a guard page. The kernel runs on the copy. Unless it set errno,
      changed bytes are copied back after `c: filc_check_write(arg,
      limited)`. On `c: EFAULT` the runtime panics if `c: limited` was
      below the limit (the object was too small), and otherwise
      doubles the limit and retries, so a request whose kernel
      footprint exceeds 128 bytes writes beyond 128 bytes.
    - A nonzero native errno is stored through user glibc's errno
      handler ([errno_spans]).

    The contract admits pointer arguments only for requests whose
    kernel footprint is known ([ioctl_footprint]) and fits in the
    object: then the kernel never faults on the copy, there is no
    retry, and the call writes at most the first `c: min(avail, 128)`
    bytes ([ioctl_root]). An integer argument writes no Fil-C memory;
    that the kernel does not take it for a user pointer is the
    runtime's own assumption. A [W] request is the low 32 bits.

    The model's addresses are not native ones: Run.v lays globals out
    from [data_base], 65536, below `c: min_address`, and a runtime's
    allocations may be anywhere below 2^48. Natively every Fil-C object
    lies above 2^32 (PIE or static PIE, as the runtime's comment says
    and the probe checks), so the contract trusts that a pointer with
    an [Obj] capability takes the guarded path. A model global below
    2^32 passed natively would instead trip the integer path's
    assertion. *)

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

(** The bytes the kernel reads and writes through the argument of the
    request req, for the requests the contract knows: `c: TCGETS2`
    (`c: _IOR('T', 0x2A, struct termios2)`, 44 bytes) and `c: TCGETS`
    (the kernel's 36-byte `c: struct termios`). *)
Definition ioctl_footprint (req : Z) : option Z :=
  if req =? 2150388778 then Some 44          (* 0x802C542A *)
  else if req =? 21505 then Some 36          (* 0x5401 *)
  else None.

(** The bytes available from p to the end of the object of the
    region reg: what `c: filc_ptr_available` computes. *)
Definition ioctl_avail (reg : region) (p : ptr) : Z := r_end reg - ptr_addr p.

(** The span the runtime may copy back: `c: min(available, 128)` bytes
    from p, inside the object of identity b, or nothing. *)
Definition ioctl_root (m : mem) (p : ptr) : list span :=
  match ptr_cap p with
  | Obj b => match object_region b (m_regions m) with
             | Some reg => [mkSpan p (Z.min (ioctl_avail reg p) 128)]
             | None => []
             end
  | _ => []
  end.

(** The argument p of the request req passes the guarded-pointer path
    without a panic: an integer below 2^32 with no capability; or a
    pointer into a live object, its rest readable
    (`c: filc_check_read`, a capability check only), its first
    `c: min(avail, 128)` bytes writable, for a request whose footprint
    fits in it. *)
Definition ioctl_arg (m : mem) (req : Z) (p : ptr) : Prop :=
  (ptr_cap p = CNone /\ 0 <= ptr_addr p < 2 ^ 32) \/
  (exists b reg k, ptr_cap p = Obj b /\ live_at m b reg /\ b <= ptr_addr p /\
     ioctl_footprint req = Some k /\ k <= ioctl_avail reg p /\
     access_res m (ptr_addr p) (Obj b) (ioctl_avail reg p) Read 1 = Some ok /\
     writable_span m (mkSpan p (Z.min (ioctl_avail reg p) 128))).

(** `c: zsys_ioctl(fd, req, arg)`: [W], [W], [P] to [W], or a
    discarded result. *)
Definition os_ioctl_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists fd req p, args = [Arg W fd; Arg W req; Arg P p].

(** Precondition: the argument passes ([ioctl_arg]), `c: fd` is not the
    log descriptor, and errno is a writable `c: int`. *)
Definition os_ioctl_pre (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists fd req p e, xs = [WInt fd; WInt req; WPtr p] /\ ioctl_arg m req p /\
    ow_log_fd w <> Some fd /\ ow_errno w = Some e /\ errno_cell m e.

(** The writable roots: the copy-back span, then errno. *)
Definition os_ioctl_writes (xs : list word) (m : mem) (w : os_world) : list span :=
  match xs with [WInt _; WInt _; WPtr p] => ioctl_root m p | _ => [] end ++ errno_spans w.

(** The contract: [RClass] [W]; no sources, releases, allocations,
    observations or resource endings; a nonnegative `c: int` or
    `c: -1` ([2 ^ 32 - 1]). *)
Definition os_ioctl_contract : contract os_world :=
  mkContract os_world (RClass W) os_ioctl_abi os_ioctl_pre
    (fun _ _ _ => []) os_ioctl_writes (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun _ _ w born trace ending _ w' => born = [] /\ w' = w /\ trace = [] /\
       exists k, ((0 <= k < 2 ^ 31) \/ k = 2 ^ 32 - 1) /\ ending = CallReturn [WInt k])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** `c: TCGETS2`, `c: 0x802C542A`, is the request `c: __isatty_nostatus`
    passes, with its 44-byte footprint; any other number has none. *)
Example tcgets2_footprint : ioctl_footprint 2150388778 = Some 44 /\ ioctl_footprint 2150389802 = None.
Proof. split; reflexivity. Qed.

(** A pointer at offset o of a live object, through its [Obj]
    capability, for a known request whose footprint fits, passes
    [ioctl_arg]. *)
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

(** ## Over a Logic instance *)

(** The rule for `c: zsys_ioctl(fd, req, arg)` over the [[runtime]] R
    and [LogicSig] LG0. *)
Module OsIoctlOn (R : Runtime) (LG0 : LogicSig R).
Module OW := OsWorldOn R LG0.
Import OW OW.L OW.LG.

(** A returning call keeps the world and yields a nonnegative
    `c: int` or `c: -1`. *)
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

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance os_ioctl_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** The bytes of the copy-back block of a pointer at offset o of the
    object b with region reg. *)
Definition ioctl_n (reg : region) (b o : Z) : Z := Z.min (r_end reg - (b + o)) 128.

(** `c: zsys_ioctl(fd, req, arg)` (`c: __isatty_nostatus`'s
    `c: TCGETS2`) with `c: fd` among w0's descriptors, `c: arg` at
    offset o of the live object b, the request's footprint fitting in
    the object, the first [ioctl_n] bytes there owned with their aux
    slots, and errno owned: the block and errno come back holding
    whatever the call left, and d is bound to a nonnegative `c: int` or
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

(** The same, lending errno holding bs. *)
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
