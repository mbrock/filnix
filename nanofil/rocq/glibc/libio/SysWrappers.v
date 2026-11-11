(** Triples for user glibc's C wrappers over libpizlo's `zsys_*` calls
    (SysCode.v), over the [os_world] of [OsWorld](../zsys/OsWorld.v)
    and any registry holding [glibc_os_registry]'s contracts, for any
    genv where the `zsys_*` names are external: `c: _exit`,
    `c: __libc_write`, `c: __fstat64`, `c: __lseek64`,
    `c: __close_nocancel` and its `_nostatus` twin,
    and `c: __isatty_nostatus`. SysCleanup.v has the cleanup push and
    pop over FileInv.v's [tcb_cleanup_inv].

    Each wrapper's body is one call of its contract and a return, so
    each triple is the contract's rule (OsWrite.v to OsExit.v) between
    entering the block and returning, stated for the callee frame
    [call_frame] makes of the arguments: a caller binds it with
    Logic.v's [wp_call_bind]. A failing call leaves errno holding
    whatever libpizlo's handler stored ([errno_any]); `c: _exit`
    never returns, so its triple proves any postcondition. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsWrite OsFstat OsIoctl OsLseek OsClose OsExit OsThread
  OsRegistry SysCode FileInv LibioLogic.
Import ListNotations.
Open Scope Z_scope.

(** Integer arithmetic stays folded on an unknown under [cbn]
    (Symbolic.v's decisions): on numbers it computes. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The `zsys_*` names the wrappers call. *)
Definition sys_externals : list string :=
  ["zsys_write"; "zsys_fstat"; "zsys_ioctl"; "zsys_lseek"; "zsys_close"; "zsys_exit_hard";
   "zsys_exit_soft"; "zthread_self_cookie"].

(** The genv ge defines none of them, as function or data: each call
    of one is a call of its contract. *)
Definition sys_external (ge : genv) : Prop :=
  Forall (fun s => find_fn ge (TAtom s) = None /\ lookup (TAtom s) (ge_globals ge) = None) sys_externals.

(** The registry holds the contracts of [glibc_os_registry]. *)
Definition holds_os (registry : name -> option (contract os_world)) : Prop :=
  forall n c, glibc_os_registry n = Some c -> registry n = Some c.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module SysWrappersOn (R : Runtime) (LG0 : LogicSig R).
Module FI := FileInvOn R LG0.
Module OWr := OsWriteOn R LG0.
Module OFs := OsFstatOn R LG0.
Module OIo := OsIoctlOn R LG0.
Module OLs := OsLseekOn R LG0.
Module OCl := OsCloseOn R LG0.
Module OEx := OsExitOn R LG0.
Module OTh := OsThreadOn R LG0.
Module OW := OWr.OW.
Module ST := LibioStepOn R LG0.
Import FI.ML FI.LG FI.L OW FI ST.

(** A signed 32-bit load of an owned [int_cell]'s bytes, H naming the
    object's life and the bytes. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | ar |];
  iNext; iIntros H.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance sys_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The registry's contract of a `zsys_*` name. *)
Lemma reg_of s c : glibc_os_registry (TAtom s) = Some c -> registry (TAtom s) = Some c.
Proof. apply Hreg. Qed.

(** The genv neither defines nor holds one of [sys_externals]. *)
Lemma ext_fn s : In s sys_externals -> find_fn ge (TAtom s) = None.
Proof. intros Hin. exact (proj1 (proj1 (Forall_forall _ _) Hext s Hin)). Qed.
Lemma ext_data s : In s sys_externals -> lookup (TAtom s) (ge_globals ge) = None.
Proof. intros Hin. exact (proj2 (proj1 (Forall_forall _ _) Hext s Hin)). Qed.

(** The premises of a contract call's rule: its registry entry and
    the name's being external. *)
Ltac os_side :=
  first [ apply reg_of; reflexivity
        | apply ext_fn; cbn; tauto
        | apply ext_data; cbn; tauto ].


(** The arguments of a call, read from the frame: computed, with each
    wrap of a canonical value dropped. *)
Ltac args_x := first [cbn; repeat (rewrite Z.mod_small; [|lia]); reflexivity | reflexivity].

(** Every pure premise of a contract call's rule: by [os_side],
    [args_x] or a hypothesis. *)
Ltac sides := try first [os_side | args_x | assumption].

(** ## `c: _exit` *)

(** `c: _exit(status)` ends the process through `c: zsys_exit_hard`:
    any postcondition. *)
Lemma wp_glibc__exit fr bits Φ :
  call_frame glibc__exit [WInt bits] = Some fr -> ⊢ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr. injection Hfr as <-. enter.
  iApply (OEx.wp_zsys_exit_hard w0 registry ge); sides.
Qed.

(** ## `c: __libc_write` *)

(** `c: __libc_write(fd, p, n)`, `c: fd` one of w0's and the owned
    pieces ps making p pass `c: filc_check_read(p, n)`: what
    `c: zsys_write` returns, a count k up to n and below 2^31 or
    `c: -1`, with ps and errno back. *)
Lemma wp_glibc___libc_write fr fd p n eb ps Φ :
  call_frame glibc___libc_write [WInt fd; WPtr p; WInt n] = Some fr ->
  0 <= fd < 2 ^ 32 -> 0 <= n < 2 ^ 64 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (forall m, all_agree m ps -> os_readable m p n) ->
  pts ps -∗ errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ pts ps -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd Hn He Hin Hrd. injection Hfr as <-. iIntros "Hps Herr HK". enter.
  iApply (OWr.wp_zsys_write w0 registry ge with "Hps Herr"); sides.
  iNext. iIntros (k Hk) "Hps Herr".
  assert (Hk' : 0 <= k < 2 ^ 64) by lia.
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite !(Z.mod_small k); [|lia|lia].
  iNext. iApply ("HK" with "[%] Hps Herr"). exact Hk.
Qed.

(** ## `c: __fstat64` *)

(** `c: __fstat64(fd, st)`, st at offset o of the live object b with
    the 144 bytes of `c: struct stat` there owned: 0 or `c: -1`, the
    block holding whatever the kernel left. *)
Lemma wp_glibc___fstat64 fr fd b reg o eb Φ :
  call_frame glibc___fstat64 [WInt fd; WPtr (mkPtr (b + o) (Obj b))] = Some fr ->
  0 <= fd < 2 ^ 32 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> b + o + stat_size <= r_end reg ->
  live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
       Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd He Hin Ho Hend. injection Hfr as <-. iIntros "Hl Hb Herr HK". enter.
  iApply (OFs.wp_zsys_fstat w0 registry ge with "Hl Hb Herr");
    sides.
  iNext. iIntros (k Hk) "Hl Hb Herr".
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite Z.mod_small; [|lia].
  iNext. iApply ("HK" with "[%] Hl Hb Herr"). exact Hk.
Qed.

(** ## `c: __lseek64` *)

(** `c: __lseek64(fd, off, whence)`: the new offset, below 2^63, or
    `c: -1`. *)
Lemma wp_glibc___lseek64 fr fd off wh eb Φ :
  call_frame glibc___lseek64 [WInt fd; WInt off; WInt wh] = Some fr ->
  0 <= fd < 2 ^ 32 -> 0 <= off < 2 ^ 64 -> 0 <= wh < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1⌝ -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd Hoff Hwh He Hin. injection Hfr as <-. iIntros "Herr HK". enter.
  iApply (OLs.wp_zsys_lseek w0 registry ge with "Herr");
    sides.
  iNext. iIntros (k Hk) "Herr".
  assert (Hk' : 0 <= k < 2 ^ 64) by lia.
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite !(Z.mod_small k); [|lia|lia].
  iNext. iApply ("HK" with "[%] Herr"). exact Hk.
Qed.

(** ## `c: __close_nocancel` *)

(** `c: __close_nocancel(fd)`: 0 or `c: -1`. Any descriptor: libpizlo's
    close does not check it. *)
Lemma wp_glibc___close_nocancel fr fd eb Φ :
  call_frame glibc___close_nocancel [WInt fd] = Some fr -> 0 <= fd < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  errno_any eb -∗ ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd He. injection Hfr as <-. iIntros "Herr HK". enter.
  iApply (OCl.wp_zsys_close w0 registry ge with "Herr"); sides.
  iNext. iIntros (k Hk) "Herr".
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite Z.mod_small; [|lia].
  iNext. iApply ("HK" with "[%] Herr"). exact Hk.
Qed.

(** `c: __close_nocancel_nostatus(fd)`: the same, returning nothing. *)
Lemma wp_glibc___close_nocancel_nostatus fr fd eb Φ :
  call_frame glibc___close_nocancel_nostatus [WInt fd] = Some fr -> 0 <= fd < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  errno_any eb -∗ ▷ (errno_any eb -∗ Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd He. injection Hfr as <-. iIntros "Herr HK". enter.
  iApply (OCl.wp_zsys_close w0 registry ge with "Herr"); sides.
  iNext. iIntros (k Hk) "Herr". iApply wp_ret_void. iNext. iApply ("HK" with "Herr").
Qed.

(** ## `c: __isatty_nostatus` *)

(** A fresh heap object's pieces are its life and a block of its whole
    extent ([blk_any]), whatever it holds. *)
Lemma obj_blk b q :
  0 <= req_extent q -> obj b q -∗ live b (mkRegion b (b + req_extent q) (req_kind q) Live) ∗ blk_any b 0 (req_extent q).
Proof.
  iIntros (H) "Ho". rewrite obj_zero_block; [|exact H]. iDestruct "Ho" as "($ & Hb & Ha)".
  iExists (replicate (Z.to_nat (req_extent q)) 0), (replicate (Z.to_nat (req_extent q)) CNone).
  rewrite /bytes /auxes pts_app. iFrame. iPureIntro. rewrite !length_replicate. done.
Qed.

(** `c: __isatty_nostatus(fd)`: a fresh 44-byte `c: struct termios2`
    on the heap for `c: zsys_ioctl(fd, TCGETS2, &k_termios)`, then 1
    if it returned 0, else 0; errno holds whatever the call left. *)
Lemma wp_glibc___isatty_nostatus fr fd eb Φ :
  call_frame glibc___isatty_nostatus [WInt fd] = Some fr -> 0 <= fd < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  errno_any eb -∗ ▷ (∀ r, ⌜r = 0 \/ r = 1⌝ -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd He Hin. injection Hfr as <-. iIntros "Herr HK". enter.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
                    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (base (Hb0 & _ & Hb48)) "Ho".
  iDestruct (obj_blk with "Ho") as "[Hl Hb]"; [vm_compute; congruence|]. cbn [req_extent req_kind heap_req] in *.
  replace ((44 + 15) / 16 * 16) with 48 by reflexivity.
  iApply (OIo.wp_zsys_ioctl w0 registry ge _ _ _ _ _ _ _ _ _ _ fd 2150388778 44 base _ 0 eb
            with "Hl [Hb] Herr"); sides.
  - cbn. rewrite Z.add_0_r !Z.mod_small; [reflexivity | lia | lia].
  - cbn. lia.
  - unfold OIo.ioctl_n. cbn [r_end]. rewrite Z.add_0_r. replace (Z.min (base + 48 - base) 128) with 48 by lia.
    iExact "Hb".
  - iNext. iIntros (x Hx) "_ _ Herr".
    iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |]. iNext.
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    iApply ("HK" with "[%] Herr"). cbn. destruct (_ =? _); [right | left]; reflexivity.
Qed.

End rules.
End SysWrappersOn.
