From Glibc Require Import GlibcProgram.
(** Glibc wraps runtime system calls in C functions that normalize their results.
    This module proves contracts for those wrappers over the OS state in
    [OsWorld](../zsys/OsWorld.v). The linked program must leave the runtime
    calls external and supply their contracts in its registry.

    Each wrapper calls the runtime and then returns, except for the exit wrapper,
    which never returns. Failed calls preserve ownership of errno but may change
    its bytes. Named contracts in [LibioSpecs] let stream callers use these
    results without constructing the callee's [[frame]]. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsWrite OsFstat OsIoctl OsLseek OsClose OsExit OsThread
  OsRegistry SysCode FileInv LibioLogic.
From Glibc Require FileInv LibioLogic OsClose OsExit OsFstat OsIoctl OsLseek OsWorld OsWrite.
From Glibc Require Import Fix.
From Glibc Require Import GlibcSpec LibioSpecs.
Import ListNotations.
Open Scope Z_scope.

(** Arithmetic computes on concrete numbers but stays folded on unknown inputs. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The wrappers call these runtime operations. *)
Definition sys_externals : list string :=
  ["zsys_write"; "zsys_fstat"; "zsys_ioctl"; "zsys_lseek"; "zsys_close"; "zsys_exit_hard";
   "zsys_exit_soft"; "zthread_self_cookie"].

(** The program leaves these names undefined as functions and global data.
    Calls therefore use the external contracts supplied by the registry. *)
Definition sys_external (ge : genv) : Prop :=
  Forall (fun s => find_fn ge (TAtom s) = None /\ lookup (TAtom s) (ge_globals ge) = None) sys_externals.

(** The registry holds the contracts of [glibc_os_registry]. *)
Definition holds_os (registry : name -> option (contract os_world)) : Prop :=
  forall n c, glibc_os_registry n = Some c -> registry n = Some c.


Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (registry : name -> option (contract os_world))
  (ge : genv)
  (Hreg : holds_os registry)
  (Hext : sys_external ge).
Existing Instance gen_heapGS0.
Lemma reg_of s c : glibc_os_registry (TAtom s) = Some c -> registry (TAtom s) = Some c.
Proof. apply Hreg. Qed.
Lemma ext_fn s : In s sys_externals -> find_fn ge (TAtom s) = None.
Proof. intros Hin. exact (proj1 (proj1 (Forall_forall _ _) Hext s Hin)). Qed.
Lemma ext_data s : In s sys_externals -> lookup (TAtom s) (ge_globals ge) = None.
Proof. intros Hin. exact (proj2 (proj1 (Forall_forall _ _) Hext s Hin)). Qed.
Lemma obj_blk b q :
  0 <= req_extent q -> obj b q -∗ live b (mkRegion b (b + req_extent q) (req_kind q) Live) ∗ blk_any b 0 (req_extent q).
Proof.
  iIntros (H) "Ho". rewrite obj_zero_block; [|exact H]. iDestruct "Ho" as "($ & Hb & Ha)".
  iExists (replicate (Z.to_nat (req_extent q)) 0), (replicate (Z.to_nat (req_extent q)) CNone).
  rewrite /bytes /auxes pts_app. iFrame. iPureIntro. rewrite !length_replicate. done.
Qed.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).


(** The expression type uses this caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A runtime call is safe only if its name is external and its contract is registered. *)
Ltac os_side :=
  first [ apply (reg_of registry Hreg); reflexivity
        | apply (ext_fn ge Hext); cbn; tauto
        | apply (ext_data ge Hext); cbn; tauto ].


(** Argument evaluation removes integer wrapping when bounds show that the value already fits. *)
Ltac args_x := first [cbn; repeat (rewrite Z.mod_small; [|lia]); reflexivity | reflexivity].

(** A wrapper can run once its arguments and external-call conditions have been checked. *)
Ltac sides := try first [os_side | args_x | assumption].

(** ## `c: _exit` *)

(** The exit wrapper calls the runtime's hard-exit operation, which halts.
    It therefore satisfies any postcondition without returning to its caller. *)
Lemma wp_glibc__exit fr bits Φ :
  call_frame glibc__exit [WInt bits] = Some fr -> ⊢ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr. injection Hfr as <-. step.
  iApply (OsExit.wp_zsys_exit_hard); sides.
Qed.

(** ## `c: __libc_write` *)

(** The write wrapper accepts a known descriptor and a readable buffer.
    It returns a bounded byte count or minus one, preserving the buffer and errno ownership. *)
Lemma wp_glibc___libc_write fr fd p n eb ps Φ :
  call_frame glibc___libc_write [WInt fd; WPtr p; WInt n] = Some fr ->
  0 <= fd < 2 ^ 32 -> 0 <= n < 2 ^ 64 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (forall m, all_agree m ps -> os_readable m p n) ->
  pts ps -∗ errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k <= n /\ k < 2 ^ 31) \/ k = 2 ^ 64 - 1⌝ -∗ pts ps -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd Hn He Hin Hrd. injection Hfr as <-. iIntros "Hps Herr HK". step.
  iApply (OsWrite.wp_zsys_write with "Hps Herr"); sides.
  iNext. iIntros (k Hk) "Hps Herr".
  assert (Hk' : 0 <= k < 2 ^ 64) by lia.
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite !(Z.mod_small k); [|lia|lia].
  iNext. iApply ("HK" with "[%] Hps Herr"). exact Hk.
Qed.

(** ## `c: __fstat64` *)

(** The stat wrapper writes into an owned buffer for a known descriptor.
    It returns zero or minus one and restores ownership of the buffer's new bytes. *)
Lemma wp_glibc___fstat64 fr fd b reg o eb Φ :
  call_frame glibc___fstat64 [WInt fd; WPtr (mkPtr (b + o) (Obj b))] = Some fr ->
  0 <= fd < 2 ^ 32 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> b + o + stat_size <= r_end reg ->
  live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
       Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd He Hin Ho Hend. injection Hfr as <-. iIntros "Hl Hb Herr HK". step.
  iApply (OsFstat.wp_zsys_fstat with "Hl Hb Herr");
    sides.
  iNext. iIntros (k Hk) "Hl Hb Herr".
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite Z.mod_small; [|lia].
  iNext. iApply ("HK" with "[%] Hl Hb Herr"). exact Hk.
Qed.

(** ## `c: __lseek64` *)

(** The seek wrapper changes the position of a known descriptor.
    It returns the new offset below 2^63, or minus one on failure. *)
Lemma wp_glibc___lseek64 fr fd off wh eb Φ :
  call_frame glibc___lseek64 [WInt fd; WInt off; WInt wh] = Some fr ->
  0 <= fd < 2 ^ 32 -> 0 <= off < 2 ^ 64 -> 0 <= wh < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  errno_any eb -∗
  ▷ (∀ k, ⌜(0 <= k < 2 ^ 63) \/ k = 2 ^ 64 - 1⌝ -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd Hoff Hwh He Hin. injection Hfr as <-. iIntros "Herr HK". step.
  iApply (OsLseek.wp_zsys_lseek with "Herr");
    sides.
  iNext. iIntros (k Hk) "Herr".
  assert (Hk' : 0 <= k < 2 ^ 64) by lia.
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite !(Z.mod_small k); [|lia|lia].
  iNext. iApply ("HK" with "[%] Herr"). exact Hk.
Qed.

(** ## `c: __close_nocancel` *)

(** The close wrapper returns zero or minus one and preserves errno ownership.
    It accepts any descriptor because the runtime does not require a registered descriptor for close. *)
Lemma wp_glibc___close_nocancel fr fd eb Φ :
  call_frame glibc___close_nocancel [WInt fd] = Some fr -> 0 <= fd < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  errno_any eb -∗ ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd He. injection Hfr as <-. iIntros "Herr HK". step.
  iApply (OsClose.wp_zsys_close with "Herr"); sides.
  iNext. iIntros (k Hk) "Herr".
  iApply wp_ret; [reflexivity | reflexivity |]. rewrite Z.mod_small; [|lia].
  iNext. iApply ("HK" with "[%] Herr"). exact Hk.
Qed.

(** The no-status variant discards close's result and returns void. *)
Lemma wp_glibc___close_nocancel_nostatus fr fd eb Φ :
  call_frame glibc___close_nocancel_nostatus [WInt fd] = Some fr -> 0 <= fd < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  errno_any eb -∗ ▷ (errno_any eb -∗ Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd He. injection Hfr as <-. iIntros "Herr HK". step.
  iApply (OsClose.wp_zsys_close with "Herr"); sides.
  iNext. iIntros (k Hk) "Herr". iApply wp_ret_void. iNext. iApply ("HK" with "Herr").
Qed.

(** ## `c: __isatty_nostatus` *)

(** The terminal query allocates a temporary buffer and asks the kernel for terminal settings.
    It returns one when the query succeeds and zero otherwise, preserving errno ownership. *)
Lemma wp_glibc___isatty_nostatus fr fd eb Φ :
  call_frame glibc___isatty_nostatus [WInt fd] = Some fr -> 0 <= fd < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  errno_any eb -∗ ▷ (∀ r, ⌜r = 0 \/ r = 1⌝ -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfd He Hin. injection Hfr as <-. iIntros "Herr HK". step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
                    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (base (Hb0 & _ & Hb48)) "Ho".
  iDestruct (obj_blk with "Ho") as "[Hl Hb]"; [vm_compute; congruence|]. cbn [req_extent req_kind heap_req] in *.
  replace ((44 + 15) / 16 * 16) with 48 by reflexivity.
  iApply (OsIoctl.wp_zsys_ioctl _ _ _ _ _ _ _ _ _ _ fd 2150388778 44 base _ 0 eb
            with "Hl [Hb] Herr"); sides.
  - cbn. rewrite Z.add_0_r !Z.mod_small; [reflexivity | lia | lia].
  - cbn. lia.
  - unfold OsIoctl.ioctl_n. cbn [r_end]. rewrite Z.add_0_r. replace (Z.min (base + 48 - base) 128) with 48 by lia.
    iExact "Hb".
  - iNext. iIntros (x Hx) "_ _ Herr".
    iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |]. iNext.
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    iApply ("HK" with "[%] Herr"). cbn. destruct (_ =? _); [right | left]; reflexivity.
Qed.

(** The linked close wrapper establishes the descriptor-close contract. *)
#[global] Instance close_has_spec n `{!Defines ge n glibc___close_nocancel} :
  HasSpec registry (os_wi w0) ge (TAtom n) LibioSpecs.close_spec.
Proof.
  intros [fd eb]. exists glibc___close_nocancel. split; [apply defines|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post LibioSpecs.close_spec]. iIntros "((%Hfd & %He) & Herr) HK".
  iApply (wp_glibc___close_nocancel fr fd eb with "Herr"); try assumption.
  iNext. iIntros (k Hk) "Herr". iApply "HK". iExists k. by iFrame.
Qed.

(** The linked terminal wrapper establishes the terminal-query contract. *)
#[global] Instance isatty_has_spec n `{!Defines ge n glibc___isatty_nostatus} :
  HasSpec registry (os_wi w0) ge (TAtom n) isatty_spec.
Proof.
  intros [fd eb]. exists glibc___isatty_nostatus. split; [apply defines|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post isatty_spec]. iIntros "((%Hfd & %He & %Hin) & Herr) HK".
  iApply (wp_glibc___isatty_nostatus fr fd eb with "Herr"); try assumption.
  iNext. iIntros (k Hk) "Herr". iApply "HK". iExists k. by iFrame.
Qed.

(** The linked stat wrapper establishes the stat-buffer contract. *)
#[global] Instance fstat_has_spec n `{!Defines ge n glibc___fstat64} :
  HasSpec registry (os_wi w0) ge (TAtom n) fstat_spec.
Proof.
  intros [[[[fd b] reg] o] eb]. exists glibc___fstat64. split; [apply defines|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fstat_spec]. iIntros "((%Hfd & %He & %Hin & %Ho & %Hend) & Hl & Hb & Herr) HK".
  iApply (wp_glibc___fstat64 fr fd b reg o eb with "Hl Hb Herr"); try assumption.
  iNext. iIntros (k Hk) "Hl Hb Herr". iApply "HK". iExists k. by iFrame.
Qed.

End rules.
