(** The end of `c: _IO_flush_all` (LibioFlushCode.v), from block
    `c: L414`, after the loop has passed every stream: the function
    releases `c: list_all_lock`, which the thread holds once at count
    0, so the owner becomes null and the lock word 0 with no futex
    wake. It then pops the cleanup buffer with
    `c: __libc_cleanup_pop_restore`, whose triple ([pop_spec])
    SysCleanupPop.v proves, and returns the result in `c: pr.4`. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean
  LibioFlushStart.
From Glibc Require FileInv LibioCloseSteps LibioFlushClean LibioFlushStart LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioFlushStart LibioFlushClean LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance flush_tail_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: __libc_cleanup_pop_restore`'s triple for the cleanup buffer
    cb that [push_spec] pushed, as SysCleanupPop.v's
    [wp_glibc___libc_cleanup_pop_restore] states it at offset 0; a
    premise for the reason [push_spec] is, proved in
    LibioCleanupExit.v. *)
Definition pop_spec : Prop := forall fr cb creg Φ,
  call_frame glibc___libc_cleanup_pop_restore [WPtr (mkPtr cb (Obj cb))] = Some fr ->
  0 < cb -> cb mod 8 = 0 -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 ->
  ⊢ tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
    ▷ (tcb_cleanup_inv (ow_self w0) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗ Φ RetVoid) -∗
    WP (ERun fr : sexpr) {{ Φ }}.

(** [pop_spec] holds. *)
Context (Hpop_spec : pop_spec).

(** Block `c: L414` of `c: _IO_flush_all` to its return, the result r
    in `c: pr.4` and the cleanup buffer cb in `c: v3`:
    `c: list_all_lock` is free again, the buffer is popped, restoring
    [tcb_cleanup_inv], and the function returns r. *)
Lemma wp_flush_L414 e r cb creg lk lkreg sb sreg Φ :
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "v3") e = Some (WPtr (mkPtr cb (Obj cb))) -> lookup (TAtom "pr.4") e = Some (WInt r) ->
  0 <= r < 2 ^ 32 -> 0 < cb -> cb mod 8 = 0 -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 ->
  single_ro ge sb sreg -∗ lock_state lk lkreg 1 0 (ow_self w0) -∗
  tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
  ▷ (lock_state lk lkreg 0 0 null -∗ tcb_cleanup_inv (ow_self w0) -∗ live cb creg -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L414") (Some (TAtom "L82")))) : sexpr)
    {{ Φ }}.
Proof.
  intros Hglk Hv3 Hp4 Hr Hcb Hcal Hcend Hcreg.
  iIntros "#(%Hs & Hsl & Hsb) (%Hlk & Hll & Hl0 & [%Hc0 Hl4] & Hlo) Htcb Hcl Hcp Hct HK".
  destruct Hs as (Hgs & Hsend). destruct Hlk as (Hlal & Hlend & Hlreg).
  iApply (wp_live_fit1 w0 registry ge with "Hll"). iIntros ([Hlk0 Hlk48]) "Hll".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* L414, L423, L424: single threaded, the count 0. *)
  step. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. step. check "Hll". load_s32 "Hll" "Hl4". step. step. step. branch.
  (* L417: the owner null, then the lock word 0. *)
  step. step. step. check "Hll". store "Hll" "Hlo". step. check "Hll".
  iDestruct "Hl0" as "[%Hl0r Hl0]". store_int "Hll" "Hl0". step. step.
  (* L476: pop the cleanup buffer and return. *)
  iApply wp_call_bind; [vx | exact Hpop | reflexivity |]. iNext.
  iApply (Hpop_spec with "Htcb Hcl Hcp Hct"); [reflexivity | lia | exact Hcal | lia | lia |].
  iNext. iIntros "Htcb Hcl _ _". resume.
  iApply wp_ret; [reflexivity | vx |]. iNext. rewrite (Z.mod_small r (2 ^ 32)); [|exact Hr].
  iApply ("HK" with "[Hll Hl0 Hl4 Hlo] Htcb Hcl").
  iFrame. iPureIntro. unfold int_bytes. split_and!; try lia.
Qed.

End rules.
