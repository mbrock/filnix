(** This file proves how `c: _IO_cleanup` (LibioCleanupCode.v) takes
    and releases `c: list_all_lock` around the loop of
    `c: _IO_unbuffer_all`. Before the loop the thread finds the lock's
    owner null and takes the lock, so the lock word becomes 1 and the
    owner the cookie in `c: iw_1.v16`; block `c: iw_1.L14` then reads
    the head of `c: _IO_list_all`, a stream whose life the caller
    lends, or null. After the loop the thread releases the lock with
    no futex wake, pops the cleanup buffer and returns the flush's
    result. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode LibioCleanupCode FileInv
  LibioLogic SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean LibioFlushStart
  LibioFlushTail LibioFlushBody LibioFlush LibioCleanupFpLock LibioCleanupMode LibioCleanupFpUnlock
  LibioCleanupStart.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioCleanupLockOn (R : Runtime) (LG0 : LogicSig R).
Module CT := LibioCleanupStartOn R LG0.
Import CT CT.CU CT.CU.CM CT.CU.CM.CL CT.CU.CM.CL.FA CT.CU.CM.CL.FA.FB CT.CU.CM.CL.FA.FB.FT CT.CU.CM.CL.FA.FB.FT.FS
  CT.CU.CM.CL.FA.FB.FT.FS.FC CT.CU.CM.CL.FA.FB.FT.FS.FC.FU CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL
  CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL.CS CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL.CS.SW
  CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.FI.ML CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.FI.LG
  CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.FI.L CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.OW
  CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.FI CT.CU.CM.CL.FA.FB.FT.FS.FC.FU.FL.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance cleanup_lock_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: iw_1.L23` of `c: _IO_cleanup` to the loop's head, the
    thread's cookie in `c: iw_1.v16`: the free `c: list_all_lock` is
    held once by the thread, and the head is entered from
    `c: iw_1.L14` with the list's head h in `c: iw_1.v80`. The flush's
    result in `c: v1` and the cleanup buffer in `c: iw_1.v2` are
    kept. *)
Lemma wp_cleanup_L23 e la lareg lk lkreg h hreg r cb Φ :
  lookup (TAtom "__GI__IO_list_all") (ge_globals ge) = Some (mkPtr la (Obj la)) ->
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "iw_1.v16") e = Some (WPtr (ow_self w0)) -> lookup (TAtom "v1") e = Some (WInt r) ->
  lookup (TAtom "iw_1.v2") e = Some (WPtr cb) ->
  la mod 8 = 0 -> la + 8 <= r_end lareg -> 0 <= ptr_addr h < 2 ^ 64 ->
  live la lareg -∗ pcell la 0 h -∗ live_cap (ptr_cap h) hreg -∗ lock_state lk lkreg 0 0 null -∗
  ▷ (∀ e', ⌜lookup (TAtom "iw_1.v80") e' = Some (WPtr h) /\ lookup (TAtom "v1") e' = Some (WInt r) /\
            lookup (TAtom "iw_1.v2") e' = Some (WPtr cb)⌝ -∗
     live la lareg -∗ pcell la 0 h -∗ live_cap (ptr_cap h) hreg -∗ lock_state lk lkreg 1 0 (ow_self w0) -∗
     WP (ERun (mkFrame glibc__IO_cleanup e' [] None (Enter (TAtom "iw_1.L81") (Some (TAtom "iw_1.L14")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_cleanup e [] None (Enter (TAtom "iw_1.L23") (Some (TAtom "start")))) : sexpr)
    {{ Φ }}.
Proof.
  intros Hgla Hglk Hv16 Hv1 Hv2 Hlaal Hlaend Hh.
  iIntros "Hla Hlah Hhl Hlk HK".
  iDestruct "Hlk" as "(%Hk & Hkl & [%Hk0r Hk0] & [%Hk4r Hk4] & Hko)". destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 w0 registry ge with "Hla"). iIntros ([Hla0 Hla48]) "Hla".
  iApply (wp_live_fit1 w0 registry ge with "Hkl"). iIntros ([Hlk0 Hlk48]) "Hkl".
  (* iw_1.L23, iw_1.L24: the owner null. *)
  fs. fs. fs. fchk "Hkl". fldn "Hkl" "Hko". fs. fs. fs. fs. fs. fbr.
  (* iw_1.L17: the lock word 1, the owner the cookie. *)
  fs. fs. fchk "Hkl". fsti "Hkl" "Hk0". fs. fs. fchk "Hkl". fstp "Hkl" "Hko". fs.
  (* iw_1.L14: the head of the list. *)
  fs. fs. fchk "Hla". fldp "Hla" "Hlah" "Hhl". iApply wp_goto. iNext.
  iApply ("HK" with "[%] Hla Hlah Hhl [Hkl Hk0 Hk4 Hko]").
  - split_and!; lk_prove.
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

(** `c: __libc_cleanup_pop_restore`'s triple at offset 0 holds. *)
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).

(** [pop_spec] holds. *)
Context (Hpop_spec : pop_spec w0 registry ge).

(** Block `c: iw_1.L386` of `c: _IO_cleanup`, after the loop, to its
    return, the flush's result r in `c: v1` and the cleanup buffer cb
    in `c: iw_1.v2`: `c: list_all_lock`, held once at count 0, is
    released with no futex wake, the buffer is popped, restoring
    [tcb_cleanup_inv], and the function returns r. *)
Lemma wp_cleanup_L386 e r cb creg lk lkreg sb sreg Φ :
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "iw_1.v2") e = Some (WPtr (mkPtr cb (Obj cb))) -> lookup (TAtom "v1") e = Some (WInt r) ->
  0 <= r < 2 ^ 32 -> 0 < cb -> cb mod 8 = 0 -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 ->
  single_ro ge sb sreg -∗ lock_state lk lkreg 1 0 (ow_self w0) -∗
  tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
  ▷ (lock_state lk lkreg 0 0 null -∗ tcb_cleanup_inv (ow_self w0) -∗ live cb creg -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_cleanup e [] None (Enter (TAtom "iw_1.L386") (Some (TAtom "iw_1.L81")))) : sexpr)
    {{ Φ }}.
Proof.
  intros Hglk Hv2 Hv1 Hr Hcb Hcal Hcend Hcreg.
  iIntros "#(%Hs & Hsl & Hsb) (%Hlk & Hll & Hl0 & [%Hc0 Hl4] & Hlo) Htcb Hcl Hcp Hct HK".
  destruct Hs as (Hgs & Hsend). destruct Hlk as (Hlal & Hlend & Hlreg).
  iApply (wp_live_fit1 w0 registry ge with "Hll"). iIntros ([Hlk0 Hlk48]) "Hll".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* iw_1.L386, iw_1.L395, iw_1.L396: single threaded, the count 0. *)
  fs. fs. chkp "Hsl". ldbp "Hsl Hsb". fs. fbr.
  fs. fs. fs. fchk "Hll". fldi "Hll" "Hl4". fs. fs. fs. fbr.
  (* iw_1.L389: the owner null, then the lock word 0. *)
  fs. fs. fs. fchk "Hll". fstp "Hll" "Hlo". fs. fchk "Hll".
  iDestruct "Hl0" as "[%Hl0r Hl0]". fsti "Hll" "Hl0". fs. fs.
  (* iw_1.L448: pop the cleanup buffer and return. *)
  iApply wp_call_bind; [vx | exact Hpop | reflexivity |]. iNext.
  iApply (Hpop_spec with "Htcb Hcl Hcp Hct"); [reflexivity | lia | exact Hcal | lia | lia |].
  iNext. iIntros "Htcb Hcl _ _". resume.
  iApply wp_ret; [reflexivity | vx |]. iNext. rewrite (Z.mod_small r (2 ^ 32)); [|exact Hr].
  iApply ("HK" with "[Hll Hl0 Hl4 Hlo] Htcb Hcl").
  iFrame. iPureIntro. unfold int_bytes. split_and!; try lia.
Qed.

End rules.
End LibioCleanupLockOn.
