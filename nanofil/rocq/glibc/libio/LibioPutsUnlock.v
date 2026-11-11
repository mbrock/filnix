(** Block `c: L103` of `c: puts(s)` (LibioPutsCode.v,
    libio/ioputs.c), `c: _IO_release_lock(stdout)`: stdout's lock,
    which LibioPutsLock.v's [wp_puts_start] took, is released, the
    owner becoming null and the lock word 0 since the count is 0 and
    the process single-threaded, and the result is returned
    ([wp_puts_unlock]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  LibioPutsCode LibioPutsInv LibioPutsLock.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L103` of `c: puts`, which releases the lock. *)
Definition pu_L103 : block := Eval vm_compute in
  match find_block (TAtom "L103") (fn_blocks glibc__IO_puts) with
  | Some b => b | None => mkBlock (TAtom "L103") [] [] JRetVoid end.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioPutsUnlockOn (R : Runtime) (LG0 : LogicSig R).
Module PL := LibioPutsLockOn R LG0.
Import PL PL.PI PL.PI.CS PL.PI.CS.SW PL.PI.CS.SW.FI.ML PL.PI.CS.SW.FI.LG PL.PI.CS.SW.FI.L PL.PI.CS.SW.OW
  PL.PI.CS.SW.FI PL.PI.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance puts_unlock_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L103` of `c: puts`, its result r in `c: pr.1` and stdout
    fb in `c: v12` and `c: chk1`: the lock lb, held once by this
    thread, is released, the owner becoming null and the lock word 0,
    and r is returned. *)
Lemma wp_puts_unlock e r fb freg fl lb lbreg sb sreg Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "v12") e = Some (WPtr fp) -> lookup (TAtom "chk1") e = Some (WPtr fp) ->
  lookup (TAtom "pr.1") e = Some (WInt r) -> 0 <= r < 2 ^ 32 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 1 0 (ow_self w0) -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 0 0 null -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_puts e [] None (Exec (TAtom "L103") (b_insts pu_L103) (b_jump pu_L103)))
        : sexpr) {{ Φ }}.
Proof.
  intros fp Hv12 Hc1 Hr Hrr Hfb Hfal Hfend Hfreg Hfl Hul. subst fp.
  unfold file_size in Hfend.
  assert (Hcu' : Z.land (fl mod 2 ^ 32) (32768 mod 2 ^ 32) mod 2 ^ 32 = 0).
  { rewrite (Z.mod_small fl); [|lia]. change (32768 mod 2 ^ 32) with 32768. rewrite Hul. reflexivity. }
  iIntros "#Hs Hl [_ Hfl] Hlp Hlb HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlb" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  cbn [pu_L103 b_insts b_jump].
  (* The user lock is clear, and the process single-threaded. *)
  fchk "Hl". fldi "Hl" "Hfl". fs. fs. fbrv false.
  fs. fldi "Hl" "Hfl". fs. fs. fbrv false.
  fs. fs. chkp "Hsl". ldbp "Hsl Hsb". fs. fbr.
  (* The count is 0: the owner becomes null, then the lock word 0. *)
  fs. fs. fchk "Hl". fldp "Hl" "Hlp" "Hbl". fs. fchk "Hbl". fldi "Hbl" "Hb4". fs. fs. fs. fbr.
  fs. fs. fchk "Hl". fldp "Hl" "Hlp" "Hbl". fs. fchk "Hbl". fstp "Hbl" "Hbo".
  fchk "Hl". fldp "Hl" "Hlp" "Hbl". fchk "Hbl". fsti "Hbl" "Hb0". fs.
  fs. iApply wp_ret; [reflexivity | vx |]. iNext. rewrite (Z.mod_small r); [|lia].
  iApply ("HK" with "Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo]").
  - iSplit; [done | iExact "Hfl"].
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

End rules.
End LibioPutsUnlockOn.
