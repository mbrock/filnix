(** The end of one pass of `c: _IO_flush_all`'s loop
    (LibioFlushCode.v), from block `c: L182`: the pass releases the
    stream's lock (`c: _IO_funlockfile`), which the thread holds once
    at count 0, so the owner becomes null and the lock word 0 with no
    futex wake. Block `c: L329` then clears `c: run_fp` and reads the
    stream's `c: _chain`, the next stream or null, and the loop goes
    back to its head `c: L82`.

    Reading `c: _chain` loads a pointer, which needs the life of the
    object it names: the next stream's, given as [live_cap], or
    nothing for null. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry LibioFlushCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioFlushFpUnlockOn (R : Runtime) (LG0 : LogicSig R).
Module FL := LibioFlushFpLockOn R LG0.
Import FL FL.CS FL.CS.SW FL.CS.SW.FI.ML FL.CS.SW.FI.LG FL.CS.SW.FI.L FL.CS.SW.OW FL.CS.SW.FI FL.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance flush_fp_unlock_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L182` of `c: _IO_flush_all`, entered from `c: L257`
    with the pass's result r1 in `c: pr.2`, to the loop's head: the
    stream's lock, held once by the thread, is released,
    `c: run_fp` is null again, and the head is entered with the next
    stream nx in `c: v413` and r1, a 32-bit result, in `c: pr.1`. *)
Lemma wp_flush_L182 e r1 fb freg fl lb lbreg rf rfreg sb sreg x cb nx nreg Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "pr.5") e = Some (WPtr fp) -> lookup (TAtom "chk13") e = Some (WPtr fp) ->
  lookup (TAtom "pr.2") e = Some (WInt r1) -> lookup (TAtom "v3") e = Some (WPtr cb) ->
  0 <= r1 < 2 ^ 32 -> 0 <= ptr_addr nx < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 -> rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 1 0 (ow_self w0) -∗ live rf rfreg -∗ pcell rf 0 x -∗
  pcell fb off_chain nx -∗ live_cap (ptr_cap nx) nreg -∗
  ▷ (∀ e', ⌜lookup (TAtom "v413") e' = Some (WPtr nx) /\ lookup (TAtom "pr.1") e' = Some (WInt r1) /\
            lookup (TAtom "v3") e' = Some (WPtr cb)⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 0 0 null -∗ live rf rfreg -∗ pcell rf 0 null -∗
     pcell fb off_chain nx -∗ live_cap (ptr_cap nx) nreg -∗
     WP (ERun (mkFrame glibc__IO_flush_all e' [] None (Enter (TAtom "L82") (Some (TAtom "L329")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L182") (Some (TAtom "L257")))) : sexpr)
    {{ Φ }}.
Proof.
  intros fp Hgrf Hp5 Hc13 Hp2 Hv3 Hr1 Hnx Hfb Hfal Hfend Hfreg Hfl Hul Hral Hrend. subst fp.
  unfold file_size in Hfend. assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul; lia).
  iIntros "#Hs Hl [_ Hfl] Hlp Hlb Hrl Hrc Hch Hnl HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlb" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  iApply (wp_live_fit1 w0 registry ge with "Hrl"). iIntros ([Hrf0 Hrf48]) "Hrl".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* L182, L334: `c: _IO_USER_LOCK` clear, single threaded. *)
  fs. fchk "Hl". fldi "Hl" "Hfl". fs. fs. fbrv false.
  fs. fs. chkp "Hsl". ldbp "Hsl Hsb". fs. fbr.
  (* L343, L344: the count is 0. *)
  fs. fs. fchk "Hl". fldp "Hl" "Hlp" "Hbl". fs. fchk "Hbl". fldi "Hbl" "Hb4". fs. fs. fs. fbr.
  (* L337: the owner null, then the lock word 0. *)
  fs. fs. fchk "Hl". fldp "Hl" "Hlp" "Hbl". fs. fchk "Hbl". fstp "Hbl" "Hbo".
  fchk "Hl". fldp "Hl" "Hlp" "Hbl". fchk "Hbl". fsti "Hbl" "Hb0". fs.
  (* L329: `c: run_fp` null, and the next stream. *)
  fs. fs. fchk "Hrl". fstp "Hrl" "Hrc". fs. fchk "Hl". fldp "Hl" "Hch" "Hnl". fs.
  rewrite (Z.mod_small r1 (2 ^ 32)); [|exact Hr1].
  iApply ("HK" with "[%] Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo] Hrl Hrc Hch Hnl").
  - split_and!; lk_prove.
  - iSplit; [done | iExact "Hfl"].
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

End rules.
End LibioFlushFpUnlockOn.
