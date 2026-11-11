(** The start of one pass of `c: _IO_flush_all`'s loop over
    `c: _IO_list_all` (LibioFlushCode.v), from block `c: L83`: the
    pass sets `c: run_fp` to the stream and takes the stream's lock
    (`c: _IO_flockfile`). The stream's `c: _IO_USER_LOCK` is clear, its
    lock is free and the process is single threaded ([single_ro]), so
    the lock word becomes 1 and the owner the thread's cookie, as
    LibioUnlinkLock.v does for `c: _IO_un_link`. Block `c: L94` then
    tests what the stream has to flush; LibioFlushClean.v and
    LibioFlushOver.v go on from there. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry LibioFlushCode FileInv LibioLogic
  SysWrappers LibioCloseSteps.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioFlushFpLockOn (R : Runtime) (LG0 : LogicSig R).
Module CS := LibioCloseStepsOn R LG0.
Import CS CS.SW CS.SW.FI.ML CS.SW.FI.LG CS.SW.FI.L CS.SW.OW CS.SW.FI CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance flush_fp_lock_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** A call of `c: zthread_self_cookie`, whose result is the thread's
    cookie, not null (H). *)
Ltac self H := iApply (OTh.wp_zthread_self_cookie w0 registry ge); try self_side; [exact H|]; iNext.

(** Block `c: L83` of `c: _IO_flush_all` to block `c: L94`, the
    stream fb in `c: pr.5`: `c: run_fp` becomes fb, and the stream's
    free lock lb is taken by the thread, count 0. The pass's other
    values, the result so far r in `c: pr.4` and the cleanup buffer
    in `c: v3`, are kept, and `c: chk13` holds the stream. *)
Lemma wp_flush_L83 e fb freg fl lb lbreg rf rfreg sb sreg x r cb Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "pr.5") e = Some (WPtr fp) -> lookup (TAtom "pr.4") e = Some (WInt r) ->
  lookup (TAtom "v3") e = Some (WPtr cb) -> lookup (TAtom "v88") e = Some (WInt 0) ->
  ptr_addr (ow_self w0) <> 0 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 -> rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗ live rf rfreg -∗ pcell rf 0 x -∗
  ▷ (∀ e', ⌜lookup (TAtom "pr.5") e' = Some (WPtr fp) /\ lookup (TAtom "chk13") e' = Some (WPtr fp) /\
            lookup (TAtom "pr.4") e' = Some (WInt r) /\ lookup (TAtom "v3") e' = Some (WPtr cb)⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 1 0 (ow_self w0) -∗ live rf rfreg -∗ pcell rf 0 fp -∗
     WP (ERun (mkFrame glibc__IO_flush_all e' [] None (Enter (TAtom "L94") (Some (TAtom "L104")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L83") (Some (TAtom "L82")))) : sexpr) {{ Φ }}.
Proof.
  intros fp Hgrf Hp5 Hp4 Hv3 Hv88 Hsz Hfb Hfal Hfend Hfreg Hfl Hul Hral Hrend. subst fp.
  unfold file_size in Hfend. assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul; lia).
  iIntros "#Hs Hl [_ Hfl] Hlp Hlb Hrl Hrc HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlb" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  iApply (wp_live_fit1 w0 registry ge with "Hrl"). iIntros ([Hrf0 Hrf48]) "Hrl".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* L83: `c: run_fp`, and `c: _IO_USER_LOCK` clear. *)
  fs. fs. fchk "Hrl". fstp "Hrl" "Hrc". fchk "Hl". fldi "Hl" "Hfl". fs. fs. fbrv false.
  (* L99, L110, L111: single threaded, the owner null. *)
  fs. self Hsz. fs. chkp "Hsl". ldbp "Hsl Hsb". fs. fbr.
  fs. fs. fchk "Hl". fldp "Hl" "Hlp" "Hbl". fs. fchk "Hbl". fldn "Hbl" "Hbo". fs. fs. fs. fs. fbr.
  (* L104: the lock word 1, the owner the cookie. *)
  fs. fs. fchk "Hl". fldp "Hl" "Hlp" "Hbl". fchk "Hbl". fsti "Hbl" "Hb0". fldp "Hl" "Hlp" "Hbl". fs.
  fchk "Hbl". fstp "Hbl" "Hbo". fs.
  iApply ("HK" with "[%] Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo] Hrl Hrc").
  - split_and!; lk_prove.
  - iSplit; [done | iExact "Hfl"].
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

End rules.
End LibioFlushFpLockOn.
