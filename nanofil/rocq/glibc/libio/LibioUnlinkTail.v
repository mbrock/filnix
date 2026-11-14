(** The end of `c: _IO_un_link` (LibioUnlinkCode.v), from block
    `c: L179`, after the stream has left the list: `c: _IO_LINKED`
    cleared, the stream's lock released ([wp_unlink_L179]), then
    `c: run_fp` null again, `c: list_all_lock` released and the
    cleanup buffer popped ([wp_unlink_L257]). LibioUnlink.v proves the
    whole function.

    Single threaded ([single_ro]) with each lock taken once, at count
    0, each release takes the path that stores a null owner and a free
    lock word, with no futex wake. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioUnlinkCode FileInv LibioLogic
  SysWrappers SysCleanup SysCleanupPop LibioCloseSteps.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysCleanupPop SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance unlink_tail_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L257` of `c: _IO_un_link` and what follows: `c: run_fp`
    is null again, `c: list_all_lock`, held once by the thread, is
    released, and the cleanup buffer at v10 is popped, restoring
    [tcb_cleanup_inv]. *)
Lemma wp_unlink_L257 e from cb creg lk lkreg rf rfreg sb sreg x Φ :
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  0 < cb -> cb mod 8 = 0 -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 ->
  rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  single_ro ge sb sreg -∗ live rf rfreg -∗ pcell rf 0 x -∗ lock_state lk lkreg 1 0 (ow_self w0) -∗
  tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
  ▷ (live rf rfreg -∗ pcell rf 0 null -∗ lock_state lk lkreg 0 0 null -∗ tcb_cleanup_inv (ow_self w0) -∗
     live cb creg -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc__IO_un_link e [] None (Enter (TAtom "L257") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hglk Hgrf Hv10 Hcb Hcal Hcend Hcreg Hral Hrend.
  iIntros "#(%Hs & Hsl & Hsb) Hrl Hrc (%Hlk & Hll & Hl0 & [%Hc0 Hl4] & Hlo) Htcb Hcl Hcp Hct HK".
  destruct Hs as (Hgs & Hsend). destruct Hlk as (Hlal & Hlend & Hlreg).
  iApply (wp_live_fit1 w0 registry ge with "Hrl"). iIntros ([Hrf0 Hrf48]) "Hrl".
  iApply (wp_live_fit1 w0 registry ge with "Hll"). iIntros ([Hlk0 Hlk48]) "Hll".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  step. step. check "Hrl". store "Hrl" "Hrc". step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. step. check "Hll". load_s32 "Hll" "Hl4". step. step. step. branch.
  step. step. step. check "Hll". store "Hll" "Hlo". step. check "Hll".
  iDestruct "Hl0" as "[%Hl0r Hl0]". store_int "Hll" "Hl0". step. step.
  iApply wp_call_bind; [vx | exact Hpop | reflexivity |]. iNext.
  assert (E : mkPtr cb (Obj cb) = mkPtr (cb + 0) (Obj cb)) by (rewrite Z.add_0_r; reflexivity).
  iEval (rewrite E) in "Htcb".
  iApply (SysCleanupPop.wp_glibc___libc_cleanup_pop_restore w0 registry ge Hreg Hext _ cb creg 0
            with "Htcb Hcl Hcp Hct"); [rewrite Z.add_0_r; reflexivity | lia | lia | rewrite Z.add_0_r; exact Hcal | lia | lia |].
  iNext. iIntros "Htcb Hcl _ _". resume. step. step. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hrl Hrc [Hll Hl0 Hl4 Hlo] Htcb Hcl").
  iFrame. iPureIntro. unfold int_bytes. split_and!; try lia.
Qed.

(** The flags with `c: _IO_LINKED` (128) cleared. *)
Definition unlinked_flags (fl : Z) : Z := Z.land fl 4294967167.

(** [unlinked_flags] keeps the flags' range. *)
Lemma unlinked_flags_range fl : 0 <= fl < 2 ^ 32 -> 0 <= unlinked_flags fl < 2 ^ 32.
Proof. intros H. unfold unlinked_flags. apply land_lt32; lia. Qed.

(** Clearing `c: _IO_LINKED` keeps `c: _IO_USER_LOCK` (32768) clear. *)
Lemma unlinked_user_lock fl : Z.land fl 32768 = 0 -> Z.land (unlinked_flags fl) 32768 = 0.
Proof.
  intros H. unfold unlinked_flags. rewrite <- Z.land_assoc.
  change (Z.land 4294967167 32768) with 32768. exact H.
Qed.

(** Block `c: L179` of `c: _IO_un_link` to its return: `c: _flags`
    loses `c: _IO_LINKED`, the stream's lock, held once by the thread
    (`c: _IO_funlockfile` single threaded, count 0), is released, and
    [wp_unlink_L257] ends the call. *)
Lemma wp_unlink_L179 e from fb freg fl lb lbreg cb creg lk lkreg rf rfreg sb sreg x Φ :
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 ->
  0 < cb -> cb mod 8 = 0 -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 ->
  rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 1 0 (ow_self w0) -∗
  live rf rfreg -∗ pcell rf 0 x -∗ lock_state lk lkreg 1 0 (ow_self w0) -∗
  tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (unlinked_flags fl) -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
     lock_state lb lbreg 0 0 null -∗
     live rf rfreg -∗ pcell rf 0 null -∗ lock_state lk lkreg 0 0 null -∗ tcb_cleanup_inv (ow_self w0) -∗
     live cb creg -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc__IO_un_link e [] None (Enter (TAtom "L179") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hglk Hgrf Hv0 Hc0 Hv10 Hfb Hfal Hfend Hfreg Hfl Hul Hcb Hcal Hcend Hcreg Hral Hrend.
  iIntros "#Hs Hl [_ Hfl] Hlp (%Hb & Hbl & Hb0 & [%Hb4r Hb4] & Hbo) Hrl Hrc Hlk Htcb Hcl Hcp Hct HK".
  destruct Hb as (Hbal & Hbend & Hbreg). unfold file_size in Hfend.
  iPoseProof "Hs" as "(%Hs & Hsl & Hsb)". destruct Hs as (Hgs & Hsend).
  iApply (wp_live_fit1 w0 registry ge with "Hbl"). iIntros ([Hb0' Hb48]) "Hbl".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  pose proof (unlinked_flags_range fl Hfl) as Hfl'.
  step. check "Hl". load_s32 "Hl" "Hfl". step. check "Hl".
  store_int "Hl" "Hfl".
  assert (E : Z.land (fl mod 2 ^ 32) (4294967167 mod 2 ^ 32) mod 2 ^ 32 = unlinked_flags fl).
  { replace (fl mod 2 ^ 32) with fl by (symmetry; apply Z.mod_small; lia).
    change (4294967167 mod 2 ^ 32) with 4294967167. apply Z.mod_small. exact Hfl'. }
  iEval (rewrite E) in "Hfl". clear E.
  pose proof (unlinked_user_lock fl Hul) as Hul'.
  assert (0 <= Z.land (unlinked_flags fl) 32768 < 2 ^ 32) by lia.
  load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch. step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl".
  load_s32 "Hbl" "Hb4". step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo". check "Hl". load "Hl" "Hlp" "Hbl".
  check "Hbl". iDestruct "Hb0" as "[%Hb0r Hb0]". store_int "Hbl" "Hb0". step.
  iApply (wp_unlink_L257 with "Hs Hrl Hrc Hlk Htcb Hcl Hcp Hct"); try close_side.
  iNext. iIntros "Hrl Hrc Hlk Htcb Hcl". iApply ("HK" with "Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo] Hrl Hrc Hlk Htcb Hcl").
  - iSplit; [iPureIntro; exact Hfl'|]. iExact "Hfl".
  - iFrame. iPureIntro. unfold int_bytes. split_and!; try lia.
Qed.

End rules.
