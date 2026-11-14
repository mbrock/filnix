(** The start of `c: _IO_cleanup ()` (LibioCleanupCode.v,
    libio/genops.c), to the head of the loop of the
    `c: _IO_unbuffer_all` it inlines. `c: _IO_cleanup` first calls
    `c: _IO_flush_all` (LibioFlush.v's [wp_glibc__IO_flush_all]),
    whose result it returns at the end. `c: _IO_unbuffer_all` then
    pushes a fresh cleanup buffer ([push_spec]) and reads the thread's
    cookie, as `c: _IO_flush_all` does (LibioFlushStart.v). Block
    `c: iw_1.L23` then takes `c: list_all_lock` (LibioCleanupLock.v). *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode LibioCleanupCode FileInv
  LibioLogic SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean LibioFlushStart
  LibioFlushTail LibioFlushBody LibioFlush LibioCleanupFpLock LibioCleanupMode LibioCleanupFpUnlock.
From Glibc Require FileInv LibioCleanupFpLock LibioCleanupFpUnlock LibioCleanupMode LibioCloseSteps LibioFlush LibioFlushBody LibioFlushClean LibioFlushFpLock LibioFlushFpUnlock LibioFlushStart LibioFlushTail LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCleanupFpUnlock LibioCleanupMode LibioCleanupFpLock LibioFlush LibioFlushBody LibioFlushTail LibioFlushStart LibioFlushClean LibioFlushFpUnlock LibioFlushFpLock LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hpush : find_fn ge (TAtom "__GI___libc_cleanup_push_defer") =
                 Some (Defined glibc___libc_cleanup_push_defer)).
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).
Context (Hflush : find_fn ge (TAtom "__GI__IO_flush_all") = Some (Defined glibc__IO_flush_all)).
Context (Hpush_spec : push_spec w0 registry ge) (Hpop_spec : pop_spec w0 registry ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance cleanup_start_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** A call of `c: zthread_self_cookie`, whose result is the thread's
    cookie, not null (H). *)
Ltac self H := iApply (OsThread.wp_zthread_self_cookie w0 registry ge); try self_side; [exact H|]; iNext.

(** `c: _IO_cleanup ()` from its frame fr to block `c: iw_1.L23`,
    over [io_list_inv]'s streams fs, each with its life and P, each
    pass of `c: _IO_flush_all` the [flush_body] P Q: the flush runs,
    its result r in `c: v1`, each stream then has Q, a fresh cleanup
    buffer cb in `c: iw_1.v2` is pushed, and the thread's cookie is in
    `c: iw_1.v16`. *)
Lemma wp_cleanup_start fr (P Q : ptr -> iProp Σ) fs sb sreg fcp Φ :
  flush_body w0 registry ge P Q -> call_frame glibc__IO_cleanup [] = Some fr ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗ io_list_inv ge fs -∗
  ([∗ list] g ∈ fs, stream_life g ∗ P g) -∗
  ▷ (∀ e r cb creg la lareg lk lkreg rf rfreg,
     ⌜lookup (TAtom "iw_1.v16") e = Some (WPtr (ow_self w0)) /\ lookup (TAtom "v1") e = Some (WInt r) /\
      lookup (TAtom "iw_1.v2") e = Some (WPtr (mkPtr cb (Obj cb))) /\ (r = 0 \/ r = 2 ^ 32 - 1) /\
      0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= r_end creg /\ r_end creg <= 2 ^ 63 /\
      lookup (TAtom "__GI__IO_list_all") (ge_globals ge) = Some (mkPtr la (Obj la)) /\
      lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) /\
      lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) /\
      la mod 8 = 0 /\ la + 8 <= r_end lareg /\ rf mod 8 = 0 /\ rf + 8 <= r_end rfreg /\
      ptr_addr (ow_self w0) <> 0⌝ -∗
     tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
     live la lareg -∗ pcell la 0 (head_ptr fs) -∗ chain_links (mkPtr la (Obj la)) fs -∗
     lock_state lk lkreg 0 0 null -∗ live rf rfreg -∗ pcell rf 0 null -∗
     ([∗ list] g ∈ fs, stream_life g ∗ Q g) -∗
     WP (ERun (mkFrame glibc__IO_cleanup e [] None (Enter (TAtom "iw_1.L23") (Some (TAtom "start")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hbody Hfr Hfc Hfcr. injection Hfr as <-.
  iIntros "#Hs Htcb Hio Hfs HK".
  (* start: `c: _IO_flush_all ()`. *)
  step. iApply wp_call_bind; [vx | exact Hflush | reflexivity |]. iNext.
  iApply (wp_glibc__IO_flush_all w0 registry ge Hreg Hext Hpush Hpop Hpush_spec Hpop_spec
            with "Hs Htcb Hio Hfs"); [exact Hbody | reflexivity | exact Hfc | exact Hfcr |].
  iNext. iIntros (r Hr) "Htcb Hio Hfs". resume.
  iDestruct "Hio" as (la lareg lk lkreg rf rfreg Hio) "(Hla & Hlah & Hch & Hlk & Hrl & Hrc)".
  destruct Hio as (Hgla & Hglk & Hgrf & Hlaal & Hlaend & Hral & Hrend).
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Htcb" as (tb treg jb Ht) "Htcb". pose proof Ht as (Hself & Htb & _).
  iAssert (tcb_cleanup_inv (ow_self w0)) with "[Htcb]" as "Htcb".
  { iExists tb, treg, jb. iSplit; [iPureIntro; exact Ht | iExact "Htcb"]. }
  assert (Hsz : ptr_addr (ow_self w0) <> 0) by (rewrite Hself; cbn; lia).
  iApply (wp_live_fit1 w0 registry ge with "Hla"). iIntros ([Hla0 Hla48]) "Hla".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* The cleanup buffer, pushed. *)
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (cb [Hcb [Hcal Hcend]]) "Hobj". cbn in Hcal, Hcend.
  change (Z.pos (32 + 15) / 16 * 16) with 32 in Hcend.
  assert (Hcal8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj32 with "Hobj") as "(Hcl & Hc0 & Hc8 & Hc16 & Hc24)".
  set (creg := mkRegion cb (cb + 32) Heap Live). assert (Hcre : r_end creg = cb + 32) by reflexivity.
  step. step. check "Hcl". store "Hcl" "Hc8". check "Hcl". store "Hcl" "Hc0".
  iApply wp_call_bind; [vx | exact Hpush | reflexivity |]. iNext.
  iApply (Hpush_spec with "Htcb Hcl Hc24 Hc16"); [reflexivity | lia | exact Hcal8 | lia | lia | reflexivity |].
  iNext. iIntros "Htcb Hcl Hc24 Hc16". resume.
  (* The thread's cookie, and a single thread. *)
  self Hsz. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  assert (Hrm : r mod 2 ^ 32 = r) by (apply Z.mod_small; destruct Hr as [-> | ->]; lia).
  rewrite ?Hrm.
  iApply ("HK" $! _ r cb creg la lareg lk lkreg rf rfreg with "[%] Htcb Hcl Hc24 Hc16 Hla Hlah Hch
            Hlk Hrl Hrc Hfs").
  split_and!; try lk_prove; try assumption; lia.
Qed.

End rules.
