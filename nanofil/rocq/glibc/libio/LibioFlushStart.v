From Glibc Require Import GlibcProgram.
(** The start of `c: _IO_flush_all` (LibioFlushCode.v), to the head
    of its loop over `c: _IO_list_all`: `c: _IO_cleanup_region_start_noarg`
    allocates a 32-byte cleanup buffer, stores `c: flush_cleanup` in it
    and pushes it with `c: __libc_cleanup_push_defer`, whose triple
    ([push_spec]) SysCleanup.v proves. The function then takes
    `c: list_all_lock`, which is free, as the single thread
    ([single_ro]): the lock word becomes 1 and the owner the thread's
    cookie. Last it reads the head of the list, a stream whose life
    the caller lends ([live_cap]) or null. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioFlushCode FileInv LibioLogic
  SysWrappers LibioCloseSteps LibioFlushFpLock LibioFlushFpUnlock LibioFlushClean.
From Glibc Require FileInv LibioCloseSteps LibioFlushClean LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioFlushClean LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance flush_start_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition push_spec : Prop := forall fr cb creg pv xs Φ,
  call_frame glibc___libc_cleanup_push_defer [WPtr (mkPtr cb (Obj cb))] = Some fr ->
  0 < cb -> cb mod 8 = 0 -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 -> length xs = 4%nat ->
  ⊢ tcb_cleanup_inv (ow_self w0) -∗ live cb creg -∗ pcell cb 24 pv -∗ bytes cb 16 xs -∗
    ▷ (tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
       Φ RetVoid) -∗
    WP (ERun fr : sexpr) {{ Φ }}.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context `{Hpush : !Defines ge "__GI___libc_cleanup_push_defer" glibc___libc_cleanup_push_defer}.


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: __libc_cleanup_push_defer`'s triple for a fresh 32-byte
    cleanup buffer cb, as SysCleanup.v's
    [wp_glibc___libc_cleanup_push_defer] states it at offset 0. It is
    a premise here, so that these proofs do not instantiate
    SysCleanup.v's module; LibioCleanupExit.v proves it. *)

(** [push_spec] holds. *)
Context (Hpush_spec : (push_spec w0 registry ge)).

(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** A call of `c: zthread_self_cookie`, whose result is the thread's
    cookie, not null (H). *)
Ltac self H := iApply (OsThread.wp_zthread_self_cookie); try self_side; [exact H|]; iNext.

(** `c: _IO_flush_all ()` from its frame fr to the head of its loop:
    the cleanup buffer cb is pushed, `c: list_all_lock` is held once
    by the thread, and the loop's head is entered from `c: L15` with
    the list's head h in `c: v81` and cb in `c: v3`. *)
Lemma wp_flush_start fr la lareg lk lkreg h hreg sb sreg fcp Φ :
  call_frame glibc__IO_flush_all [] = Some fr ->
  lookup (TAtom "__GI__IO_list_all") (ge_globals ge) = Some (mkPtr la (Obj la)) ->
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  la mod 8 = 0 -> la + 8 <= r_end lareg -> 0 <= ptr_addr h < 2 ^ 64 ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗ live la lareg -∗ pcell la 0 h -∗
  live_cap (ptr_cap h) hreg -∗ lock_state lk lkreg 0 0 null -∗
  ▷ (∀ e cb creg, ⌜lookup (TAtom "v81") e = Some (WPtr h) /\
                   lookup (TAtom "v3") e = Some (WPtr (mkPtr cb (Obj cb))) /\
                   0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= r_end creg /\ r_end creg <= 2 ^ 63⌝ -∗
     tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗ live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
     live la lareg -∗ pcell la 0 h -∗ live_cap (ptr_cap h) hreg -∗ lock_state lk lkreg 1 0 (ow_self w0) -∗
     WP (ERun (mkFrame glibc__IO_flush_all e [] None (Enter (TAtom "L82") (Some (TAtom "L15")))) : sexpr)
       {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hgla Hglk Hfc Hfcr Hlaal Hlaend Hh. injection Hfr as <-.
  iIntros "#Hs Htcb Hla Hlah Hhl Hlk HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Htcb" as (tb treg jb Ht) "Htcb". pose proof Ht as (Hself & Htb & _).
  iAssert (tcb_cleanup_inv (ow_self w0)) with "[Htcb]" as "Htcb".
  { iExists tb, treg, jb. iSplit; [iPureIntro; exact Ht | iExact "Htcb"]. }
  assert (Hsz : ptr_addr (ow_self w0) <> 0) by (rewrite Hself; cbn; lia).
  iDestruct "Hlk" as "(%Hk & Hkl & [%Hk0r Hk0] & [%Hk4r Hk4] & Hko)". destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 with "Hla"). iIntros ([Hla0 Hla48]) "Hla".
  iApply (wp_live_fit1 with "Hkl"). iIntros ([Hlk0 Hlk48]) "Hkl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* start: the cleanup buffer, pushed. *)
  step. iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
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
  (* start, L24, L25, L18: single threaded, the owner null; take the lock. *)
  self Hsz. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. step. check "Hkl". load_null "Hkl" "Hko". step. step. step. step. step. branch.
  step. step. check "Hkl". store_int "Hkl" "Hk0". step. step. check "Hkl". store "Hkl" "Hko". step.
  (* L15: the head of the list. *)
  step. step. check "Hla". load "Hla" "Hlah" "Hhl". step.
  iApply ("HK" $! _ cb creg with "[%] Htcb Hcl Hc24 Hc16 Hla Hlah Hhl [Hkl Hk0 Hk4 Hko]").
  - split_and!; try lk_prove; lia.
  - iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.

End rules.
