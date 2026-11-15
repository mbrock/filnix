(** Printing to a byte-oriented stream does not require converting the
    format string to wide characters. This proof follows that route through
    __vfxprintf, including its temporary allocations and call to
    __vfprintf_internal. The called formatter may fail or change errno.
    Its contract must return the fields needed to release the stream lock. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps FxprintfNormalCode VfxprintfReturn Fix.
Module NarrowVL := VariadicLogicOn R LG0.
Import NarrowVL.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Section narrow.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The cursor belongs to the caller; V identifies the same ap before and
    after formatting. Q can record a changed orientation and errno. Format
    and argument bytes are supplied in R, not inferred from pointer values. *)
Definition vfxprintf_formatter fb freg fl lb lbreg fmt ap flags md dqf fmtreg
    (V : ptr -> iProp Σ) (R : iProp Σ) (Q : Z -> iProp Σ) : Prop :=
  exists fn fr, find_fn ge (TAtom "__vfprintf_internal") = Some (Defined fn) /\
    call_frame fn [WPtr (mkPtr fb (Obj fb));WPtr fmt;WPtr ap;WInt (flags mod 2 ^ 32)] = Some fr /\
    (⊢ live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
      lock_state lb lbreg 1 0 (ow_self w0) -∗ int_cell fb 192 md -∗
      live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live fb freg ∗ int_cell fb 0 fl ∗
        pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 1 0 (ow_self w0) ∗
        live_capq dqf (ptr_cap fmt) fmtreg ∗ V ap ∗ Q r }}).

Lemma wp_vfxprintf_narrow e from fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    (V : ptr -> iProp Σ) (R E : iProp Σ) (Q : Z -> iProp Σ) Φ :
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr fmt) -> lookup (TAtom "v4") e = Some (WPtr ap) ->
  lookup (TAtom "v6") e = Some (WInt flags) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= ptr_addr fmt < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  vfxprintf_formatter fb freg fl lb lbreg fmt ap flags md dqf fmtreg V R Q ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r, live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
    lock_state lb lbreg 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame glibc_vfxprintf e [] None (Enter (TAtom "iw_1.start") (Some from))) : gexpr) {{ Φ }}.
Proof.
  intros Hpr Hchk Hfmt Hap Hflags Hfb Hal Hend Hreg Huser Hfmtr Hmd (fn & fr & Hfn & Hframe & Hcall).
  iIntros "#Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b [Hb [Hba Hbe]]) "Hobj".
  change (b mod 16 = 0) in Hba. change (b + 16 <= 2 ^ 48) in Hbe.
  assert (Hb8 : b mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "Hobj") as "(Hbl & Hx & Ha)"; [compute; discriminate |].
  iAssert (live b (mkRegion b (b + 16) Heap Live)) with "Hbl" as "Hbl".
  iDestruct (zero_cell_prefix b 0 8 with "Hx Ha") as "(Hbc & _ & _)".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b63 _) "_".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b69 _) "_".
  set (breg := mkRegion b (b + 16) Heap Live) in *. assert (Hbre : r_end breg = b + 16) by reflexivity.
  check "Hbl". store "Hbl" "Hbc".
  step. check "Hl". iDestruct "Hmd" as "[%Hmdr Hmd]". load_s32 "Hl" "Hmd". step.
  assert (Hsle : sign_extension (2 ^ 32) (2 ^ 31) (md mod 2 ^ 32) <=?
    sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32) = true) by (destruct Hmd as [-> | ->]; reflexivity).
  rewrite Hsle. branch. step. check "Hbl".
  iApply (wp_raw_load_pointer_dq with "Hbl Hbc Hfmt");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hfmtr |].
  iNext. iIntros "Hbl Hbc Hfmt".
  iApply wp_call_bind; [vx | exact Hfn | exact Hframe |]. iNext.
  iApply (wp_wand with "[Hl Hfl Hlp Hlk Hmd Hfmt HV HR]").
  { iApply (Hcall with "Hl Hfl Hlp Hlk [Hmd] Hfmt HV HR"). iSplit; [done | iExact "Hmd"]. }
  iIntros (v) "H". iDestruct "H" as (r ->) "(Hl & Hfl & Hlp & Hlk & Hfmt & HV & HQ)". resume. step.
  iApply (wp_vfxprintf_return _ (r mod 2 ^ 32) fb freg fl lb lbreg sb sreg
    (live_capq dqf (ptr_cap fmt) fmtreg ∗ V ap ∗ Q r ∗ E)%I
    with "Hs Hl Hfl Hlp Hlk [$Hfmt $HV $HQ $HE] [HK]"); try assumption; try lk_prove;
    try (apply Z.mod_pos_bound; lia).
  iNext. iIntros "Hl Hfl Hlp Hlk (Hfmt & HV & HQ & HE)".
  iApply ("HK" with "Hl Hfl Hlp Hlk Hfmt HV HQ HE").
Qed.
End narrow.
