(** glibc's `c: error` prints through `c: __vfxprintf`, which locks
    the stream, calls the formatter `c: __vfprintf_internal`, and
    unlocks the stream again. The modules VfxprintfNarrow.v,
    VfxprintfAcquire.v, VfxprintfSelect.v and VfxprintfCall.v prove
    that function for a formatter that leaves the stream's flags word
    as it found it. The real formatter does not: it marks the stream
    as writing on its first output. This module repeats those proofs
    for a formatter that may change the flags word, so that a caller
    can use the formatter's proved contract. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsThread OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfNormalCode VfxprintfReturn VfxprintfSelect Fix.
Module FlVL := VariadicLogicOn R LG0.
Import FlVL.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section fl.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Printing can change the stream's flags word, for example to record
    that the stream is writing or that a write failed. It never sets
    the bit that says the caller locks the stream, and unlocking reads
    that bit again. The formatter's contract does not promise to keep
    the stream's region or its lock, so the rule lets both be new. The
    result resource Q receives the result and all three. *)
Definition vfxprintf_formatter_fl fb freg fl lb lbreg fmt ap flags md dqf fmtreg
    (V : ptr -> iProp Σ) (R : iProp Σ) (Q : Z -> Z -> region -> Z -> region -> iProp Σ) : Prop :=
  exists fn fr, find_fn ge (TAtom "__vfprintf_internal") = Some (Defined fn) /\
    call_frame fn [WPtr (mkPtr fb (Obj fb));WPtr fmt;WPtr ap;WInt (flags mod 2 ^ 32)] = Some fr /\
    (⊢ live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
      lock_state lb lbreg 1 0 (ow_self w0) -∗ int_cell fb 192 md -∗
      live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r fl' freg' lb' lbreg', ⌜v = Ret (WInt r) /\ Z.land fl' 32768 = 0 /\
          fb + 224 <= r_end freg' /\ r_end freg' <= 2 ^ 63⌝ ∗ live fb freg' ∗ int_cell fb 0 fl' ∗
        pcell fb 136 (mkPtr lb' (Obj lb')) ∗ lock_state lb' lbreg' 1 0 (ow_self w0) ∗
        live_capq dqf (ptr_cap fmt) fmtreg ∗ V ap ∗ Q r fl' freg' lb' lbreg' }}).

(** The narrow route calls the formatter between taking and releasing the lock. *)
Lemma wp_vfxprintf_narrow_fl e from fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    (V : ptr -> iProp Σ) (R E : iProp Σ) (Q : Z -> Z -> region -> Z -> region -> iProp Σ) Φ :
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr fmt) -> lookup (TAtom "v4") e = Some (WPtr ap) ->
  lookup (TAtom "v6") e = Some (WInt flags) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= ptr_addr fmt < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  vfxprintf_formatter_fl fb freg fl lb lbreg fmt ap flags md dqf fmtreg V R Q ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r fl' freg' lb' lbreg', ⌜Z.land fl' 32768 = 0 /\ fb + 224 <= r_end freg' /\ r_end freg' <= 2 ^ 63⌝ -∗
    live fb freg' -∗ int_cell fb 0 fl' -∗ pcell fb 136 (mkPtr lb' (Obj lb')) -∗
    lock_state lb' lbreg' 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r fl' freg' lb' lbreg' -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame glibc_vfxprintf e [] None (Enter (TAtom "iw_1.start") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
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
  iIntros (v) "H". iDestruct "H" as (r fl' freg' lb' lbreg' (-> & Hfl' & Hend' & Hreg')) "(Hl & Hfl & Hlp & Hlk & Hfmt & HV & HQ)". resume. step.
  iApply (wp_vfxprintf_return _ (r mod 2 ^ 32) fb freg' fl' lb' lbreg' sb sreg
    (live_capq dqf (ptr_cap fmt) fmtreg ∗ V ap ∗ Q r fl' freg' lb' lbreg' ∗ E)%I
    with "Hs Hl Hfl Hlp Hlk [$Hfmt $HV $HQ $HE] [HK]"); try assumption; try lk_prove;
    try (apply Z.mod_pos_bound; lia).
  iNext. iIntros "Hl Hfl Hlp Hlk (Hfmt & HV & HQ & HE)".
  iApply ("HK" $! r fl' freg' lb' lbreg' with "[//] Hl Hfl Hlp Hlk Hfmt HV HQ HE").
Qed.

Section entry.
Context (Hregistry : holds_os registry) (Hext : sys_external ge).

(** Taking the free lock leads to the narrow route. *)
Lemma wp_vfxprintf_acquire_fl e fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    (V : ptr -> iProp Σ) (R E : iProp Σ) (Q : Z -> Z -> region -> Z -> region -> iProp Σ) Φ :
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v13") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr fmt) -> lookup (TAtom "v4") e = Some (WPtr ap) ->
  lookup (TAtom "v6") e = Some (WInt flags) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= ptr_addr fmt < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  vfxprintf_formatter_fl fb freg fl lb lbreg fmt ap flags md dqf fmtreg V R Q ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r fl' freg' lb' lbreg', ⌜Z.land fl' 32768 = 0 /\ fb + 224 <= r_end freg' /\ r_end freg' <= 2 ^ 63⌝ -∗
    live fb freg' -∗ int_cell fb 0 fl' -∗ pcell fb 136 (mkPtr lb' (Obj lb')) -∗
    lock_state lb' lbreg' 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r fl' freg' lb' lbreg' -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame glibc_vfxprintf e [] None (Enter (TAtom "L24") (Some (TAtom "L10")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hpr Hchk Hz Hfmt Hap Hflags Hfb Hal Hend Hreg Huser Hfmtr Hmd Hself Hselfr Hcall.
  iIntros "#Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlk" as "(%Hk & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)".
  destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hl0 Hl48]) "Hbl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  step. iApply OsThread.wp_zthread_self_cookie;
    try (apply (reg_of registry Hregistry); reflexivity);
    try (apply (ext_fn ge Hext); cbn; tauto);
    try (apply (ext_data ge Hext); cbn; tauto); [exact Hself |]. iNext.
  step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_null "Hbl" "Hbo".
  step. step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0".
  load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo". step.
  iAssert (lock_state lb lbreg 1 0 (ow_self w0)) with "[Hbl Hb0 Hb4 Hbo]" as "Hlk".
  { iSplit; [iPureIntro; lia |]. iFrame "Hbl".
    iSplitL "Hb0"; [iSplit; [done | iExact "Hb0"] |].
    iSplitL "Hb4"; [iSplit; [done | iExact "Hb4"] |]. iExact "Hbo". }
  iApply (wp_vfxprintf_narrow_fl _ (TAtom "L29") fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    V R E Q with "Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK"); try assumption; lk_prove.
Qed.
End entry.

Section select.
Context (Hregistry : holds_os registry) (Hext : sys_external ge).
Context (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (fmt ap : ptr) (flags md : Z)
  (dqf : dfrac) (fmtreg : region) (sb : Z) (sreg : region)
  (V : ptr -> iProp Σ) (R E : iProp Σ) (Q : Z -> Z -> region -> Z -> region -> iProp Σ) (Φ : outcome -> iProp Σ).
Context (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg)
  (Hreg : r_end freg <= 2 ^ 63) (Huser : Z.land fl 32768 = 0)
  (Hfmtr : 0 <= ptr_addr fmt < 2 ^ 64) (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
  (Hself : ptr_addr (ow_self w0) <> 0) (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64)
  (Hcall : vfxprintf_formatter_fl fb freg fl lb lbreg fmt ap flags md dqf fmtreg V R Q).

(** The flags check before locking leads to taking the lock. *)
Lemma wp_vfxprintf_selected_fl e from :
  (from = TAtom "L8" /\ lookup (TAtom "v16") e = Some (WPtr (mkPtr fb (Obj fb)))) \/
  (from = TAtom "start" /\ lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb)))) ->
  lookup (TAtom "v13") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr fmt) -> lookup (TAtom "v4") e = Some (WPtr ap) ->
  lookup (TAtom "v6") e = Some (WInt flags) ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r fl' freg' lb' lbreg', ⌜Z.land fl' 32768 = 0 /\ fb + 224 <= r_end freg' /\ r_end freg' <= 2 ^ 63⌝ -∗
    live fb freg' -∗ int_cell fb 0 fl' -∗ pcell fb 136 (mkPtr lb' (Obj lb')) -∗
    lock_state lb' lbreg' 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r fl' freg' lb' lbreg' -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame glibc_vfxprintf e [] None (Enter (TAtom "L10") (Some from))) : gexpr) {{ Φ }}.
Proof using Hal Hcall Hend Hext Hfb Hfmtr Hmd Hreg Hregistry Hself Hselfr Huser.
  intros Hselect Hz Hfmt Hap Hflags. iIntros "#Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iDestruct "Hfl" as "[%Hflr Hfl]".
  destruct Hselect as [[-> Hv] | [-> Hv]]; step; check "Hl"; load_s32 "Hl" "Hfl"; step; step; branch_as false;
    iApply (wp_vfxprintf_acquire_fl Hregistry Hext _ fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
      V R E Q with "Hs Hl [Hfl] Hlp Hlk Hmd Hfmt HV HR HE HK");
    try assumption; try lk_prove; (iSplit; [done | iExact "Hfl"]).
Qed.

End select.

Section call.
Context (Hregistry : holds_os registry) (Hext : sys_external ge).
Context (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (fmt ap : ptr) (flags md : Z)
  (dqf : dfrac) (fmtreg : region) (sb : Z) (sreg : region)
  (V : ptr -> iProp Σ) (R E : iProp Σ) (Q : Z -> Z -> region -> Z -> region -> iProp Σ) (Φ : outcome -> iProp Σ).
Context (Hfb : 0 < fb) (Hal : fb mod 8 = 0) (Hend : fb + 224 <= r_end freg)
  (Hreg : r_end freg <= 2 ^ 63) (Huser : Z.land fl 32768 = 0)
  (Hfmtr : 0 <= ptr_addr fmt < 2 ^ 64) (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
  (Hself : ptr_addr (ow_self w0) <> 0) (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64)
  (Hcall : vfxprintf_formatter_fl fb freg fl lb lbreg fmt ap flags md dqf fmtreg V R Q).

(** A null stream means stderr, which the function loads from its global. *)
Lemma wp_vfxprintf_null_fl gb greg :
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  single_ro ge sb sreg -∗ live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗
  live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r fl' freg' lb' lbreg', ⌜Z.land fl' 32768 = 0 /\ fb + 224 <= r_end freg' /\ r_end freg' <= 2 ^ 63⌝ -∗
    live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗
    live fb freg' -∗ int_cell fb 0 fl' -∗ pcell fb 136 (mkPtr lb' (Obj lb')) -∗
    lock_state lb' lbreg' 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r fl' freg' lb' lbreg' -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (vfxprintf_frame null fmt ap flags) : gexpr) {{ Φ }}.
Proof using Hal Hcall Hend Hext Hfb Hfmtr Hmd Hreg Hregistry Hself Hselfr Huser.
  intros Hg Hgb Hga Hge Hgr. iIntros "#Hs Hgl Hgp Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iApply (wp_live_fit1 with "Hgl"). iIntros ([Hg0 Hg48]) "Hgl".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  unfold vfxprintf_frame. step. step. step. step. branch.
  step. step. check "Hgl". load "Hgl" "Hgp" "Hl". step.
  iApply (wp_vfxprintf_selected_fl Hregistry Hext fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    V R (live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗ E)%I Q Φ
    with "Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR [$Hgl $Hgp $HE] [HK]"); try assumption; try lk_prove.
  { left. split; [reflexivity | lk_prove]. }
  iNext. iIntros (r fl' freg' lb' lbreg' Hf') "Hl Hfl Hlp Hlk Hfmt HV HQ (Hgl & Hgp & HE)".
  iApply ("HK" $! r fl' freg' lb' lbreg' Hf' with "Hgl Hgp Hl Hfl Hlp Hlk Hfmt HV HQ HE").
Qed.

Lemma wp_vfxprintf_explicit_fl :
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ int_cell fb 192 md -∗
  live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ R -∗ E -∗
  ▷ (∀ r fl' freg' lb' lbreg', ⌜Z.land fl' 32768 = 0 /\ fb + 224 <= r_end freg' /\ r_end freg' <= 2 ^ 63⌝ -∗
    live fb freg' -∗ int_cell fb 0 fl' -∗ pcell fb 136 (mkPtr lb' (Obj lb')) -∗
    lock_state lb' lbreg' 0 0 null -∗ live_capq dqf (ptr_cap fmt) fmtreg -∗ V ap -∗ Q r fl' freg' lb' lbreg' -∗ E -∗
    Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (vfxprintf_frame (mkPtr fb (Obj fb)) fmt ap flags) : gexpr) {{ Φ }}.
Proof using Hal Hcall Hend Hext Hfb Hfmtr Hmd Hreg Hregistry Hself Hselfr Huser.
  iIntros "#Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  unfold vfxprintf_frame. step. step. step. step. branch_as true.
  iApply (wp_vfxprintf_selected_fl Hregistry Hext fb freg fl lb lbreg fmt ap flags md dqf fmtreg sb sreg
    V R E Q Φ with "Hs Hl Hfl Hlp Hlk Hmd Hfmt HV HR HE HK"); try assumption; try lk_prove.
  right. split; [reflexivity | lk_prove].
Qed.
End call.
End fl.
