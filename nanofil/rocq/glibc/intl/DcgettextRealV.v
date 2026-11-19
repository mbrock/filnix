From Glibc Require Import Unit_intl_dcgettext_os Unit_intl_dcigettext_os Unit_locale_localename_os Unit_misc_tsearch_os Unit_nptl_pthread_rwlock_rdlock_os.
From Glibc Require Import Unit_nptl_pthread_rwlock_unlock_os Unit_string_memcpy_os Unit_string_mempcpy_os Unit_string_stpcpy_os.
From Glibc Require Import GlibcProgram.
(** GNU Hello starts with the privilege flag `__libc_enable_secure` set
    to 1, but the translation proofs of DcgettextC.v and DcgettextReal.v
    lend a flag that reads 0. This module proves the same translation for
    any 32-bit value of the flag, so that a getopt diagnostic can be
    translated in a program whose flag is set.

    A set flag makes gettext look for a slash in the locale name, and it
    uses strchr to look. So the caller must then show that the program
    links strchr and strchrnul to the code that the proof runs. Nothing
    else changes. The caller gets back the message, the flag with the
    share and value it lent, and the other resources. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic WordString SysWrappers.
From Glibc Require Import AllocLogic HiAtexitAlloc GetoptMallocGlibc.
From Glibc Require Import LibioSetb TfindEmpty LocalenameLogic.
From Glibc Require Import RdlockLogic RwunlockLogic.
From Glibc Require Import GetoptLongPfxAlloc GetoptDiag GetoptLongDiag GetoptDiagFx.
From Glibc Require Import DcigettextFree DcigettextExit DcigettextPreRules DcigettextRoute.
From Glibc Require Import DcigettextSecure DcigettextRouteV.
From Glibc Require Import DcgettextC DcgettextStpcpy DcgettextTfind DcgettextLocale DcgettextRwlock DcgettextReal.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dcg_v_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** ## The resources of one translation

    These are the resources of DcgettextC.v, except that the flag may
    hold any value v. *)

Section resources.
Context (dom : ptr) (ds : list Z) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
  (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (dqi : dfrac) (ireg : region)
  (sec : Z) (dqs : dfrac) (secreg : region) (v : Z) (L1 L1'' L2 L2'' T T'' K C M : iProp Σ) (bs : list Z).

(** The caller lends these resources before the call. *)
Definition dcg_before_v : iProp Σ :=
  dci_reads_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v ∗
  L1 ∗ L2 ∗ T ∗ K ∗ C ∗ M ∗ errno_own eb bs.

(** The call returns q, which is the message id mid, with these resources. *)
Definition dcg_after_v (mid q : ptr) : iProp Σ :=
  ⌜q = mid⌝ ∗ dci_reads_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v ∗
  L1'' ∗ L2'' ∗ T'' ∗ K ∗ C ∗ M ∗ errno_own eb (le_bytes (dci_w bs) 4).
End resources.

(** With the value 0 both resources are the old ones, so a caller of
    the old statements loses nothing. *)
Lemma dcg_before_v_0 dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs :
  dcg_before_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg 0 L1 L2 T K C M bs =
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs.
Proof using Type. reflexivity. Qed.

Lemma dcg_after_v_0 dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs :
  dcg_after_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg 0 L1'' L2'' T'' K C M bs =
  dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs.
Proof using Type. reflexivity. Qed.

(** After the call the caller holds the flag with the value it lent, and
    the returned pointer is the message. *)
Lemma dcg_after_v_flag dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
    L1'' L2'' T'' K C M bs mid q :
  dcg_after_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v L1'' L2'' T'' K C M bs mid q ⊢
  ⌜q = mid⌝ ∗ liveq dqs sec secreg ∗ int_cellq dqs sec 0 v.
Proof using Type. iIntros "(-> & (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & Hc) & _)". iFrame. done. Qed.

(** The translation lends the string "C" at cv, so cv is a machine word. *)
Lemma dcg_before_v_cv dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v L1 L2 T K C M bs :
  dcg_before_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v L1 L2 T K C M bs ⊢
  ⌜0 <= ptr_addr cv < 2 ^ 64⌝ ∗
  dcg_before_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v L1 L2 T K C M bs.
Proof using Type.
  unfold dcg_before_v, dci_reads_v. iIntros "[(Hd & Hc & #Hv & Hr) Ho]". iDestruct (word_string_life with "Hv") as (reg) "[_ %Hcv]".
  iSplit; [done|]. iFrame "∗ #".
Qed.

(** ## The wrapper *)

(** The wrapper passes the call on to the route, so it accepts every
    value of the flag that the route accepts. *)
Lemma wp_dcgettext_c_v f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg v mid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext} :
  dci_callees_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  0 <= v < 2 ^ 32 -> (v = 0 \/ dci_strchr_links) ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v L1 L2 T K C M bs -∗
  ▷ (∀ q, dcg_after_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
        L1'' L2'' T'' K C M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hcal Hglo Hbnd Hv Hlinks Hargs Hm. iIntros "(Hr & HL1 & HL2 & HT & HK & HC & HM & Herr) HΦ".
  iApply wp_call_bind; [exact Hargs | apply defines | reflexivity |]. iNext.
  step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_dci_route_v eb Herr with "Hr HL1 HL2 HT HK HC HM Herr"); try first [eassumption | reflexivity].
  iNext. iIntros "Hr HL1 HL2 HT HK HC HM Herr".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HΦ" with "[$Hr $HL1 $HL2 $HT $HK $HC $HM $Herr]"). done.
Qed.

(** ## The translation with the real callees

    DcgettextReal.v discharges the callee rules one module at a time:
    stpcpy, tfind, the locale query, the locks and the heap functions.
    The rule below does the same discharges in one step and then runs
    the wrapper above. *)
Lemma wp_dcgettext_c_real_v f e ls l d args rest j mid dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg v tc dd bs dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy,
      !Defines ge "__GI___tfind" Unit_misc_tsearch_os.fn___GI___tfind, !Defines ge "__current_locale_name" Unit_locale_localename_os.fn___current_locale_name,
      !Defines ge "__GI___pthread_rwlock_rdlock" Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock,
      !Defines ge "__GI___pthread_rwlock_unlock" Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock,
      !Defines ge "free" free_fn, !Defines ge "malloc" malloc_fn,
      !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn} :
  dci_heap_glibc mpb tcb -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  0 <= v < 2 ^ 32 -> (v = 0 \/ dci_strchr_links) ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs -∗
  ▷ (∀ q, dcg_after_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hh H1 H2 Ht Hl Hrb Hro Hal Hend Hrg Hg Hbd Hv Hlinks Hargs Hmid. iIntros "Hb HK".
  iDestruct (dcg_before_v_cv with "Hb") as "[%Hcv Hb]".
  pose proof (dci_rest_l_rwf Hreg Hext lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2
    lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid _ (dci_rest_rwf_glibc Hreg dq mpb tcb dmb mpr tcr dr Hh) H1 H2 Ht) as Hr.
  pose proof (dci_rest_cur_f _ _ _ _ _ _ _ _ _ _ _ _ _ gb go greg dqg lp lb lreg dql dqn cv dqt treg Hr Hl Hcv) as Hc.
  pose proof (conj dci_stpcpy_rule_r_proved (dci_others_empty_f _ _ _ tc _ _ _ _ _ _ _ _ _ _ _ cv dqr rb ro rreg
    Hrb Hro Hal Hend Hrg Hc)) as Hcal.
  iApply (wp_dcgettext_c_v with "Hb HK"); first [exact Hcal | eassumption | exact _].
Qed.

(** This lemma builds the short-option translation premise in the same
    way. *)
Lemma dcg_diag_translate_real_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg v
    tc dd bs dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy,
      !Defines ge "__GI___tfind" Unit_misc_tsearch_os.fn___GI___tfind, !Defines ge "__current_locale_name" Unit_locale_localename_os.fn___current_locale_name,
      !Defines ge "__GI___pthread_rwlock_rdlock" Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock,
      !Defines ge "__GI___pthread_rwlock_unlock" Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock,
      !Defines ge "free" free_fn, !Defines ge "malloc" malloc_fn,
      !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn} :
  dci_heap_glibc mpb tcb -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  0 <= v < 2 ^ 32 -> (v = 0 \/ dci_strchr_links) ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs)
    (dcg_after_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs)
    dom.
Proof using Type*.
  intros Hh H1 H2 Ht Hl Hrb Hro Hal Hend Hrg Hg Hbd Hv Hlinks Hm f e ls l d args rest j mid Φ Hmsg Hargs.
  iIntros "Hb HK". iApply (wp_dcgettext_c_real_v with "Hb HK"); try eassumption. exact (Hm mid Hmsg).
Qed.

(** This lemma builds the long-option translation premise in the same
    way. *)
Lemma dcg_ldiag_translate_real_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg v
    tc dd bs dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy,
      !Defines ge "__GI___tfind" Unit_misc_tsearch_os.fn___GI___tfind, !Defines ge "__current_locale_name" Unit_locale_localename_os.fn___current_locale_name,
      !Defines ge "__GI___pthread_rwlock_rdlock" Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock,
      !Defines ge "__GI___pthread_rwlock_unlock" Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock,
      !Defines ge "free" free_fn, !Defines ge "malloc" malloc_fn,
      !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn} :
  dci_heap_glibc mpb tcb -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  0 <= v < 2 ^ 32 -> (v = 0 \/ dci_strchr_links) ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs)
    (dcg_after_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs)
    dom.
Proof using Type*.
  intros Hh H1 H2 Ht Hl Hrb Hro Hal Hend Hrg Hg Hbd Hv Hlinks Hm f e ls l d args rest j mid Φ Hmsg Hargs.
  iIntros "Hb HK". iApply (wp_dcgettext_c_real_v with "Hb HK"); try eassumption. exact (Hm mid Hmsg).
Qed.
End rules.
