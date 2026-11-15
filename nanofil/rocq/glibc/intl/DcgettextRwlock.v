From Glibc Require Import GlibcProgram.
(** When getopt reports an error, gettext translates the message, and its
    lookup takes read locks on three rwlocks: the cache's tree lock, the
    binding state lock and the setlocale lock. The earlier proofs of that
    translation assumed how the lock calls behave. This module runs
    glibc's real `c: pthread_rwlock_rdlock` and `c: pthread_rwlock_unlock`
    instead, on top of the real stpcpy, tfind and locale query.

    A lock call is easy to state only when no other thread is using the
    lock, and the lock proofs cover only that case. So the caller must
    own each of the three locks and show that it is free: no writer, no
    waiting thread, and room for one more reader. It must also lend a
    share of the calling thread's id to each lock call. Each lock then
    gains a reader and loses it again, so the translation gives every
    lock back in the state it started in. A lock that some other thread
    holds is outside this contract.

    Some functions that gettext calls are still unproved, so the caller
    must say how they behave. It describes memmove and malloc, and it
    states that the program runs in the C locale with an empty binding
    list, an empty cache and the privilege flag clear. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic MemFwdCode WordString SysWrappers.
From Glibc Require Import LibioSetb StpcpyCode TfindCode TfindEmpty LocalenameCode LocalenameLogic.
From Glibc Require Import RdlockCode RwunlockCode RdlockLogic RwunlockLogic.
From Glibc Require Import GetoptLongPfxAlloc GetoptDiag GetoptLongDiag GetoptDiagFx.
From Glibc Require Import DcgettextCode DcigettextCode DcigettextExit DcigettextPreRules DcigettextRoute DcgettextC.
From Glibc Require Import DcgettextStpcpy DcgettextTfind DcgettextLocale.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dcg_rw_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** ## The read locks *)

(** A lock that gettext reads holds this resource: the lock's fields and
    a share of the calling thread's id. *)
Definition rw_held (lb : Z) (lreg : region) (r cw sh fl : Z) (dqt : dfrac) (tb : Z) (treg : region) (dqi : dfrac)
    (tid : Z) : iProp Σ :=
  rw_lock lb lreg r cw sh fl ∗ rw_self dqt tb treg dqi tid.

(** The lock is free: its count has room for one more reader, no flag
    is set, and the calling thread does not hold the write lock. *)
Definition rw_ready (lk : ptr) (lb : Z) (lreg : region) (tb : Z) (treg : region) (r cw tid : Z) : Prop :=
  rw_place lk lb lreg tb treg /\ 0 <= r /\ r mod 8 = 0 /\ r + 8 < 2 ^ 31 /\ cw <> tid.

(** The real read lock meets the old rule and adds one reader. *)
Lemma dci_rdlock_rule_rw `{!Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock}
    lk lb lreg tb treg r cw sh fl dqt dqi tid :
  rw_ready lk lb lreg tb treg r cw tid ->
  dci_rdlock_rule lk (rw_held lb lreg r cw sh fl dqt tb treg dqi tid) (rw_held lb lreg (r + 8) cw sh fl dqt tb treg dqi tid).
Proof.
  intros (Hp & Hr0 & Hr & Hr8 & Hcw) f e ls l d args rest j Φ Hargs. iIntros "U HK".
  iApply (wp_call_glibc_rdlock Hreg Hext with "U [HK]"); [exact Hargs | exact Hp | exact Hr | exact Hr8 | exact Hcw |].
  iNext. iIntros "U". iApply ("HK" $! 0 with "U").
Qed.

(** When the lookup releases the lock, glibc's unlock satisfies the old
    rule and the count drops back by 8. *)
Lemma dci_unlock_rule_rw `{!Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock}
    lk lb lreg tb treg r cw sh fl dqt dqi tid :
  rw_ready lk lb lreg tb treg r cw tid ->
  dci_unlock_rule lk (rw_held lb lreg (r + 8) cw sh fl dqt tb treg dqi tid) (rw_held lb lreg r cw sh fl dqt tb treg dqi tid).
Proof.
  intros (Hp & Hr0 & Hr & Hr8 & Hcw) f e ls l d args rest j Φ Hargs. iIntros "U HK".
  iApply (wp_call_glibc_rwunlock Hreg Hext with "U [HK]");
    [exact Hargs | exact Hp | Z.div_mod_to_equations; lia | lia | exact Hcw |].
  iNext. iIntros "U". rewrite Z.add_simpl_r. iApply ("HK" $! 0 with "U").
Qed.

(** These are the rules that the translation still needs once the real
    locks run: memmove, the heap functions and malloc. *)
Definition dci_rest_rw (M : iProp Σ) : Prop :=
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None /\
  heap_fns ge /\ getopt_malloc_rule w0 registry ge M.

(** The translation should not need separate promises about its locks.
    When the caller owns three free locks and describes the functions
    above, nothing else is missing, and each lock ends where it began. *)
Lemma dci_rest_l_rw `{!Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock,
      !Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock}
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid M :
  dci_rest_rw M -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  dci_rest_l lk1 lk2 lkt (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a1 ar1 (r1 + 8) cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid)
    (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid) (rw_held a2 ar2 (r2 + 8) cw2 sh2 fl2 q2 tb tbreg i2 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
    (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid) (rw_held a3 ar3 (r3 + 8) cw3 sh3 fl3 q3 tb tbreg i3 tid) (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid) M.
Proof.
  intros (H1 & H2 & H3 & H4 & H5) R1 R2 Rt. unfold dci_rest_l. split_and!; try assumption;
    first [apply dci_rdlock_rule_rw | apply dci_unlock_rule_rw]; assumption.
Qed.

(** ## The translation without lock premises *)

(** A getopt diagnostic calls dcgettext, and this lemma proves that call
    with the real stpcpy, tfind, locale query and locks. *)
Lemma wp_dcgettext_c_rw f e ls l d args rest j mid dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd M bs dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name,
      !Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock,
      !Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock} :
  dci_rest_rw M -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hh H1 H2 Ht. pose proof (dci_rest_l_rw lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2
    lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid M Hh H1 H2 Ht) as Hr.
  intros Hl Hrb Hro Hal Hend Hrg Hg Hbd Hargs Hmid. iIntros "Hb HK".
  iApply (wp_dcgettext_c_loc eb Herr with "Hb HK"); first [exact Hr | eassumption | exact _].
Qed.

(** This lemma builds the short-option translation premise in the same
    way. *)
Lemma dcg_diag_translate_rw dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd M bs dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name,
      !Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock,
      !Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock} :
  dci_rest_rw M -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    dom.
Proof.
  intros Hh H1 H2 Ht. pose proof (dci_rest_l_rw lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2
    lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid M Hh H1 H2 Ht) as Hr.
  eapply (dcg_diag_translate_loc eb Herr); first [exact Hr | eassumption | exact _].
Qed.

(** This lemma builds the long-option translation premise in the same
    way. *)
Lemma dcg_ldiag_translate_rw dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd M bs dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name,
      !Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock,
      !Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock} :
  dci_rest_rw M -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    dom.
Proof.
  intros Hh H1 H2 Ht. pose proof (dci_rest_l_rw lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2
    lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid M Hh H1 H2 Ht) as Hr.
  eapply (dcg_ldiag_translate_loc eb Herr); first [exact Hr | eassumption | exact _].
Qed.

(** ## Controls

    A lock taken from 16 readers holds 24 while the lookup reads it and
    16 again afterwards. The contract rejects a lock whose count has no
    room left and a lock in its writer phase. *)
Example rw_pair_16 `{!Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock,
      !Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock} lk lb lreg tb treg cw sh fl dqt dqi tid :
  rw_place lk lb lreg tb treg -> cw <> tid ->
  dci_rdlock_rule lk (rw_held lb lreg 16 cw sh fl dqt tb treg dqi tid) (rw_held lb lreg 24 cw sh fl dqt tb treg dqi tid) /\
  dci_unlock_rule lk (rw_held lb lreg 24 cw sh fl dqt tb treg dqi tid) (rw_held lb lreg 16 cw sh fl dqt tb treg dqi tid).
Proof.
  intros Hp Hcw. assert (Hr : rw_ready lk lb lreg tb treg 16 cw tid) by (split_and!; first [exact Hp | exact Hcw | reflexivity | lia]).
  split; [exact (dci_rdlock_rule_rw lk lb lreg tb treg 16 cw sh fl dqt dqi tid Hr)
         | exact (dci_unlock_rule_rw lk lb lreg tb treg 16 cw sh fl dqt dqi tid Hr)].
Qed.
Example rw_ready_rejects lk lb lreg tb treg cw tid :
  ~ rw_ready lk lb lreg tb treg (2 ^ 31 - 8) cw tid /\ ~ rw_ready lk lb lreg tb treg 1 cw tid /\
  ~ rw_ready lk lb lreg tb treg 16 tid tid.
Proof. unfold rw_ready. split_and!; intros (_ & _ & H1 & H2 & H3); first [lia | discriminate | exact (H3 eq_refl)]. Qed.
End rules.
