From Glibc Require Import Unit_intl_dcgettext_os Unit_intl_dcigettext_os Unit_locale_localename_os Unit_misc_tsearch_os Unit_nptl_pthread_rwlock_rdlock_os.
From Glibc Require Import Unit_nptl_pthread_rwlock_unlock_os Unit_string_memcpy_os Unit_string_mempcpy_os Unit_string_stpcpy_os.
From Glibc Require Import GlibcProgram.
(** When getopt reports an error, gettext translates the message, and
    the C-locale route allocates two strings with malloc and frees them
    before it returns. The earlier proofs of that route asked the genv to
    leave malloc and free to the model, as [heap_fns] says. A program that
    links glibc's own malloc and free, as GNU Hello does, can never meet
    that premise. This module proves the translation with glibc's
    captured malloc and free instead, on top of the real stpcpy, tfind,
    locale query and locks.

    Malloc reads a cache that belongs to the thread, so the caller lends
    a share of it for each call and gets the share back. Glibc's malloc
    either stalls or returns new memory; it never returns null. The proof
    keeps the route's paths for a failed allocation, but this malloc never
    takes them. Glibc's free passes its memory to the runtime, which must
    therefore free heap objects.

    The route copies memory through the runtime's `c: zmemmove`. The OS
    registry already holds the contract for that call. This module cannot
    see whether the program defines the name itself, so the caller states
    that it does not. The caller also lends the locale, cache, binding, privilege
    and lock resources that DcgettextRwlock.v lists. These are conditions
    on the caller's state, not facts proved about startup. *)
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
From Glibc Require Import DcgettextC DcgettextStpcpy DcgettextTfind DcgettextLocale DcgettextRwlock.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** ## What the linked heap functions need

    Malloc and free work only if the program is linked as glibc expects.
    Malloc finds its settings at mpb and the thread's cache pointer at
    tcb. Free needs the runtime to free heap objects and needs the program
    to leave the runtime's free and `c: zmemmove` to the runtime. *)
Definition dci_heap_glibc (mpb tcb : Z) : Prop :=
  frees_heap (ge_free ge) /\ find_fn ge zgc_free_name = None /\ lookup zgc_free_name (ge_globals ge) = None /\
  lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr mpb (Obj mpb)) /\
  lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tcb (Obj tcb)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None.

(** With those facts, the caller no longer promises anything about how
    memmove, free or malloc behave. The registry gives the memmove
    contract, glibc's free gives the free rule, and glibc's malloc gives
    the malloc rule over a share of the idle cache. *)
Lemma dci_rest_rwf_glibc `{!Defines ge "free" free_fn, !Defines ge "malloc" malloc_fn,
      !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn} dq mpb tcb dmb mpr tcr dr :
  dci_heap_glibc mpb tcb -> dci_rest_rwf (hi_malloc_state dq mpb tcb dmb mpr tcr dr).
Proof using Hreg.
  intros (Hfh & Hzf & Hzg & Hmp & Htc & Hmf & Hmd). split_and!.
  - apply Hreg. reflexivity.
  - exact Hmf.
  - exact Hmd.
  - exact (dci_free_rule_glibc Hfh Hzf Hzg).
  - exact (getopt_malloc_rule_glibc dq mpb tcb dmb mpr tcr dr Hmp Htc).
Qed.

(** ## The translation with glibc's heap functions *)

(** A getopt diagnostic calls dcgettext. This lemma proves that call in
    a program that links glibc's own malloc and free. The call also runs
    the real stpcpy, tfind, locale query and locks. *)
Lemma wp_dcgettext_c_real f e ls l d args rest j mid dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd bs dq mpb tcb dmb mpr tcr dr dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
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
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hh. pose proof (dci_rest_rwf_glibc dq mpb tcb dmb mpr tcr dr Hh) as Hr.
  eapply (wp_dcgettext_c_rwf eb Herr Hreg Hext); first [exact Hr | exact _].
Qed.

(** This lemma builds the short-option translation premise in the same
    way. *)
Lemma dcg_diag_translate_real dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
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
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs)
    dom.
Proof using Type*.
  intros Hh. pose proof (dci_rest_rwf_glibc dq mpb tcb dmb mpr tcr dr Hh) as Hr.
  eapply (dcg_diag_translate_rwf eb Herr Hreg Hext); first [exact Hr | exact _].
Qed.

(** This lemma builds the long-option translation premise in the same
    way. *)
Lemma dcg_ldiag_translate_real dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
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
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hi_malloc_state dq mpb tcb dmb mpr tcr dr) bs)
    dom.
Proof using Type*.
  intros Hh. pose proof (dci_rest_rwf_glibc dq mpb tcb dmb mpr tcr dr Hh) as Hr.
  eapply (dcg_ldiag_translate_rwf eb Herr Hreg Hext); first [exact Hr | exact _].
Qed.
End rules.

(** ## Controls

    Glibc's free passes its one argument to `c: zgc_free` and returns, so
    the rule for free rests on the runtime's free alone. *)
Example free_fn_forwards :
  fn_params free_fn = [(P, TAtom "v0")] /\
  map b_insts (fn_blocks free_fn) = [[Call CVoid (Global zgc_free_name) [Arg P (Tmp (TAtom "v0"))]]].
Proof. split; vm_compute; reflexivity. Qed.
