(** When getopt reports an error in Hello, gettext translates the
    message. DcgettextReal.v proves that translation in any program that
    links glibc's own malloc, free and the gettext callees. This module
    connects that proof to Hello's link record [hello_link].

    Hello's own record already says where malloc, free and strlen live.
    It is silent about the other functions that gettext calls and about
    memmove. So a second, smaller record lists only those missing facts.

    We checked those facts against a real link of the units that
    gettext needs. In that link every name that gettext calls finds the
    code that the proofs ran, even the stpcpy name that a smaller
    fixture loses.

    This check does not cover all of Hello. Hello links many more units
    than gettext needs, and its full link might resolve a name another
    way, so a caller must still show that it does not.
    HelloGettextImage.v checks the record against a selection from
    Hello's own link, relying on checks that the producer makes. The caller also
    lends the memory that gettext reads, three locks and errno, and
    nothing here says how startup prepares them. *)
From Glibc Require Import HelloObjects.
From Glibc Require Import GetoptMessages Unit_intl_dcgettext_os Unit_intl_dcigettext_os
  Unit_locale_localename_os Unit_misc_tsearch_os Unit_nptl_pthread_rwlock_rdlock_os
  Unit_nptl_pthread_rwlock_unlock_os Unit_string_memcpy_os Unit_string_mempcpy_os Unit_string_stpcpy_os
  GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic MemFwdCode
  WordString SysWrappers AllocLogic AllocCall HelloGlibcLibsT StpcpyCode TfindCode
  TfindEmpty LocalenameCode LocalenameLogic RdlockCode RwunlockCode DcgettextCode DcigettextCode
  DcigettextRoute DcgettextC DcgettextLocale DcgettextRwlock DcgettextReal GettextLinkCode Fix.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.

(** ## The missing link facts

    Gettext finds each function it calls by name. Each field below says
    which body one such name runs, spelled as gettext spells it. The last
    field says that the program leaves memmove to the runtime. *)
Record hello_gettext_link (ge : genv) : Prop := mkHelloGettextLink {
  hg_mempcpy : find_fn ge (TAtom "__GI_mempcpy") = Some (Defined Unit_string_mempcpy_os.fn___GI___mempcpy);
  hg_memcpy : find_fn ge (TAtom "__GI_memcpy") = Some (Defined Unit_string_memcpy_os.fn___GI_memcpy);
  hg_dcgettext : find_fn ge (TAtom "__GI___dcgettext") = Some (Defined Unit_intl_dcgettext_os.fn___GI___dcgettext);
  hg_dcigettext : find_fn ge (TAtom "__dcigettext") = Some (Defined Unit_intl_dcigettext_os.fn___dcigettext);
  hg_stpcpy : find_fn ge (TAtom "__GI_stpcpy") = Some (Defined Unit_string_stpcpy_os.fn___GI___stpcpy);
  hg_tfind : find_fn ge (TAtom "__GI___tfind") = Some (Defined Unit_misc_tsearch_os.fn___GI___tfind);
  hg_locale : find_fn ge (TAtom "__current_locale_name") = Some (Defined Unit_locale_localename_os.fn___current_locale_name);
  hg_rdlock : find_fn ge (TAtom "__GI___pthread_rwlock_rdlock") = Some (Defined Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock);
  hg_unlock : find_fn ge (TAtom "__GI___pthread_rwlock_unlock") = Some (Defined Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock);
  hg_zmemmove : find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None
}.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).
Context (Hreg : holds_os registry).

(** Hello keeps a read-only share of malloc's idle cache. The
    translation lends that share to each malloc call and gets it back. *)
Definition hello_gettext_cache (ob : hello_objs) : iProp Σ :=
  malloc_call_state DfracDiscarded (ho_mp ob) (ho_tc ob) (ho_dm ob) (ho_mpreg ob) (ho_tcreg ob) (ho_dmreg ob).

(** Most heap facts already follow from Hello's own record. The new
    record adds only the two facts about memmove. *)
Lemma hello_heap_glibc ob : hello_link ge ob -> hello_gettext_link ge -> dci_heap_glibc (ho_mp ob) (ho_tc ob).
Proof using Type.
  intros Hk Hg. destruct (hk_frees _ _ Hk) as (Hfh & Hzf & Hzg).
  split_and!; first [exact Hfh | exact Hzf | exact Hzg | exact (hk_mp _ _ Hk) | exact (hk_tc _ _ Hk)
                    | exact (proj1 (hg_zmemmove _ Hg)) | exact (proj2 (hg_zmemmove _ Hg))].
Qed.

(** ## The translation in Hello's link *)

(** In Hello's link, a getopt diagnostic's call to dcgettext follows the
    C-locale route. The caller supplies the two link records and lends
    the locale, cache, binding, privilege, lock and errno resources. *)
Lemma wp_dcgettext_c_hello f e ls l d args rest j mid dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd bs ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid Φ :
  hello_link ge ob -> hello_gettext_link ge -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hk Hg. pose proof (hello_heap_glibc ob Hk Hg) as Hh.
  pose proof (hk_gi_strlen _ _ Hk). pose proof (hk_free _ _ Hk).
  pose proof (hk_malloc _ _ Hk). pose proof (hk_malloc2 _ _ Hk).
  destruct Hg as [? ? ? ? ? ? ? ? ? _].
  eapply (wp_dcgettext_c_real eb Herr Hreg (hk_sys _ _ Hk)); first [exact Hh | exact _].
Qed.

(** This lemma builds the short-option translation premise in the same
    way. *)
Lemma dcg_diag_translate_hello dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd bs ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid :
  hello_link ge ob -> hello_gettext_link ge -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    dom.
Proof using Type*.
  intros Hk Hg. pose proof (hello_heap_glibc ob Hk Hg) as Hh.
  pose proof (hk_gi_strlen _ _ Hk). pose proof (hk_free _ _ Hk).
  pose proof (hk_malloc _ _ Hk). pose proof (hk_malloc2 _ _ Hk).
  destruct Hg as [? ? ? ? ? ? ? ? ? _].
  eapply (dcg_diag_translate_real eb Herr Hreg (hk_sys _ _ Hk)); first [exact Hh | exact _].
Qed.

(** This lemma builds the long-option translation premise in the same
    way. *)
Lemma dcg_ldiag_translate_hello dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd bs ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid :
  hello_link ge ob -> hello_gettext_link ge -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    dom.
Proof using Type*.
  intros Hk Hg. pose proof (hello_heap_glibc ob Hk Hg) as Hh.
  pose proof (hk_gi_strlen _ _ Hk). pose proof (hk_free _ _ Hk).
  pose proof (hk_malloc _ _ Hk). pose proof (hk_malloc2 _ _ Hk).
  destruct Hg as [? ? ? ? ? ? ? ? ? _].
  eapply (dcg_ldiag_translate_real eb Herr Hreg (hk_sys _ _ Hk)); first [exact Hh | exact _].
Qed.
End rules.

(** ## Controls

    These checks read the captured objects. The direct names are defined
    under the spelling that the route calls, and the two lock names are
    aliases of the captured lock functions. *)
Example gettext_link_spellings :
  find_direct (TAtom "__GI_memcpy") memfwd_module = Some (Defined Unit_string_memcpy_os.fn___GI_memcpy) /\
  find_direct (TAtom "__GI___dcgettext") dcgettext_module = Some (Defined Unit_intl_dcgettext_os.fn___GI___dcgettext) /\
  find_direct (TAtom "__dcigettext") dcigettext_module = Some (Defined Unit_intl_dcigettext_os.fn___dcigettext) /\
  find_direct (TAtom "__GI___tfind") tfind_module = Some (Defined Unit_misc_tsearch_os.fn___GI___tfind) /\
  find_direct (TAtom "__current_locale_name") localename_module = Some (Defined Unit_locale_localename_os.fn___current_locale_name) /\
  find_alias (TAtom "__GI___pthread_rwlock_rdlock") rdlock_module = Some (TAtom "___pthread_rwlock_rdlock") /\
  find_direct (TAtom "___pthread_rwlock_rdlock") rdlock_module = Some (Defined Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock) /\
  find_alias (TAtom "__GI___pthread_rwlock_unlock") rwunlock_module = Some (TAtom "___pthread_rwlock_unlock") /\
  find_direct (TAtom "___pthread_rwlock_unlock") rwunlock_module = Some (Defined Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** This function lists the names that a function calls directly, in
    order. *)
Definition gettext_calls (f : func) : list name :=
  flat_map (fun b => flat_map (fun i => match i with Call _ (Global g) _ => [g] | _ => [] end) (b_insts b))
    (fn_blocks f).

(** The lookup calls stpcpy and mempcpy through `__GI_stpcpy` and
    `__GI_mempcpy`. The small fixtures do not keep those spellings,
    because each one is linked from the plain name alone and the linker
    drops aliases that nothing uses. *)
Example gettext_link_gaps :
  In (TAtom "__GI_stpcpy") (gettext_calls Unit_intl_dcigettext_os.fn___dcigettext) /\
  In (TAtom "__GI_mempcpy") (gettext_calls Unit_intl_dcigettext_os.fn___dcigettext) /\
  find_direct (TAtom "__GI___stpcpy") stpcpy_module = Some (Defined Unit_string_stpcpy_os.fn___GI___stpcpy) /\
  find_alias (TAtom "stpcpy") stpcpy_module = Some (TAtom "__GI___stpcpy") /\
  find_direct (TAtom "__GI_stpcpy") stpcpy_module = None /\ find_alias (TAtom "__GI_stpcpy") stpcpy_module = None /\
  find_direct (TAtom "__GI_mempcpy") memfwd_module = None /\ find_alias (TAtom "__GI_mempcpy") memfwd_module = None.
Proof. repeat split; vm_compute; first [reflexivity | tauto]. Qed.

(** The new record names none of the functions that [hello_link]
    already binds, so it adds facts rather than repeating them. *)
Example gettext_link_fresh :
  Forall (fun n => ~ In n ["mbszero"; "memset"; "set_program_name"; "strrchr"; "__GI_strlen"; "__GI___memrchr";
                           "memcmp"; "memeq"; "strncmp"; "strlen"; "__errno_location"; "xmalloc"; "malloc";
                           "glibc_malloc#__libc_malloc2"; "free"; "atexit"; "exit"; "__run_exit_handlers";
                           "__GI___call_tls_dtors"; "__GI___libc_cleanup_push_defer";
                           "__GI___libc_cleanup_pop_restore"; "__GI__IO_flush_all"; "_IO_cleanup"; "close_stdout"]%string)
    ["__GI_mempcpy"; "__GI_memcpy"; "__GI___dcgettext"; "__dcigettext"; "__GI_stpcpy"; "__GI___tfind";
     "__current_locale_name"; "__GI___pthread_rwlock_rdlock"; "__GI___pthread_rwlock_unlock"; "zmemmove"]%string.
Proof. repeat constructor; cbn; intuition discriminate. Qed.

(** ## The linked gettext image

    The linker starts from dcgettext and keeps what it reaches. Glibc
    declares `__GI_stpcpy` as a weak alias of `__GI___stpcpy`, and the
    image keeps it because the lookup calls it. *)
Example gettext_image_aliases :
  find_alias (TAtom "__GI_stpcpy") gettextlink_module = Some (TAtom "__GI___stpcpy") /\
  find_alias (TAtom "__GI_mempcpy") gettextlink_module = Some (TAtom "__GI___mempcpy").
Proof. split; vm_compute; reflexivity. Qed.

(** We want to know whether a real link gives gettext the functions
    that its proofs assumed. It does: in this link, each name that
    gettext calls runs the same code that the proofs ran, and memmove
    stays undefined. Only the list of globals is left for the caller,
    who must say that none of them is named memmove. *)
Lemma hello_gettext_link_image gl fr :
  lookup (TAtom "zmemmove") gl = None -> hello_gettext_link (mkGenv gettextlink_module gl fr).
Proof. intros H. constructor; try (vm_compute; reflexivity). split; [vm_compute; reflexivity | exact H]. Qed.
