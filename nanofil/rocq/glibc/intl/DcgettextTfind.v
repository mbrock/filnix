From Glibc Require Import GlibcProgram.
(** The C-locale translation searches glibc's cache of translations
    before it builds a catalog file name, and the earlier proofs assumed
    that this search misses. In a program that has translated nothing,
    the cache's root cell holds null. This module proves the miss from
    glibc's captured tfind for such a cell and restates the translation
    without the assumption, after DcgettextStpcpy.v removed the one for
    stpcpy.

    Whether the cache is empty depends on what the program did before,
    so the caller must show it. It lends part of the cache's first cell,
    which holds null, and each translation gives that part back. Nothing
    here proves that the program starts with an empty cache.

    Some functions that the lookup calls are still unproved, so the
    caller must say how they behave. It describes the rwlock operations,
    the locale query and malloc, and it states that the program runs in
    the C locale with an empty binding list and the privilege flag clear. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic MemFwdCode WordString.
From Glibc Require Import LibioSetb StpcpyCode TfindCode TfindEmpty.
From Glibc Require Import GetoptLongPfxAlloc GetoptDiag GetoptLongDiag GetoptDiagFx.
From Glibc Require Import DcgettextCode DcigettextCode DcigettextFree DcigettextExit DcigettextPreRules DcigettextRoute.
From Glibc Require Import DcgettextC DcgettextStpcpy.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dcg_tf_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## The cache miss *)

(** The C route goes on to build a file name only after its cache search
    misses. An empty tree always misses, so the real search meets the
    miss rule for every key and comparison function. The resource that
    the search borrows and returns is the empty root cell. *)
Lemma dci_tfind_miss_rule_empty `{!Defines ge "__GI___tfind" glibc_tfind} key cmp dq rb ro rreg :
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_tfind_miss_rule key (mkPtr (rb + ro) (Obj rb)) cmp (tfind_root dq rb ro rreg).
Proof.
  intros Hrb Hro Hal Hend Hreg f e ls l d args rest j Φ Hargs. iIntros "[Hl Hp] HK".
  iApply (wp_call_glibc_tfind_empty with "Hl Hp");
    [exact Hargs | apply defines | left; reflexivity | reflexivity | exact Hrb | exact Hro | exact Hal | exact Hend |
     exact Hreg |].
  iNext. iIntros "Hl Hp". iApply ("HK" with "[$Hl $Hp]").
Qed.

(** Some functions that the route calls are still unproved, so the
    caller must say how they behave. This predicate lists them: memmove,
    malloc, the locale query and the four rwlock operations. *)
Definition dci_rest (lk1 lk2 lkt : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' C M : iProp Σ) (cv : ptr) : Prop :=
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None /\
  heap_fns ge /\ getopt_malloc_rule w0 registry ge M /\ dci_locale_rule 5 C cv /\
  dci_rdlock_rule lkt T T' /\ dci_unlock_rule lkt T' T'' /\
  dci_rdlock_rule lk1 L1 L1' /\ dci_rdlock_rule lk2 L2 L2' /\
  dci_unlock_rule lk1 L1' L1'' /\ dci_unlock_rule lk2 L2' L2''.

(** An empty cache answers the one question about tfind that the
    earlier translation asks. With it, the rules listed above are all
    that translation still needs. *)
Lemma dci_others_empty `{!Defines ge "__GI___tfind" glibc_tfind} lk1 lk2 lkt tc L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv
    dq rb ro rreg :
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_rest lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  dci_others lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc L1 L1' L1'' L2 L2' L2'' T T' T'' (tfind_root dq rb ro rreg) C M cv.
Proof.
  intros Hrb Hro Hal Hend Hreg (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  unfold dci_others. split_and!; try assumption.
  intros sb. apply dci_tfind_miss_rule_empty; assumption.
Qed.

(** A program that links glibc's free needs the rule for free in place
    of [heap_fns], so this predicate makes that one change. *)
Definition dci_rest_f (lk1 lk2 lkt : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' C M : iProp Σ) (cv : ptr) : Prop :=
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None /\
  dci_free_rule /\ getopt_malloc_rule w0 registry ge M /\ dci_locale_rule 5 C cv /\
  dci_rdlock_rule lkt T T' /\ dci_unlock_rule lkt T' T'' /\
  dci_rdlock_rule lk1 L1 L1' /\ dci_rdlock_rule lk2 L2 L2' /\
  dci_unlock_rule lk1 L1' L1'' /\ dci_unlock_rule lk2 L2' L2''.

(** The model's free meets that rule. *)
Lemma dci_rest_f_of lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv :
  dci_rest lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  dci_rest_f lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv.
Proof. intros (H1 & H2 & H3 & H4 & H). split_and!; try tauto. exact (dci_free_rule_heap H4). Qed.

(** The empty cache answers the tfind question here as well. *)
Lemma dci_others_empty_f `{!Defines ge "__GI___tfind" glibc_tfind} lk1 lk2 lkt tc L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv
    dq rb ro rreg :
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_rest_f lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  dci_others_f lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc L1 L1' L1'' L2 L2' L2'' T T' T'' (tfind_root dq rb ro rreg) C M cv.
Proof.
  intros Hrb Hro Hal Hend Hreg (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  unfold dci_others_f. split_and!; try assumption.
  intros sb. apply dci_tfind_miss_rule_empty; assumption.
Qed.

(** ## The translation without stpcpy or cache premises *)

(** A getopt diagnostic calls dcgettext, and this lemma proves that call
    with the real stpcpy and tfind. The cache's root cell lies at offset
    ro of object rb. *)
Lemma wp_dcgettext_c_tff f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' C M bs dqr rb ro rreg Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind} :
  dci_rest_f lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T
    (tfind_root dqr rb ro rreg) C M bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' (tfind_root dqr rb ro rreg) C M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hr Hrb Hro Hal Hend Hreg.
  pose proof (dci_others_empty_f lk1 lk2 lkt tc _ _ _ _ _ _ _ _ _ _ _ cv dqr rb ro rreg Hrb Hro Hal Hend Hreg Hr) as Ho.
  eapply (wp_dcgettext_c_stpf eb Herr); first [exact Ho | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma wp_dcgettext_c_tf f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' C M bs dqr rb ro rreg Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind} :
  dci_rest lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T
    (tfind_root dqr rb ro rreg) C M bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' (tfind_root dqr rb ro rreg) C M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof. intros Hr. eapply wp_dcgettext_c_tff; first [exact (dci_rest_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr) | exact _]. Qed.

(** This lemma builds the short-option translation premise in the same
    way. *)
Lemma dcg_diag_translate_tff dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' C M bs dqr rb ro rreg
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind} :
  dci_rest_f lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T (tfind_root dqr rb ro rreg) C M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T''
      (tfind_root dqr rb ro rreg) C M bs)
    dom.
Proof.
  intros Hr Hrb Hro Hal Hend Hreg.
  pose proof (dci_others_empty_f lk1 lk2 lkt tc _ _ _ _ _ _ _ _ _ _ _ cv dqr rb ro rreg Hrb Hro Hal Hend Hreg Hr) as Ho.
  eapply (dcg_diag_translate_stpf eb Herr); first [exact Ho | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma dcg_diag_translate_tf dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' C M bs dqr rb ro rreg
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind} :
  dci_rest lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T (tfind_root dqr rb ro rreg) C M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T''
      (tfind_root dqr rb ro rreg) C M bs)
    dom.
Proof. intros Hr. eapply dcg_diag_translate_tff; first [exact (dci_rest_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr) | exact _]. Qed.

(** This lemma builds the long-option translation premise in the same
    way. *)
Lemma dcg_ldiag_translate_tff dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' C M bs dqr rb ro rreg
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind} :
  dci_rest_f lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T (tfind_root dqr rb ro rreg) C M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T''
      (tfind_root dqr rb ro rreg) C M bs)
    dom.
Proof.
  intros Hr Hrb Hro Hal Hend Hreg.
  pose proof (dci_others_empty_f lk1 lk2 lkt tc _ _ _ _ _ _ _ _ _ _ _ cv dqr rb ro rreg Hrb Hro Hal Hend Hreg Hr) as Ho.
  eapply (dcg_ldiag_translate_stpf eb Herr); first [exact Ho | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma dcg_ldiag_translate_tf dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' C M bs dqr rb ro rreg
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind} :
  dci_rest lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' C M cv ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T (tfind_root dqr rb ro rreg) C M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T''
      (tfind_root dqr rb ro rreg) C M bs)
    dom.
Proof. intros Hr. eapply dcg_ldiag_translate_tff; first [exact (dci_rest_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr) | exact _]. Qed.
End rules.
