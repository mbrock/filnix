From Glibc Require Import GlibcProgram.
(** Each diagnostic that getopt prints is first translated, and the
    getopt proofs take that translation as a premise. This module proves
    the translation in the C locale. Getopt calls glibc's dcgettext with
    the domain, the message and the message category. That function passes
    the call on to dcigettext with no plural form, and in the C locale the
    call returns the message it was given. The module proves the wrapper
    and then builds both translation premises of GetoptDiagFx.v from
    it.

    The constructed premises keep every condition of the route visible.
    The caller still states the rules for the rwlock operations, the
    locale query, the cache search, malloc and stpcpy, and it still states
    that the program runs in the C locale with an empty binding list and
    the privilege flag clear. A translation returns the message unchanged
    and gives back the resources that the caller lent, with errno holding
    its saved value. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic MemFwdCode.
From Glibc Require Import GetoptDiag GetoptLongDiag GetoptDiagFx.
From Glibc Require Import DcgettextCode DcigettextCode DcigettextPreRules DcigettextRoute.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dcg_c_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## The resources of one translation

    A translation borrows the memory that the route reads, the callee
    resources in their initial states and errno's bytes. It gives back
    the same memory, the callee resources in their final states and
    errno holding the value that the route saved. *)

Section resources.
Context (dom : ptr) (ds : list Z) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
  (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (dqi : dfrac) (ireg : region)
  (sec : Z) (dqs : dfrac) (secreg : region) (L1 L1'' L2 L2'' T T'' K C M : iProp Σ) (bs : list Z).

(** The caller lends these resources before the call. *)
Definition dcg_before : iProp Σ :=
  dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ∗
  L1 ∗ L2 ∗ T ∗ K ∗ C ∗ M ∗ errno_own eb bs.

(** The call returns q, which is the message id mid, with these resources. *)
Definition dcg_after (mid q : ptr) : iProp Σ :=
  ⌜q = mid⌝ ∗ dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ∗
  L1'' ∗ L2'' ∗ T'' ∗ K ∗ C ∗ M ∗ errno_own eb (le_bytes (dci_w bs) 4).
End resources.

(** ## The wrapper *)

(** A translation in the C locale must hand back the message it was
    given. When getopt calls the wrapper with its domain, a nonnull message
    and the message category, the wrapper runs the C-locale route. The
    caller then gets back the same message and the resources it lent. *)
Lemma wp_dcgettext_c_f f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs -∗
  ▷ (∀ q, dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' K C M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hcal Hglo Hbnd Hargs Hm. iIntros "(Hr & HL1 & HL2 & HT & HK & HC & HM & Herr) HΦ".
  iApply wp_call_bind; [exact Hargs | apply defines | reflexivity |]. iNext.
  step.
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_dci_route_f eb Herr with "Hr HL1 HL2 HT HK HC HM Herr"); try first [eassumption | reflexivity].
  iNext. iIntros "Hr HL1 HL2 HT HK HC HM Herr".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HΦ" with "[$Hr $HL1 $HL2 $HT $HK $HC $HM $Herr]"). done.
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma wp_dcgettext_c_r f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees_r lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs -∗
  ▷ (∀ q, dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' K C M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof. intros Hc. eapply wp_dcgettext_c_f; first [exact (dci_callees_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) | exact _]. Qed.

(** This corollary keeps the statement that assumed the old stpcpy rule. *)
Lemma wp_dcgettext_c f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs -∗
  ▷ (∀ q, dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' K C M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*. intros Hc. pose proof (dci_callees_r_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) as Hr. eapply wp_dcgettext_c_r; first [exact Hr | exact _]. Qed.

(** ## The translation premises of getopt *)

(** The short-option parser assumes that its messages can be
    translated, and the wrapper rule proves that assumption in the C
    locale. It applies to each message the parser translates, once the
    caller shows that those messages have nonzero addresses. *)
Lemma dcg_diag_translate_f dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof.
  intros Hcal Hglo Hbnd Hmsg f e ls l d args rest j mid Φ Hd Hargs.
  iIntros "HG HK". iApply (wp_dcgettext_c_f with "HG HK"); try eassumption. exact (Hmsg mid Hd).
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma dcg_diag_translate_r dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees_r lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof. intros Hc. eapply dcg_diag_translate_f; first [exact (dci_callees_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) | exact _]. Qed.

(** This corollary keeps the statement that assumed the old stpcpy rule. *)
Lemma dcg_diag_translate dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof. intros Hc. pose proof (dci_callees_r_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) as Hr. eapply dcg_diag_translate_r; first [exact Hr | exact _]. Qed.

(** The long-option premise follows in the same way. *)
Lemma dcg_ldiag_translate_f dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof.
  intros Hcal Hglo Hbnd Hmsg f e ls l d args rest j mid Φ Hd Hargs.
  iIntros "HG HK". iApply (wp_dcgettext_c_f with "HG HK"); try eassumption. exact (Hmsg mid Hd).
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma dcg_ldiag_translate_r dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees_r lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof. intros Hc. eapply dcg_ldiag_translate_f; first [exact (dci_callees_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) | exact _]. Qed.

(** This corollary keeps the statement that assumed the old stpcpy rule. *)
Lemma dcg_ldiag_translate dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext} :
  dci_callees lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof. intros Hc. pose proof (dci_callees_r_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) as Hr. eapply dcg_ldiag_translate_r; first [exact Hr | exact _]. Qed.
End rules.
