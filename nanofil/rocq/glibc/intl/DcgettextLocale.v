From Glibc Require Import GlibcProgram.
(** When getopt reports an error, it first asks gettext to translate the
    message, and gettext asks which locale the thread uses for messages.
    The earlier proofs of that translation assumed the answer. This
    module runs glibc's real locale query instead, on top of the real
    stpcpy and tfind that DcgettextStpcpy.v and DcgettextTfind.v proved.

    The caller still decides which locale the thread uses, and nothing
    here proves that a program starts in the C locale. To state its
    choice, the caller lends the two memory cells that the query reads:
    the cell that points to the thread's locale, and the place in that
    locale where the message locale's name is kept. That place must hold
    the string "C" that the translation already reads.

    The query also checks that the name it returns is alive, so the
    caller lends a share of that string's lifetime. The string "C" that
    the caller already lends carries a persistent share, and this module
    shows that this share is enough, so the caller needs no second share.

    Some functions that gettext calls are still unproved, so the caller
    must say how they behave. It describes the rwlock operations, memmove
    and malloc, and it states that the program has an empty binding list,
    an empty cache and the privilege flag clear. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic MemFwdCode WordString.
From Glibc Require Import LibioSetb StpcpyCode TfindCode TfindEmpty LocalenameCode LocalenameLogic.
From Glibc Require Import GetoptLongPfxAlloc GetoptDiag GetoptLongDiag GetoptDiagFx.
From Glibc Require Import DcgettextCode DcigettextCode DcigettextFree DcigettextExit DcigettextPreRules DcigettextRoute.
From Glibc Require Import DcgettextC.
From Glibc Require Import DcgettextStpcpy DcgettextTfind.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dcg_loc_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## The locale query *)

(** The query's two loads must stay inside their objects. This predicate
    places the thread's locale cell at offset go of object gb, the
    global that the code names, and bounds the locale object lb that its
    pointer lp names far enough to hold entry 5 of the names table. *)
Definition locale_cells (gb go : Z) (greg : region) (lp : ptr) (lb : Z) (lreg : region) : Prop :=
  lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (mkPtr (gb + go) (Obj gb)) /\
  0 < gb /\ 0 <= go /\ (gb + go) mod 8 = 0 /\ gb + go + 8 <= r_end greg /\ r_end greg <= 2 ^ 48 /\
  (ptr_cap lp = Obj lb \/ ptr_cap lp = Ro lb) /\ 0 < lb <= ptr_addr lp /\ ptr_addr lp mod 8 = 0 /\
  ptr_addr lp + 128 + 8 * 5 + 8 <= r_end lreg /\ r_end lreg <= 2 ^ 48.

(** The earlier proofs assumed how the query behaves, and this lemma
    shows that glibc's own query behaves that way. When the caller lends
    the two cells and the lifetimes that the query checks, the query
    returns the name cv that the second cell holds. *)
Lemma dci_locale_rule_cur `{!Defines ge "__current_locale_name" glibc_current_locale_name}
    gb go greg dqg lp lb lreg dql dqn cv dqt treg :
  locale_cells gb go greg lp lb lreg -> 0 <= ptr_addr cv < 2 ^ 64 ->
  dci_locale_rule 5 (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) cv.
Proof.
  intros (Hgl & Hgb & Hgo & Hgal & Hgend & Hgreg & Hlc & Hlb & Hlal & Hlend & Hlreg) Hcv f e ls l d args rest j Φ Hargs.
  iIntros "Hc HK". iApply (wp_call_glibc_current_locale_name with "Hc HK"); first [exact Hargs | apply defines | eassumption | lia].
Qed.

(** The string that the entry names carries a persistent share of its
    object's lifetime, and its address is a machine word. The caller can
    therefore copy the lifetime share that the query checks from the
    string "C" it lends, without giving up any part of that string. *)
Lemma word_string_life p s :
  word_string DfracDiscarded p s ⊢ ∃ reg, live_capq DfracDiscarded (ptr_cap p) reg ∗ ⌜0 <= ptr_addr p < 2 ^ 64⌝.
Proof.
  iIntros "(%b & %reg & %ws & %Hsh & Hlv & _)".
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  pose proof (ss_base _ _ _ _ _ Hsh). pose proof (ss_start _ _ _ _ _ Hsh).
  pose proof (ss_fit _ _ _ _ _ Hsh). pose proof (ss_space _ _ _ _ _ Hsh). unfold wstart in *.
  iExists reg. iSplit; [|iPureIntro; lia].
  destruct (ss_cap _ _ _ _ _ Hsh) as [-> | ->]; cbn; iExact "Hlv".
Qed.

(** The translation lends the string "C" at cv, so cv is a machine word. *)
Lemma dcg_before_cv dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs :
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs ⊢
  ⌜0 <= ptr_addr cv < 2 ^ 64⌝ ∗
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs.
Proof using Type.
  unfold dcg_before, dci_reads. iIntros "[(Hd & Hc & #Hv & Hr) Ho]". iDestruct (word_string_life with "Hv") as (reg) "[_ %Hcv]".
  iSplit; [done|]. iFrame "∗ #".
Qed.

(** These are the rules that the translation still needs once the real
    stpcpy, tfind and locale query run: memmove, malloc and the four
    rwlock operations. *)
Definition dci_rest_l (lk1 lk2 lkt : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' M : iProp Σ) : Prop :=
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None /\
  heap_fns ge /\ getopt_malloc_rule w0 registry ge M /\
  dci_rdlock_rule lkt T T' /\ dci_unlock_rule lkt T' T'' /\
  dci_rdlock_rule lk1 L1 L1' /\ dci_rdlock_rule lk2 L2 L2' /\
  dci_unlock_rule lk1 L1' L1'' /\ dci_unlock_rule lk2 L2' L2''.

(** The translation should not need a separate promise about the locale
    query. Once the caller describes the other functions and lends the
    two locale cells, nothing else is missing. *)
Lemma dci_rest_cur `{!Defines ge "__current_locale_name" glibc_current_locale_name}
    lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M gb go greg dqg lp lb lreg dql dqn cv dqt treg :
  dci_rest_l lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M ->
  locale_cells gb go greg lp lb lreg -> 0 <= ptr_addr cv < 2 ^ 64 ->
  dci_rest lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T''
    (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M cv.
Proof using Type.
  intros (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10 & H11 & H12) Hl Hcv.
  unfold dci_rest. split_and!; try assumption. apply dci_locale_rule_cur; assumption.
Qed.

(** A program that links glibc's free needs the rule for free in place
    of [heap_fns], so this predicate makes that one change. *)
Definition dci_rest_lf (lk1 lk2 lkt : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' M : iProp Σ) : Prop :=
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None /\
  dci_free_rule /\ getopt_malloc_rule w0 registry ge M /\
  dci_rdlock_rule lkt T T' /\ dci_unlock_rule lkt T' T'' /\
  dci_rdlock_rule lk1 L1 L1' /\ dci_rdlock_rule lk2 L2 L2' /\
  dci_unlock_rule lk1 L1' L1'' /\ dci_unlock_rule lk2 L2' L2''.

(** The model's free meets that rule. *)
Lemma dci_rest_lf_of lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M :
  dci_rest_l lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M -> dci_rest_lf lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M.
Proof using Type. intros (H1 & H2 & H3 & H4 & H). split_and!; try tauto. exact (dci_free_rule_heap H4). Qed.

(** The real locale query answers here as well. *)
Lemma dci_rest_cur_f `{!Defines ge "__current_locale_name" glibc_current_locale_name}
    lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M gb go greg dqg lp lb lreg dql dqn cv dqt treg :
  dci_rest_lf lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M ->
  locale_cells gb go greg lp lb lreg -> 0 <= ptr_addr cv < 2 ^ 64 ->
  dci_rest_f lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T''
    (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M cv.
Proof using Type.
  intros (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10 & H11 & H12) Hl Hcv.
  unfold dci_rest_f. split_and!; try assumption. apply dci_locale_rule_cur; assumption.
Qed.

(** These lemmas say nothing about a thread whose message locale is not
    C. Such a thread holds another name in entry 5, and a caller cannot
    lend that entry as holding the "C" string unless the two pointers are
    equal. DcigettextNotC.v follows the other route, and this module
    claims no translation for it. *)
Lemma locale_name_res_other dqg gb go greg lp dql lb lreg dqn cv dqt treg dq cv' :
  0 <= ptr_addr cv < 2 ^ 64 -> 0 <= ptr_addr cv' < 2 ^ 64 ->
  locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg -∗
  pcellq dq lb (ptr_addr lp - lb + 128 + 8 * 5) cv' -∗ ⌜cv = cv'⌝.
Proof.
  intros H1 H2. iIntros "(_ & _ & _ & Hn & _) Ho". iApply (locale_name_entry_agree with "Hn Ho"); assumption.
Qed.

(** ## The translation without stpcpy, cache or locale premises *)

(** A getopt diagnostic calls dcgettext, and this lemma proves that call
    with the real stpcpy, tfind and locale query. *)
Lemma wp_dcgettext_c_locf f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' M bs dqr rb ro rreg
    gb go greg dqg lp lb lreg dql dqn dqt treg Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name} :
  dci_rest_lf lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M -> locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T
    (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg)
        M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hr Hl Hrb Hro Hal Hend Hreg Hg Hb Hargs Hmid. iIntros "Hb HK".
  iDestruct (dcg_before_cv with "Hb") as "[%Hcv Hb]".
  pose proof (dci_rest_cur_f _ _ _ _ _ _ _ _ _ _ _ _ _ gb go greg dqg lp lb lreg dql dqn cv dqt treg Hr Hl Hcv) as Hc.
  iApply (wp_dcgettext_c_tff eb Herr with "Hb HK"); first [exact Hc | eassumption | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma wp_dcgettext_c_loc f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' M bs dqr rb ro rreg
    gb go greg dqg lp lb lreg dql dqn dqt treg Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name} :
  dci_rest_l lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M -> locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T
    (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg)
        M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof. intros Hr. eapply wp_dcgettext_c_locf; first [exact (dci_rest_lf_of _ _ _ _ _ _ _ _ _ _ _ _ _ Hr) | exact _]. Qed.

(** This lemma builds the short-option translation premise in the same
    way. *)
Lemma dcg_diag_translate_locf dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' M bs dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name} :
  dci_rest_lf lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M -> locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T''
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    dom.
Proof.
  intros Hr Hl Hrb Hro Hal Hend Hreg Hg Hb Hm f e ls l d args rest j mid Φ Hmsg Hargs. iIntros "Hb HK".
  iDestruct (dcg_before_cv with "Hb") as "[%Hcv Hb]".
  pose proof (dci_rest_cur_f _ _ _ _ _ _ _ _ _ _ _ _ _ gb go greg dqg lp lb lreg dql dqn cv dqt treg Hr Hl Hcv) as Hc.
  iApply (dcg_diag_translate_tff eb Herr with "Hb HK"); first [exact Hc | eassumption | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma dcg_diag_translate_loc dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' M bs dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name} :
  dci_rest_l lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M -> locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T''
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    dom.
Proof. intros Hr. eapply dcg_diag_translate_locf; first [exact (dci_rest_lf_of _ _ _ _ _ _ _ _ _ _ _ _ _ Hr) | exact _]. Qed.

(** This lemma builds the long-option translation premise in the same
    way. *)
Lemma dcg_ldiag_translate_locf dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' M bs dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name} :
  dci_rest_lf lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M -> locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T''
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    dom.
Proof.
  intros Hr Hl Hrb Hro Hal Hend Hreg Hg Hb Hm f e ls l d args rest j mid Φ Hmsg Hargs. iIntros "Hb HK".
  iDestruct (dcg_before_cv with "Hb") as "[%Hcv Hb]".
  pose proof (dci_rest_cur_f _ _ _ _ _ _ _ _ _ _ _ _ _ gb go greg dqg lp lb lreg dql dqn cv dqt treg Hr Hl Hcv) as Hc.
  iApply (dcg_ldiag_translate_tff eb Herr with "Hb HK"); first [exact Hc | eassumption | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma dcg_ldiag_translate_loc dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' M bs dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy, !Defines ge "__GI___dcgettext" glibc_dcgettext,
      !Defines ge "__dcigettext" glibc_dcigettext, !Defines ge "__GI_stpcpy" glibc_stpcpy,
      !Defines ge "__GI___tfind" glibc_tfind, !Defines ge "__current_locale_name" glibc_current_locale_name} :
  dci_rest_l lk1 lk2 lkt L1 L1' L1'' L2 L2' L2'' T T' T'' M -> locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T''
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) M bs)
    dom.
Proof. intros Hr. eapply dcg_ldiag_translate_locf; first [exact (dci_rest_lf_of _ _ _ _ _ _ _ _ _ _ _ _ _ Hr) | exact _]. Qed.
End rules.
