From Glibc Require Import Unit_intl_dcgettext_os Unit_intl_dcigettext_os Unit_string_memcpy_os Unit_string_mempcpy_os Unit_string_stpcpy_os.
From Glibc Require Import GlibcProgram.
(** A getopt diagnostic is translated before it is printed, and in the C
    locale the translation copies strings with stpcpy. The earlier proof
    of that translation assumed how stpcpy behaves. This module proves
    that behaviour from glibc's captured stpcpy and restates the
    translation without the assumption, once the program binds the name
    that the lookup calls to that body.

    The old rule cannot be proved from the body as it stands. It promises
    that every byte of the buffer is a valid byte after the call, but the
    copy leaves the bytes outside the string as they were, and owning a
    byte does not bound its value. The proved rule therefore asks that
    the buffer hold valid bytes before the call. The lookup meets that
    premise at all three calls, because the first one writes into fresh
    zeros and each later one into the buffer that the previous copy left
    valid. The example at the end of this module shows the counterexample
    to the old rule.

    Some functions that the lookup calls are still unproved, so the
    caller must say how they behave. It describes the rwlock operations,
    the locale query, the cache search and malloc, and it still states that the program runs in the C locale
    with an empty binding list and the privilege flag clear. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry OsMemLogic StrlenLogic WordString.
From Glibc Require Import BufferCopy StpcpyBytes StpcpyLogic.
From Glibc Require Import GetoptMessages.
From Glibc Require Import DcigettextCopy DcigettextRoute DcgettextC.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld OsMemLogic.

(** A copy of valid bytes into a buffer of valid bytes leaves valid
    bytes. *)
Lemma Forall_splice (P : Z -> Prop) xs k zs : Forall P xs -> Forall P zs -> Forall P (splice xs k zs).
Proof.
  intros Hx Hz. unfold splice. apply Forall_app. split; [apply Forall_take, Hx|].
  apply Forall_app. split; [exact Hz | apply Forall_drop, Hx].
Qed.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dcg_stp_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## The stpcpy rule *)

(** The lookup needs each copy to leave valid bytes in its buffer. When
    its name for stpcpy is bound to the captured body, a copy into valid
    bytes does so, because the string's bytes lie between 1 and 255. The
    copy does not touch the buffer's auxiliary bytes. *)
Lemma dci_stpcpy_rule_r_proved `{!Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy} : dci_stpcpy_rule_r.
Proof using Type.
  intros f e ls l d args rest j a b reg xs cs dq q s Φ Hargs Hba Hfit Hend Hcs Hxs.
  iIntros "Hl Hb Ha Hs HK".
  iDestruct "Hs" as (bq rq wq Hsh) "Hw".
  pose proof (ss_chars _ _ _ _ _ Hsh) as Hch.
  replace a with (b + (a - b)) in Hargs |- * by lia.
  iApply (wp_call_glibc_stpcpy _ _ _ _ _ _ _ _ _ b reg xs (a - b) dq q s with "Hl Hb [Hw]");
    [exact Hargs | apply defines | lia | lia | exact Hend | |].
  { iExists bq, rq, wq. iFrame "Hw". done. }
  iNext. iIntros "Hl Hb Hs". iApply ("HK" with "Hl [Hb Ha] Hs").
  iExists _, cs. iFrame "Hb Ha". iPureIntro. split_and!.
  - apply length_splice. rewrite length_app. cbn. lia.
  - exact Hcs.
  - apply Forall_splice; [exact Hxs|]. apply Forall_app. split; [|constructor; [lia | constructor]].
    eapply Forall_impl; [|exact Hch]. cbn. lia.
Qed.

(** ## The translation without a stpcpy premise *)

(** This lemma restates the wrapper rule of DcgettextC.v so that it uses
    the captured stpcpy instead of a rule for it. *)
Lemma wp_dcgettext_c_stpf f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy} :
  dci_others_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' K C M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Ho. pose proof (conj dci_stpcpy_rule_r_proved Ho) as Hr. eapply (wp_dcgettext_c_f eb Herr); first [exact Hr | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma wp_dcgettext_c_stp f e ls l d args rest j dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg
    sec dqs secreg mid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy} :
  dci_others lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1 L2 T K C M bs -∗
  ▷ (∀ q, dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
        L1'' L2'' T'' K C M bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*. intros Ho. eapply wp_dcgettext_c_stpf; first [exact (dci_others_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ho) | exact _]. Qed.

(** This lemma builds the short-option translation premise from the
    captured stpcpy. *)
Lemma dcg_diag_translate_stpf dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy} :
  dci_others_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof using Type*.
  intros Ho. pose proof (conj dci_stpcpy_rule_r_proved Ho) as Hr. eapply (dcg_diag_translate_f eb Herr); first [exact Hr | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma dcg_diag_translate_stp dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy} :
  dci_others lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof using Type*. intros Ho. eapply dcg_diag_translate_stpf; first [exact (dci_others_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ho) | exact _]. Qed.

(** This lemma builds the long-option translation premise in the same way. *)
Lemma dcg_ldiag_translate_stpf dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy} :
  dci_others_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof using Type*.
  intros Ho. pose proof (conj dci_stpcpy_rule_r_proved Ho) as Hr. eapply (dcg_ldiag_translate_f eb Herr); first [exact Hr | exact _].
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma dcg_ldiag_translate_stp dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy,
      !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy, !Defines ge "__GI___dcgettext" Unit_intl_dcgettext_os.fn___GI___dcgettext,
      !Defines ge "__dcigettext" Unit_intl_dcigettext_os.fn___dcigettext, !Defines ge "__GI_stpcpy" Unit_string_stpcpy_os.fn___GI___stpcpy} :
  dci_others lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      L1 L2 T K C M bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg L1'' L2'' T'' K C M bs)
    dom.
Proof using Type*. intros Ho. eapply dcg_ldiag_translate_stpf; first [exact (dci_others_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ho) | exact _]. Qed.
End rules.

(** ## The counterexample to the old rule

    A buffer [1000; 0; 0] is owned byte by byte even though its first
    entry is no byte value. Copying the empty string to offset 1 writes
    only the terminator, so the body's exact result keeps 1000, and the
    old rule's promise of valid bytes fails. *)
Example dci_stpcpy_old_counterexample :
  splice [1000; 0; 0] 1 ([] ++ [0]) = [1000; 0; 0] /\
  ~ Forall (fun x => 0 <= x < 256) (splice [1000; 0; 0] 1 ([] ++ [0])).
Proof. split; [reflexivity|]. cbn. intros H. inversion H. lia. Qed.
