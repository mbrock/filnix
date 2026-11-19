From Glibc Require Import Unit_intl_dcigettext_os.
From Glibc Require Import GlibcProgram.
(** The C-locale route of glibc's `c: __dcigettext` calls malloc twice,
    once for the name of the catalog file and once for a copy of the
    locale name. Either call may fail. This module proves that a failed
    allocation still ends safely. The lookup jumps to the block that the
    source labels `c: return_untranslated`, frees whatever it holds,
    releases both locale locks, restores errno and returns the message id
    unchanged.

    A failed allocation must not leak or double-free memory, and what the
    lookup holds depends on which allocation failed. When the first one
    fails, the lookup holds no string at all. When the second one fails,
    it holds only the catalog-file name, which the block frees. The same
    block ends the successful route, whose proof is in DcigettextExit.v. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic LibioSetb DcigettextFree DcigettextExit.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dci_fail_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## The first allocation fails *)

(** When malloc returns null for the catalog-file name, the lookup holds
    neither that name nor the locale-name copy. All three frees in the
    block receive null and do nothing. *)
Lemma wp_dci_fail_join_fr e xs xsreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  dci_free_rule -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr null) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 ->
  live xs xsreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L205") (Some (TAtom "iw_3.join")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros [Hfn Hfl] Hge Hlk1 Hlk2 Hu1 Hu2 Hv17 Hc0 Hv232 Hv69 Hs Hv6 Hv2 Hxs0 Hxs8 Hxsend Hxsr.
  iIntros "Hxl Hxc HU1 HU2 Herr HK".
  step. check "Hxl". load_null "Hxl" "Hxc".
  iApply Hfn; [vx |]. iNext.
  iApply Hfn; [vx |]. iNext.
  iApply Hfn; [vx |]. iNext.
  step_global Hlk1; iApply (Hu1 with "HU1"); [vx |]; iNext; iIntros (x1) "HU1".
  step_global Hlk2; iApply (Hu2 with "HU2"); [vx |]; iNext; iIntros (x2) "HU2".
  step_global Hge; iApply (wp_dci_errno_check eb Herr); [vx |]; iNext.
  iDestruct "Herr" as (cs [Hbs Hcs]) "Hp"; rewrite pts_app; iDestruct "Hp" as "[Hb Haux]".
  iApply (wp_dci_errno_store eb Herr with "Hb"); [vx | vx | eassumption |]; iNext; iIntros "Hb".
  step; branch; step.
  iApply wp_ret; [reflexivity | vx |]; iNext.
  iApply ("HK" with "Hxl Hxc HU1 HU2 [Hb Haux]").
  iExists cs; rewrite pts_app; iSplitR; [iPureIntro; rewrite length_le_bytes; auto|].
  iFrame "Haux"; rewrite (Z.mod_small s); [iExact "Hb" | lia].
Qed.

(** The older statement takes the model's free, which meets the rule. *)
Lemma wp_dci_fail_join e xs xsreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  heap_fns ge -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr null) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 ->
  live xs xsreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L205") (Some (TAtom "iw_3.join")))) : gexpr) {{ Φ }}.
Proof using Type*. intros Hh. apply wp_dci_fail_join_fr, dci_free_rule_heap, Hh. Qed.

(** ## The second allocation fails *)

(** When malloc returns null for the locale-name copy, the lookup still
    holds the catalog-file name xd. The block frees xd, and the free of
    the null copy does nothing. *)
Lemma wp_dci_fail_name_fr e xs xsreg xd xreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  dci_free_rule -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) -> lookup (TAtom "v254") e = Some (WPtr null) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 -> r_kind xreg = Heap -> 0 < xd < 2 ^ 64 ->
  live xs xsreg -∗ pcell xs 0 null -∗ live xd xreg -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L205") (Some (TAtom "L235")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros [Hfn Hfl] Hge Hlk1 Hlk2 Hu1 Hu2 Hv17 Hc0 Hv232 Hv254 Hv69 Hs Hv6 Hv2
    Hxs0 Hxs8 Hxsend Hxsr Hxk Hxd.
  iIntros "Hxl Hxc Hdl HU1 HU2 Herr HK".
  step. check "Hxl". load_null "Hxl" "Hxc".
  iApply Hfn; [vx |]. iNext.
  iApply (Hfl with "Hdl"); [vx | exact Hxk | lia |]. iNext.
  iApply Hfn; [vx |]. iNext.
  step_global Hlk1; iApply (Hu1 with "HU1"); [vx |]; iNext; iIntros (x1) "HU1".
  step_global Hlk2; iApply (Hu2 with "HU2"); [vx |]; iNext; iIntros (x2) "HU2".
  step_global Hge; iApply (wp_dci_errno_check eb Herr); [vx |]; iNext.
  iDestruct "Herr" as (cs [Hbs Hcs]) "Hp"; rewrite pts_app; iDestruct "Hp" as "[Hb Haux]".
  iApply (wp_dci_errno_store eb Herr with "Hb"); [vx | vx | eassumption |]; iNext; iIntros "Hb".
  step; branch; step.
  iApply wp_ret; [reflexivity | vx |]; iNext.
  iApply ("HK" with "Hxl Hxc HU1 HU2 [Hb Haux]").
  iExists cs; rewrite pts_app; iSplitR; [iPureIntro; rewrite length_le_bytes; auto|].
  iFrame "Haux"; rewrite (Z.mod_small s); [iExact "Hb" | lia].
Qed.

(** The older statement takes the model's free, which meets the rule. *)
Lemma wp_dci_fail_name e xs xsreg xd xreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  heap_fns ge -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) -> lookup (TAtom "v254") e = Some (WPtr null) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 -> r_kind xreg = Heap -> 0 < xd < 2 ^ 64 ->
  live xs xsreg -∗ pcell xs 0 null -∗ live xd xreg -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L205") (Some (TAtom "L235")))) : gexpr) {{ Φ }}.
Proof using Type*. intros Hh. apply wp_dci_fail_name_fr, dci_free_rule_heap, Hh. Qed.
End rules.
