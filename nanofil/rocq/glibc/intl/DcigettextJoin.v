From Glibc Require Import GlibcProgram.
(** Once glibc's `c: __dcigettext` has chosen the locale name, it builds
    the name of the catalog file that it would open. This module proves
    the first step of that construction on the C-locale route. The lookup
    measures the domain and the category name with glibc's own strlen,
    proved in StrlenWord.v, and asks malloc for a buffer that holds both
    names and five more bytes.

    The rule for malloc is a premise of the caller. When malloc fails,
    the lookup returns the message id through the exit of
    DcigettextFail.v, which releases both locale locks and restores
    errno. When it succeeds, the lookup goes on to copy the names into
    the buffer. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic LibioSetb WordString StrlenLogic StrlenWord.
From Glibc Require Import GetoptLongPfxAlloc DcigettextCode DcigettextFree DcigettextExit DcigettextPreRules DcigettextFail.
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
Local Instance dci_join_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** A string at any share fits below the 48-bit address limit. *)
Lemma dci_ws_bounds dq p s : word_string dq p s ⊢
  ⌜0 < ptr_addr p /\ ptr_addr p + Z.of_nat (length s) + 1 <= 2 ^ 48⌝ ∗ word_string dq p s.
Proof.
  iIntros "(%b & %reg & %ws & %Hs & H)". iSplit; [iPureIntro | iExists b, reg, ws; by iFrame].
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hr Hby Hch]. unfold wstart in Hf.
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). lia.
Qed.

(** ## From the locale name to the file-name buffer *)

(** To build the file name, the lookup must first know how long it is.
    It starts with the chosen locale name cv and the category name at cp,
    and it borrows the domain and category strings and the allocator
    resource M. If malloc succeeds, the lookup holds a fresh buffer large
    enough for the category name, the domain and five more bytes, and it
    goes on to the right conjunct. If malloc fails, the lookup returns
    through the left conjunct with the exit resources. *)
Lemma wp_dci_join_fr e xs xreg rl sb dom msgid cv s cp cat dqc ds dqd lk1 lk2 U1 U1' U2 U2' bs M Φ
    `{!Defines ge "__GI_strlen" glibc_strlen} :
  dci_pre_env e xs rl sb dom msgid cv s -> lookup (TAtom "iw_3.v7") e = Some (WPtr cv) ->
  lookup (TAtom "iw_2.v9") e = Some (WPtr cp) -> 0 <= s < 2 ^ 32 ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xreg -> r_end xreg <= 2 ^ 48 ->
  dci_free_rule -> getopt_malloc_rule w0 registry ge M ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗
  live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ ((live xs xreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗ Φ (Ret (WPtr msgid))) ∧
     (∀ e' xd, ⌜dci_pre_env e' xs rl sb dom msgid cv s /\
         lookup (TAtom "v224") e' = Some (WPtr cv) /\ lookup (TAtom "iw_2.v9") e' = Some (WPtr cp) /\
         lookup (TAtom "v226") e' = Some (WInt (Z.of_nat (length ds))) /\
         lookup (TAtom "v232") e' = Some (WPtr (mkPtr xd (Obj xd))) /\
         0 < xd /\ xd mod 16 = 0 /\ xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) <= 2 ^ 48⌝ -∗
      obj xd (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗
      live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
      WP (ERun (mkFrame glibc_dcigettext e' [] None (Enter (TAtom "L235") (Some (TAtom "iw_3.join")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "iw_3.join") (Some (TAtom "iw_3.L16")))) : gexpr) {{ Φ }}.
Proof.
  intros Henv Hv7 Hv9 Hs Hxs0 Hxs8 Hxsend Hxsr Hheap Hmal Hge Hlk1 Hlk2 Hu1 Hu2.
  pose proof Henv as (Hv17 & Hc0 & Hv21 & Hv23 & Hpr1 & Hv2 & Hv6 & Hv10 & Hv32 & Hv69 & Hv90).
  iIntros "Hcat Hdom HM Hxl Hxc HU1 HU2 Herr HK".
  step.
  iApply (wp_call_glibc_strlen registry (os_wi w0) ge with "Hdom"); [vx | apply defines | reflexivity |].
  iNext. iIntros "Hdom". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply (wp_call_glibc_strlen registry (os_wi w0) ge with "Hcat"); [vx | apply defines | reflexivity |].
  iNext. iIntros "Hcat". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iDestruct (dci_ws_bounds with "Hcat") as "[%Hcb Hcat]". iDestruct (dci_ws_bounds with "Hdom") as "[%Hdb' Hdom]".
  step. step.
  set (n := Z.of_nat (length cat + length ds) + 5).
  iApply (Hmal _ _ _ _ _ _ _ _ n with "HM").
  { cbn. rewrite !(Z.mod_small (Z.of_nat _)); try lia. f_equal. f_equal. unfold n. rewrite Nat2Z.inj_add.
    rewrite (Z.mod_small 5); [|lia]. rewrite !Z.mod_small; lia. }
  { unfold n. lia. }
  iNext. iIntros (p) "HM [-> | (%xd & %Hxd & Ho)]".
  - step. step. branch.
    iApply (wp_dci_fail_join_fr eb Herr with "Hxl Hxc HU1 HU2 Herr"); try first [exact Hheap | exact Hge | exact Hlk1 |
      exact Hlk2 | exact Hu1 | exact Hu2 | exact Hs | lia | lk_prove].
    iNext. iIntros "Hxl Hxc HU1 HU2 Herr". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "Hxl Hxc HU1 HU2 Herr Hcat Hdom HM").
  - destruct Hxd as (-> & Hxd0 & Hxd16 & Hxdend).
    assert (0 <= req_extent (heap_req 16 n)) by (cbn; Z.div_mod_to_equations; lia).
    step. step.
    assert (Hnn : ((if ptr_addr (mkPtr xd (Obj xd)) mod 2 ^ 64 =? 0 mod 2 ^ 64 mod 2 ^ 64 then 1 else 0) mod 2 ^ 32 =? 0) = true).
    { cbn [ptr_addr]. change (0 mod 2 ^ 64 mod 2 ^ 64) with 0. rewrite (Z.mod_small xd); [|lia].
      destruct (Z.eqb_spec xd 0); [lia | reflexivity]. }
    branch_symbolic. rewrite Hnn. cbn [edge_label].
    iDestruct "HK" as "[_ HK]".
    iApply ("HK" with "[%] Ho Hcat Hdom HM Hxl Hxc HU1 HU2 Herr").
    rewrite (Z.mod_small (Z.of_nat (length ds)) (2 ^ 64)); [|lia].
    unfold dci_pre_env. split_and!; try lk_prove; try lia.
Qed.

(** The older statement takes the model's free, which meets the rule. *)
Lemma wp_dci_join e xs xreg rl sb dom msgid cv s cp cat dqc ds dqd lk1 lk2 U1 U1' U2 U2' bs M Φ
    `{!Defines ge "__GI_strlen" glibc_strlen} :
  dci_pre_env e xs rl sb dom msgid cv s -> lookup (TAtom "iw_3.v7") e = Some (WPtr cv) ->
  lookup (TAtom "iw_2.v9") e = Some (WPtr cp) -> 0 <= s < 2 ^ 32 ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xreg -> r_end xreg <= 2 ^ 48 ->
  heap_fns ge -> getopt_malloc_rule w0 registry ge M ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗
  live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ ((live xs xreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗ Φ (Ret (WPtr msgid))) ∧
     (∀ e' xd, ⌜dci_pre_env e' xs rl sb dom msgid cv s /\
         lookup (TAtom "v224") e' = Some (WPtr cv) /\ lookup (TAtom "iw_2.v9") e' = Some (WPtr cp) /\
         lookup (TAtom "v226") e' = Some (WInt (Z.of_nat (length ds))) /\
         lookup (TAtom "v232") e' = Some (WPtr (mkPtr xd (Obj xd))) /\
         0 < xd /\ xd mod 16 = 0 /\ xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) <= 2 ^ 48⌝ -∗
      obj xd (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗
      live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
      WP (ERun (mkFrame glibc_dcigettext e' [] None (Enter (TAtom "L235") (Some (TAtom "iw_3.join")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "iw_3.join") (Some (TAtom "iw_3.L16")))) : gexpr) {{ Φ }}.
Proof. intros. eapply wp_dci_join_fr; eauto using dci_free_rule_heap. Qed.
End rules.
