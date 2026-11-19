From Glibc Require Import Unit_intl_dcigettext_os Unit_string_strchr_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcProgram.
(** In the C locale glibc's `c: __dcigettext` copies the locale name "C"
    into a fresh buffer and then reads the privilege flag
    `__libc_enable_secure`. The pinned source tests
    `__libc_enable_secure && strchr (single_locale, '/') != NULL`, so a
    nonzero flag makes the function search the copied name for a slash.
    The name "C" has no slash, so the search returns null and the
    function goes on as it does for the flag value 0.

    GNU Hello starts with the flag set to 1 in its linked image, so a
    proof that covers only the value 0 does not reach Hello's first call.
    This module proves the block for every 32-bit value of the flag. When
    the flag is nonzero, the proof runs the captured strchr, which reads
    the buffer's whole first word through strchrnul, and the caller must
    show that the program links both functions. The caller gets the flag
    back with the value that it lent. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic LibioSetb WordString GetoptBytes DcigettextFree DcigettextExit.
From Glibc Require Import StrlenLogic MemFwdLogic StrchrnulLogic DcigettextCName.
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
Local Instance dci_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** This tactic proves that a byte access stays inside its object. *)
Ltac ra := unfold raw_address; cbn [ptr_addr length Z.of_nat Pos.of_succ_nat] in *;
  first [apply Z.mod_1_r | rewrite ?Z.add_0_r; rewrite Z.mod_small; lia].

(** The privileged branch calls strchr, which glibc implements with
    strchrnul. This predicate says that the program links both names to
    the captured functions. *)
Definition dci_strchr_links : Prop :=
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) /\
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul).

(** The privileged branch looks for a slash in the copied name. The
    captured strchr reads a whole word at a time, so the caller lends the
    eight bytes of the buffer's first word. Strchr gets half of each
    byte. It finds no slash in "C" and returns null. The rule then joins
    the two halves, and the caller gets back the same bytes. *)
Lemma wp_dci_sl_strchr f e ls l r args rest j sl sreg cf' Φ :
  dci_strchr_links -> map_option (arg_x ge e) args = Some [WPtr (mkPtr sl (Obj sl)); WInt 47] ->
  0 < sl -> sl mod 8 = 0 -> sl + 8 <= r_end sreg -> r_end sreg <= 2 ^ 48 ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WPtr (mkPtr 0 CNone))) = Some cf' ->
  live sl sreg -∗ ibyte sl 0 67 -∗ ibyte sl 1 0 -∗ bytes sl 2 (replicate 6 0) -∗
  ▷ (live sl sreg -∗ ibyte sl 0 67 -∗ ibyte sl 1 0 -∗ bytes sl 2 (replicate 6 0) -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global (TAtom "__GI_strchr")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros [Hg Hn] Hx Hsl0 Hsl8 Hslend Hslr Hr. iIntros "Hl Hb0 Hb1 Hbs HK".
  assert (Hws : words_ps sl 0 [67] = byte_ps sl 0 ([67] ++ [0] ++ replicate 6 0)).
  { rewrite words_ps_bytes. reflexivity. }
  iAssert (wwin (DfracOwn 1) sl sreg 0 [67]) with "[Hl Hb0 Hb1 Hbs]" as "Hw".
  { rewrite /wwin Hws. iFrame "Hl". rewrite !byte_ps_app !ptsq_app. iFrame. }
  rewrite -{1}Qp.half_half wwin_split. iDestruct "Hw" as "[H1 H2]".
  assert (Hsh : str_shape (mkPtr sl (Obj sl)) sl sreg [67] [67]).
  { split; cbn [ptr_cap ptr_addr length Z.of_nat]; unfold wstart; cbn [ptr_addr];
      first [by left | lia | rewrite Hsl8; cbn; lia | rewrite Hsl8; reflexivity | repeat constructor; lia |
             rewrite Hsl8; reflexivity | idtac]. }
  iDestruct (word_string_intro _ _ sl sreg [67] [67] Hsh with "[H1]") as "Hs".
  { unfold wstart. cbn [ptr_addr]. rewrite Hsl8 Z.sub_0_r Z.sub_diag. iExact "H1". }
  iApply (wp_call_glibc_strchr registry (os_wi w0) ge with "Hs"); [exact Hx | lia | exact Hg | exact Hn | exact Hr |].
  iNext. iIntros "(%b & %reg & %ws & %Hs & H1)".
  destruct (str_shape_same _ _ _ _ _ _ _ _ Hs Hsh) as [-> Hlen].
  unfold wstart in *. cbn [ptr_addr] in *. rewrite Hsl8 Z.sub_0_r Z.sub_diag.
  iDestruct (wwin_agree with "H1 H2") as %[-> ->]; [exact Hlen | exact (ss_words _ _ _ _ _ Hs) | repeat constructor; lia |].
  iCombine "H1 H2" as "Hw". rewrite -wwin_split Qp.half_half /wwin Hws.
  iDestruct "Hw" as "[Hl Hw]". rewrite !byte_ps_app !ptsq_app. iDestruct "Hw" as "(Hb0 & Hb1 & Hbs)".
  iApply ("HK" with "Hl Hb0 Hb1 Hbs").
Qed.

(** After the flag test, both branches go on to check the copied name
    and leave the function in the same way. This tactic proves that
    common end once for both branches. *)
Ltac c_tail Hheap Hge Hlk1 Hlk2 Hu1 Hu2 Hs Es1 xs xsreg xd xreg sl sreg s msgid lk1 lk2 U1 U1' U2 U2' bs :=
  step; check "Hl";
  iApply (wp_raw_load_byte with "Hl Hb0"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ra |];
  iNext; iIntros "Hl Hb0";
  step; branch; step; step; rewrite Es1; check "Hl";
  iApply (wp_raw_load_byte with "Hl Hb1"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ra |];
  iNext; iIntros "Hl Hb1";
  step; branch; step; branch; step; branch;
  iApply (wp_dci_exit_fr eb Herr _ xs xsreg xd xreg sl sreg s msgid lk1 lk2 U1 U1' U2 U2' bs
    with "Hxl Hxc Hdl Hl HU1 HU2 Herr [HK Hsecl Hsecb]");
    try first [exact Hheap | exact Hge | exact Hlk1 | exact Hlk2 | exact Hu1 | exact Hu2 | exact Hs | lia | lk_prove];
  iNext; iIntros "Hxl Hxc HU1 HU2 Herr"; iApply ("HK" with "Hxl Hxc Hsecl [Hsecb] HU1 HU2 Herr");
  iSplit; [done | iExact "Hsecb"].

(** The suffix rule starts where the copy has stopped. *)
Lemma wp_dci_c_secure_tail e cv9 sl sreg a1 sec secreg dqs v xs xsreg xd xreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  dci_free_rule -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "__libc_enable_secure") (ge_globals ge) = Some (mkPtr sec (Obj sec)) ->
  0 < sec -> sec mod 4 = 0 -> sec + 4 <= r_end secreg -> r_end secreg <= 2 ^ 48 -> 0 <= v < 2 ^ 32 ->
  (v = 0 \/ dci_strchr_links) ->
  lookup (TAtom "pr.19") e = Some (WPtr (mkPtr (sl + 1) (Obj sl))) -> lookup (TAtom "pr.9") e = Some (WPtr cv9) ->
  lookup (TAtom "v254") e = Some (WPtr (mkPtr sl (Obj sl))) ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) -> lookup (TAtom "v32") e = Some (WInt 0) ->
  0 < sl -> sl mod 8 = 0 -> sl + 8 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> r_kind sreg = Heap ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 -> r_kind xreg = Heap -> 0 < xd < 2 ^ 64 ->
  liveq dqs sec secreg -∗ int_cellq dqs sec 0 v -∗
  live sl sreg -∗ ibyte sl 0 67 -∗ ibyte sl 1 a1 -∗ bytes sl 2 (replicate 6 0) -∗
  live xs xsreg -∗ pcell xs 0 null -∗ live xd xreg -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ liveq dqs sec secreg -∗ int_cellq dqs sec 0 v -∗ U1' -∗ U2' -∗
     errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L298") (Some (TAtom "L304")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hheap Hge Hlk1 Hlk2 Hu1 Hu2 Hsec Hsec0 Hsec4 Hsecend Hsecr Hv Hlinks Hp19 Hp9 Hsl Hv17 Hc0 Hv232 Hv69 Hs Hv6 Hv2 Hv32
    Hsl0 Hsl8 Hslend Hslr Hsk Hxs0 Hxs8 Hxsend Hxsr Hxk Hxd.
  iIntros "Hsecl [% Hsecb] Hl Hb0 Hb1 Hbs Hxl Hxc Hdl HU1 HU2 Herr HK".
  assert (Es1 : (ptr_addr (mkPtr sl (Obj sl)) mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 = sl + 1).
  { cbn [ptr_addr]. rewrite (Z.mod_small sl); [|lia]. apply Z.mod_small. lia. }
  step. check "Hl".
  iApply (wp_raw_store_byte with "Hl Hb1"); [reflexivity | vx | reflexivity | ra | wi_store |].
  iNext. iIntros "Hl Hb1".
  step_global Hsec. check_shared "Hsecl".
  rule2 "Hsecl" "Hsecb" ltac:(eapply wp_raw_load_sub_bytes_dq; inst;
    [reflexivity | vx | reflexivity | apply load_sw_int; lia | left; reflexivity | a2]).
  iEval (change ((0 mod 2 ^ 32) mod 256) with 0) in "Hb1".
  destruct (Z.eqb_spec v 0) as [-> | Hv0].
  - branch. step. branch. c_tail Hheap Hge Hlk1 Hlk2 Hu1 Hu2 Hs Es1 xs xsreg xd xreg sl sreg s msgid lk1 lk2 U1 U1' U2 U2' bs.
  - assert (Hvm : (v mod 2 ^ 32 =? 0) = false) by (rewrite Z.mod_small; [apply Z.eqb_neq|]; lia).
    destruct Hlinks as [-> | Hlinks]; [lia |].
    branch_symbolic. rewrite Hvm. cbn [edge_label]. step.
    iApply (wp_dci_sl_strchr with "Hl Hb0 Hb1 Hbs"); [exact Hlinks | vx | lia | lia | lia | lia | reflexivity |].
    iNext. iIntros "Hl Hb0 Hb1 Hbs". step. step. step. step. branch.
    c_tail Hheap Hge Hlk1 Hlk2 Hu1 Hu2 Hs Es1 xs xsreg xd xreg sl sreg s msgid lk1 lk2 U1 U1' U2 U2' bs.
Qed.

(** ## The whole locale test

    The rule starts where the copy loop begins, like the zero-flag rule in
    DcigettextC.v, and holds for every 32-bit value of the privilege flag.
    A nonzero flag makes the function search the copied name for a slash,
    so the buffer must be a whole aligned word and the program must link
    strchr and strchrnul. The caller gets back the flag cell with its
    value unchanged. *)
Lemma wp_dci_c_locale_v_fr e cv sl sreg a0 a1 sec secreg dqs v xs xsreg xd xreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  dci_free_rule -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "__libc_enable_secure") (ge_globals ge) = Some (mkPtr sec (Obj sec)) ->
  0 < sec -> sec mod 4 = 0 -> sec + 4 <= r_end secreg -> r_end secreg <= 2 ^ 48 -> 0 <= v < 2 ^ 32 ->
  (v = 0 \/ dci_strchr_links) ->
  lookup (TAtom "v224") e = Some (WPtr cv) -> lookup (TAtom "v254") e = Some (WPtr (mkPtr sl (Obj sl))) ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) -> lookup (TAtom "v32") e = Some (WInt 0) ->
  0 < sl -> sl mod 8 = 0 -> sl + 8 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> r_kind sreg = Heap ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 -> r_kind xreg = Heap -> 0 < xd < 2 ^ 64 ->
  word_string DfracDiscarded cv [67] -∗ liveq dqs sec secreg -∗ int_cellq dqs sec 0 v -∗
  live sl sreg -∗ ibyte sl 0 a0 -∗ ibyte sl 1 a1 -∗ bytes sl 2 (replicate 6 0) -∗
  live xs xsreg -∗ pcell xs 0 null -∗ live xd xreg -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ liveq dqs sec secreg -∗ int_cellq dqs sec 0 v -∗ U1' -∗ U2' -∗
     errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L263") (Some (TAtom "L235")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hheap Hge Hlk1 Hlk2 Hu1 Hu2 Hsec Hsec0 Hsec4 Hsecend Hsecr Hv Hlinks Hcv Hsl Hv17 Hc0 Hv232 Hv69 Hs Hv6 Hv2 Hv32
    Hsl0 Hsl8 Hslend Hslr Hsk Hxs0 Hxs8 Hxsend Hxsr Hxk Hxd.
  iIntros "Hcv Hsecl Hsecb Hl Hb0 Hb1 Hbs Hxl Hxc Hdl HU1 HU2 Herr HK".
  iApply (wp_dci_c_name with "Hcv Hl Hb0 Hb1"); [exact Hcv | exact Hsl | lia | lia | lia |].
  iNext. iIntros (e' (Hp19 & Hp9 & Hk)) "Hl Hb0 Hb1".
  unfold dci_c_kept in Hk. repeat (match goal with H : Forall _ (_ :: _) |- _ => inversion_clear H end).
  iApply (wp_dci_c_secure_tail with "Hsecl Hsecb Hl Hb0 Hb1 Hbs Hxl Hxc Hdl HU1 HU2 Herr HK");
    try first [eassumption | lia | congruence].
Qed.
End rules.
