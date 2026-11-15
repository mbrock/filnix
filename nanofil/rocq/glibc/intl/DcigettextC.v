From Glibc Require Import GlibcProgram.
(** GNU Hello asks glibc to translate getopt's messages, and glibc's
    `c: __dcigettext` returns a message unchanged when the program runs in
    the C locale. This module proves the part of that route that decides
    the locale is C. It starts where the lookup has allocated its
    locale-name buffer and ends with the untranslated return of
    DcigettextExit.v.

    In the C locale the lookup copies the name "C" into a small buffer
    and stops at its terminator. It then checks whether the program runs
    with raised privileges, and this rule covers only the ordinary case,
    where the flag `c: __libc_enable_secure` reads 0. Finally it sees that
    the buffer starts with 'C' followed by the terminator, so it leaves
    the loop before it searches for a message catalog. The earlier blocks,
    which take the locks, search the cache and allocate the buffers,
    remain an entry contract of this rule. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic LibioSetb WordString GetoptBytes DcigettextCode DcigettextExit.
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

(** These tactics check and load bytes of the locale name "C". The first
    reads byte 0 with its check, the second reads the terminator after an
    advanced pointer, and the last two reuse the byte 0 pieces. *)

Ltac rdchr H q s k :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  iDestruct (ws_byte q s k with H) as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [cbn; lia|];
  destruct Hbb as (Hcap & Hb0' & Hbq & Hbe & Hbr);
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | arith | arith | arith |]; iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | arith |];
  iNext; iIntros "_ _".
Ltac ra := unfold raw_address; cbn [ptr_addr length Z.of_nat Pos.of_succ_nat] in *;
  first [apply Z.mod_1_r | rewrite ?Z.add_0_r; rewrite Z.mod_small; lia].
Ltac rdchr1 :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  iDestruct (ws_byte _ [67] 1 with "Hw") as (bb breg) "(%Hbb & #Hbl1 & #Hbt1)"; [cbn; lia|];
  destruct Hbb as (Hcap1 & Hb01 & Hbq1 & Hbe1 & Hbr1);
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl1");
    [reflexivity | vx | exact Hcap1 | ra | ra | ra |]; iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl1 Hbt1");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap1 | ra |];
  iNext; iIntros "_ _".
Ltac chkchr :=
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | eassumption | arith | arith | arith |]; iNext; iIntros "_".
Ltac ldchr :=
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | eassumption | arith |];
  iNext; iIntros "_ _".

(** ## From the locale name to the untranslated return *)

(** This rule describes one untranslated lookup in the C locale. It
    starts after the lookup has allocated the two-byte buffer sl for the
    locale name. The caller shows that the locale name cv reads "C", that
    the directory slot xs holds null, and that s is the errno value saved
    at entry. The caller also lends a share of the privilege flag that
    reads 0, the two lock resources and errno's bytes. The lookup frees
    sl and the domain-file string xd. It returns the message id with the
    locks released, errno restored to s, and the slot and the flag share
    given back. *)
Lemma wp_dci_c_locale e cv sl sreg a0 a1 sec secreg dqs xs xsreg xd xreg s msgid lk1 lk2 U1 U1' U2 U2' bs Φ :
  heap_fns ge -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  lookup (TAtom "__libc_enable_secure") (ge_globals ge) = Some (mkPtr sec (Obj sec)) ->
  0 < sec -> sec mod 4 = 0 -> sec + 4 <= r_end secreg -> r_end secreg <= 2 ^ 48 ->
  lookup (TAtom "v224") e = Some (WPtr cv) -> lookup (TAtom "v254") e = Some (WPtr (mkPtr sl (Obj sl))) ->
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) ->
  lookup (TAtom "v69") e = Some (WInt s) -> 0 <= s < 2 ^ 32 -> lookup (TAtom "v6") e = Some (WInt 0) ->
  lookup (TAtom "v2") e = Some (WPtr msgid) ->
  0 < sl -> sl + 2 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> r_kind sreg = Heap ->
  0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xsreg -> r_end xsreg <= 2 ^ 48 -> r_kind xreg = Heap -> 0 < xd < 2 ^ 64 ->
  word_string DfracDiscarded cv [67] -∗ liveq dqs sec secreg -∗ int_cellq dqs sec 0 0 -∗
  live sl sreg -∗ ibyte sl 0 a0 -∗ ibyte sl 1 a1 -∗ live xs xsreg -∗ pcell xs 0 null -∗ live xd xreg -∗
  U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ (live xs xsreg -∗ pcell xs 0 null -∗ liveq dqs sec secreg -∗ int_cellq dqs sec 0 0 -∗ U1' -∗ U2' -∗
     errno_own eb (le_bytes s 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "L263") (Some (TAtom "L235")))) : gexpr) {{ Φ }}.
Proof.
  intros Hheap Hge Hlk1 Hlk2 Hu1 Hu2 Hsec Hsec0 Hsec4 Hsecend Hsecr Hcv Hsl Hv17 Hc0 Hv232 Hv69 Hs Hv6 Hv2
    Hsl0 Hslend Hslr Hsk Hxs0 Hxs8 Hxsend Hxsr Hxk Hxd.
  iIntros "#Hw Hsecl [% Hsecb] Hl Hb0 Hb1 Hxl Hxc Hdl HU1 HU2 Herr HK".
  step. step. step.
  rdchr "Hw" cv [67] 0%nat. change (chr_w (sbyte [67] 0)) with 67.
  step. branch. step. ldchr. change (chr_w (sbyte [67] 0)) with 67. step. step. step. branch.
  step. ldchr. change (chr_w (sbyte [67] 0)) with 67. step. branch.
  step. chkchr. ldchr. change (chr_w (sbyte [67] 0)) with 67.
  step. branch. step. ldchr. change (chr_w (sbyte [67] 0)) with 67. step. step. step. branch.
  step. step. step. ldchr. change (chr_w (sbyte [67] 0)) with 67. check "Hl".
  iApply (wp_raw_store_byte with "Hl Hb0"); [reflexivity | vx | reflexivity | a2 | wi_store |].
  iNext. iIntros "Hl Hb0".
  step. step.
  assert (Ec1 : (ptr_addr cv mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 = ptr_addr cv + 1).
  { cbn [length Z.of_nat] in Hbe. rewrite (Z.mod_small (ptr_addr cv)); [|lia]. apply Z.mod_small. lia. }
  assert (Es1 : (ptr_addr (mkPtr sl (Obj sl)) mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 = sl + 1).
  { cbn [ptr_addr]. rewrite (Z.mod_small sl); [|lia]. apply Z.mod_small. lia. }
  rewrite Ec1 Es1. cbn [ptr_cap].
  rdchr1. change (chr_w (sbyte [67] 1)) with 0.
  step. branch. step. branch. step. check "Hl".
  iApply (wp_raw_store_byte with "Hl Hb1"); [reflexivity | vx | reflexivity | ra | wi_store |].
  iNext. iIntros "Hl Hb1".
  step_global Hsec. check_shared "Hsecl".
  rule2 "Hsecl" "Hsecb" ltac:(eapply wp_raw_load_sub_bytes_dq; inst;
    [reflexivity | vx | reflexivity | apply load_sw_int; lia | left; reflexivity | a2]).
  branch. step. branch. step. check "Hl".
  iApply (wp_raw_load_byte with "Hl Hb0"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ra |].
  iNext. iIntros "Hl Hb0".
  step. branch. step. step. rewrite Es1. check "Hl".
  iApply (wp_raw_load_byte with "Hl Hb1"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ra |].
  iNext. iIntros "Hl Hb1".
  step. branch. step. branch. step. branch.
  iApply (wp_dci_exit eb Herr _ xs xsreg xd xreg sl sreg s msgid lk1 lk2 U1 U1' U2 U2' bs
    with "Hxl Hxc Hdl Hl HU1 HU2 Herr [HK Hsecl Hsecb]");
    try first [exact Hheap | exact Hge | exact Hlk1 | exact Hlk2 | exact Hu1 | exact Hu2 | exact Hs | lia | lk_prove].
  iNext. iIntros "Hxl Hxc HU1 HU2 Herr". iApply ("HK" with "Hxl Hxc Hsecl [Hsecb] HU1 HU2 Herr").
  iSplit; [done | iExact "Hsecb"].
Qed.
End rules.
