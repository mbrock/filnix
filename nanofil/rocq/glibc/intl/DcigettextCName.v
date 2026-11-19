From Glibc Require Import Unit_intl_dcigettext_os.
From Glibc Require Import GlibcProgram.
(** In the C locale glibc's `c: __dcigettext` copies the locale name "C"
    into a two-byte buffer before it tests that name. DcigettextC.v proves
    the whole C-locale test in one rule, for the ordinary case where the
    privilege flag reads 0. This module proves only the copy, so that
    DcigettextSecure.v can continue it with either value of the flag.

    The copy skips no separators, because the name has none, and writes
    'C' into the first byte of the buffer. It stops at the terminator of
    the name, before the block that writes the terminator into the buffer
    and reads the flag. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic LibioSetb WordString GetoptBytes DcigettextFree DcigettextExit.
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


(** The copy leaves alone the names that the rest of the route reads:
    the buffer, the directory slot, the domain-file string, the saved
    errno value, the plural flag, the message id and the search mode. *)
Definition dci_c_kept (e e' : env) : Prop :=
  Forall (fun x => lookup (TAtom x) e' = lookup (TAtom x) e) ["v254"; "v17"; "chk0"; "v232"; "v69"; "v6"; "v2"; "v32"]%string.

Ltac kept := repeat (first [reflexivity | eapply lookup_put_miss; [vm_compute; reflexivity |]]).

(** ## Copying the name

    The function copies the locale name "C" into a fresh buffer before
    it tests the name. This rule starts at the copy loop and ends where
    the loop has written 'C' and reached the end of the name. The caller gets back the
    buffer with 'C' in its first byte and an environment that names the
    next byte of both strings. *)
Lemma wp_dci_c_name e cv sl sreg a0 a1 Φ :
  lookup (TAtom "v224") e = Some (WPtr cv) -> lookup (TAtom "v254") e = Some (WPtr (mkPtr sl (Obj sl))) ->
  0 < sl -> sl + 2 <= r_end sreg -> r_end sreg <= 2 ^ 48 ->
  word_string DfracDiscarded cv [67] -∗ live sl sreg -∗ ibyte sl 0 a0 -∗ ibyte sl 1 a1 -∗
  ▷ (∀ e', ⌜lookup (TAtom "pr.19") e' = Some (WPtr (mkPtr (sl + 1) (Obj sl))) /\
            lookup (TAtom "pr.9") e' = Some (WPtr (mkPtr (ptr_addr cv + 1) (ptr_cap cv))) /\ dci_c_kept e e'⌝ -∗
     live sl sreg -∗ ibyte sl 0 67 -∗ ibyte sl 1 a1 -∗
     WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e' [] None (Enter (TAtom "L298") (Some (TAtom "L304")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "L263") (Some (TAtom "L235")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hcv Hsl Hsl0 Hslend Hslr.
  iIntros "#Hw Hl Hb0 Hb1 HK".
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
  step. branch. step. branch.
  iApply ("HK" with "[%] Hl [Hb0] Hb1"); [split_and!; [lk_prove | lk_prove | repeat constructor; kept] |].
  iExact "Hb0".
Qed.
End rules.
