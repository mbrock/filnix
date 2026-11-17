From Glibc Require Import GlibcProgram.
(** The C-locale rule in DcigettextC.v depends on the test that sends a
    locale name starting with 'C' to the untranslated return. This module
    checks the other side of that test on the same captured code. When
    the first byte of the copied locale name is not 'C', the lookup goes
    on to compare the name with "POSIX" instead of returning. That path
    and the catalog search after it are outside the proved C route. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic GetoptBytes DcigettextCode.
From Glibc Require Import DcigettextPreRules.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic DcigettextPreRules.DciVL.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dci_not_c_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The test reads the first byte x of the locale-name buffer sl after
    the copy loop has left its cursor p9. When x is not 'C', the lookup
    enters the block that calls strcmp with
    "POSIX", whatever the rest of the name holds. *)
Lemma wp_dci_not_c e sl sreg x p9 Φ :
  lookup (TAtom "v254") e = Some (WPtr (mkPtr sl (Obj sl))) -> lookup (TAtom "pr.9") e = Some p9 ->
  0 < sl -> sl + 2 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> 0 <= x < 256 -> x <> 67 ->
  live sl sreg -∗ ibyte sl 0 x -∗
  ▷ (∀ e', live sl sreg -∗ ibyte sl 0 x -∗
     WP (ERun (mkFrame glibc_dcigettext e' [] None (Enter (TAtom "L355") (Some (TAtom "L340")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "L285") (Some (TAtom "L323")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hsl Hp9 Hsl0 Hslend Hslr Hx Hx67. iIntros "Hl Hb HK".
  assert (Ex : extended Sb W x = Some (WInt (chr_w x))).
  { pose proof (extended_chr x) as E. unfold StrlenBits.of_bytes in E. cbn in E. rewrite Z.add_0_r in E. exact E. }
  step. check "Hl".
  iApply (wp_raw_load_byte with "Hl Hb"); [reflexivity | vx | reflexivity | exact Ex | left; reflexivity |
    unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r Z.mod_small; lia |].
  iNext. iIntros "Hl Hb". step.
  assert (Hne : (chr_w x mod 2 ^ 32 =? 67 mod 2 ^ 32) = false).
  { pose proof (chr_w_range x). rewrite (Z.mod_small (chr_w x)); [|lia]. change (67 mod 2 ^ 32) with 67.
    rewrite chr_w_eqb; [|lia|lia]. apply Z.eqb_neq. exact Hx67. }
  branch_symbolic. rewrite Hne. cbn [edge_label]. step. branch.
  iApply ("HK" with "Hl Hb").
Qed.

(** The same test accepts 'C' and rejects the first letters of "POSIX"
    and "en_US". *)
Example dci_c_byte_controls : chr_w 67 = 67 /\ (chr_w 80 =? 67) = false /\ (chr_w 101 =? 67) = false.
Proof using Type*. repeat split. Qed.

(** The prefix tests the message id before it touches errno or a lock. A
    null message id makes the lookup return null at once, so that call
    needs none of the lock, locale, cache or errno resources. *)
Lemma wp_dci_null_msgid e Φ :
  lookup (TAtom "v2") e = Some (WPtr null) ->
  ▷ Φ (Ret (WPtr null)) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv2. iIntros "HK".
  step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]. iNext. iIntros (xs [Hxs [Hxsal Hxsend]]) "Hxo".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]. iNext. iIntros (rl _) "_".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]. iNext. iIntros (sb _) "_".
  change (req_align (heap_req 8 8)) with 16 in Hxsal. change (req_extent (heap_req 8 8)) with 16 in Hxsend.
  iDestruct (obj_zero_block with "Hxo") as "(Hxl & Hxb & Hxa)"; [vm_compute; discriminate|].
  change (req_extent (heap_req 8 8)) with 16. change (req_kind (heap_req 8 8)) with Heap.
  iDestruct (zero_cell_prefix xs 0 8 with "Hxb Hxa") as "(Hxc & _ & _)".
  set (xreg := mkRegion xs (xs + 16) Heap Live). assert (Hxre : r_end xreg = xs + 16) by reflexivity.
  assert (Hxs8 : xs mod 8 = 0) by (Z.div_mod_to_equations; lia).
  check "Hxl". store "Hxl" "Hxc". step. step. step. branch. step.
  iApply wp_ret; [reflexivity | vx |]. iNext. iExact "HK".
Qed.

End rules.
