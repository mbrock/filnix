(** Glibc's formatter copies a literal format before looking for arguments.
    This proof follows the complete captured __printf_buffer body when the
    format contains no percent sign and fits in staging. It includes the
    temporary allocations, errno read, cursor copy, scan and actual write.

    The rule covers the newline format used by error, given its padded
    string ownership and the other resources stated below. It does not
    establish those resources from startup. Conversion directives, empty
    formats and writes needing a flush remain outside this rule.
    The surrounding FILE wrapper and wide fallback are not proved here. *)
From Glibc Require FixVariadic.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_write_os Unit_stdioZ2dcommon_vfprintfZ2dinternal_os Unit_string_memcpy_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  LibioPutsInv MemFwdLogic WordString Fix FormatterCode FormatterScan
  StrchrnulLogic PrintfStagingCopy FormatterLiteralWrite.
(** The variadic memory rules provide cells for the local cursor copy. *)
Module LiteralVL := FixVariadic.VL0.
Import LiteralVL.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** This selector retains the captured helper that checks the buffer mode. *)
Definition glibc_format_failed : func := Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_has_failed.
(** Lookup finds the actual helper rather than the selector's fallback. *)
Lemma glibc_format_failed_found :
  find_direct (TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed") formatter_module =
    Some (Defined glibc_format_failed).
Proof. vm_compute. reflexivity. Qed.

Section literal.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Mode four makes the actual failure test return false without changing
    the buffer. Other fields remain in the caller's [[frame]]. *)
Lemma wp_format_has_not_failed fr bb reg Φ :
  call_frame glibc_format_failed [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end reg -> r_end reg <= 2 ^ 63 ->
  live bb reg -∗ int_cell bb 32 4 -∗
  ▷ (live bb reg -∗ int_cell bb 32 4 -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hb Ha He Hr. injection Hfr as <-. iIntros "Hl [%Hm Hmode] HK".
  step. step. norm. check "Hl".
  load_bytes_dq "Hl Hmode" decode (cbn; reflexivity) by ar.
  iNext. iIntros "Hl Hmode". step. closed_ints.
  iApply wp_ret; [reflexivity|reflexivity|]. iNext.
  iApply ("HK" with "Hl [Hmode]"). iSplit; [done|iExact "Hmode"].
Qed.

(** The scan condition excludes conversion directives by computation.
    The returned staging window contains the literal bytes and preserves
    earlier content. Errno, the caller's cursor, mode and end pointer are
    unchanged; the write pointer advances by the literal length. FILE
    fields and locks stay in the frame, and no output success is claimed. *)
Lemma wp_printf_buffer_literal fr bb reg off xs cs dq p s ab areg vb vreg cur
    eb ereg err flags Φ :
  call_frame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
    [WPtr (mkPtr bb (Obj bb)); WPtr p; WPtr (mkPtr ab (Obj ab)); WInt flags] = Some fr ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined Unit_string_memcpy_os.fn___GI_memcpy) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed") = Some (Defined glibc_format_failed) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end reg -> r_end reg <= 2 ^ 63 ->
  48 <= off -> 0 < Z.of_nat (length s) -> off + Z.of_nat (length s) <= 176 ->
  length xs = 128%nat -> length cs = length xs -> Forall (fun x => 0 <= x < 256) xs ->
  chr_idx 37 s = length s ->
  0 < ab -> ab mod 8 = 0 -> ab + 8 <= r_end areg -> r_end areg <= 2 ^ 63 ->
  0 <= cur < 2 ^ 64 -> 0 < eb -> eb + 4 <= r_end ereg -> r_end ereg <= 2 ^ 63 ->
  live bb reg -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + off) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ bytes bb 48 xs -∗ auxes bb 48 cs -∗
  word_string dq p s -∗ live ab areg -∗ pcell ab 0 (mkPtr cur (Ro vb)) -∗ live vb vreg -∗
  live eb ereg -∗ int_cell eb 0 err -∗
  ▷ (live bb reg -∗ int_cell bb 32 4 -∗
    pcell bb 8 (mkPtr (bb + off + Z.of_nat (length s)) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ window_after bb 48 xs off s -∗
    word_string dq p s -∗ live ab areg -∗ pcell ab 0 (mkPtr cur (Ro vb)) -∗ live vb vreg -∗
    live eb ereg -∗ int_cell eb 0 err -∗ Φ RetVoid) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hcpy Hchr Hscan Hwrite Hfailed Herr Hb Ha He Hr Ho Hn Hroom Hxs Hcs Hx Hlit
    Hab Haa Hae Har Hcur Heb Hee Her.
  injection Hfr as <-.
  iIntros "Hl Hmode Hptr Hend Hx Hcs Hs Hal Hap Hvl Hel Herr HK".
  step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b10 [Hb10 [Ha10 He10]]) "Ho10".
  iDestruct (obj_zero_block with "Ho10") as "(Hl10 & Hx10 & Hcs10)"; [compute; discriminate|].
  iAssert (live b10 (mkRegion b10 (b10 + 16) Heap Live)) with "Hl10" as "Hl10".
  iDestruct (zero_cell_prefix b10 0 8 with "Hx10 Hcs10") as "(Hc10 & _ & _)".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b13 _) "_".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b15 [Hb15 [Ha15 He15]]) "Ho15".
  iDestruct (obj_zero_block with "Ho15") as "(Hl15 & Hx15 & Hcs15)"; [compute; discriminate|].
  iAssert (live b15 (mkRegion b15 (b15 + 32) Heap Live)) with "Hl15" as "Hl15".
  iDestruct (zero_cell_prefix b15 0 24 with "Hx15 Hcs15") as "(Hc15 & _ & _)".
  do 8 (iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext; iIntros (? _) "_").
  step. check "Hel". iDestruct "Herr" as "[%Herrr Herr]". load_s32 "Hel" "Herr".
  step. check "Hal".
  iApply (wp_raw_load_pointer_dq with "Hal Hap Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hcur |].
  iNext. iIntros "Hal Hap Hvl".
  change (b15 mod 16 = 0) in Ha15. change (b15 + 32 <= 2 ^ 48) in He15.
  assert (Hb158 : b15 mod 8 = 0) by (Z.div_mod_to_equations; lia).
  set (r15 := mkRegion b15 (b15 + 32) Heap Live) in *.
  assert (Hr15 : r_end r15 = b15 + 32) by reflexivity.
  check "Hl15". store "Hl15" "Hc15".
  iApply wp_call_bind; [vx | exact Hscan | reflexivity |]. iNext.
  iApply (wp_wand with "[Hs]").
  { iApply (wp_find_specmb dq p s (fun v => ⌜v = Ret (WPtr (ptr_add p (Z.of_nat (length s))))⌝ ∗
      word_string dq p s)%I with "Hs"); [exact Hchr|].
    iIntros "Hs". iFrame. iPureIntro. by rewrite Hlit. }
  iIntros (v) "[-> Hs]". resume.
  iDestruct "Hs" as (sb sreg ws) "[%Hshape Hw]".
  pose proof Hshape as [Hcap Hsb Hsa Hst Hfit Hspace Hlen Hws Hbytes Hchars].
  assert (Hpend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end sreg).
  { unfold wstart in Hfit. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hshape|].
  change (b10 mod 16 = 0) in Ha10. change (b10 + 16 <= 2 ^ 48) in He10.
  assert (Hb108 : b10 mod 8 = 0) by (Z.div_mod_to_equations; lia).
  set (r10 := mkRegion b10 (b10 + 16) Heap Live) in *.
  assert (Hr10 : r_end r10 = b10 + 16) by reflexivity.
  cbn [ptr_add ptr_addr]. check "Hl10". store "Hl10" "Hc10".
  do 3 step. norm.
  iApply wp_call_bind; [vx | exact Hwrite | reflexivity |]. iNext.
  iApply (wp_wand with "[Hl Hmode Hptr Hend Hx Hcs Hs]").
  { iApply (wp_printf_buffer_write_word Hmove Hmove_fn Hmove_sym
      _ bb reg off xs cs dq p s
      (fun v => ⌜v = RetVoid⌝ ∗ live bb reg ∗ int_cell bb 32 4 ∗
        pcell bb 8 (mkPtr (bb + off + Z.of_nat (length s)) (Obj bb)) ∗
        pcell bb 16 (mkPtr (bb + 176) (Obj bb)) ∗ window_after bb 48 xs off s ∗ word_string dq p s)%I
      with "Hl Hmode Hptr Hend Hx Hcs Hs"); try assumption; try reflexivity.
    { cbn. replace (ptr_addr p + Z.of_nat (length s) - ptr_addr p) with (Z.of_nat (length s)) by lia.
      rewrite Z.mod_small; [reflexivity|lia]. }
    iNext. iIntros "Hl Hmode Hptr Hend Hx Hs". iFrame. done. }
  iIntros (v) "(-> & Hl & Hmode & Hptr & Hend & Hx & Hs)". resume.
  iApply wp_call_bind; [vx | exact Hfailed | reflexivity |]. iNext.
  iApply (wp_wand with "[Hl Hmode]").
  { iApply (wp_format_has_not_failed _ bb reg
      (fun v => ⌜v = Ret (WInt 0)⌝ ∗ live bb reg ∗ int_cell bb 32 4)%I
      with "Hl Hmode"); try assumption; try reflexivity; try lia.
    iNext. iIntros "Hl Hmode". iFrame. done. }
  iIntros (v) "(-> & Hl & Hmode)". resume. step. branch. step.
  iDestruct (word_string_bytes with "Hs") as (sb2 sr2 ws2) "(%Hshape2 & Hsl & Hsbytes & Hback)".
  pose proof Hshape2 as [Hcap2 Hsb2 Hsa2 Hst2 Hfit2 Hspace2 Hlen2 Hws2 Hbytes2 Hchars2].
  assert (Hpend2 : ptr_addr p + Z.of_nat (length s) + 1 <= r_end sr2).
  { unfold wstart in Hfit2. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iAssert (live_capq dq (ptr_cap p) sr2) with "[Hsl]" as "Hsl".
  { destruct Hcap2 as [-> | ->]; iExact "Hsl". }
  check "Hl10".
  iApply (wp_raw_load_pointer_dq with "Hl10 Hc10 Hsl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hl10 Hc10 Hsl".
  iAssert (liveq dq sb2 sr2) with "[Hsl]" as "Hsl".
  { destruct Hcap2 as [Hc | Hc]; iEval (cbn [ptr_cap]; rewrite Hc) in "Hsl"; iExact "Hsl". }
  check_read_dq "Hsl" by (cbn [ptr_add ptr_addr]; ar).
  iNext. iIntros "Hsl".
  iEval (unfold MemFwdLogic.ML.bytesq; rewrite byte_ps_app ptsq_app) in "Hsbytes".
  iDestruct "Hsbytes" as "[Hsbytes Hnul]".
  load_bytes_dq "Hsl Hnul" decode (reflexivity) by (cbn [ptr_add ptr_addr]; ar).
  iNext. iIntros "Hsl Hnul".
  step. closed_ints. branch. step. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl Hmode Hptr Hend Hx [Hsl Hsbytes Hnul Hback] Hal Hap Hvl Hel [Herr]").
  - iApply ("Hback" with "Hsl [Hsbytes Hnul]").
    rewrite /MemFwdLogic.ML.bytesq byte_ps_app ptsq_app. iFrame.
  - iSplit; [done|iExact "Herr"].
Qed.
End literal.
