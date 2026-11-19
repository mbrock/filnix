(** After a conversion, the formatter scans and writes the remaining
    literal text before returning. These rules compose those captured
    operations for empty suffixes and nonempty suffixes that fit in
    staging memory. They preserve the source's original ownership share.
    A suffix containing another percent sign requires further formatting
    and does not meet the final-return rule's scan premise.
    FILE flushing, registration initialization and startup remain outside
    these contracts. *)
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_write_os Unit_stdioZ2dcommon_vfprintfZ2dinternal_os Unit_string_memcpy_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  Fix WordString MemFwdLogic PrintfStagingCopy FormatterLiteralWrite
  StrchrnulLogic FormatterScan.
From Glibc Require Import FormatterSuffixScan FormatterSuffixReturn.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Section suffix.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A supplied write contract connects the scanned pointer to the
    final NUL read. The concrete rules below discharge this contract
    using the captured buffer writer rather than assuming write success. *)
Lemma wp_formatter_suffix_call e cb cr bb dq p s (P Q : iProp Σ) Φ :
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v2115") e = Some (WPtr p) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write) ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  (forall fr Ψ, call_frame Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write
    [WPtr (mkPtr bb (Obj bb)); WPtr p; WInt (Z.of_nat (length s))] = Some fr ->
    P -∗ word_string dq p s -∗ ▷ (Q -∗ word_string dq p s -∗ Ψ RetVoid) -∗
    WP (ERun fr : gexpr) {{ Ψ }}) ->
  live cb cr -∗ pcell cb 0 (ptr_add p (Z.of_nat (length s))) -∗ word_string dq p s -∗ P -∗
  ▷ (live cb cr -∗ pcell cb 0 (ptr_add p (Z.of_nat (length s))) -∗
    word_string dq p s -∗ Q -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e [] None
    (Exec (TAtom "L1150") (skipn 9 (b_insts suffix_block)) (b_jump suffix_block))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv Hchk Hp Hb Hwrite Hcb Hca Hce Hcr Hcall. iIntros "Hl Hcell Hs HP HK".
  iDestruct "Hs" as (sb sr ws) "[%Hshape [Hsl Hwords]]".
  pose proof Hshape as [Hcap Hsb Hsa Hst Hfit Hspace Hlen Hws Hbytes Hchars].
  assert (Hpend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end sr).
  { unfold wstart in Hfit. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iAssert (live_capq dq (ptr_cap p) sr) with "[Hsl]" as "Hsl".
  { destruct Hcap as [-> | ->]; iExact "Hsl". }
  cbn [skipn b_insts b_jump suffix_block]. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hcell Hsl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hl Hcell Hsl".
  iAssert (liveq dq sb sr) with "[Hsl]" as "Hsl".
  { destruct Hcap as [Hc | Hc]; iEval (cbn [ptr_cap]; rewrite Hc) in "Hsl"; iExact "Hsl". }
  iAssert (word_string dq p s) with "[Hsl Hwords]" as "Hs".
  { iExists sb, sr, ws. iSplit; [done|iFrame]. }
  do 3 step. norm.
  iApply wp_call_bind; [vx | exact Hwrite | reflexivity |]. iNext.
  iApply (wp_wand with "[HP Hs]").
  { iApply (Hcall _ (fun v => ⌜v = RetVoid⌝ ∗ Q ∗ word_string dq p s)%I with "HP Hs").
    - cbn. replace (ptr_addr p + Z.of_nat (length s) - ptr_addr p) with (Z.of_nat (length s)) by lia.
      rewrite Z.mod_small; [reflexivity|lia].
    - iNext. iIntros "HQ Hs". iFrame. done. }
  iIntros (v) "(-> & HQ & Hs)". resume.
  iApply (wp_formatter_suffix_return with "Hl Hcell Hs"); try assumption.
  - lookups; done.
  - lookups; done.
  - iNext. iIntros "Hl Hcell Hs". iApply ("HK" with "Hl Hcell Hs HQ").
Qed.
(** An empty suffix takes the actual zero-length write path. The rule
    needs the buffer mode but no staging bytes or output pointer fields. *)
Lemma wp_formatter_suffix_empty e cb cr bb br dq p n count Φ :
  lookup (TAtom "pr.16") e = Some (WInt n) ->
  lookup (TAtom "pr.11") e = Some (WInt count) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write) ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end br -> r_end br <= 2^63 ->
  0 < ptr_addr p < 2^63 ->
  live cb cr -∗ pcell cb 0 (mkPtr (ptr_addr p - 1) (ptr_cap p)) -∗ word_string dq p [] -∗
  live bb br -∗ int_cell bb 32 4 -∗
  ▷ (live cb cr -∗ pcell cb 0 (ptr_add p 0) -∗ word_string dq p [] -∗
    live bb br -∗ int_cell bb 32 4 -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e [] None
    (Enter (TAtom "L1150") (Some (TAtom "L1887")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hn Hcount Hv Hchk Hb Hchr Hscan Hwrite Hcb Hca Hce Hcr Hbb Hba Hbe Hbr Hp.
  iIntros "Hcl Hcell Hs Hl Hmode HK".
  iApply (wp_formatter_suffix_scan e [] cb cr p dq [] n count with "Hcl Hcell Hs"); try assumption.
  iNext. iIntros "Hcl Hcell Hs".
  iApply (wp_formatter_suffix_call _ cb cr bb dq p []
    (live bb br ∗ int_cell bb 32 4)%I (live bb br ∗ int_cell bb 32 4)%I
    with "Hcl Hcell Hs [Hl Hmode]"); try assumption.
  - unfold suffix_scan_env. cbn [fold_left fst snd]. lookups; done.
  - unfold suffix_scan_env. cbn [fold_left fst snd]. lookups; done.
  - unfold suffix_scan_env. cbn [fold_left fst snd]. lookups; done.
  - unfold suffix_scan_env. cbn [fold_left fst snd]. lookups; done.
  - intros fr Ψ Hfr. iIntros "[Hl Hmode] Hs HK".
    iApply (wp_printf_buffer_write_zero fr bb br p with "Hl Hmode"); try assumption.
    iNext. iIntros "Hl Hmode". iApply ("HK" with "[Hl Hmode] Hs"). iFrame.
  - iFrame.
  - iNext. iIntros "Hcl Hcell Hs [Hl Hmode]".
    iApply ("HK" with "Hcl Hcell Hs Hl Hmode").
Qed.
(** A nonempty final suffix must fit in the remaining staging window.
    The captured writer calls memcpy under its explicit external-move
    contract and returns the updated cursor and copied-window assertion.
    Exact fill is allowed; this path does not flush the filled buffer. *)
Lemma wp_formatter_suffix_literal e cb cr bb br off xs cs dq p s n count Φ :
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract OsWorld.os_world)) ->
  find_fn ge (TAtom "zmemmove") = None -> lookup (TAtom "zmemmove") (ge_globals ge) = None ->
  lookup (TAtom "pr.16") e = Some (WInt n) ->
  lookup (TAtom "pr.11") e = Some (WInt count) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write) ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined Unit_string_memcpy_os.fn___GI_memcpy) ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end br -> r_end br <= 2^63 ->
  0 < ptr_addr p < 2^63 -> chr_idx 37 s = length s ->
  48 <= off -> 0 < Z.of_nat (length s) -> off + Z.of_nat (length s) <= 176 ->
  length xs = 128%nat -> length cs = length xs -> Forall (fun x => 0 <= x < 256) xs ->
  live cb cr -∗ pcell cb 0 (mkPtr (ptr_addr p - 1) (ptr_cap p)) -∗ word_string dq p s -∗
  live bb br -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + off) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ bytes bb 48 xs -∗ auxes bb 48 cs -∗
  ▷ (live cb cr -∗ pcell cb 0 (ptr_add p (Z.of_nat (length s))) -∗ word_string dq p s -∗
    live bb br -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + off + Z.of_nat (length s)) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ window_after bb 48 xs off s -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e [] None
    (Enter (TAtom "L1150") (Some (TAtom "L1887")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hmove Hmf Hms Hn Hcount Hv Hchk Hb Hchr Hscan Hwrite Hcpy
    Hcb Hca Hce Hcr Hbb Hba Hbe Hbr Hp Hliteral Ho Hlen Hroom Hxs Hcs Hbytes.
  iIntros "Hcl Hcell Hs Hl Hmode Hptr Hend Hx Hcs HK".
  iApply (wp_formatter_suffix_scan e [] cb cr p dq s n count with "Hcl Hcell Hs"); try assumption.
  iNext. iIntros "Hcl Hcell Hs". rewrite Hliteral.
  iApply (wp_formatter_suffix_call _ cb cr bb dq p s
    (live bb br ∗ int_cell bb 32 4 ∗ pcell bb 8 (mkPtr (bb + off) (Obj bb)) ∗
      pcell bb 16 (mkPtr (bb + 176) (Obj bb)) ∗ bytes bb 48 xs ∗ auxes bb 48 cs)%I
    (live bb br ∗ int_cell bb 32 4 ∗ pcell bb 8 (mkPtr (bb + off + Z.of_nat (length s)) (Obj bb)) ∗
      pcell bb 16 (mkPtr (bb + 176) (Obj bb)) ∗ window_after bb 48 xs off s)%I
    with "Hcl Hcell Hs [Hl Hmode Hptr Hend Hx Hcs]"); try assumption.
  - unfold suffix_scan_env. cbn [fold_left fst snd]. lookups; done.
  - unfold suffix_scan_env. cbn [fold_left fst snd]. lookups; done.
  - unfold suffix_scan_env. cbn [fold_left fst snd]. lookups; done.
  - unfold suffix_scan_env. cbn [fold_left fst snd]. lookups; done.
  - intros fr Ψ Hfr. iIntros "(Hl & Hmode & Hptr & Hend & Hx & Hcs) Hs HK".
    iApply (wp_printf_buffer_write_word Hmove Hmf Hms fr bb br off xs cs dq p s
      with "Hl Hmode Hptr Hend Hx Hcs Hs"); try assumption.
    iNext. iIntros "Hl Hmode Hptr Hend Hx Hs".
    iApply ("HK" with "[Hl Hmode Hptr Hend Hx] Hs"). iFrame.
  - iFrame.
  - iNext. iIntros "Hcl Hcell Hs (Hl & Hmode & Hptr & Hend & Hx)".
    iApply ("HK" with "Hcl Hcell Hs Hl Hmode Hptr Hend Hx").
Qed.
End suffix.
