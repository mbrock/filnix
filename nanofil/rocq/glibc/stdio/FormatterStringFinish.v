(** When a format ends with a string conversion, glibc copies the
    argument into its buffer, reads the format's terminating zero and
    returns. This proof follows those operations after the letter s
    has been read. The caller keeps permission to read both strings.

    The argument must be nonempty and fit in the remaining staging
    window. The caller supplies the table contents, function lookups
    and saved format pointer. Earlier percent parsing, registration
    initialization, FILE flushing and startup are not covered. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps FormatterCode
  Fix WordString PrintfBufferIoCode MemFwdCode MemFwdLogic PrintfStagingCopy
  FormatterStringRead FormatterStringTable FormatterStringDispatch FormatterStringLength
  FormatterStringWrite FormatterSuffixWrite StrlenLogic StrchrCode FormatterScan.
Import ReadVL ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Section finish.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** Even an empty suffix needs a readable terminating zero. The caller
    supplies that memory separately from the argument string and keeps
    both after the call. The result also records the copied bytes and
    advances the saved argument pointer to the next argument. *)
Lemma wp_formatter_final_string e from jb jr tb tr dqj dqt p9 p4
    cb cr sb sr off p dq s fb fr fp dqf bb br bo xs cs n count Φ :
  lookup (TAtom "v111") e = Some (WInt 115) ->
  lookup (TAtom "pr.9") e = Some (WPtr p9) ->
  lookup (TAtom "pr.4") e = Some (WPtr p4) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v55") e = Some (WInt 0) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "pr.16") e = Some (WInt n) ->
  lookup (TAtom "pr.11") e = Some (WInt count) ->
  lookup (TAtom "glibc_vfprintf_internal#jump_table") (ge_globals ge) = Some (mkPtr jb (Ro jb)) ->
  lookup (TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") (ge_globals ge) =
    Some (mkPtr tb (Ro tb)) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined glibc___printf_buffer_write) ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy) ->
  0 < jb -> jb + 84 <= r_end jr -> r_end jr <= 2^63 ->
  0 < tb -> tb + 88 <= r_end tr -> r_end tr <= 2^63 ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr ->
  r_end sr <= 2^48 -> (sb + off) mod 8 = 0 -> 0 < ptr_addr p < 2^64 ->
  0 < fb -> fb mod 8 = 0 -> fb + 8 <= r_end fr -> r_end fr <= 2^63 ->
  0 < ptr_addr fp < 2^63 ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end br -> r_end br <= 2^63 ->
  48 <= bo -> 0 < Z.of_nat (length s) -> bo + Z.of_nat (length s) <= 176 ->
  length xs = 128%nat -> length cs = length xs -> Forall (fun x => 0 <= x < 256) xs ->
  liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗ liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
  pts (va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))) -∗
  live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
  live fb fr -∗ pcell fb 0 (mkPtr (ptr_addr fp - 1) (ptr_cap fp)) -∗ word_string dqf fp [] -∗
  live bb br -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + bo) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ bytes bb 48 xs -∗ auxes bb 48 cs -∗
  ▷ (liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗ liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
    pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗
    live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
    live fb fr -∗ pcell fb 0 (ptr_add fp 0) -∗ word_string dqf fp [] -∗
    live bb br -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + bo + Z.of_nat (length s)) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ window_after bb 48 xs bo s -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_printf_buffer e [] None (Enter (TAtom "L113") from)) : gexpr) {{ Φ }}.
Proof.
  intros Hs H9 H4 Hv Hz Hfv Hfc Hb Hn Hcount Hj Ht Hstrlen Hchr Hscan Hwrite Hcpy
    Hjb Hje Hjr Htb Hte Htr Hcb Hsb Ho He Hr Ha Hp Hfb Hfa Hfe Hfr Hfp
    Hbb Hba Hbe Hbr Hbo Hlen Hroom Hxs Hcs Hbytes.
  iIntros "Hjl Hjb Htl Htb Hc Hsl Hsp Hs Hfl Hfc Hfs Hl Hmode Hptr Hend Hx Hcs HK".
  iApply (wp_formatter_table_string_read e [] from jb jr tb tr dqj dqt p9 p4 cb cr sb sr off p dq s
    with "Hjl Hjb Htl Htb Hc Hsl Hsp Hs"); try assumption.
  iNext. iIntros "Hjl Hjb Htl Htb Hc Hsl Hsp Hs".
  iApply (wp_formatter_string_write Hmove Hmove_fn Hmove_sym _ [] bb br bo xs cs dq p s
    with "Hl Hmode Hptr Hend Hx Hcs Hs"); try assumption.
  - unfold string_length_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_length_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_length_env, string_dispatch_env, string_table_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_length_env, string_dispatch_env, string_table_env. cbn [fold_left fst snd]. lookups; done.
  - iNext. iIntros "Hl Hmode Hptr Hend Hx Hs".
    iApply (wp_formatter_suffix_empty _ fb fr bb br dqf fp n count
      with "Hfl Hfc Hfs Hl Hmode"); try assumption.
    + unfold string_write_env, string_length_env, string_dispatch_env, string_table_env.
      cbn [fold_left fst snd]. lookups; done.
    + unfold string_write_env, string_length_env, string_dispatch_env, string_table_env.
      cbn [fold_left fst snd]. lookups; done.
    + unfold string_write_env, string_length_env, string_dispatch_env, string_table_env.
      cbn [fold_left fst snd]. lookups; done.
    + unfold string_write_env, string_length_env, string_dispatch_env, string_table_env.
      cbn [fold_left fst snd]. lookups; done.
    + unfold string_write_env, string_length_env, string_dispatch_env, string_table_env.
      cbn [fold_left fst snd]. lookups; done.
    + lia.
    + iNext. iIntros "Hfl Hfc Hfs Hl Hmode".
      iApply ("HK" with "Hjl Hjb Htl Htb Hc Hsl Hsp Hs Hfl Hfc Hfs Hl Hmode Hptr Hend Hx").
Qed.
End finish.
