(** Glibc can read a string argument without taking exclusive ownership
    of its contents. This proof lends the string's existing lifetime share
    to the variadic read and restores it before measuring the string.
    The same argument works for fractional and discarded shares.

    A string conversion selects an argument and measures it before
    writing any output. This rule covers those steps after glibc has
    read the letter s from the format. Earlier scanning, output writes,
    and initialization of the required memory remain separate work. *)
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld FileInv LibioLogic Fix WordString
  FormatterStringTable FormatterStringDispatch FormatterStringLength StrlenLogic.
(** The variadic rule uses the same heap and runtime as the formatter. *)
Module ReadVL := VariadicLogicOn R LG0.
Import ReadVL ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic.
Open Scope Z_scope.
Section read.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** Reading the argument lends only the lifetime already inside the
    string ownership. The returned pointer keeps its capability, and
    the caller recovers the same string share and advanced cursor. *)
Lemma wp_formatter_string_arg_word e ls from cb cr sb sr off p dq s Φ :
  lookup (TAtom "v4") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr ->
  r_end sr <= 2 ^ 48 -> (sb + off) mod 8 = 0 -> 0 <= ptr_addr p < 2 ^ 64 ->
  pts (va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))) -∗
  live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
  ▷ (pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗
    live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (put (TAtom "v1828") (WPtr p) e) ls None
      (Enter (TAtom "L1695") (Some (TAtom "L1825")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L1825") from)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv Hcb Hsb Ho He Hr Ha Hp.
  assert (Hwi : forall m w h,
    (forall k v, (k, v) ∈ va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb)) -> h !! k = Some v) ->
    os_wi w0 m w h -> os_wi w0 (store_bytes m cb 8 (sb + off + 8)) w
      (overwrite (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) h)).
  { intros m w h Hown Hw. eapply os_wi_store; [reflexivity | | exact Hw].
    intros k v Hin. destruct k; try done.
    apply Hown. unfold va_cursor_ps, cell in *. simpl in *. set_solver. }
  iIntros "Hc Hl Hx Hs HK".
  iDestruct "Hs" as (b reg ws) "[%Hshape [Htarget Hwords]]".
  iApply wp_enter; [reflexivity | destruct from; reflexivity |]. iNext.
  iApply (wp_va_arg_pointer_shared with "Hc Hl Hx Htarget");
    [vx | exact Hcb | exact Hsb | exact Ho | exact He | exact Hr |
     exact Ha | exact Hp | | exact Hwi |].
  { right. exists b, reg. split; [exact (ss_cap _ _ _ _ _ Hshape)|]. by left. }
  iNext. iIntros "Hc Hl Hx Htarget". iApply wp_goto. iNext.
  iApply ("HK" with "Hc Hl Hx [Htarget Hwords]").
  iExists b, reg, ws. iSplit; [done|]. iFrame.
Qed.

(** Glibc first chooses the string handler, then reads the pointer and
    measures the string. This composition preserves the table shares,
    snapshot and string share while advancing the cursor by eight bytes. *)
Lemma wp_formatter_table_string_read e ls from jb jr tb tr dqj dqt p9 p4
    cb cr sb sr off p dq s Φ :
  lookup (TAtom "v111") e = Some (WInt 115) ->
  lookup (TAtom "pr.9") e = Some (WPtr p9) ->
  lookup (TAtom "pr.4") e = Some (WPtr p4) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v55") e = Some (WInt 0) ->
  lookup (TAtom "glibc_vfprintf_internal#jump_table") (ge_globals ge) = Some (mkPtr jb (Ro jb)) ->
  lookup (TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") (ge_globals ge) =
    Some (mkPtr tb (Ro tb)) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  0 < jb -> jb + 84 <= r_end jr -> r_end jr <= 2 ^ 63 ->
  0 < tb -> tb + 88 <= r_end tr -> r_end tr <= 2 ^ 63 ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr ->
  r_end sr <= 2 ^ 48 -> (sb + off) mod 8 = 0 -> 0 < ptr_addr p < 2 ^ 64 ->
  liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗
  liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
  pts (va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))) -∗
  live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
  ▷ (liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗
    liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
    pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗
    live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
      (string_length_env (put (TAtom "v1828") (WPtr p)
        (string_dispatch_env (string_table_env e jb tb) p9 p4)) p (Z.of_nat (length s))) ls None
      (Enter (TAtom "L1831") (Some (TAtom "L1871")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L113") from)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hs H9 H4 Hv Hzero Hj Ht Hstrlen Hjb Hje Hjr Htb Hte Htr
    Hcb Hsb Ho He Hr Ha Hp.
  iIntros "Hjl Hjb Htl Htb Hc Hl Hx Hs HK".
  iApply (wp_formatter_string_table with "Hjl Hjb Htl Htb"); try assumption.
  iNext. iIntros "Hjl Hjb Htl Htb".
  iApply wp_formatter_string_dispatch.
  - unfold string_table_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_table_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_table_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_table_env. cbn [fold_left fst snd]. lookups; done.
  - iNext. iApply (wp_formatter_string_arg_word with "Hc Hl Hx Hs"); try assumption.
    + unfold string_dispatch_env, string_table_env. cbn [fold_left fst snd]. lookups; done.
    + lia.
    + iNext. iIntros "Hc Hl Hx Hs".
      iApply (wp_formatter_string_length with "Hs"); try assumption.
      * lookups; done.
      * unfold string_dispatch_env, string_table_env. cbn [fold_left fst snd]. lookups; done.
      * unfold string_dispatch_env, string_table_env. cbn [fold_left fst snd]. lookups; done.
      * unfold string_dispatch_env, string_table_env. cbn [fold_left fst snd]. lookups; done.
      * unfold string_dispatch_env, string_table_env. cbn [fold_left fst snd]. lookups; done.
      * iNext. iIntros "Hs". iApply ("HK" with "Hjl Hjb Htl Htb Hc Hl Hx Hs").
Qed.
End read.
