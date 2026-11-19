(** To print a string, glibc must choose its string handler and read the
    next pointer argument. This proof joins the two table reads to that
    choice and argument read. It preserves the tables and argument memory
    while advancing the caller's cursor.

    A string argument must be selected before it can be printed. This
    proof covers that selection after glibc has read the letter s from
    the format. It does not cover reading or printing the string, flushing
    the output stream, or initializing the formatter's global variables. *)
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld FileInv LibioLogic Fix
  FormatterStringTable FormatterStringArg.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic.
Import StringVL.
Open Scope Z_scope.

(** The initial dispatch sets the default width and precision and carries
    the earlier format pointers into the handler. This environment records
    those updates and the comparisons made by the dispatch tree. *)
Definition string_dispatch_env e p9 p4 :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "v138", WInt 21); (TAtom "v139", WInt 21); (TAtom "v140", WInt 21);
     (TAtom "v141", WPtr (mkPtr 22 CNone)); (TAtom "v143", WInt 22);
     (TAtom "pr.98", WInt 22); (TAtom "pr.97", WInt 115); (TAtom "pr.92", WInt 32);
     (TAtom "pr.88", WInt 0); (TAtom "pr.82", WInt 4294967295); (TAtom "pr.66", WInt 0);
     (TAtom "pr.65", WInt 0); (TAtom "pr.62", WInt 0); (TAtom "pr.60", WInt 0);
     (TAtom "pr.57", WInt 0); (TAtom "pr.55", WInt 0); (TAtom "pr.52", WInt 0);
     (TAtom "pr.47", WInt 0); (TAtom "pr.46", WInt 0); (TAtom "pr.42", WInt 0);
     (TAtom "pr.5", WPtr p9); (TAtom "pr.1", WPtr p4);
     (TAtom "v2147", WInt 0); (TAtom "v2191", WInt 1); (TAtom "v2194", WInt 0);
     (TAtom "v2205", WInt 0); (TAtom "v2207", WInt 1)] e.

Section dispatch.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Glibc chooses the string handler by adding one to the table result
    and comparing it with other possible targets. This rule follows those
    comparisons until the program is ready to read the pointer argument. *)
Lemma wp_formatter_string_dispatch e ls p9 p4 Φ :
  lookup (TAtom "v137") e = Some (WInt 21) ->
  lookup (TAtom "v111") e = Some (WInt 115) ->
  lookup (TAtom "pr.9") e = Some (WPtr p9) ->
  lookup (TAtom "pr.4") e = Some (WPtr p4) ->
  ▷ WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (string_dispatch_env e p9 p4) ls None
    (Enter (TAtom "L1825") (Some (TAtom "L2206")))) : gexpr) {{ Φ }} -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L114") (Some (TAtom "L113")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hr Hs H9 H4. iIntros "HK".
  iApply wp_enter; [reflexivity | vx |]. iNext.
  cbn [b_insts b_jump]. do 4 step. closed_ints. step. step.
  step. closed_ints. branch. step.
  step. closed_ints. branch. step.
  step. closed_ints. branch. step.
  step. closed_ints. branch. step.
  step. closed_ints. branch.
  norm. iExact "HK".
Qed.

(** Printing a string requires a pointer from the caller's argument list.
    This rule follows the table reads and handler selection to obtain that
    pointer with its authority. It preserves the argument memory and
    advances the cursor by eight bytes, but does not print the string. *)
Lemma wp_formatter_table_string_arg e ls from jb jr tb tr dqj dqt p9 p4
    cb cr sb sr off x ps Φ :
  lookup (TAtom "v111") e = Some (WInt 115) ->
  lookup (TAtom "pr.9") e = Some (WPtr p9) ->
  lookup (TAtom "pr.4") e = Some (WPtr p4) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "glibc_vfprintf_internal#jump_table") (ge_globals ge) = Some (mkPtr jb (Ro jb)) ->
  lookup (TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") (ge_globals ge) =
    Some (mkPtr tb (Ro tb)) ->
  0 < jb -> jb + 84 <= r_end jr -> r_end jr <= 2 ^ 63 ->
  0 < tb -> tb + 88 <= r_end tr -> r_end tr <= 2 ^ 63 ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr ->
  r_end sr <= 2 ^ 48 -> (sb + off) mod 8 = 0 -> 0 <= ptr_addr x < 2 ^ 64 ->
  (ptr_cap x = CNone \/ exists xb xr,
    (ptr_cap x = Obj xb \/ ptr_cap x = Ro xb) /\ (PLive xb, VLive xr) ∈ ps) ->
  liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗
  liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
  pts (va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))) -∗
  live sb sr -∗ pcell sb off x -∗ pts ps -∗
  ▷ (liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗
    liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
    pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗
    live sb sr -∗ pcell sb off x -∗ pts ps -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
      (put (TAtom "v1828") (WPtr x) (string_dispatch_env (string_table_env e jb tb) p9 p4)) ls None
      (Enter (TAtom "L1695") (Some (TAtom "L1825")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L113") from)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hs H9 H4 Hv Hj Ht Hjb Hje Hjr Htb Hte Htr Hcb Hsb Ho He Hr Ha Hx Htarget.
  iIntros "Hjl Hjb Htl Htb Hc Hl Hx Hps HK".
  iApply (wp_formatter_string_table with "Hjl Hjb Htl Htb"); try assumption.
  iNext. iIntros "Hjl Hjb Htl Htb".
  iApply wp_formatter_string_dispatch.
  - unfold string_table_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_table_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_table_env. cbn [fold_left fst snd]. lookups; done.
  - unfold string_table_env. cbn [fold_left fst snd]. lookups; done.
  - iNext. iApply (wp_formatter_string_arg with "Hc Hl Hx Hps"); try assumption.
    + unfold string_dispatch_env, string_table_env. cbn [fold_left fst snd]. lookups; done.
    + iNext. iIntros "Hc Hl Hx Hps".
      iApply ("HK" with "Hjl Hjb Htl Htb Hc Hl Hx Hps").
Qed.
End dispatch.
