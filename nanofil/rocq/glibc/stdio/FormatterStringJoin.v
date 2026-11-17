(** Glibc must leave the format string unchanged while printing its
    argument. This proof follows a final string conversion from the
    checks for custom conversions through the buffer write and return.
    The caller retains the same permission to read the original format.

    This result covers nonempty arguments that fit in the buffer when
    no custom conversions are registered. It assumes that earlier code
    has found the percent sign. It does not prove program initialization
    or writing the buffer to a file. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From iris.bi Require Import fractional.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps FormatterCode
  Fix WordString PrintfBufferIoCode MemFwdCode MemFwdLogic PrintfStagingCopy
  FormatterStringRead FormatterRegistration StrlenLogic StrchrCode FormatterScan.
From Glibc Require Import FormatterPercentString FormatterStringFinish.
Import ReadVL ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Section join.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** Lending the final zero keeps enough of an owned format behind to
    recover all its original bytes. Persistent read-only formats can
    instead retain their original ownership while lending the suffix. *)
Lemma final_format_tail dq p :
  (dq = DfracDiscarded \/ exists q, dq = DfracOwn q) ->
  word_string dq p [37;115] -∗
  ∃ dt, word_string dt (ptr_add p 2) [] ∗
    (word_string dt (ptr_add p 2) [] -∗ word_string dq p [37;115]).
Proof using Type.
  intros [-> | [q ->]].
  - iIntros "#Hs". iExists DfracDiscarded. iSplit.
    + iApply (word_string_suffix DfracDiscarded p [37;115] [] with "Hs").
    + iIntros "_". iExact "Hs".
  - iIntros "Hs".
    iDestruct (word_string_borrow (q/2) (q/2) p [37;115] [] with "[Hs]") as "[Htail Hback]".
    { rewrite Qp.div_2. iExact "Hs". }
    iExists (DfracOwn (q/2)). iFrame "Htail".
    iIntros "Htail". iSpecialize ("Hback" with "Htail").
    iEval (rewrite Qp.div_2) in "Hback". iExact "Hback".
Qed.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
(** The joined rule starts at the registration checks and returns after
    printing one final string argument. The caller recovers the original
    format share rather than only its empty tail. *)
Lemma wp_formatter_registered_final_string e from rb rr mb mr ab ar
    jb jr tb tr dqj dqt cb cr sb sr off p dq s fb fr fp dqf wb p9 bb br bo xs cs Φ :
  (dqf = DfracDiscarded \/ exists q, dqf = DfracOwn q) ->
  lookup (TAtom "__printf_function_table") (ge_globals ge) = Some (mkPtr rb (Obj rb)) ->
  lookup (TAtom "__printf_modifier_table") (ge_globals ge) = Some (mkPtr mb (Obj mb)) ->
  lookup (TAtom "__printf_va_arg_table") (ge_globals ge) = Some (mkPtr ab (Obj ab)) ->
  lookup (TAtom "v23") e = Some (WPtr p9) ->
  lookup (TAtom "v13") e = Some (WPtr (mkPtr wb (Obj wb))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "glibc_vfprintf_internal#jump_table") (ge_globals ge) = Some (mkPtr jb (Ro jb)) ->
  lookup (TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined glibc___printf_buffer_write) ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy) ->
  0 < rb -> rb mod 8 = 0 -> rb + 8 <= r_end rr -> r_end rr <= 2^63 ->
  0 < mb -> mb mod 8 = 0 -> mb + 8 <= r_end mr -> r_end mr <= 2^63 ->
  0 < ab -> ab mod 8 = 0 -> ab + 8 <= r_end ar -> r_end ar <= 2^63 ->
  0 < jb -> jb + 84 <= r_end jr -> r_end jr <= 2^63 ->
  0 < tb -> tb + 88 <= r_end tr -> r_end tr <= 2^63 ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr ->
  r_end sr <= 2^48 -> (sb + off) mod 8 = 0 -> 0 < ptr_addr p < 2^64 ->
  0 < fb -> fb mod 8 = 0 -> fb + 8 <= r_end fr -> r_end fr <= 2^63 ->
  0 <= wb -> wb + 1000 < 2^64 ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end br -> r_end br <= 2^63 ->
  48 <= bo -> 0 < Z.of_nat (length s) -> bo + Z.of_nat (length s) <= 176 ->
  length xs = 128%nat -> length cs = length xs -> Forall (fun x => 0 <= x < 256) xs ->
  live rb rr -∗ pcell rb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗ live ab ar -∗ pcell ab 0 null -∗
  liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗ liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
  pts (va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))) -∗ live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
  live fb fr -∗ pcell fb 0 fp -∗ word_string dqf fp [37;115] -∗
  live bb br -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + bo) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ bytes bb 48 xs -∗ auxes bb 48 cs -∗
  ▷ (live rb rr -∗ pcell rb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗ live ab ar -∗ pcell ab 0 null -∗
    liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗ liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
    pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗ live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
    live fb fr -∗ pcell fb 0 (ptr_add fp 2) -∗ word_string dqf fp [37;115] -∗
    live bb br -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + bo + Z.of_nat (length s)) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ window_after bb 48 xs bo s -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_printf_buffer e [] None (Enter (TAtom "L44") from)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hshare Hrf Hmf Haf H9 Hw Hv Hfv Hfc Hb Hj Ht Hstrlen Hchr Hscan Hwrite Hcpy
    Hrb Hra Hre Hrr Hmb Hma Hme Hmr Hab Haa Hae Har Hjb Hje Hjr Htb Hte Htr
    Hcb Hsb Ho He Hr Ha Hp Hfb Hfa Hfe Hfr Hwb Hwe Hbb Hba Hbe Hbr Hbo Hlen Hroom Hxs Hcs Hbytes.
  iIntros "Hrl Hrc Hml Hmc Hal Hac Hjl Hjb Htl Htb Hc Hsl Hsp Hs Hfl Hfc Hfs Hl Hmode Hptr Hend Hx Hcs HK".
  iDestruct "Hfs" as (b r ws) "[%Hshape Hwindow]".
  pose proof Hshape as [Hcap Hbase Halign Hstart Hfit Hspace Hlength Hwords Hencoding Hchars].
  assert (Hfp : 0 < ptr_addr (ptr_add fp 2) < 2^63).
  { unfold wstart in Hfit. cbn [length] in Hlength. cbn [ptr_add ptr_addr].
    pose proof (Z.div_mod (ptr_addr fp mod 8 + 2 + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr fp mod 8 + 2 + 8) 8 ltac:(lia)). lia. }
  iAssert (word_string dqf fp [37;115]) with "[Hwindow]" as "Hfs".
  { iExists b, r, ws. iSplit; [done|iExact "Hwindow"]. }
  iApply (wp_formatter_registered_string e [] from rb rr mb mr ab ar fb fr wb p9 fp dqf
    with "Hrl Hrc Hml Hmc Hal Hac Hfl Hfc Hfs"); try assumption.
  iNext. iIntros "Hrl Hrc Hml Hmc Hal Hac Hfl Hfc Hfs".
  iDestruct (final_format_tail with "Hfs") as (dt) "[Htail Hback]"; [exact Hshare|].
  assert (Hbefore : mkPtr (ptr_addr (ptr_add fp 2) - 1) (ptr_cap (ptr_add fp 2)) = ptr_add fp 1).
  { destruct fp. unfold ptr_add. cbn. f_equal. lia. }
  iEval (rewrite -Hbefore) in "Hfc".
  iApply (wp_formatter_final_string Hmove Hmove_fn Hmove_sym _ _ jb jr tb tr dqj dqt p9 null
    cb cr sb sr off p dq s fb fr (ptr_add fp 2) dt bb br bo xs cs 0 0
    with "Hjl Hjb Htl Htb Hc Hsl Hsp Hs Hfl Hfc Htail Hl Hmode Hptr Hend Hx Hcs"); try assumption.
  all: try (unfold percent_string_env, registration_env; cbn [fold_left fst snd]; lookups; done).
  iNext. iIntros "Hjl Hjb Htl Htb Hc Hsl Hsp Hs Hfl Hfc Htail Hl Hmode Hptr Hend Hx".
  iDestruct ("Hback" with "Htail") as "Hfs".
  replace (ptr_add (ptr_add fp 2) 0) with (ptr_add fp 2) by (destruct fp; unfold ptr_add; cbn; f_equal; lia).
  iApply ("HK" with "Hrl Hrc Hml Hmc Hal Hac Hjl Hjb Htl Htb Hc Hsl Hsp Hs Hfl Hfc Hfs Hl Hmode Hptr Hend Hx").
Qed.
End join.
