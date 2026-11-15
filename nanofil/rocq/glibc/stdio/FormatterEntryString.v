(** With format "%s", glibc copies the argument string into its formatting
    buffer. This proof follows that operation from the call to its return,
    including temporary allocation and the initial scan. The caller keeps
    errno and permission to read both strings.

    The argument must be nonempty and fit the remaining buffer space.
    The caller supplies three null pointers showing that no custom
    conversions are registered, plus the function definitions used by
    the call. Initialization and writing the buffer to a FILE remain
    outside this rule. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps FormatterCode
  Fix WordString PrintfBufferIoCode MemFwdCode MemFwdLogic PrintfStagingCopy
  FormatterLiteral FormatterInitialScan FormatterStringRead FormatterStringJoin
  StrlenLogic StrchrCode FormatterScan.
From Glibc Require Import FormatterEntry.
Import ReadVL ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Section entry_string.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** Returning from a function must invalidate its stack objects, if it
    has any. The captured formatter allocates its temporary storage on
    the heap instead. Its stack-object list stays empty throughout
    this call. *)
Lemma wp_printf_buffer_final_string fr bb br bo xs cs fp dqf
    ab ar sb sr off p dq s eb er err flags rb rr mb mr gb gr jb jr tb tr dqj dqt Φ :
  call_frame glibc_printf_buffer
    [WPtr (mkPtr bb (Obj bb)); WPtr fp; WPtr (mkPtr ab (Obj ab)); WInt flags] = Some fr ->
  (dqf = DfracDiscarded \/ exists q, dqf = DfracOwn q) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "__printf_function_table") (ge_globals ge) = Some (mkPtr rb (Obj rb)) ->
  lookup (TAtom "__printf_modifier_table") (ge_globals ge) = Some (mkPtr mb (Obj mb)) ->
  lookup (TAtom "__printf_va_arg_table") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  lookup (TAtom "glibc_vfprintf_internal#jump_table") (ge_globals ge) = Some (mkPtr jb (Ro jb)) ->
  lookup (TAtom "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined glibc___printf_buffer_write) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed") = Some (Defined glibc_format_failed) ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy) ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end br -> r_end br <= 2^63 ->
  48 <= bo -> 0 < Z.of_nat (length s) -> bo + Z.of_nat (length s) <= 176 ->
  length xs = 128%nat -> length cs = length xs -> Forall (fun x => 0 <= x < 256) xs ->
  0 < ab -> ab mod 8 = 0 -> ab + 8 <= r_end ar -> r_end ar <= 2^63 ->
  0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr -> r_end sr <= 2^48 ->
  (sb + off) mod 8 = 0 -> 0 < ptr_addr p < 2^64 ->
  0 < eb -> eb + 4 <= r_end er -> r_end er <= 2^63 ->
  0 < rb -> rb mod 8 = 0 -> rb + 8 <= r_end rr -> r_end rr <= 2^63 ->
  0 < mb -> mb mod 8 = 0 -> mb + 8 <= r_end mr -> r_end mr <= 2^63 ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end gr -> r_end gr <= 2^63 ->
  0 < jb -> jb + 84 <= r_end jr -> r_end jr <= 2^63 ->
  0 < tb -> tb + 88 <= r_end tr -> r_end tr <= 2^63 ->
  pts (va_cursor_ps ab ar (mkPtr (sb+off) (Ro sb))) -∗
  live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗ word_string dqf fp [37;115] -∗
  live eb er -∗ int_cell eb 0 err -∗
  live rb rr -∗ pcell rb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗ live gb gr -∗ pcell gb 0 null -∗
  liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗ liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
  live bb br -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb+bo) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb+176) (Obj bb)) -∗ bytes bb 48 xs -∗ auxes bb 48 cs -∗
  ▷ (pts (va_cursor_ps ab ar (mkPtr (sb+off+8) (Ro sb))) -∗
    live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗ word_string dqf fp [37;115] -∗
    live eb er -∗ int_cell eb 0 err -∗
    live rb rr -∗ pcell rb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗ live gb gr -∗ pcell gb 0 null -∗
    liveq dqj jb jr -∗ bytesq dqj jb 83 [21] -∗ liveq dqt tb tr -∗ bytesq dqt tb 84 [21;0;0;0] -∗
    live bb br -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb+bo+Z.of_nat (length s)) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb+176) (Obj bb)) -∗ window_after bb 48 xs bo s -∗ Φ RetVoid) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof.
  intros Hfr Hshare Herr Hrf Hmf Hgf Hj Ht Hstrlen Hchr Hscan Hwrite Hfailed Hcpy
    Hbb Hba Hbe Hbr Hbo Hlen Hroom Hxs Hcs Hbytes Hab Haa Hae Har
    Hsb Ho He Hr Ha Hp Heb Hee Her Hrb Hra Hre Hrr Hmb Hma Hme Hmr
    Hgb Hga Hge Hgr Hjb Hje Hjr Htb Hte Htr.
  iIntros "Hc Hsl Hsp Hs Hfs Hel Herr Hrl Hrc Hml Hmc Hgl Hgc Hjl Hjb Htl Htb Hl Hmode Hptr Hend Hx Hcs HK".
  iDestruct (pts_app [(PLive ab, VLive ar)]
    ((PAux ab 0, VAux (Ro sb)) :: cell ab 0 (sb+off)) with "Hc") as "[Hal Hap]".
  iApply (wp_formatter_entry fr (mkPtr bb (Obj bb)) fp ab ar flags sb sr (sb+off) eb er err
    with "Hal Hap Hsl Hel Herr"); try assumption; [lia|].
  iNext. iIntros (e fb wb vb [Hinputs [Hfb [Hfa [Hfe [Hwb [Hwe Hvb]]]]]])
    "Hal Hap Hsl Hel Herr Hfl Hfc Hwork Hvl Hvc".
  destruct Hinputs as (Hv0 & Hv2 & Hv4 & Hv6 & Hv10 & Hv13 & Hv15 & Hv23).
  iApply (wp_formatter_initial_scan e [] fb (mkRegion fb (fb+16) Heap Live) null bb br fp dqf
    with "Hfl Hfc Hfs Hl Hmode"); try assumption; try (cbn; lia).
  iNext. iIntros "Hfl Hfc Hfs Hl Hmode".
  iAssert (pts (va_cursor_ps ab ar (mkPtr (sb+off) (Ro sb)))) with "[Hal Hap]" as "Hc".
  { iApply (pts_app [(PLive ab, VLive ar)]
      ((PAux ab 0, VAux (Ro sb)) :: cell ab 0 (sb+off))). iFrame. }
  iApply (wp_formatter_registered_final_string Hmove Hmove_fn Hmove_sym _ (Some (TAtom "L37"))
    rb rr mb mr gb gr jb jr tb tr dqj dqt ab ar sb sr off p dq s
    fb (mkRegion fb (fb+16) Heap Live) fp dqf wb (mkPtr (2^64-1) CNone) bb br bo xs cs
    with "Hrl Hrc Hml Hmc Hgl Hgc Hjl Hjb Htl Htb Hc Hsl Hsp Hs Hfl Hfc Hfs Hl Hmode Hptr Hend Hx Hcs");
    try assumption; try (cbn; lia).
  all: try (unfold initial_percent_env, initial_scan_env; cbn [fold_left fst snd]; lookups; done).
  iNext. iIntros "Hrl Hrc Hml Hmc Hgl Hgc Hjl Hjb Htl Htb Hc Hsl Hsp Hs Hfl Hfc Hfs Hl Hmode Hptr Hend Hx".
  iApply ("HK" with "Hc Hsl Hsp Hs Hfs Hel Herr Hrl Hrc Hml Hmc Hgl Hgc Hjl Hjb Htl Htb Hl Hmode Hptr Hend Hx").
Qed.
End entry_string.
