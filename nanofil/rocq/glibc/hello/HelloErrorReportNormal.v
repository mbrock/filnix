(** Hello's returning error call prints a default prefix, message, errno
    text and newline through the captured wrappers. This rule composes
    the closed-stdout entry with the narrow report rule.

    Printing can leave stderr oriented for wide characters. This proof
    only handles later calls that start in mode zero or UINT_MAX. Printing
    the prefix may violate that requirement, and the ENOMEM fallback does
    not repair a positive mode. Those paths cannot complete this proof. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  PrintfStateCode ErrorCode ErrorCall ErrorEntry ErrorText ErrorMessage ErrorReport
  FflushCode FileSyncCode HelloErrorClosed HelloErrorCall HelloErrorReturning
  FxprintfStream FxprintfNormalCode FxprintfNormalCall VfxprintfNarrow ErrorNewline
  ErrorTextPrint ErrorTextTailNormal ErrorPrefix HelloErrorPrefix ErrorReportNormal
  ErrorMessageNarrow ErrorMessageNormal Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic
  LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section returning.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (fb : Z) (freg : region) (vb lb : Z) (lbreg : region) (ob : Z) (oreg : region)
  (pb : Z) (preg : region) (callback : ptr) (dqc : dfrac) (cbr : region)
  (nb : Z) (nreg : region) (pname : ptr) (dqn : dfrac) (namer : region).
Let loan := error_stdout_loan fb freg ob oreg.
Let private := error_private_cells pb preg callback dqc cbr nb nreg pname dqn namer.
Context (Hreg : holds_os registry) (Hext : sys_external ge)
  (Hsync : ge_fn ge "_IO_new_file_sync" glibc__IO_new_file_sync).
Context (errnum : Z) (fmt : ptr) (ys : list word) (state : Z)
  (rsb : Z) (rsreg : region) (rfb : Z) (rfreg : region)
  (countb : Z) (countreg : region) (count : Z)
  (wide : ptr) (flushframe : frame) (strerrorfn widefn : func) (wideframe : frame)
  (eb : Z) (ereg : region) (fl rlb : Z) (rlreg : region)
  (md txb : Z) (txreg : region) (nlb : Z) (nlreg : region) (ssb : Z) (ssreg : region)
  (Ready P RP RM RT RN Q K : iProp Σ) (TQ NQ : Z -> Z -> iProp Σ) (U : Z -> Z -> Z -> iProp Σ).
Context (mmd fmtb : Z) (fmtreg : region) (dqf dqm : dfrac) (mchars : list Z)
  (vbreg : region) (sb : Z) (sreg : region).
Context (pmd pxb : Z) (pxreg : region) (nameb : Z) (dqb : dfrac) (chars : list Z)
  (PR : iProp Σ) (PQ : Z -> Z -> iProp Σ).
Let prefix := mkPtr pxb (Ro pxb).
Let stderr_loan := (live rsb rsreg ∗ pcell rsb 0 (mkPtr rfb (Obj rfb)) ∗ live rfb rfreg)%I.
Let prefix_fields := error_prefix_fields rfb fl rlb rlreg.
Let name := error_prefix_name pname nameb namer dqb chars.
Let kept := (error_closed_flush fb vb lb lbreg vbreg sb sreg K ∗ name)%I.
Let format_own := (live_capq dqf (ptr_cap fmt) fmtreg ∗
  bytesq dqm fmtb (ptr_addr fmt - fmtb) (mchars ++ [0]))%I.
Let message_ready := (single_ro ge ssb ssreg ∗ int_cell rfb 0 fl ∗ pcell rfb 136 (mkPtr rlb (Obj rlb)) ∗
  lock_state rlb rlreg 0 0 null ∗ int_cell rfb 192 mmd ∗ format_own ∗ RM)%I.
Let remaining r en m := (int_cell rfb 0 fl ∗ pcell rfb 136 (mkPtr rlb (Obj rlb)) ∗
  lock_state rlb rlreg 0 0 null ∗ error_message_spare rfb eb ereg r en m ∗ U r en m)%I.
Let fields := error_message_fields rfb fl rlb rlreg fmt fmtb fmtreg dqf dqm mchars eb ereg U.
Let newline := mkPtr nlb (Ro nlb).
Let textfmt := mkPtr txb (Ro txb).
Let R := error_text_newline_ready rfb fl rlb rlreg nlb nlreg ssb ssreg RN.
Let S := error_newline_done rfb fl rlb rlreg nlb nlreg NQ.
Let T := (single_ro ge ssb ssreg ∗ error_text_fields rfb fl rlb rlreg md txb txreg ∗ RT)%I.
Let RQ := error_text_done rfb fl rlb rlreg txb txreg TQ.
Let cursor ap := error_va ap (WInt 0 :: WInt errnum :: WPtr fmt :: ys).
Let returned := error_returned fb freg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer
  errnum fmt ys state rsb rsreg rfb (DfracOwn 1) rfreg countb countreg count error_borrowed_text
    (format_own ∗ Q)%I kept.

(** The prefix returns the existing stderr cell and full stream lifetime.
    Message handling supplies the fields for text without extracting that
    lifetime again. The final exchange prepares the newline without a call. *)
Context (Hpost : Ready ⊢ live countb countreg ∗ int_cell countb 0 count ∗
  live rsb rsreg ∗ pcell rsb 0 (mkPtr rfb (Obj rfb)) ∗ live rfb rfreg ∗ P ∗ kept)
  (Hentry : P ⊢ message_ready)
  (Hmmd : mmd = 0 \/ mmd = 2 ^ 32 - 1)
  (Hfmtr : 0 <= ptr_addr fmt < 2 ^ 64) (Hstring : StringLogic.string_ok fmt fmtb fmtreg mchars)
  (Herrno : error_errno_bounds eb ereg).
Context (Hgstderr : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr rsb (Obj rsb)))
  (Hrsb : 0 < rsb) (Hrsa : rsb mod 8 = 0) (Hrse : rsb + 8 <= r_end rsreg)
  (Hrsr : r_end rsreg <= 2 ^ 63)
  (Hrfb : 0 < rfb) (Hrfa : rfb mod 8 = 0) (Hrfe : rfb + 224 <= r_end rfreg) (Hrfr : r_end rfreg <= 2 ^ 63)
  (Huser : Z.land fl 32768 = 0) (Htxb : 0 <= txb < 2 ^ 64) (Hnlb : 0 <= nlb < 2 ^ 64)
  (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
  (Hself : ptr_addr (ow_self w0) <> 0) (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64)
  (Hcount : lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr countb (Obj countb)))
  (Hcountb : 0 < countb) (Hcounte : countb + 4 <= r_end countreg) (Hcountr : r_end countreg <= 2 ^ 63)
  (Hnewline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some newline)
  (Htext : lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some textfmt)
  (Hwide : lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide)
  (Hflushframe : call_frame glibc__IO_fflush [WPtr (mkPtr rfb (Obj rfb))] = Some flushframe)
  (Hstr : find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn))
  (Hvfx : find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf))
  (Hwidefn : find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn))
  (Hwideframe : call_frame widefn [WPtr wide;WPtr (mkPtr rfb (Obj rfb))] = Some wideframe).

(** Text and newline have separate argument snapshots and format resources.
    Their formatters may fail or mutate errno. The actual mode returned by
    the newline remains available to the open-stderr flush contract. *)
Context (Htextformat : forall b p ap, vfxprintf_formatter rfb rfreg fl rlb rlreg textfmt ap 0 md DfracDiscarded txreg
    (fun q => fx_va q [WPtr null;WPtr textfmt;WPtr p])
    (bytesq DfracDiscarded txb 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗ RT)%I
    (fun r => bytesq DfracDiscarded txb 0 [58;32;37;115;0] ∗ error_text_buffer error_borrowed_text b p ∗
      ∃ md', int_cell rfb 192 md' ∗ TQ r md')%I)
  (Hnewlineformat : forall md', md' = 0 \/ md' = 2 ^ 32 - 1 -> forall ap,
    vfxprintf_formatter rfb rfreg fl rlb rlreg newline ap 0 md' DfracDiscarded nlreg
      (fun p => fx_va p [WPtr null;WPtr newline])
      (bytesq DfracDiscarded nlb 0 [10;0] ∗ RN)%I
      (fun r => bytesq DfracDiscarded nlb 0 [10;0] ∗ ∃ md'', int_cell rfb 192 md'' ∗ NQ r md'')%I)
  (Hstderrflush : ⊢ live rfb rfreg -∗ S -∗ WP (ERun flushframe : gexpr)
    {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live rfb rfreg ∗ Q }})
  (Hstrcall : forall b, exists fr,
    call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ RP -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer error_borrowed_text b p ∗ T }}))
  (Hformat : forall ap, vfxprintf_formatter rfb rfreg fl rlb rlreg fmt ap 0 mmd dqf fmtreg
    (fun p => cursor p)
    (bytesq dqm fmtb (ptr_addr fmt - fmtb) (mchars ++ [0]) ∗ RM)%I
    (fun r => bytesq dqm fmtb (ptr_addr fmt - fmtb) (mchars ++ [0]) ∗
      ∃ en m, live eb ereg ∗ int_cell eb 0 en ∗ int_cell rfb 192 m ∗ U (r mod 2 ^ 32) en m)%I)
  (Hwidecall : forall r en md, 0 < md < 2 ^ 31 -> ⊢ live rfb rfreg -∗ int_cell rfb 192 md -∗
    (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ fields r en md) -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ result, ⌜v = Ret (WInt result)⌝ ∗ live rfb rfreg ∗
      int_cell rfb 192 md ∗ (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ fields r en md) }})
  (Hexchange : forall r en md, error_message_returned rfb rfreg eb ereg r en md ∗ remaining r en md ⊢ RP)
  (Hready_text : (if decide (errnum = 0) then RP else RQ) ⊢ R).

(** All three normal wrappers create their own argument snapshots. The
    message uses the original cursor, which remains available on return.
    This endpoint does not return ownership of the wrapper-local snapshots.
    Lending resources and preparing the message are logical exchanges;
    they neither print bytes nor change the stream mode. *)
Lemma wp_call_error_returning_report_normal_zero f e ls l args rest j
    cbname cbfn cbframe (D E : iProp Σ) Φ :
  let flush := error_closed_flush fb vb lb lbreg vbreg sb sreg D in
  map_option (arg_x ge e) args = Some (WInt 0 :: WInt errnum :: WPtr fmt :: ys) ->
  find_fn ge (TAtom "error") = Some (Defined glibc_error) ->
  forallb snapshot_word ys = true -> 0 <= errnum < 2 ^ 32 ->
  find_fn ge (TAtom "__error_internal") = Some (Defined glibc_error_internal) ->
  state = 0 \/ state = 1 ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  0 <= ptr_addr callback < 2 ^ 64 ->
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  0 <= ptr_addr pname < 2 ^ 64 ->
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some prefix ->
  find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined glibc__IO_fflush) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined glibc_fxprintf) ->
  0 <= pxb < 2 ^ 64 -> pmd = 0 \/ pmd = 2 ^ 32 - 1 ->
  (D ⊢ stderr_loan ∗ prefix_fields pmd pxb pxreg ∗ name ∗ PR) ->
  (forall r md', error_closed_flush fb vb lb lbreg vbreg sb sreg
    (stderr_loan ∗ prefix_fields md' pxb pxreg ∗ name ∗ PQ r md') ⊢ Ready) ->
  (forall fx_ap, vfxprintf_formatter rfb rfreg fl rlb rlreg prefix fx_ap 0 pmd DfracDiscarded pxreg
    (fun q => fx_va q [WPtr null;WPtr prefix;WPtr pname])
    (bytesq DfracDiscarded pxb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗ name ∗ PR)%I
    (fun r => bytesq DfracDiscarded pxb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗
      name ∗ ∃ md', int_cell rfb 192 md' ∗ PQ r md')%I) ->
  (ptr_addr callback <> 0 -> ptr_cap callback = Fn cbname) ->
  (ptr_addr callback <> 0 -> function_check_res ge callback = Some ok) ->
  find_fn ge cbname = Some (Defined cbfn) ->
  indirect_call_conv cbfn CVoid [] [] = Some (Converted [] None) ->
  call_frame cbfn [] = Some cbframe ->
  (⊢ flush -∗ WP (ERun cbframe : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ Ready }}) ->
  error_thread_ready state -∗ loan -∗ private -∗ flush -∗ E -∗
  ▷ (returned -∗ E -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call CVoid (Global (TAtom "error")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Hcount Hcountb Hcounte Hcountr Hentry Herrno Hexchange Hext Hflushframe Hfmtr Hformat Hgstderr Hmd Hmmd Hnewline Hnewlineformat Hnlb Hpost Hready_text Hreg Hrfa Hrfb Hrfe Hrfr Hrsa Hrsb Hrse Hrsr Hself Hselfr Hstderrflush Hstr Hstrcall Hstring Hsync Htext Htextformat Htxb Huser Hvfx Hwide Hwidecall Hwidefn Hwideframe cbr dqc.
  intros flush Hargs Hpublic Hys Herr Hinternal Hstate Hcancel
    Ho Hob Hoa Hoe Hor Hfb Hfa Hfe Hfr Hp Hpb Hpa Hpe Hpr Hcu
    Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush Hfx Hpxb Hpmd Hlend Hready_prefix Hprefixformat
    Hcap Hcheck Hcbfn Hconv Hcbframe Hcbcall.
  iIntros "Ht Ho Hp Hflush HE HK".
  iApply (wp_call_error_closed fb freg vb lb lbreg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer
    Hreg Hext Hsync f e ls l args rest j 0 errnum fmt ys state
    vbreg sb sreg prefix glibc_fxprintf (fxprintf_normal_frame null prefix [WPtr pname])
    cbname cbfn cbframe D Ready returned E
    with "Ht Ho Hp Hflush HE HK"); try assumption; try (split; lia).
  { apply (wp_error_closed_prefix Hreg Hext fb vb lb lbreg pname dqn namer
      rfb rfreg fl rlb rlreg pmd pxb pxreg rsb rsreg nameb dqb chars vbreg sb sreg D PR Ready PQ);
      assumption. }
  intros tb treg jb ap Hthread Htb Hta Hte Htr.
  iIntros (env from saved Hinputs) "Ht Hflag Hsavedl Hsaved Ho Hp Hready [Hva Hcleanup]".
  iDestruct (Hpost with "Hready") as "(Hnl & Hcount & Hsl & Hsp & Hfl & HP & HK)".
  iApply (wp_error_report_normal_zero Hreg Hext tb treg state rsb rsreg rfb rfreg fl rlb rlreg
    mmd md txb txreg nlb nlreg ssb ssreg glibc__IO_fflush flushframe
    fmt fmtb fmtreg dqf dqm mchars errnum ys 0 eb ereg wide widefn wideframe
    P RM RP RT RN U TQ NQ Q (loan ∗ private ∗ error_cleanup_fields tb jb ∗ kept)%I
    with "Hnl Hcount Ht Hflag Hsavedl Hsaved Hsl Hsp Hfl Hva HP [$Ho $Hp $Hcleanup $HK]");
    try eassumption.
  { apply Hformat. }
  iIntros "Hnl Hcount Hscratch Ht Hflag Hsavedl Hsaved Hsl Hsp Hfl Hva Hfmt HQ (Ho & Hp & Hcleanup & HK)".
  iSplit; [done |]. unfold returned, error_returned.
  iExists ap, saved. iSplitL "Ht Hflag Hcleanup".
  { unfold error_thread_ready. iExists tb, treg, jb. iFrame. done. }
  iFrame "Ho Hp Hsavedl Hsaved Hnl Hcount Hscratch Hsl Hsp Hfl Hva Hfmt HQ HK".
Qed.
End returning.
