(** Error prints a final newline before it flushes stderr and returns.
    This proof follows the captured printf wrapper for that newline. The
    wrapper borrows the caller's stderr pointer and stream, then returns
    both before the flush reads them again.

    The caller must supply the newline string and an unlocked stream that
    accepts ordinary character output. Earlier printing must leave them
    available. Printing the prefix and errno text still needs separate
    proofs because those calls cannot yet borrow stderr from the caller. *)
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
  FxprintfStream FxprintfNormalCode FxprintfNormalCall VfxprintfNarrow ErrorNewline Fix.
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
  (textfmt wide : ptr) (flushframe : frame) (strerrorfn widefn : func) (wideframe : frame)
  (eb : Z) (ereg : region) (borrowed : ptr -> iProp Σ)
  (fl rlb : Z) (rlreg : region) (md nlb : Z) (nlreg : region) (ssb : Z) (ssreg : region)
  (Ready P R0 Q T K : iProp Σ) (NQ : Z -> Z -> iProp Σ) (U : Z -> Z -> Z -> iProp Σ).
Let newline := mkPtr nlb (Ro nlb).
Let R := (single_ro ge ssb ssreg ∗ error_newline_fields rfb fl rlb rlreg md nlb nlreg ∗ R0)%I.
Let S := error_newline_done rfb fl rlb rlreg nlb nlreg NQ.
Let cursor ap := error_va ap (WInt 0 :: WInt errnum :: WPtr fmt :: ys).
Let returned := error_returned fb freg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer
  errnum fmt ys state rsb rsreg rfb (DfracOwn 1) rfreg countb countreg count borrowed Q K.

(** The prefix must supply the existing stream lifetime, not another copy.
    The message exchange supplies newline fields separately from that life. *)
Context (Hpost : Ready ⊢ live countb countreg ∗ int_cell countb 0 count ∗
  live rsb rsreg ∗ pcell rsb 0 (mkPtr rfb (Obj rfb)) ∗ live rfb rfreg ∗ P ∗ K).
Context (Hgstderr : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr rsb (Obj rsb)))
  (Hrsb : 0 < rsb) (Hrsa : rsb mod 8 = 0) (Hrse : rsb + 8 <= r_end rsreg)
  (Hrsr : r_end rsreg <= 2 ^ 63)
  (Hrfb : 0 < rfb) (Hrfa : rfb mod 8 = 0) (Hrfe : rfb + 224 <= r_end rfreg)
  (Hrfr : r_end rfreg <= 2 ^ 63)
  (Huser : Z.land fl 32768 = 0) (Hnlb : 0 <= nlb < 2 ^ 64) (Hmd : md = 0 \/ md = 2 ^ 32 - 1)
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

(** The newline has its own fresh argument snapshot. Its formatter may
    fail or change errno, but must return the actual stream mode in NQ's
    accompanying cell so the following flush can use it. *)
Context (Hnewlineformat : forall ap, vfxprintf_formatter rfb rfreg fl rlb rlreg newline ap 0 md DfracDiscarded nlreg
    (fun p => fx_va p [WPtr null;WPtr newline])
    (bytesq DfracDiscarded nlb 0 [10;0] ∗ R0)%I
    (fun r => bytesq DfracDiscarded nlb 0 [10;0] ∗ ∃ md', int_cell rfb 192 md' ∗ NQ r md')%I)
  (Hstderrflush : ⊢ live rfb rfreg -∗ S -∗ WP (ERun flushframe : gexpr)
    {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live rfb rfreg ∗ Q }})
  (Hstrcall : forall b, exists fr,
    call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ R -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer borrowed b p ∗ T }}))
  (Htextcall : forall b p, exists fr,
    call_frame glibc_fxprintf [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ error_text_buffer borrowed b p -∗ T -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ error_text_buffer borrowed b p ∗ R }}))
  (Hformat : forall ap, exists fr,
    call_frame glibc_vfxprintf [WPtr (mkPtr rfb (Obj rfb));WPtr fmt;WPtr ap;WInt 0] = Some fr /\
    (⊢ live rfb rfreg -∗ cursor ap -∗ P -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r en md, ⌜v = Ret (WInt r)⌝ ∗ live rfb rfreg ∗ cursor ap ∗
        error_message_pending rfb rfreg eb ereg r en md ∗ U r en md }}))
  (Hwidecall : forall r en md, 0 < md < 2 ^ 31 -> ⊢ live rfb rfreg -∗ int_cell rfb 192 md -∗
    (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ U r en md) -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ result, ⌜v = Ret (WInt result)⌝ ∗ live rfb rfreg ∗
      int_cell rfb 192 md ∗ (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ U r en md) }})
  (Hexchange : forall r en md, error_message_returned rfb rfreg eb ereg r en md ∗ U r en md ⊢ R).

(** This endpoint removes only the abstract newline-wrapper contract.
    Message formatting, prefix and errno-text printing, the wide fallback,
    and flushing open stderr remain explicit obligations. *)
Lemma wp_call_error_returning_normal_zero f e ls l args rest j
    vbreg sb sreg prefix prefixframe cbname cbfn cbframe (D E : iProp Σ) Φ :
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
  call_frame glibc_fxprintf [WPtr null;WPtr prefix;WPtr pname] = Some prefixframe ->
  (⊢ live_capq dqn (ptr_cap pname) namer -∗ flush -∗
    WP (ERun prefixframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dqn (ptr_cap pname) namer ∗ Ready }}) ->
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
Proof using Hcount Hcountb Hcounte Hcountr Hexchange Hext Hflushframe Hformat Hgstderr Hmd Hnewline Hnewlineformat Hnlb Hpost Hreg Hrfa Hrfb Hrfe Hrfr Hrsa Hrsb Hrse Hrsr Hself Hselfr Hstderrflush Hstr Hstrcall Hsync Htext Htextcall Huser Hvfx Hwide Hwidecall Hwidefn Hwideframe cbr dqc.
  intros flush Hargs Hpublic Hys Herr Hinternal Hstate Hcancel
    Ho Hob Hoa Hoe Hor Hfb Hfa Hfe Hfr Hp Hpb Hpa Hpe Hpr Hcu
    Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush Hfx Hfxframe Hfxcall
    Hcap Hcheck Hcbfn Hconv Hcbframe Hcbcall.
  iIntros "Ht Ho Hp Hflush HE HK".
  iApply (wp_call_error_returning_zero_loan fb freg vb lb lbreg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer
    Hreg Hext Hsync errnum fmt ys state rsb rsreg rfb (DfracOwn 1) rfreg countb countreg count
    newline textfmt wide glibc_fxprintf (fxprintf_normal_frame null newline []) flushframe
    strerrorfn glibc_vfxprintf widefn wideframe eb ereg borrowed Ready P R S Q T K U
    with "Ht Ho Hp Hflush HE HK"); try eassumption.
  { lia. }
  { apply fxprintf_normal_call_frame. }
  apply (wp_error_newline Hreg Hext rfb rfreg fl rlb rlreg md nlb nlreg ssb ssreg rsb rsreg R0 NQ);
    assumption.
Qed.
End returning.
