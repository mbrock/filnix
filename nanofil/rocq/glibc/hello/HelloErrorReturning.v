(** Hello reports a failed close by calling error with status zero.
    This proof follows that call from argument setup through reporting
    and return, assuming contracts for the printing functions it calls.

    The caller lends the memory that reporting reads and writes. The
    function returns the stream pointers and argument cursor, and restores
    cancellation to its previous setting. A thread that entered with
    cancellation disabled still has it disabled on return. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  PrintfStateCode ErrorCode ErrorCall ErrorEntry ErrorText ErrorMessage ErrorReport
  FflushCode FileSyncCode HelloErrorClosed HelloErrorCall Fix.
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
  (rsb : Z) (rsreg : region) (rfb : Z) (rdq : dfrac) (rfreg : region)
  (countb : Z) (countreg : region) (count : Z)
  (newline textfmt wide : ptr) (fxfn : func) (newlineframe : frame)
  (flushframe : frame) (strerrorfn formatter widefn : func) (wideframe : frame)
  (eb : Z) (ereg : region) (borrowed : ptr -> iProp Σ)
  (Ready P R S Q T K : iProp Σ) (U : Z -> Z -> Z -> iProp Σ).
Let cursor ap := error_va ap (WInt 0 :: WInt errnum :: WPtr fmt :: ys).

(** Printing the program name must leave enough memory available to print
    the message. Hpost exposes the counter, stderr pointer and stream from
    that returned ownership. K keeps the resources not used by printing. *)
Context (Hpost : Ready ⊢ live countb countreg ∗ int_cell countb 0 count ∗
  live rsb rsreg ∗ pcell rsb 0 (mkPtr rfb (Obj rfb)) ∗ liveq rdq rfb rfreg ∗ P ∗ K).
Context (Hgstderr : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr rsb (Obj rsb)))
  (Hrsb : 0 < rsb) (Hrsa : rsb mod 8 = 0) (Hrse : rsb + 8 <= r_end rsreg)
  (Hrsr : r_end rsreg <= 2 ^ 63) (Hrptr : 0 <= rfb < 2 ^ 64)
  (Hcount : lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr countb (Obj countb)))
  (Hcountb : 0 < countb) (Hcounte : countb + 4 <= r_end countreg) (Hcountr : r_end countreg <= 2 ^ 63)
  (Hnewline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some newline)
  (Htext : lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some textfmt)
  (Hwide : lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide)
  (Hnewlineframe : call_frame fxfn [WPtr null;WPtr newline] = Some newlineframe)
  (Hflushframe : call_frame glibc__IO_fflush [WPtr (mkPtr rfb (Obj rfb))] = Some flushframe)
  (Hstr : find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn))
  (Hformatter : find_fn ge (TAtom "__vfxprintf") = Some (Defined formatter))
  (Hwidefn : find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn))
  (Hwideframe : call_frame widefn [WPtr wide;WPtr (mkPtr rfb (Obj rfb))] = Some wideframe).
Context (Hnewlinecall : ⊢ R -∗ WP (ERun newlineframe : gexpr)
    {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ S }})
  (Hstderrflush : ⊢ liveq rdq rfb rfreg -∗ S -∗ WP (ERun flushframe : gexpr)
    {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ liveq rdq rfb rfreg ∗ Q }})
  (Hstrcall : forall b, exists fr,
    call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ R -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer borrowed b p ∗ T }}))
  (Htextcall : forall b p, exists fr,
    call_frame fxfn [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ error_text_buffer borrowed b p -∗ T -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ error_text_buffer borrowed b p ∗ R }}))
  (Hformat : forall ap, exists fr,
    call_frame formatter [WPtr (mkPtr rfb (Obj rfb));WPtr fmt;WPtr ap;WInt 0] = Some fr /\
    (⊢ liveq rdq rfb rfreg -∗ cursor ap -∗ P -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r en md, ⌜v = Ret (WInt r)⌝ ∗ liveq rdq rfb rfreg ∗ cursor ap ∗
        error_message_pending rfb rfreg eb ereg r en md ∗ U r en md }}))
  (Hwidecall : forall r en md, 0 < md < 2 ^ 31 -> ⊢ liveq rdq rfb rfreg -∗ int_cell rfb 192 md -∗
    (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ U r en md) -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ result, ⌜v = Ret (WInt result)⌝ ∗ liveq rdq rfb rfreg ∗
      int_cell rfb 192 md ∗ (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ U r en md) }})
  (Hexchange : forall r en md, error_message_returned rfb rfreg eb ereg r en md ∗ U r en md ⊢ R).

(** The returned ownership keeps the saved cell distinct from the thread
    flag. It retains both global stream cells, one lifetime per stream,
    the argument cursor and any scratch produced by strerror. *)
Definition error_returned : iProp Σ :=
  ∃ ap saved, error_thread_ready state ∗ loan ∗ private ∗
    live saved (mkRegion saved (saved + 16) Heap Live) ∗ int_cell saved 0 state ∗
    live countb countreg ∗ int_cell countb 0 ((count + 1) mod 2 ^ 32) ∗
    error_text_scratch borrowed errnum ∗ live rsb rsreg ∗ pcell rsb 0 (mkPtr rfb (Obj rfb)) ∗
    liveq rdq rfb rfreg ∗ cursor ap ∗ Q ∗ K.

(** The call first flushes closed stdout and prints the program name,
    either directly or through a callback. It then prints the message and
    restores cancellation. Flushing stderr still needs its own contract:
    the proof for closed stdout does not apply to that open stream. *)
Lemma wp_call_error_returning_zero f e ls l args rest j
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
  find_fn ge (TAtom "__fxprintf") = Some (Defined fxfn) ->
  call_frame fxfn [WPtr null;WPtr prefix;WPtr pname] = Some prefixframe ->
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
  ▷ (error_returned -∗ E -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call CVoid (Global (TAtom "error")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros flush Hargs Hpublic Hys Herr Hinternal Hstate Hcancel
    Ho Hob Hoa Hoe Hor Hfb Hfa Hfe Hfr Hp Hpb Hpa Hpe Hpr Hcu
    Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush Hfx Hfxframe Hfxcall
    Hcap Hcheck Hcbfn Hconv Hcbframe Hcbcall.
  iIntros "Ht Ho Hp Hflush HE HK".
  iApply (wp_call_error_closed fb freg vb lb lbreg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer
    Hreg Hext Hsync f e ls l args rest j 0 errnum fmt ys state
    vbreg sb sreg prefix fxfn prefixframe cbname cbfn cbframe D Ready error_returned E
    with "Ht Ho Hp Hflush HE HK"); try assumption; try (split; lia).
  intros tb treg jb ap Hself Htb Hta Hte Htr.
  iIntros (env from saved Hinputs) "Ht Hflag Hsavedl Hsaved Ho Hp Hready [Hva Hcleanup]".
  iDestruct (Hpost with "Hready") as "(Hnl & Hcount & Hsl & Hsp & Hfl & HP & HK)".
  destruct (Hformat ap) as (fr & Hframe & Hcall).
  iApply (wp_error_report_zero Hreg Hext tb treg state rsb rsreg rfb rdq rfreg
    newline fxfn newlineframe glibc__IO_fflush flushframe R S Q T
    (loan ∗ private ∗ error_cleanup_fields tb jb ∗ K)%I
    Hstate Hself Htb Hta Hte Htr Hcancel Hgstderr Hrsb Hrsa Hrse Hrsr Hrptr
    Hnewline Hfx Hnewlineframe Hflush Hflushframe Hnewlinecall Hstderrflush
    eb ereg wide widefn wideframe cursor P U Hwide Hwidefn Hwideframe Hwidecall Hexchange
    env from errnum fmt ap 0 saved countb countreg count textfmt strerrorfn formatter fr borrowed
    with "Hnl Hcount Ht Hflag Hsavedl Hsaved Hsl Hsp Hfl Hva HP [$Ho $Hp $Hcleanup $HK]");
    try eassumption.
  iIntros "Hnl Hcount Hscratch Ht Hflag Hsavedl Hsaved Hsl Hsp Hfl Hva HQ (Ho & Hp & Hcleanup & HK)".
  iSplit; [done |]. unfold error_returned.
  iExists ap, saved. iSplitL "Ht Hflag Hcleanup".
  { unfold error_thread_ready. iExists tb, treg, jb. iFrame. done. }
  iFrame "Ho Hp Hsavedl Hsaved Hnl Hcount Hscratch Hsl Hsp Hfl Hva HQ HK".
Qed.
End returning.
