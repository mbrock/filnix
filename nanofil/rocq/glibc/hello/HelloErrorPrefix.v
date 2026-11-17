(** Error reporting can print the program name after stdout has closed.
    This proof uses the normal NULL-stream printf wrapper for that default
    prefix. It keeps the closed stdout fields apart from the resources lent
    to stderr and stops before printing the message.

    The caller supplies readable name bytes and the stderr and format
    resources. Printing returns the actual stream mode, which may differ
    from its initial value. A logical resource exchange prepares the message
    continuation without assuming that the returned mode is narrow. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  PrintfStateCode ErrorCode ErrorEntry FflushCode FileSyncCode HelloClosedStdout HelloErrorClosed
  FxprintfStream FxprintfNormalCode FxprintfNormalCall VfxprintfNarrow ErrorPrefix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section prefix.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge)
  (Hsync : ge_fn ge "_IO_new_file_sync" glibc__IO_new_file_sync).
Context (fb : Z) (freg : region) (vb lb : Z) (lbreg : region) (ob : Z) (oreg : region)
  (pb : Z) (preg : region) (callback : ptr) (dqc : dfrac) (cbr : region)
  (nb : Z) (nreg : region) (pname : ptr) (dqn : dfrac) (namer : region).
Context (efb : Z) (efreg : region) (fl elb : Z) (elreg : region) (md xb : Z) (xreg : region)
  (gb : Z) (greg : region) (nameb : Z) (dqb : dfrac) (chars : list Z).
Let loan := (live gb greg ∗ pcell gb 0 (mkPtr efb (Obj efb)) ∗ live efb efreg)%I.
Let fields := error_prefix_fields efb fl elb elreg.
Let name := error_prefix_name pname nameb namer dqb chars.

(** The prefix returns the fields that the following message needs. This
    rule keeps the closed stdout state aside while stderr is borrowed,
    then passes both streams to the caller's resource exchange. *)
Lemma wp_error_closed_prefix vbreg sb sreg (D R Ready : iProp Σ) (Q : Z -> Z -> iProp Σ) :
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  0 < efb -> efb mod 8 = 0 -> efb + 224 <= r_end efreg -> r_end efreg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= xb < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf) ->
  (D ⊢ loan ∗ fields md xb xreg ∗ name ∗ R) ->
  (forall r md', error_closed_flush fb vb lb lbreg vbreg sb sreg
    (loan ∗ fields md' xb xreg ∗ name ∗ Q r md') ⊢ Ready) ->
  (forall fx_ap, vfxprintf_formatter efb efreg fl elb elreg (mkPtr xb (Ro xb)) fx_ap 0 md DfracDiscarded xreg
    (fun q => fx_va q [WPtr null;WPtr (mkPtr xb (Ro xb));WPtr pname])
    (bytesq DfracDiscarded xb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗ name ∗ R)%I
    (fun r => bytesq DfracDiscarded xb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗
      name ∗ ∃ md', int_cell efb 192 md' ∗ Q r md')%I) ->
  live_capq dqn (ptr_cap pname) namer -∗ error_closed_flush fb vb lb lbreg vbreg sb sreg D -∗
  WP (ERun (fxprintf_normal_frame null (mkPtr xb (Ro xb)) [WPtr pname]) : gexpr)
    {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live_capq dqn (ptr_cap pname) namer ∗ Ready }}.
Proof using Hext Hreg chars dqb nameb.
  intros Hg Hgb Hga Hge Hgr Hefb Hefa Hefe Hefr Huser Hxb Hmd Hself Hselfr Hvfx Hlend Hready Hformat.
  iIntros "Hname (Hclosed & #Hvt & #Hslot & #Hs & HD)".
  iDestruct (Hlend with "HD") as "((Hgl & Hgp & Hl) & Hfields & Hbytes & HR)".
  iApply (wp_wand with "[Hname Hclosed Hgl Hgp Hl Hfields Hbytes HR]").
  { iApply (wp_error_prefix Hreg Hext efb efreg fl elb elreg md xb xreg sb sreg gb greg
      pname nameb namer dqn dqb chars R (closed_stdout_fields fb vb lb lbreg) Q
      with "Hname [$Hs $Hgl $Hgp $Hl $Hfields $Hbytes $HR] Hclosed"); assumption. }
  iIntros (v) "H". iDestruct "H" as (r md' ->) "(Hname & Hgl & Hgp & Hl & Hfields & Hbytes & HQ & Hclosed)".
  iExists (r mod 2 ^ 32). iSplit; [done |]. iFrame "Hname".
  iApply (Hready r md'). unfold error_closed_flush, loan. iFrame "Hclosed Hvt Hslot Hs Hgl Hgp Hl Hfields Hbytes HQ".
Qed.

(** Before printing the message, the caller receives the stream and name
    memory that it lent to prefix printing. The caller must show that these
    resources suffice for the continuation. A custom program-name callback
    keeps its own contract. *)
Lemma wp_error_closed_entry_prefix status errnum fmt ap mode tb treg state vbreg sb sreg
    cbname cbfn cbframe (D R Ready E : iProp Σ) (Q : Z -> Z -> iProp Σ) Φ :
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
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
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some (mkPtr xb (Ro xb)) ->
  find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined glibc__IO_fflush) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined glibc_fxprintf) ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  0 < efb -> efb mod 8 = 0 -> efb + 224 <= r_end efreg -> r_end efreg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= xb < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  (D ⊢ loan ∗ fields md xb xreg ∗ name ∗ R) ->
  (forall r md', error_closed_flush fb vb lb lbreg vbreg sb sreg
    (loan ∗ fields md' xb xreg ∗ name ∗ Q r md') ⊢ Ready) ->
  (forall fx_ap, vfxprintf_formatter efb efreg fl elb elreg (mkPtr xb (Ro xb)) fx_ap 0 md DfracDiscarded xreg
    (fun q => fx_va q [WPtr null;WPtr (mkPtr xb (Ro xb));WPtr pname])
    (bytesq DfracDiscarded xb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗ name ∗ R)%I
    (fun r => bytesq DfracDiscarded xb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗
      name ∗ ∃ md', int_cell efb 192 md' ∗ Q r md')%I) ->
  (ptr_addr callback <> 0 -> ptr_cap callback = Fn cbname) ->
  (ptr_addr callback <> 0 -> function_check_res ge callback = Some ok) ->
  find_fn ge cbname = Some (Defined cbfn) ->
  indirect_call_conv cbfn CVoid [] [] = Some (Converted [] None) ->
  call_frame cbfn [] = Some cbframe ->
  (⊢ error_closed_flush fb vb lb lbreg vbreg sb sreg D -∗
    WP (ERun cbframe : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ Ready }}) ->
  live tb treg -∗ int_cell tb 792 state -∗ error_stdout_loan fb freg ob oreg -∗
  error_private_cells pb preg callback dqc cbr nb nreg pname dqn namer -∗
  error_closed_flush fb vb lb lbreg vbreg sb sreg D -∗ E -∗
  error_closed_report fb freg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer
    tb treg state status errnum fmt ap mode Ready E Φ -∗
  WP (ERun (error_internal_frame status errnum fmt ap mode) : gexpr) {{ Φ }}.
Proof using Hext Hreg Hsync chars dqb nameb.
  intros Hself Htb Hta Hte Htr Hstate Hcancel Ho Hob Hoa Hoe Hor Hfb Hfa Hfe Hfr
    Hp Hpb Hpa Hpe Hpr Hcu Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush Hfx Hvfx
    Hg Hgb Hga Hge Hgr Hefb Hefa Hefe Hefr Huser Hxb Hmd Hlend Hready Hformat
    Hcap Hcheck Hcbfn Hconv Hcbframe Hcbcall.
  assert (Hprefixcall : ⊢ live_capq dqn (ptr_cap pname) namer -∗
    error_closed_flush fb vb lb lbreg vbreg sb sreg D -∗
    WP (ERun (fxprintf_normal_frame null (mkPtr xb (Ro xb)) [WPtr pname]) : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live_capq dqn (ptr_cap pname) namer ∗ Ready }}).
  { apply (wp_error_closed_prefix vbreg sb sreg D R Ready Q);
      try assumption; rewrite Hself; cbn; lia. }
  iIntros "Ht Hstate Hout Hprivate HD HE HK".
  iApply (wp_error_closed_entry fb freg vb lb lbreg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer
    Hreg Hext Hsync status errnum fmt ap mode tb treg state vbreg sb sreg
    (mkPtr xb (Ro xb)) glibc_fxprintf (fxprintf_normal_frame null (mkPtr xb (Ro xb)) [WPtr pname])
    cbname cbfn cbframe D Ready E with "Ht Hstate Hout Hprivate HD HE HK");
    try assumption; reflexivity.
Qed.
End prefix.
