(** A file-backed printf buffer either publishes bytes already in the
    stream or sends bytes from its own staging array. After a successful
    staged write it consults the stream again, because the write may have
    allocated a buffer or changed how much room remains. *)

From Glibc Require Import Unit_libio_fileops_os Unit_libio_genops_os Unit_stdioZ2dcommon_printf_buffer_flush_os Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Machine ExternalCalls ExternalMachine
  Pieces Heap Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileTidy LibioLogic LibioFputsSpec AllocRo
  CStruct CFrame CBlocks PrintfLayout PrintfOut PrintfSpec PrintfFileOut PrintfBufferFileNames
  PrintfBufferXsputnCall PrintfBufferOverflowCall PrintfFlush PrintfFlushDirect PrintfFlushChoice PrintfFlushStage PrintfFlushSwitch.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Import PrintfBufferFileNames.fn___printf_buffer_flush_to_file.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Section flush.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{!Defines ge "__printf_buffer_to_file_switch" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_switch}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Variable a : fout.
Let F fp := file_tidy (fo_vb a) (fo_self a) fp (fo_fd a) (fo_flags2 a) (fo_held a).
Let E := (errno_any (fo_eb a) ∗ fputs_ro (fo_vb a) ∗ malloc_ro)%I.

(** The switch needs only the three pointer fields. The count and mode
    stay with the caller, which puts them beside the new pointers when
    the switch returns. *)
Lemma flush_reselect l from e bb br n cap count Φ :
  (l = "L40" \/ l = "L88") -> lookup ‹buf› e = Some (WPtr (mkPtr bb (Obj bb))) ->
  bb+176 <= r_end br -> 0 <= count < 2^64 -> let w := staged bb br n cap in
  printf_buf bb br w count 4 -∗ win_own bb (pw_end w) (bb+stage_end) -∗
  pcell bb 40 (fo_fp a) -∗ F (fo_fp a) -∗ E -∗
  (fs_post (flush_to_file_spec (file_R a)) bb RetVoid -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file e [] None (Enter (TAtom l) from)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hlab He Hsize Hcount w. iIntros "Hbuf Htail Hfp HF (Herr & #Hro & #Hm) HK". buf_open "Hbuf".
  assert (Hlo : pw_lo w = bb + stage_off) by (unfold w, pw_lo, staged, stage_off; cbn [pw_base]; Z.div_mod_to_equations; lia).
  change (pw_obj w) with bb. rewrite Hlo. iCombine "Hwin Htail" as "Hstage".
  iAssert (⌜bb+stage_off <= pw_end w <= bb+stage_end⌝)%I as %Hbounds.
  { iDestruct "Hstage" as "[(%xs & %cs1 & %Hp & _) (%ys & %cs2 & %Ht & _)]". iPureIntro. lia. }
  iEval (rewrite (win_own_join _ _ _ _ Hbounds)) in "Hstage".
  iApply (wp_file_choice _ a bb br with "[Hl] Hstage HF"); [struct_live_close "Hl"|].
  iIntros (freg dq cs) "Hbb Hs Hback". set (i := FWinIn bb br (fo_fb a) freg dq cs).
  iPoseProof (flush_switch_block l Hlab) as "#Hswitch".
  iApply ("Hswitch" $! i e from with "[%] [%] [Hbb Hs Hbase Hptr Hend Hfp]"); [done| | |].
  - destruct Hlab as [->| ->]; c_env_close.
  - iFrame "Hbb Hs". iSplitL "Hfp"; [struct_close|]. iExists _, _, _. struct_close.
  - iIntros (o) "(-> & Hs & Hbb & Hfp & Hptrs)". iDestruct ("Hback" with "Hs") as "(%Hok & Hnew & Hwin & HR)".
    iDestruct ("HR" with "Hfp Herr Hro Hm") as "HR". iApply "HK". iExists br, (fwin_choice i), count, 4.
    iSplit; [iPureIntro; pose proof (flush_choice_room i); intuition|]. iFrame "HR". unfold printf_buf. iFrame "Hnew Hwin".
    iSplit; [done|]. struct_live_open "Hbb" as "[%Hbb' Hl]". iSplitL "Hl"; [struct_live_close "Hl"|].
    struct_open "Hptrs" as "(Hbase & Hptr & Hend & _)". struct_close.
Qed.

Context (Hfn : ge_fn ge "_IO_new_file_xsputn" Unit_libio_fileops_os.fn__IO_new_file_xsputn).
Context `{!Defines ge "__GI___overflow" Unit_libio_genops_os.fn___GI___overflow}.
Context (Hbulk : printf_xsputn_call_spec w0 registry ge F E) (Hchar : printf_overflow_call_spec w0 registry ge F E).

(** An unsuccessful stream call leaves the buffer marked failed. An
    empty one-byte stage needs no stream call. Every other success
    chooses an empty window with room for the next byte. *)
Lemma flush_to_file_has_spec `{!Defines ge "__printf_buffer_flush_to_file" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush_to_file") (flush_to_file_spec (file_R a)).
Proof using Type*.
  intros bb. exists Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. iIntros "(%br & %w & %written & Hbuf & HR) HK".
  destruct (Z.eq_dec (pw_obj w) bb) as [Hsame|Hdirect]; last first.
  { iApply (flush_direct_post _ a with "Hbuf HR"); try assumption. iApply "HK". }
  destruct w as [db dr base ptr e]. cbn [pw_obj] in Hsame. subst db.
  unfold file_R, pw_place. cbn [pw_obj pw_reg pw_base pw_end]. destruct (Z.eq_dec bb bb); [|contradiction].
  iDestruct "HR" as "(%Hsize & Hfp & Herr & #Hro & #Hm & (%Hbase & %Hcap) & Htail & HF)".
  subst base. iAssert (⌜dr = br⌝)%I as %->.
  { iDestruct "Hbuf" as "(_ & _ & _ & Hwl & _)". unfold win_live. cbn [pw_obj pw_reg]. destruct (numbers.Z.eq_dec bb bb); [done|contradiction]. }
  set (n := ptr-(bb+48)). set (cap := e-(bb+48)).
  replace (PWin bb br (bb+stage_off) ptr e) with (staged bb br n cap) by (unfold staged, n, cap, stage_off; f_equal; lia).
  iPoseProof "Hro" as (vr sb sr) "[#Hvt _]". struct_open "Hfp" as "[Hfp _]".
  iApply (wp_flush_staged (fo_vb a) (fo_self a) (fo_fd a) (fo_flags2 a) (fo_held a) E Hfn Hbulk Hchar
    fr bb br (fo_fb a) vr n cap written with "Hvt [$Hbuf $Hfp $HF $Herr $Hro $Hm]"); try assumption.
  { unfold cap, stage_end, stage_off in *. lia. }
  assert (Hcount : 0 <= (written+n) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
  iSplit.
  - iIntros (m Hm') "(Hbuf & Hfp & HF & Herr & _ & _)". iApply "HK". iExists br, (staged bb br n cap), ((written+n) mod 2^64), m.
    iSplit; [iPureIntro; cbn [staged pw_base pw_ptr pw_end]; intuition lia|]. iFrame "Hbuf".
    unfold file_R, pw_place. cbn [staged pw_obj pw_reg pw_base pw_end]. destruct (Z.eq_dec bb bb); [|contradiction].
    replace (bb+48+cap) with e by (unfold cap; lia). iFrame "Herr Hro Hm HF Htail". iSplit; [done|]. iSplitL "Hfp"; [struct_close|]. done.
  - iIntros (l from env [Hlab He]) "(Hbuf & Hfp & HF & HE)".
    iApply (flush_reselect _ _ _ bb br n cap with "Hbuf [Htail] Hfp HF HE"); try assumption.
    + cbn [staged pw_end]. replace (bb+48+cap) with e by (unfold cap; lia). iExact "Htail".
    + iApply "HK".
Qed.

(** A flush in file mode now gets its result by calling the file
    backend. The dispatcher needs no separate facts about the stream. *)
Lemma flush_file_has_spec `{!Defines ge "__printf_buffer_flush_to_file" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file}
    `{!Defines ge "__printf_buffer_flush" Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush") (flush_spec 4 (file_R a)).
Proof using Type*. apply flush_dispatch_has_spec; [apply flush_to_file_has_spec|assumption]. Qed.
End flush.
