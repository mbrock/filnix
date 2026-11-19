(** Wide overflow allocates storage on the first write to stdout. An
    unbuffered stream can start with a one-character wide buffer and
    then replace it when it allocates its narrow buffer. Once both
    buffers are ready, the same code handles the first character, a
    later character, and a request to flush. *)

From Glibc Require Import Unit_io_fstat64_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os Unit_libio_wfiledoalloc_os.
From Glibc Require Import Unit_libio_wgenops_os Unit_misc_makedev_os Unit_termios_isatty_nostatus_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry Fix FileInv LibioLogic LibioCloseSteps LibioPutsInv AllocLogic
  SysWrappers LibioSetb LibioWIdle LibioWXsputnWindow LibioWAllocSetb
  LibioWOverflowDispatch LibioWOverflowPut LibioWOverflowWrite LibioWOverflowSetp LibioWOverflowState LibioWOverflowLoan
  LibioWOverflowEntry LibioWOverflowReady LibioWOverflowBackup LibioWOverflowAllocateSteps LibioWOverflowAllocate
  LibioWOverflowAllocated LibioWOverflowAllocFlags CBlocks.
Import ListNotations ProgramAbbreviations SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).

Section overflow.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation run e a := (ERun (mkFrame wfile_overflow_fn e [] None a) : sexpr).
Context `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn} (Hwrite : wdo_pending_spec vb self 1 E)
  `{!Defines ge "__GI__IO_free_wbackup_area" wfree_backup_fn} `{!Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}
  `{!Defines ge "__GI__IO_wdoallocbuf" Unit_libio_wgenops_os.fn___GI__IO_wdoallocbuf}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hstat : ge_fn ge "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat)
  `{!Defines ge "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64} `{!Defines ge "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major}
  `{!Defines ge "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus} `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{!Defines ge "free" free_fn} (Hfh : frees_heap (ge_free ge)) (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None) `{!Defines ge "malloc" malloc_fn}
  `{!Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn} `{!Defines ge "__GI__IO_wsetb" Unit_libio_wgenops_os.fn___GI__IO_wsetb}
  `{!Defines ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate} (Hwdaf : ge_fn ge "_IO_wfile_doallocate" Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate).
Context (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region)
  (Hmp : lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (objp mp))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (objp tc))
  (Henv : wo_alloc_env vb E dq mp tc dummy mpr tcr dr).
Local Abbreviation both := (wo_alloc_both vb E Hreg Hext Hstat Hfh Hzf Hzg Hwdaf dq mp tc dummy mpr tcr dr Hmp Htc Henv).
Local Abbreviation short := (wo_alloc_short vb E Hreg Hext Hstat Hfh Hzf Hzg Hwdaf dq mp tc dummy mpr tcr dr Hmp Htc Henv).
Local Abbreviation buffered := (wo_alloc_buffered vb E Hreg Hext Hstat Hfh Hzf Hzg Hwdaf dq mp tc dummy mpr tcr dr Hmp Htc Henv).

(** A new pair of heap buffers can come from either allocator. The
    caller of the first allocator must still test the narrow write
    base; the caller of the second can set the read pointers at once. *)
Local Lemma wo_two_heaps (first : bool) e fb fr ch st fl1 f2 wd wr bb sz p Φ :
  0 <= ch < 2^32 -> wo_setup_regs e fb ch -> (first = true -> reg e "v43" (WInt 0)) ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> wflags_ok st ->
  (fl1 = fs_flags st \/ fl1 = Z.lor (fs_flags st) io_line_buf) -> 0 < sz -> 0 < p -> p+4*sz <= 2^48 ->
  (forall m, (m = 2 \/ m = 32 \/ m = io_need_lock) -> Z.land f2 m = Z.land (fs_flags2 st) m) ->
  wo_cells vb fb fr (setb_flags fl1 1) (wsetb_flags2 f2 1) (NbHeap bb sz) wd wr (WbHeap p (4*sz)) (wo_new_narrow bb sz) (wo_new_wide wd (WbHeap p (4*sz))) -∗
  wo_close ge vb self fb fr st wd wr -∗ E -∗ wo_post vb self E fb ch Φ -∗ WP (run e (if first then wo_after_walloc else wo_after_alloc)) {{ Φ }}.
Proof using Type*.
  intros Ch G H43 Fb Fa Fe Fr Wd Wa We Wr Flags Flag Sz P End B2. iIntros "HC Hclose HE HK".
  pose proof (wo_fresh_ok fb st f2 fl1 bb sz p (proj1 Flags) Flag Sz P End B2) as Ok.
  destruct first.
  - iApply (wp_wo_after_walloc Hfh Hzf Hzg false e ch vb fb fr (setb_flags fl1 1) (wsetb_flags2 f2 1) (NbHeap bb sz) wd wr (WbHeap p (4*sz))
      null null null null null null (objp bb) (mkPtr (bb+sz) (Obj bb)) with "HC [-]"); try assumption; try reflexivity;
      [eapply wo_backup_clear; [exact Flags|apply (proj2 (proj2 (wo_nflags _ _ (proj1 Flags) Flag)))]|by apply H43|].
    iIntros (ee Ge) "HC". iApply (wo_alloc_have vb self E Hwrite ee fb fr ch st with "HC Hclose HE HK"); assumption.
  - iApply (wp_wo_after_alloc e ch vb fb fr (setb_flags fl1 1) (wsetb_flags2 f2 1) (NbHeap bb sz) wd wr (WbHeap p (4*sz))
      (objp bb) (mkPtr (bb+sz) (Obj bb)) with "HC [-]"); try assumption; [cbn; split; [done|lia]|].
    iIntros (ee Ge) "HC". iApply (wo_alloc_setg vb self E Hwrite ee fb fr ch st (NbHeap bb sz) _ _ wd wr (WbHeap p (4*sz))
      (objp bb) (objp bb) null null null (mkPtr (bb+sz) (Obj bb)) with "HC Hclose HE HK"); assumption.
Qed.

Local Lemma wo_no_narrow e fb fr ch st wd wr Φ : 0 <= ch < 2^32 -> wo_setup_regs e fb ch -> reg e "v43" (WInt 0) ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> wflags_ok st ->
  wo_cells vb fb fr (fs_flags st) (fs_flags2 st) NbNone wd wr WbNone (replicate 8 null) (wo_new_wide wd WbNone) -∗
  wo_close ge vb self fb fr st wd wr -∗ E -∗ wo_post vb self E fb ch Φ -∗ WP (run e (body_at wfile_overflow_fn "L34")) {{ Φ }}.
Proof using Type*.
  intros Ch G Z43 Fb Fa Fe Fr Wd Wa We Wr Flags. pose proof G as (Hfp & Hch & Hck & H7). iIntros "HC Hclose HE HK".
  body_start wfile_overflow_fn "L34"%string. iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  destruct (Z.eq_dec (Z.land (fs_flags st) io_unbuffered) 0) as [Buffered|Unbuffered].
  - iApply (both true _ fb fr (fs_flags st) (fs_flags2 st) wd wr with "HC HE"); try assumption; [reflexivity|].
    iNext. iIntros (fl1 bb sz p R) "HC HE". resume. iApply (wo_two_heaps true e fb fr ch st fl1 (fs_flags2 st) wd wr bb sz p with "HC Hclose HE HK");
      try assumption; try reflexivity; try tauto; lia.
  - iApply (short _ fb fr (fs_flags st) (fs_flags2 st) NbNone wd wr _ with "HC"); try assumption; [reflexivity|].
    iNext. iIntros "HC". resume.
    iApply (wp_wo_after_walloc Hfh Hzf Hzg false e ch vb fb fr (fs_flags st) (wsetb_flags2 (fs_flags2 st) 0) NbNone wd wr WbShort
      null null null null null null null null with "HC [-]"); try assumption; try reflexivity; [eapply wo_backup_clear; [exact Flags|done]|].
    iIntros (ee Ge) "HC". pose proof Ge as (Hfp' & _). body_start wfile_overflow_fn "L47"%string.
    iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
    iApply (both false _ fb fr (fs_flags st) (wsetb_flags2 (fs_flags2 st) 0) wd wr with "HC HE"); try assumption; [reflexivity|apply (wsetb_flags2_bit _ 0)|].
    iNext. iIntros (fl1 bb sz p R) "HC HE". resume. iApply (wo_two_heaps false ee fb fr ch st fl1 (wsetb_flags2 (fs_flags2 st) 0) wd wr bb sz p with "HC Hclose HE HK");
      try assumption; try discriminate; try tauto; try lia. apply wo_f2_mask.
Qed.

Local Lemma wo_have_narrow e fb fr ch st nb wd wr b rb wp we stop Φ :
  0 <= ch < 2^32 -> wo_setup_regs e fb ch -> reg e "v43" (WInt 0) ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> wflags_ok st ->
  wo_storage fb nb (fs_flags st) b stop -> in_buf fb nb b -> 0 < ptr_addr b < 2^64 ->
  wo_cells vb fb fr (fs_flags st) (fs_flags2 st) nb wd wr WbNone (wo_ptrs_before b rb b wp we stop) (wo_new_wide wd WbNone) -∗
  wo_close ge vb self fb fr st wd wr -∗ E -∗ wo_post vb self E fb ch Φ -∗ WP (run e (body_at wfile_overflow_fn "L34")) {{ Φ }}.
Proof using Type*.
  intros Ch G Z43 Fb Fa Fe Fr Wd Wa We Wr Flags S In Range. pose proof G as (Hfp & _). iIntros "HC Hclose HE HK".
  iAssert (∀ f2 w, ⌜wo_alloc_ok fb st nb (fs_flags st) f2 w b stop⌝ -∗
    wo_cells vb fb fr (fs_flags st) f2 nb wd wr w (wo_ptrs_before b rb b wp we stop) (wo_new_wide wd w) -∗ E -∗
    WP (run e wo_after_walloc) {{ Φ }})%I with "[Hclose HK]" as "Hend".
  { iIntros (f2 w Ok) "HC HE". iApply (wp_wo_after_walloc Hfh Hzf Hzg true e ch vb fb fr (fs_flags st) f2 nb wd wr w b b rb b wp we b stop with "HC [-]");
      try assumption; [eapply wo_backup_clear; [exact Flags|done]|by split|].
    iIntros (ee Ge) "HC". iApply (wo_alloc_setg vb self E Hwrite ee fb fr ch st nb _ f2 wd wr w b rb b wp we stop with "HC Hclose HE HK"); assumption. }
  body_start wfile_overflow_fn "L34"%string. iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  destruct (Z.eq_dec (Z.land (fs_flags st) io_unbuffered) 0) as [Buf|Unbuf].
  - iApply (buffered _ fb fr (fs_flags st) (fs_flags2 st) nb wd wr b b rb b wp we b stop with "HC HE"); try assumption; [reflexivity|].
    iNext. iIntros (p n (N & P & End)) "HC HE". resume. iApply ("Hend" with "[%] HC HE").
    pose proof (proj1 Flags). unfold wo_alloc_ok, wbuf_user_ok, window_bound, window_size. rewrite wsetb_flags2_bit !(Z.mul_comm 4 n).
    split_and!; try assumption; try reflexivity; try lia; try (rewrite Z.div_mul; lia); try (rewrite Z.mod_mul; lia). intros; by apply wo_f2_mask.
  - iApply (short _ fb fr (fs_flags st) (fs_flags2 st) nb wd wr _ with "HC"); try assumption; [reflexivity|].
    iNext. iIntros "HC". resume. iApply ("Hend" with "[%] HC HE"). unfold wo_alloc_ok, wbuf_user_ok. rewrite wsetb_flags2_bit.
    pose proof (proj1 Flags). split_and!; try assumption; try reflexivity; try lia. intros; by apply wo_f2_mask.
Qed.

(** The first allocation starts with every wide cursor null. The narrow
    buffer may still be absent, or it may have survived orientation.
    The stream loan distinguishes the cases without changing any field. *)
Lemma wo_prepare_fresh : wo_prepare vb self E false.
Proof using Type*.
  intros e fb ch wd w i Φ Ch G (-> & Z43). iIntros "HP HE HK".
  iDestruct (wo_open with "HP") as (fr st nb tw tm wr j (P & Wd & Wa & We & Wr & B & Hi & Hj)) "[HC Hclose]".
  assert (i=0) as -> by (cbn in Hi; lia). assert (j=0) as -> by (cbn in Hj; lia).
  pose proof P as (_ & Fa & Fb & Fe & Fr & Flags & _). unfold file_size in Fe.
  iDestruct "HC" as "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb)".
  change (window_slots wd WbNone 0 0) with (wo_new_wide wd WbNone).
  iDestruct (wo_old_storage vb _ _ _ _ _ _ _ _ _ _ P with "Hnb") as %[(-> & Ps)|(S & Ps)].
  - iApply (wo_no_narrow e fb fr ch st wd wr with "[-Hclose HE HK] Hclose HE HK"); try assumption.
    rewrite /wo_cells -Ps. iFrame "Hf Hfl Hf2 Hfd Hm Hvt Hwd Hp Hnb Hl Hw Hwvt Hb".
  - iAssert (⌜in_buf fb nb (fs_ptr st 6) /\ 0 < ptr_addr (fs_ptr st 6) < 2^64⌝)%I with "[Hnb]" as %IR.
    { destruct nb as [| |bb sz|bb]; try contradiction; destruct S as (Base & Stop & Rest); rewrite Base.
      - iPureIntro. cbn; intuition lia.
      - iDestruct "Hnb" as (br xs cs N) "_". iPureIntro. cbn; intuition lia. }
    iApply (wo_have_narrow e fb fr ch st nb wd wr (fs_ptr st 6) (fs_ptr st 2) (fs_ptr st 4) (fs_ptr st 5) (fs_ptr st 7) with
      "[-Hclose HE HK] Hclose HE HK"); try assumption; try apply IR.
    rewrite /wo_cells -Ps.
    iFrame "Hf Hfl Hf2 Hfd Hm Hvt Hwd Hp Hnb Hl Hw Hwvt Hb".
Qed.

(** Wide overflow returns either the requested character or a failure
    indication, and returns the stream in both cases. A successful
    flush request returns zero. *)
Lemma wp_wfile_overflow : woverflow_spec vb self E wfile_overflow_fn.
Proof using Type*. apply (wo_entry vb self E Hwrite); [apply (wo_prepare_existing vb self E Hwrite)|exact wo_prepare_fresh]. Qed.
End overflow.
