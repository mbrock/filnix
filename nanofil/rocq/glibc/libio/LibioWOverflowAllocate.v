(** When a wide stream has no narrow buffer, its file allocator installs
    two heap buffers. A buffered stream can do this on the first call.
    An unbuffered stream first acquires a wide short buffer, then
    replaces it when the second call allocates the two heap buffers. *)

From Glibc Require Import Unit_io_fstat64_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os Unit_libio_wfiledoalloc_os.
From Glibc Require Import Unit_libio_wgenops_os Unit_misc_makedev_os Unit_termios_isatty_nostatus_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry Fix FileInv FileIdle LibioLogic LibioCloseSteps LibioPutsInv
  AllocLogic SysWrappers LibioSetb HiAtexitBase HiAtexitSetb HiAtexitAlloc HiAtexitDoAlloc
  LibioWIdle LibioWXsputnWindow LibioWAllocBuf LibioWAllocFile LibioWAllocSetb LibioWAllocStat LibioDoAllocBase
  LibioWOverflowLoan LibioWOverflowAllocateSteps.
Import ListNotations ProgramAbbreviations SysWrappers FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation objp b := (mkPtr b (Obj b)).

Lemma wo_heap_end wd p n : wpos wd (WbHeap p (4*n)) (window_size (WbHeap p (4*n))) = mkPtr (p+4*n) (Obj p).
Proof. unfold wpos, window_base, window_size. cbn [ptr_addr ptr_cap]. rewrite (Z.mul_comm 4 n) Z.div_mul; [f_equal; lia|lia]. Qed.

Definition wo_new_narrow bb sz := [null;null;null;null;null;null;objp bb;mkPtr (bb+sz) (Obj bb)].

Section allocate.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (E : iProp Σ).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hstat : ge_fn ge "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat)
  `{!Defines ge "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64} `{!Defines ge "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major}
  `{!Defines ge "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus} `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{!Defines ge "free" free_fn} (Hfh : frees_heap (ge_free ge)) (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None) `{!Defines ge "malloc" malloc_fn}
  `{!Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn} `{!Defines ge "__GI__IO_wsetb" Unit_libio_wgenops_os.fn___GI__IO_wsetb}
  `{!Defines ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate} (Hwdaf : ge_fn ge "_IO_wfile_doallocate" Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate).
Context (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region)
  (Hmp : lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (objp mp))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (objp tc)).
Local Abbreviation Mres := (hi_malloc_state dq mp tc dummy mpr tcr dr).
Local Abbreviation malloc_rule := (hi_malloc_rule dq mp tc dummy mpr tcr dr Hmp Htc).
Local Abbreviation free_rule := (hi_free_rule Hfh Hzf Hzg).
Local Abbreviation file_alloc := (wp_glibc__IO_file_doallocate_wide Hstat Mres
  (hi_doalloc_L5 Hreg Hext Hfh Hzf Hzg dq mp tc dummy mpr tcr dr Hmp Htc)
  (hi_doalloc_L7 Hfh Hzf Hzg dq mp tc dummy mpr tcr dr Hmp Htc) (hi_file_stat Hreg Hext)).

(** The allocator borrows errno and its thread cache. The caller also
    lends read-only access to both jump tables. After the call, these
    resources go back to the surrounding printf environment. *)
Definition wo_alloc_env := E ⊢ ∃ vr eb, ⌜ow_errno w0 = Some (objp eb) /\ In 1 (ow_fds w0)⌝ ∗
  vtables_ro ge vb vr ∗ wvtables_ro ge vb ∗ errno_any eb ∗ Mres ∗ (errno_any eb -∗ Mres -∗ E).
Context (Henv : wo_alloc_env).

Local Lemma wo_new_idle bb sz : 0 < bb -> 0 < sz -> new_buf bb sz -∗ buf_idle (NbHeap bb sz).
Proof using Type.
  intros B S. iIntros "(%br & (%K & %End & %Limit & %Align) & Hl & Hb & Ha)".
  iExists br, (replicate (Z.to_nat sz) 0), (replicate (Z.to_nat sz) CNone). iFrame. iPureIntro.
  rewrite !length_replicate. split_and!; try assumption; try lia.
  - apply Z.mod_divide; [lia|exists (2*(bb/16)); pose proof (Z.div_mod bb 16 ltac:(lia)); lia].
  - apply Forall_replicate. lia.
Qed.

Lemma wo_alloc_both (first : bool) frame fb fr fl f2 wd wr Φ :
  let old := if first then WbNone else WbShort in
  call_frame (if first then Unit_libio_wgenops_os.fn___GI__IO_wdoallocbuf else Unit_libio_genops_os.fn___GI__IO_doallocbuf) [WPtr (objp fb)] = Some frame ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 ->
  (if first then Z.land fl io_unbuffered = 0 else wbuf_user_ok WbShort f2) ->
  wo_cells vb fb fr fl f2 NbNone wd wr old (replicate 8 null) (wo_new_wide wd old) -∗ E -∗
  ▷ (∀ fl1 bb sz p, ⌜(fl1 = fl \/ fl1 = Z.lor fl io_line_buf) /\ 0 < sz <= 8192 /\ 0 < bb /\ bb+sz <= 2^48 /\ 0 < p /\ p+4*sz <= 2^48⌝ -∗
    wo_cells vb fb fr (setb_flags fl1 1) (wsetb_flags2 f2 1) (NbHeap bb sz) wd wr (WbHeap p (4*sz)) (wo_new_narrow bb sz) (wo_new_wide wd (WbHeap p (4*sz))) -∗ E -∗ Φ RetVoid) -∗ WP (ERun frame : sexpr) {{ Φ }}.
Proof using Type*.
  cbn zeta. intros Call Fb Fa Fe Fr Wd Wa We Wr B. iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & _ & Hl & Hw & Hwvt & Hb) HE HK".
  iDestruct (Henv with "HE") as (vr eb (Err & Fd)) "(#Vt & #Wvt & Herr & HM & Henv)".
  iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & _)".
  iDestruct "Hw" as "(W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _)".
  destruct first.
  1: iApply (wp_glibc__IO_wdoallocbuf_from_null free_rule Hwdaf Mres malloc_rule file_alloc frame fb fr fl 1 eb null vb vr f2 wd wr null with
      "Vt Wvt Hf Hfl Hfd Herr P6 P7 Hvt Hf2 Hwd Hl W6 W7 Hwvt HM"); try assumption; try (unfold file_size; lia); try lia.
  1: iClear "Hb"; iNext; iIntros (fl1 bb sz R) "Hwvt Hvt Hfl Hfd P6 P7 Hnew Herr".
  2: iApply (wp_glibc__IO_doallocbuf_wide_null free_rule Hwdaf Mres malloc_rule file_alloc frame fb fr fl 1 eb null vb vr f2 wd wr WbShort _ with
      "Vt Wvt Hf Hfl Hm Hfd Herr P6 P7 Hvt Hf2 Hwd Hl W6 W7 Hb HM"); try assumption; try (unfold file_size; lia); try lia.
  2: iNext; iIntros (fl1 bb sz R) "Hm Hvt Hfl Hfd P6 P7 Hnew Herr".
  all: iIntros (p Bounds) "Hf Hf2 Hwd Hl W6 W7 Hb HM"; iDestruct (wo_new_idle with "Hnew") as "Hnb"; try lia;
    iDestruct ("Henv" with "Herr HM") as "HE"; iApply ("HK" $! fl1 bb sz p with "[%] [-HE] HE"); [tauto|];
    rewrite /wo_cells /wo_new_narrow /wo_new_wide wo_heap_end /=; by iFrame.
Qed.

(** An unbuffered stream starts with space for one wide character in
    the stream itself. This allocation needs no narrow buffer. *)
Lemma wo_alloc_short frame fb fr fl f2 nb wd wr ns Φ :
  call_frame Unit_libio_wgenops_os.fn___GI__IO_wdoallocbuf [WPtr (objp fb)] = Some frame ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> Z.land fl io_unbuffered <> 0 ->
  wo_cells vb fb fr fl f2 nb wd wr WbNone ns (wo_new_wide wd WbNone) -∗
  ▷ (wo_cells vb fb fr fl (wsetb_flags2 f2 0) nb wd wr WbShort ns (wo_new_wide wd WbShort) -∗ Φ RetVoid) -∗ WP (ERun frame : sexpr) {{ Φ }}.
Proof using Type*.
  intros. iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & _) HK".
  iDestruct "Hw" as "(W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _)".
  iApply (wp_glibc__IO_wdoallocbuf_short free_rule frame fb fr fl f2 wd wr null with "Hf Hfl Hf2 Hwd Hl W6 W7"); try assumption; try (unfold file_size; lia).
  iNext. iIntros "Hf Hfl Hf2 Hwd Hl W6 W7". iApply ("HK" with "[-]"). rewrite /wo_cells /wo_new_wide /=. by iFrame.
Qed.

(** A buffered stream that already owns narrow storage keeps it. The
    allocator measures that storage to choose a positive wide capacity.
    Its life token bounds the measurement by the machine address space. *)
Lemma wo_alloc_buffered frame fb fr fl f2 nb wd wr rp re rb wb wp we b stop Φ :
  call_frame Unit_libio_wgenops_os.fn___GI__IO_wdoallocbuf [WPtr (objp fb)] = Some frame ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> Z.land fl io_unbuffered = 0 ->
  LibioWOverflowState.wo_storage fb nb fl b stop -> let ns := [rp;re;rb;wb;wp;we;b;stop] in
  wo_cells vb fb fr fl f2 nb wd wr WbNone ns (wo_new_wide wd WbNone) -∗ E -∗
  ▷ (∀ p n, ⌜0 < n /\ 0 < p /\ p+4*n <= 2^48⌝ -∗
    wo_cells vb fb fr fl (wsetb_flags2 f2 1) nb wd wr (WbHeap p (4*n)) ns (wo_new_wide wd (WbHeap p (4*n))) -∗ E -∗ Φ RetVoid) -∗ WP (ERun frame : sexpr) {{ Φ }}.
Proof using Type*.
  intros Call Fb Fa Fe Fr Wd Wa We Wr Buf S. cbn zeta. iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & _) HE HK".
  iDestruct (Henv with "HE") as (vr eb (Err & Fd)) "(#Vt & #Wvt & Herr & HM & Henv)".
  iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & _)".
  iDestruct "Hw" as "(W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _)".
  destruct nb as [| |bb sz|bb]; try contradiction; destruct S as (-> & -> & Rest).
  - iApply (wp_glibc__IO_wdoallocbuf_from_short free_rule Hwdaf Mres malloc_rule frame fb fr fl vb vr f2 wd wr null with
      "Vt Wvt Hf Hfl P6 P7 Hf2 Hwd Hl W6 W7 Hwvt HM"); try assumption; try (unfold file_size; lia).
    iNext. iIntros "Hwvt Hfl P6 P7". iIntros (p Bounds) "Hf Hf2 Hwd Hl W6 W7 Hb HM".
    iDestruct ("Henv" with "Herr HM") as "HE". iApply ("HK" $! p 1 with "[%] [-HE] HE"); [lia|].
    rewrite /wo_cells /wo_new_wide wo_heap_end. iFrame "Hf Hfl Hf2 Hfd Hm Hvt Hwd Hl Hwvt Hb". iClear "Hnb".
    cbn [big_sepL]. iFrame "P0 P1 P2 P3 P4 P5 P6 P7 W0 W1 W2 W3 W4 W5 W6 W7 W8 W9 W10".
  - iDestruct "Hnb" as (br xs cs N) "(Hbl & Hx & Ha)". iApply (wp_live_fit1 with "Hbl"). iIntros (Fit) "Hbl".
    iApply (wp_glibc__IO_wdoallocbuf_from_heap free_rule Hwdaf Mres malloc_rule frame fb fr fl vb vr f2 wd wr null bb sz br with
      "Vt Wvt Hf Hfl P6 P7 Hbl Hf2 Hwd Hl W6 W7 Hwvt HM"); try assumption; try (unfold file_size; lia); try lia.
    iNext. iIntros "Hwvt Hfl P6 P7 Hbl". iIntros (p Bounds) "Hf Hf2 Hwd Hl W6 W7 Hb HM".
    iAssert (buf_idle (NbHeap bb sz)) with "[Hbl Hx Ha]" as "Hnb"; [iExists br, xs, cs; by iFrame|].
    pose proof (wide_count_range fl sz ltac:(lia)). iDestruct ("Henv" with "Herr HM") as "HE".
    iApply ("HK" $! p (wide_count fl sz) with "[%] [-HE] HE"); [lia|]. rewrite /wo_cells /wo_new_wide wo_heap_end.
    iFrame "Hf Hfl Hf2 Hfd Hm Hvt Hwd Hnb Hl Hwvt Hb". cbn [big_sepL]. iFrame "P0 P1 P2 P3 P4 P5 P6 P7 W0 W1 W2 W3 W4 W5 W6 W7 W8 W9 W10".
Qed.
End allocate.
