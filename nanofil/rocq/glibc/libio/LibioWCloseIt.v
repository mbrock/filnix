(** Closing wide stdout takes two paths. A stream in put mode flushes
    its pending wide characters before closing its descriptor. A stream
    outside put mode compares its wide read pointer and read end; both
    point to the base, so the close never seeks on that path. *)

From Glibc Require Import Unit_io_close_nocancel_os Unit_libio_fileops_os Unit_libio_genops_os Unit_libio_wgenops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry SysWrappers FileInv FileIdle LibioLogic
  LibioCloseSteps LibioSetb LibioWIdle
  LibioWXsputnWindow LibioWXsputnRoom LibioWOverflowWrite LibioWCloseItMid Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Section view.
Context `{!gen_heapGS piece pval Σ}.

(** Close reads two input cursors in read mode or two output cursors in
    put mode. Borrowing the cells keeps their exact values available to
    the converter when close hands the whole stream to it. *)
Lemma close_cursors vb tw tm wd w : wide_data vb tw tm wd w -∗ ∃ wr i j,
  ⌜0 < wd /\ wd mod 8 = 0 /\ wd+232 <= r_end wr /\ r_end wr <= 2^63 /\
    window_bound w /\ 0 <= i <= window_size w /\ 0 <= j <= window_size w⌝ ∗
  live wd wr ∗ pcell wd 0 (wpos wd w 0) ∗ pcell wd 8 (wpos wd w 0) ∗
  pcell wd 24 (wpos wd w 0) ∗ pcell wd 32 (wpos wd w i) ∗ wbuf_idle w ∗
  (live wd wr -∗ pcell wd 0 (wpos wd w 0) -∗ pcell wd 8 (wpos wd w 0) -∗ pcell wd 24 (wpos wd w 0) -∗
   pcell wd 32 (wpos wd w i) -∗ wbuf_idle w -∗ wide_data_at vb tw tm wd w wr (window_slots wd w i j)).
Proof using Type.
  iIntros "(%wr & %ps & %ib & %ie & %ob & %oe & %ifl & %ic & %ofl & %oc & %sb & %sc & %H & Hw & Hps & Hs & Ha & Hin & Hout & Hsb & Hpad & Hsc & Hvt & Hb)".
  iAssert (⌜window_bound w⌝)%I as %B.
  { destruct w; [done|done|]. iDestruct "Hb" as (r xs cs Hb) "_". iPureIntro. unfold window_bound. lia. }
  pose proof H as (Hwd & Hwa & Hwe & Hwr & Hps & _).
  destruct (window_indices _ _ _ B Hps) as (i & j & Hi & Hj & ->).
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _)".
  iExists wr, i, j. rewrite wpos_zero. iSplit; [done|]. iFrame "Hw P0 P1 P3 P4 Hb".
  iIntros "Hw P0 P1 P3 P4 Hb". iExists ib, ie, ob, oe, ifl, ic, ofl, oc, sb, sc. iSplit; [done|].
  iFrame "Hw Hs Ha Hin Hout Hsb Hpad Hsc Hvt Hb". rewrite /window_slots /=. by iFrame.
Qed.
End view.

Section close_it.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge)
  (Hfc : ge_fn ge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close)
  `{Hcn : !Defines ge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel}
  `{Hwsb : !Defines ge "__GI__IO_wsetb" Unit_libio_wgenops_os.fn___GI__IO_wsetb}
  `{Hsb : !Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{Hum : !Defines ge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers}
  `{Hdw : !Defines ge "__GI__IO_wdo_write" wdo_write_fn}.
Local Abbreviation gexpr := (language.expr (nanofil_lang registry ge)).
Context (fd vb fb : Z) (vr freg : region) (eb wd : Z) (tw tm : ptr) (E : iProp Σ).
Local Abbreviation ok st nb w := (wide_file_ok ge vb (objp fb) fd fb freg st nb wd w tw tm).

(** Close has already taken the FILE lock. It calls the converter on
    the actual buffer base and cursor index, and needs the stream back
    with the same lock pointer even if conversion fails. The converter
    can borrow its locale through E; the physical lock stays outside. *)
Definition wclose_write_rule : Prop := forall frame st nb w wr i j Ψ,
  call_frame wdo_write_fn [WPtr (objp fb); WPtr (window_base wd w); WInt i] = Some frame ->
  ok st nb w -> window_bound w -> 0 <= i <= window_size w -> 0 <= j <= window_size w ->
  has (fs_flags st) io_currently_putting = true ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ errno_any eb -∗ E -∗ live fb freg -∗ file_fields fb st -∗
  buf_idle nb -∗ wide_data_at vb tw tm wd w wr (window_slots wd w i j) -∗
  ▷ (∀ r st' nb' w', ⌜(r = 0 \/ r = 2^32-1) /\ fs_lock st' = fs_lock st /\ ok st' nb' w'⌝ -∗
    errno_any eb -∗ E -∗ live fb freg -∗ file_fields fb st' -∗ buf_idle nb' -∗ wide_data vb tw tm wd w' -∗
    Ψ (Ret (WInt r))) -∗ WP (ERun frame : gexpr) {{ Ψ }}.

Definition wclose_post lk (Φ : outcome -> iProp Σ) : iProp Σ := ∀ k st nb w,
  ⌜(k = 0 \/ k = 2^32-1) /\ fs_lock st = lk /\ ok st nb w⌝ -∗
  errno_any eb -∗ E -∗ live fb freg -∗ file_fields fb (wclosed_state st) -∗
  wide_data vb tw tm wd WbNone -∗ Φ (Ret (WInt k)).

Local Lemma after_flush e e' from r st nb w lk Φ :
  (forall b, find_block (TAtom "L18") (fn_blocks Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink) = Some b ->
    phis_env ge (b_phis b) (Some from) e = Some e') ->
  reg e' "v0" (WPtr (objp fb)) -> reg e' "chk0" (WPtr (mkPtr (fb+off_fileno) (Obj fb))) ->
  reg e' "chk1" (WPtr (objp fb)) -> reg e' "v2" (WInt 0) -> reg e' "pr.3" (WInt r) ->
  (r = 0 \/ r = 2^32-1) -> fs_lock st = lk -> ok st nb w -> ow_errno w0 = Some (objp eb) ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ errno_any eb -∗ E -∗ live fb freg -∗ file_fields fb st -∗
  buf_idle nb -∗ wide_data vb tw tm wd w -∗ wclose_post lk Φ -∗
  WP (ERun (mkFrame Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink e [] None (Enter (TAtom "L18") (Some from))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hphi Hv Hc Hc1 Hv2 Hp R Hlk H He. pose proof H as (_ & Hal & Hfb & Hend & Hfr & _ & I & Hm & Hvt & Hb & Hs & Hu & Hwd & _).
  unfold widle_ok, with_mode0, fs_ptr in I. cbn [fs_ptrs fs_flags2] in I.
  iIntros "#Hv #Hw Herr HE Hl Hfields Hb Hdata HK".
  iApply (wp_wclose_it_L18 Hreg Hext Hfree Hfc e e' from r with "Hv Hw Herr Hl Hfields Hb Hdata"); try assumption; try tauto; try lia.
  iNext. iIntros (k Hk) "Herr Hl Hfields Hdata". iApply ("HK" $! _ st nb w with "[%] Herr HE Hl Hfields Hdata").
  split_and!; try assumption. destruct Hk as [->| ->]; cbn; auto.
Qed.

(** The close function reads the caller's wide stream without touching
    the lock itself. It returns EOF if either the flush or the
    descriptor close failed. The caller gets the closed fields even
    then, so it can unlock and report the failure. *)
Lemma wp_wclose_it (Hwrite : wclose_write_rule) fr st nb w Φ :
  call_frame Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink [WPtr (objp fb); WInt 0] = Some fr ->
  fd <> 0 -> ok st nb w -> ow_errno w0 = Some (objp eb) ->
  vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗ errno_any eb -∗ E -∗ live fb freg -∗ file_fields fb st -∗
  buf_idle nb -∗ wide_data vb tw tm wd w -∗ ▷ wclose_post (fs_lock st) Φ -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr O H He. injection Hfr as <-. pose proof H as (_ & Hal & Hfb & Hend & Hfr & F & I & Hmode & _ & _ & _ & _ & Hwd & _).
  pose proof F as (Hfl & _ & _ & Hbk & _). unfold widle_ok, with_mode0 in I.
  cbn [fs_fileno fs_flags] in I. destruct I as (Hfd & Hfil & _ & _ & _ & _ & _ & _ & _ & _ & Hnw & _).
  specialize (Hnw O). unfold has in Hnw, Hbk. apply negb_false_iff, Z.eqb_eq in Hnw, Hbk.
  unfold io_no_writes in Hnw. unfold io_in_backup in Hbk. unfold file_size in Hend.
  iIntros "#Hvt #Hwv Herr HE Hl Hfields Hb Hdata HK".
  iDestruct (close_cursors with "Hdata") as (wr i j (Hw0 & Hwa & Hwe & Hwr & B & Hi & Hj)) "(Hw & P0 & P1 & P3 & P4 & Hwb & Hback)".
  iDestruct "Hfields" as "(%L & Hfl & Hps & Hfd & Hf2 & Ho & %Lc & Hcol & Hlk & Hoff & Hcv & Hwd & Hfr & Hbuf & Hmd & Hwt & Hvtp)".
  rewrite Hwd Hmode Hfil. iDestruct "Hfl" as "[_ Hfl]". iDestruct "Hfd" as "[%Rf Hfd]". iDestruct "Hmd" as "[%Rm Hmd]".
  iAssert (bytes fb off_flags (int_bytes (fs_flags st)) -∗ bytes fb off_fileno (int_bytes fd) -∗ bytes fb off_mode (int_bytes 1) -∗
    pcell fb off_wide (objp wd) -∗ file_fields fb st)%I with "[-Hfl Hfd Hmd Hwd Hl Hw P0 P1 P3 P4 Hwb Hback HK Herr HE Hb]" as "HF".
  { iIntros "Hfl Hfd Hmd Hwd". rewrite /file_fields Hmode Hfil Hwd. by iFrame. }
  iApply (wp_live_fit1 with "Hl"). iIntros ([? ?]) "Hl". iApply (wp_live_fit1 with "Hw"). iIntros ([? ?]) "Hw".
  assert (0 <= Z.land (fs_flags st) 8 < 2^32) by (rewrite Hnw; lia).
  assert (0 <= Z.land (fs_flags st) 2048 < 2^32) by (apply land_lt32; lia).
  assert (0 <= Z.land (fs_flags st) 256 < 2^32) by (rewrite Hbk; lia).
  assert (0 <= fd < 2^31) by lia.
  step. step. check "Hl". load_s32 "Hl" "Hfd". step. branch_as true.
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. load_s32 "Hl" "Hfl". step. step. step. step.
  Local Ltac regs := first [intros b Eb; vm_compute in Eb; injection Eb as <-; reflexivity |
    lazymatch goal with |- lookup _ _ = _ => lookups; norm; reflexivity end | close_side].
  destruct (Z.eq_dec (Z.land (fs_flags st) 2048) 0) as [Hput | Hput].
  - branch_as true. step. step. load_s32 "Hl" "Hfd". step. branch_as false.
    step. load_s32 "Hl" "Hfl". step. branch_as true. step. step. check "Hl". load_s32 "Hl" "Hmd". step. branch.
    step. branch. step. step. check "Hl". load_s32 "Hl" "Hmd". step. branch.
    step. step. check "Hl". load "Hl" "Hwd" "Hw". check "Hw". load_wpos "Hw" "P0" "Hwb".
    load "Hl" "Hwd" "Hw". step. check "Hw". load_wpos "Hw" "P1" "Hwb". do 3 step. step. step. branch_as true.
    iDestruct ("Hback" with "Hw P0 P1 P3 P4 Hwb") as "Hdata". iDestruct ("HF" with "Hfl Hfd Hmd Hwd") as "Hfields".
    iApply (after_flush _ _ _ 0 st nb w with "Hvt Hwv Herr HE Hl Hfields Hb [Hdata] HK"); try regs; try done.
    iExists wr, (window_slots wd w i j). done.
  - branch_as false. step. step. check "Hl". load_s32 "Hl" "Hmd". step. branch.
    step. step. check "Hl". load "Hl" "Hwd" "Hw". step. check "Hw". load_wpos "Hw" "P3" "Hwb".
    load "Hl" "Hwd" "Hw". step. check "Hw". load_wpos "Hw" "P4" "Hwb".
    load "Hl" "Hwd" "Hw". step. check "Hw". load_wpos "Hw" "P3" "Hwb". do 4 step.
    pose proof (wpos_bounds _ _ _ Hw0 ltac:(lia) B Hi) as (Ba & Ai & Cap). cbn [wpos ptr_addr] in Ai.
    rewrite wpos_zero Z.add_0_r wflush_count; try lia.
    iDestruct ("Hback" with "Hw P0 P1 P3 P4 Hwb") as "Hdata". iDestruct ("HF" with "Hfl Hfd Hmd Hwd") as "Hfields".
    iApply wp_call_bind; [vx|exact Hdw|reflexivity|]. iNext.
    rewrite (Z.mod_small i (2^64)); [|lia].
    iApply (Hwrite with "Hvt Hwv Herr HE Hl Hfields Hb Hdata"); try assumption; try reflexivity; try (unfold has; apply negb_true_iff, Z.eqb_neq; exact Hput).
    iNext. iIntros (r st' nb' w' (R & Hlk & H')) "Herr HE Hl HF Hb Hdata". resume. iApply wp_goto. iNext.
    assert (Rr : 0 <= r < 2^32) by (destruct R; lia). rewrite !(Z.mod_small r (2^32) Rr).
    iApply (after_flush _ _ _ r st' nb' w' with "Hvt Hwv Herr HE Hl HF Hb Hdata HK"); try regs; done.
Qed.
End close_it.
