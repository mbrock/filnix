(** glibc's `c: error` prints its message to stderr with
    `c: __vfxprintf`, and Hello holds stderr idle between calls. This
    module proves that such a call gives the stream back idle. It opens
    the idle stream into the few fields that `c: __vfxprintf` touches,
    runs the proof of [VfxprintfCall](../stdio/VfxprintfCall.v), and lets
    the formatter's proved contract do the printing. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysWrappers FileInv FileIdle FileTidy LibioLogic LibioCloseSteps
  WordString NarrowFormat NarrowArgs PrintfSpec AllocRo LibioFputsSpec FxprintfStream FxprintfTidy FxprintfNormalCode
  VfxprintfNarrow VfxprintfSelect VfxprintfCall FxprintfNormalCall Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section idle.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hvf : !HasSpec registry (os_wi w0) ge (TAtom "__vfprintf_internal") vfprintf_spec}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The formatter saves errno and reads it through the global
    `c: __libc_errno`, so that global must be the thread's errno cell. *)
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb)))
  (Hgerr : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb))).

(** A stream whose fields are lent out is closed again by this wand,
    which [fx_stream_fx] hands out. It fixes the stream's region, its
    flags word, its mode and its lock pointer. *)
Definition fx_close (vb fd mode fb : Z) (freg : region) (fl : Z) (lp : ptr) : iProp Σ :=
  ∀ flags2' held', ⌜Z.land flags2' io_need_lock = 0⌝ -∗ live fb freg -∗ int_cell fb off_flags fl -∗
    int_cell fb off_flags2 flags2' -∗ int_cell fb off_mode mode -∗ pcell fb off_lock lp -∗
    lock_inv (ow_self w0) lp held' -∗ fx_stream vb (ow_self w0) (mkPtr fb (Obj fb)) fd mode flags2' held'.

(** The formatter's contract is a rule of the form that
    [VfxprintfNarrow] asks for. The caller lends the second flags
    word, the wand that closes the stream, the format, the arguments,
    errno and the read-only data. The rule gives back the second flags
    word, the mode the formatter leaves, a wand that closes the stream
    at that mode, and errno. *)
Lemma vfx_formatter_idle vb fd mode flags2 fb freg fl lb lbreg fmt fmtreg bytes ds ap skip xs :
  parse_narrow bytes = Some ds -> narrow_fits ds (skipn (Z.to_nat (skip / 8)) xs) [] ->
  0 <= skip -> skip mod 8 = 0 -> In fd (ow_fds w0) -> Z.land flags2 io_need_lock = 0 ->
  vfxprintf_formatter fb freg fl lb lbreg fmt ap 0 mode DfracDiscarded fmtreg (fun _ => True)%I
    (int_cell fb off_flags2 flags2 ∗ fx_close vb fd mode fb freg fl (mkPtr lb (Obj lb)) ∗
     word_string DfracDiscarded fmt bytes ∗ va_at ap skip xs ∗
     ([∗ list] a ∈ skipn (Z.to_nat (skip / 8)) xs, str_arg a) ∗ errno_any eb ∗
     printf_ro ∗ fputs_ro vb ∗ malloc_ro)
    (fun _ fl' freg' lb' _ => ∃ mode', ⌜mode' = 0 \/ mode' = 2 ^ 32 - 1⌝ ∗
       int_cell fb off_flags2 flags2 ∗ int_cell fb off_mode mode' ∗
       fx_close vb fd mode' fb freg' fl' (mkPtr lb' (Obj lb')) ∗ errno_any eb)%I.
Proof using Herr Hgerr Hvf.
  intros Hp Hfits Hs0 Hs8 Hfd Hnl.
  destruct (Hvf (VfpIn vb (mkPtr fb (Obj fb)) fd flags2 (Some 0) fmt DfracDiscarded bytes ds ap skip xs [] eb))
    as (gf & Hg & [fr Hfr] & Ht).
  exists gf, fr. split; [exact Hg|]. split; [exact Hfr|].
  iIntros "Hl Hfl Hlp Hlk Hmd Hcap _ (Hf2 & W & Hws & Hva & Hys & He & #Hpro & #Hfro & #Hmro)".
  iAssert (file_tidy vb (ow_self w0) (mkPtr fb (Obj fb)) fd flags2 (Some 0)) with "[W Hl Hfl Hf2 Hmd Hlp Hlk]" as "Hs".
  { iApply file_tidy_fx_stream. iExists mode.
    iApply ("W" $! flags2 (Some 0) with "[//] Hl Hfl Hf2 Hmd Hlp").
    iExists lb, lbreg. iSplit; [done | iExact "Hlk"]. }
  iApply (Ht fr _ Hfr with "[Hs Hws Hva Hys He]").
  - cbn [fs_pre vfprintf_spec vi_vb vi_fp vi_fd vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_ds vi_ap vi_skip vi_xs vi_rest vi_eb].
    iSplitR.
    { iPureIntro. unfold vfp_fits. cbn.
      split_and!; [exact Hp | exact Hfits | exact Hs0 | exact Hs8 | exact Herr | exact Hfd | exact Hgerr]. }
    iSplitL "Hs"; [iExact "Hs"|]. iSplitL "Hws"; [iExact "Hws"|]. iSplitL "Hva"; [iExact "Hva"|].
    iSplitL "Hys"; [iExact "Hys"|]. iSplitL "He"; [iExact "He"|].
    iSplitR; [iExact "Hpro"|]. iSplitR; [iExact "Hfro" | iExact "Hmro"].
  - iIntros (v). cbn [fs_post vfprintf_spec vi_vb vi_fp vi_fd vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_eb].
    iIntros "(%n & [-> %Hn] & Hs & _ & He)".
    iDestruct (file_tidy_fx_stream with "Hs") as (mode') "Hs".
    iDestruct (fx_stream_mode with "Hs") as %Hm'.
    iDestruct (fx_stream_fx with "Hs") as (fb' freg' fl' lp') "(%Hf & Hl & Hfl & Hf2 & Hmd & Hlp & Hlk & W)".
    destruct Hf as (Hfp & _ & _ & Hend' & Hreg' & _ & Huser' & _ & _ & _).
    injection Hfp as <-.
    iDestruct "Hlk" as (lb' lbreg') "[-> Hlk]".
    iExists n, fl', freg', lb', lbreg'.
    iSplitR.
    { iPureIntro. split_and!; [reflexivity | exact Huser' | unfold file_size in Hend'; lia | exact Hreg']. }
    iSplitL "Hl"; [iExact "Hl"|]. iSplitL "Hfl"; [iExact "Hfl"|]. iSplitL "Hlp"; [iExact "Hlp"|].
    iSplitL "Hlk"; [iExact "Hlk"|]. iSplitL "Hcap"; [iExact "Hcap"|]. iSplitR; [done|].
    iExists mode'. iSplitR; [done|]. iSplitL "Hf2"; [iExact "Hf2"|]. iSplitL "Hmd"; [iExact "Hmd"|].
    iSplitL "W"; [iExact "W" | iExact "He"].
Qed.

(** The function also checks that the thread has an identity, and it
    reads `c: __libc_single_threaded`. *)
Context (Hregistry : holds_os registry) (Hext : sys_external ge)
  (Hself : ptr_addr (ow_self w0) <> 0) (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64).

(** A call `c: __vfxprintf (fp, fmt, ap, 0)` on an idle stream fp
    leaves the stream idle on the same descriptor. The format must be
    read-only, and the arguments the cursor reaches must fit it. *)
Lemma wp_vfxprintf_idle vb fd fb fmt fmtreg bytes ds ap skip xs Φ :
  parse_narrow bytes = Some ds -> narrow_fits ds (skipn (Z.to_nat (skip / 8)) xs) [] ->
  0 <= skip -> skip mod 8 = 0 -> In fd (ow_fds w0) -> 0 <= ptr_addr fmt < 2 ^ 64 ->
  file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd -∗ live_capq DfracDiscarded (ptr_cap fmt) fmtreg -∗
  word_string DfracDiscarded fmt bytes -∗ va_at ap skip xs -∗
  ([∗ list] a ∈ skipn (Z.to_nat (skip / 8)) xs, str_arg a) -∗ errno_any eb -∗
  printf_ro -∗ fputs_ro vb -∗ malloc_ro -∗
  ▷ (∀ n, file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd -∗ errno_any eb -∗
       live_capq DfracDiscarded (ptr_cap fmt) fmtreg -∗ Φ (Ret (WInt n))) -∗
  WP (ERun (vfxprintf_frame (mkPtr fb (Obj fb)) fmt ap 0) : gexpr) {{ Φ }}.
Proof using Herr Hext Hgerr Hregistry Hself Hselfr Hvf.
  intros Hp Hfits Hs0 Hs8 Hfd Hfmtr.
  iIntros "Hst Hcap Hws Hva Hys He #Hpro #Hfro #Hmro HK".
  iDestruct (file_idle_fx_stream with "Hst") as (mode flags2 [Hb2 Hb32]) "Hst".
  iDestruct (fx_stream_mode with "Hst") as %Hmd.
  iDestruct (fx_stream_fx with "Hst") as (fb' freg fl lp) "(%Hf & Hl & Hfl & Hf2 & Hmd & Hlp & Hlk & W)".
  destruct Hf as (Hfp & Hal & Hfb & Hend & Hreg & Hflr & Huser & Hnl & Hf2r & Hmdr).
  injection Hfp as <-.
  iDestruct "Hlk" as (lb lbreg) "[-> Hlk]".
  iPoseProof "Hfro" as (vreg sb sreg) "[_ Hs]".
  iApply (wp_vfxprintf_explicit Hregistry Hext fb freg fl lb lbreg fmt ap 0 mode DfracDiscarded fmtreg sb sreg
    (fun _ => True)%I
    (int_cell fb off_flags2 flags2 ∗ fx_close vb fd mode fb freg fl (mkPtr lb (Obj lb)) ∗
     word_string DfracDiscarded fmt bytes ∗ va_at ap skip xs ∗
     ([∗ list] a ∈ skipn (Z.to_nat (skip / 8)) xs, str_arg a) ∗ errno_any eb ∗
     printf_ro ∗ fputs_ro vb ∗ malloc_ro)%I True%I
    (fun _ fl' freg' lb' _ => ∃ mode', ⌜mode' = 0 \/ mode' = 2 ^ 32 - 1⌝ ∗
       int_cell fb off_flags2 flags2 ∗ int_cell fb off_mode mode' ∗
       fx_close vb fd mode' fb freg' fl' (mkPtr lb' (Obj lb')) ∗ errno_any eb)%I Φ
    with "Hs Hl Hfl Hlp Hlk Hmd Hcap [//] [Hf2 W Hws Hva Hys He] [//] [HK]");
    [exact Hfb | exact Hal | unfold file_size in Hend; lia | exact Hreg | exact Huser | exact Hfmtr | exact Hmd |
     exact Hself | exact Hselfr | | |].
  - apply (vfx_formatter_idle _ _ _ _ _ _ _ _ _ _ _ bytes ds); assumption.
  - iSplitL "Hf2"; [iExact "Hf2"|]. iSplitL "W"; [iExact "W"|]. iSplitL "Hws"; [iExact "Hws"|].
    iSplitL "Hva"; [iExact "Hva"|]. iSplitL "Hys"; [iExact "Hys"|]. iSplitL "He"; [iExact "He"|].
    iSplitR; [iExact "Hpro"|]. iSplitR; [iExact "Hfro" | iExact "Hmro"].
  - iNext. iIntros (r fl' freg' lb' lbreg' _) "Hl Hfl Hlp Hlk Hcap _ HQ _".
    iDestruct "HQ" as (mode' Hm') "(Hf2 & Hmd & W & He)".
    iApply ("HK" with "[Hl Hfl Hlp Hlk Hf2 Hmd W] He Hcap").
    iApply file_idle_fx_stream. iExists mode', flags2. iSplit; [done|].
    iApply ("W" $! flags2 None with "[//] Hl Hfl Hf2 Hmd Hlp"). iExists lb', lbreg'. iSplit; [done | iExact "Hlk"].
Qed.

(** A null stream stands for stderr, which the function loads from the
    global `c: stderr`. The caller needs only a read-only share of that
    global. *)
Lemma wp_vfxprintf_idle_null vb fd fb gb greg fmt fmtreg bytes ds ap skip xs Φ :
  parse_narrow bytes = Some ds -> narrow_fits ds (skipn (Z.to_nat (skip / 8)) xs) [] ->
  0 <= skip -> skip mod 8 = 0 -> In fd (ow_fds w0) -> 0 <= ptr_addr fmt < 2 ^ 64 ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  liveq DfracDiscarded gb greg -∗ pcellq DfracDiscarded gb 0 (mkPtr fb (Obj fb)) -∗
  file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd -∗ live_capq DfracDiscarded (ptr_cap fmt) fmtreg -∗
  word_string DfracDiscarded fmt bytes -∗ va_at ap skip xs -∗
  ([∗ list] a ∈ skipn (Z.to_nat (skip / 8)) xs, str_arg a) -∗ errno_any eb -∗
  printf_ro -∗ fputs_ro vb -∗ malloc_ro -∗
  ▷ (∀ n, file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd -∗ errno_any eb -∗
       live_capq DfracDiscarded (ptr_cap fmt) fmtreg -∗ Φ (Ret (WInt n))) -∗
  WP (ERun (vfxprintf_frame null fmt ap 0) : gexpr) {{ Φ }}.
Proof using Herr Hext Hgerr Hregistry Hself Hselfr Hvf.
  intros Hp Hfits Hs0 Hs8 Hfd Hfmtr Hg Hgb Hga Hge Hgr.
  iIntros "#Hgl #Hgp Hst Hcap Hws Hva Hys He #Hpro #Hfro #Hmro HK".
  iDestruct (file_idle_fx_stream with "Hst") as (mode flags2 [Hb2 Hb32]) "Hst".
  iDestruct (fx_stream_mode with "Hst") as %Hmd.
  iDestruct (fx_stream_fx with "Hst") as (fb' freg fl lp) "(%Hf & Hl & Hfl & Hf2 & Hmd & Hlp & Hlk & W)".
  destruct Hf as (Hfp & Hal & Hfb & Hend & Hreg & Hflr & Huser & Hnl & Hf2r & Hmdr).
  injection Hfp as <-.
  iDestruct "Hlk" as (lb lbreg) "[-> Hlk]".
  iPoseProof "Hfro" as (vreg sb sreg) "[_ Hs]".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  unfold vfxprintf_frame. step. step. step. step. branch. step. step.
  check_persistent "Hgl".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ gb greg 0 (mkPtr fb (Obj fb)) freg
            DfracDiscarded DfracDiscarded (DfracOwn 1) with "Hgl Hgp [Hl]");
    [reflexivity | vx | left; reflexivity |
     cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia | rewrite Z.add_0_r; exact Hga |
     cbn [ptr_addr]; unfold file_size in Hend; lia | iExact "Hl" |].
  iNext. iIntros "_ _ Hl". step.
  iApply (wp_vfxprintf_selected Hregistry Hext fb freg fl lb lbreg fmt ap 0 mode DfracDiscarded fmtreg sb sreg
    (fun _ => True)%I
    (int_cell fb off_flags2 flags2 ∗ fx_close vb fd mode fb freg fl (mkPtr lb (Obj lb)) ∗
     word_string DfracDiscarded fmt bytes ∗ va_at ap skip xs ∗
     ([∗ list] a ∈ skipn (Z.to_nat (skip / 8)) xs, str_arg a) ∗ errno_any eb ∗
     printf_ro ∗ fputs_ro vb ∗ malloc_ro)%I True%I
    (fun _ fl' freg' lb' _ => ∃ mode', ⌜mode' = 0 \/ mode' = 2 ^ 32 - 1⌝ ∗
       int_cell fb off_flags2 flags2 ∗ int_cell fb off_mode mode' ∗
       fx_close vb fd mode' fb freg' fl' (mkPtr lb' (Obj lb')) ∗ errno_any eb)%I Φ
    with "Hs Hl Hfl Hlp Hlk Hmd Hcap [//] [Hf2 W Hws Hva Hys He] [//] [HK]");
    [exact Hfb | exact Hal | unfold file_size in Hend; lia | exact Hreg | exact Huser | exact Hfmtr | exact Hmd |
     exact Hself | exact Hselfr | | left; split; [reflexivity | lk_prove] | lk_prove | lk_prove | lk_prove | lk_prove | |].
  - apply (vfx_formatter_idle _ _ _ _ _ _ _ _ _ _ _ bytes ds); assumption.
  - iSplitL "Hf2"; [iExact "Hf2"|]. iSplitL "W"; [iExact "W"|]. iSplitL "Hws"; [iExact "Hws"|].
    iSplitL "Hva"; [iExact "Hva"|]. iSplitL "Hys"; [iExact "Hys"|]. iSplitL "He"; [iExact "He"|].
    iSplitR; [iExact "Hpro"|]. iSplitR; [iExact "Hfro" | iExact "Hmro"].
  - iNext. iIntros (r fl' freg' lb' lbreg' _) "Hl Hfl Hlp Hlk Hcap _ HQ _".
    iDestruct "HQ" as (mode' Hm') "(Hf2 & Hmd & W & He)".
    iApply ("HK" with "[Hl Hfl Hlp Hlk Hf2 Hmd W] He Hcap").
    iApply file_idle_fx_stream. iExists mode', flags2. iSplit; [done|].
    iApply ("W" $! flags2 None with "[//] Hl Hfl Hf2 Hmd Hlp"). iExists lb', lbreg'. iSplit; [done | iExact "Hlk"].
Qed.

(** The wrapper `c: __fxprintf` leaves its cursor 16 bytes into the
    snapshot, past the stream and the format. That cursor is the
    formatter's argument cursor at offset 16. *)
Lemma fx_va_at ap xs : (2 <= length xs)%nat -> fx_va ap xs -∗ va_at ap 16 xs.
Proof.
  intros Hl. iIntros "H". iDestruct "H" as (cb sb Hp) "[Hc Hs]".
  iExists cb, sb. iFrame. iPureIntro. destruct Hp as (? & ? & ? & ? & ? & ? & ?). split_and!; auto; lia.
Qed.

(** A run of `c: __fxprintf (NULL, fmt, ...)` prints to stderr and
    returns it idle. Error makes three such calls. *)
Lemma wp_fxprintf_idle_null vb fd fb gb greg fmt fmtreg bytes ds ys Φ :
  find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf) ->
  forallb snapshot_word ys = true -> parse_narrow bytes = Some ds -> narrow_fits ds ys [] ->
  In fd (ow_fds w0) -> 0 <= ptr_addr fmt < 2 ^ 64 ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  liveq DfracDiscarded gb greg -∗ pcellq DfracDiscarded gb 0 (mkPtr fb (Obj fb)) -∗
  file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd -∗ live_capq DfracDiscarded (ptr_cap fmt) fmtreg -∗
  word_string DfracDiscarded fmt bytes -∗ ([∗ list] a ∈ ys, str_arg a) -∗ errno_any eb -∗
  printf_ro -∗ fputs_ro vb -∗ malloc_ro -∗
  ▷ (∀ n, file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd -∗ errno_any eb -∗
       live_capq DfracDiscarded (ptr_cap fmt) fmtreg -∗ Φ (Ret (WInt (n mod 2 ^ 32)))) -∗
  WP (ERun (fxprintf_normal_frame null fmt ys) : gexpr) {{ Φ }}.
Proof using Herr Hext Hgerr Hregistry Hself Hselfr Hvf.
  intros Hvfx Hys Hp Hfit Hfd Hfmt Hge Hgb Hga Hgend Hgr.
  iIntros "#Hgl #Hgp Hf Hcap Hws Hys He Hpro Hfro Hmro HK".
  iApply (wp_fxprintf_normal _ _ _ _ (fun ap => vfxprintf_frame null fmt ap 0)
    (liveq DfracDiscarded gb greg ∗ pcellq DfracDiscarded gb 0 (mkPtr fb (Obj fb)) ∗
     file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd ∗ live_capq DfracDiscarded (ptr_cap fmt) fmtreg ∗
     word_string DfracDiscarded fmt bytes ∗ ([∗ list] a ∈ ys, str_arg a) ∗ errno_any eb ∗
     printf_ro ∗ fputs_ro vb ∗ malloc_ro)%I emp%I
    (fun _ => file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd ∗ errno_any eb ∗
       live_capq DfracDiscarded (ptr_cap fmt) fmtreg)%I
    with "[Hf Hcap Hws Hys He Hpro Hfro Hmro] [//] [HK]");
    [exact Hys | exact Hvfx | intros; apply vfxprintf_call_frame | | | ].
  - intros ap. iIntros "Hva (Hgl & Hgp & Hf & Hcap & Hws & Hys & He & Hpro & Hfro & Hmro)".
    iPoseProof (fx_va_at with "Hva") as "Hva"; [cbn; lia |].
    iApply (wp_vfxprintf_idle_null vb fd fb gb greg fmt fmtreg bytes ds ap 16 (WPtr null :: WPtr fmt :: ys)
      with "Hgl Hgp Hf Hcap Hws Hva [Hys] He Hpro Hfro Hmro"); try done.
    iNext. iIntros (n) "Hf He Hcap". iExists n. iSplit; [done|]. iFrame.
  - iSplitR; [iExact "Hgl"|]. iSplitR; [iExact "Hgp"|]. iFrame "Hf Hcap". iSplitL "Hws"; [iExact "Hws"|].
    iFrame.
  - iNext. iIntros (r) "(Hf & He & Hcap) _". iApply ("HK" with "Hf He Hcap").
Qed.

End idle.
