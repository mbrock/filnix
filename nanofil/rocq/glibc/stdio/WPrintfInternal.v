(** The wide print call first asks stdout to become wide. A stream that
    is already narrow refuses, and the call returns minus one. A wide
    stdout permits writing and does not require a lock. The formatter
    then initializes its private staging array, prints the greeting and
    flushes the array before returning an integer result. *)

From Glibc Require Import Unit_libio_iofwide_os Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import CodePrelude Fix OsBlocks OsWorld FileInv FileIdle
  LibioLogic LibioCloseSteps LibioWIdle LibioPutsInv PrintfSpec PrintfWrap FxprintfStream WPrintfFileInit
  WPrintfFileFlush WPrintfDispatch WPrintfLength WPrintfPad WPrintfWrite WPrintfParse WPrintfScan WPrintfOut WPrintfBuffer WPrintfDone.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld WrapVL.
Open Scope Z_scope.
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Abbreviation size xs := (Z.of_nat (length xs)).
Local Abbreviation stage_reg b := (mkRegion b (b+560) Heap Live).
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Definition wprintf_internal_fn := Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn___vfwprintf_internal.
Definition wprintf_fwide_fn := Unit_libio_iofwide_os.fn__IO_fwide.

Section internal.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context (vb : Z) (self : ptr).

(** The first orientation check either refuses a narrow stream or returns
    a wide one. The conversion objects and lock come back in both cases.
    A stream that becomes wide copies the wide jump table's address into
    its own vtable field, so the check reads the jump tables' life. *)
Definition wprintf_fwide_idle_spec (W : iProp Σ) : Prop := forall fr fp vr Φ,
  call_frame wprintf_fwide_fn [WPtr fp; WInt 1] = Some fr -> vtables_ro ge vb vr -∗ file_idle vb self fp 1 -∗ W -∗
  ▷ (∀ r, ((⌜r = 4294967295⌝ ∗ file_idle vb self fp 1) ∨ (⌜r = 1⌝ ∗ file_wide ge vb self fp 1)) -∗ W -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

(** The second orientation check already has a wide stream. *)
Definition wprintf_fwide_wide_spec (W : iProp Σ) : Prop := forall fr fp Φ,
  call_frame wprintf_fwide_fn [WPtr fp; WInt 1] = Some fr -> file_wide ge vb self fp 1 -∗ W -∗
  ▷ (file_wide ge vb self fp 1 -∗ W -∗ Φ (Ret (WInt 1))) -∗ WP (ERun fr : sexpr) {{ Φ }}.

Local Lemma wide_flags fp : file_wide ge vb self fp 1 ⊢ ∃ fb fr fl f2,
  ⌜fp = obj fb /\ 0 < fb /\ fb mod 8 = 0 /\ fb+224 <= r_end fr /\ r_end fr <= 2^63 /\
    Z.land fl 8 = 0 /\ Z.land f2 128 = 0⌝ ∗
  live fb fr ∗ int_cell fb off_flags fl ∗ int_cell fb off_flags2 f2 ∗
  (live fb fr -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ file_wide ge vb self fp 1).
Proof using Type.
  iIntros "(%fb & %fr & %st & %nb & %wd & %w & %tw & %tm & %Hp & Hl & Hfields & Hrest)".
  pose proof Hp as (Hfp & Ha & Hb & He & Hr & Hok & Hid & _).
  destruct Hok as (_ & _ & _ & _ & _ & Hnl).
  destruct Hid as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnw & _).
  specialize (Hnw ltac:(lia)). change (negb (Z.land (fs_flags st) 8 =? 0) = false) in Hnw.
  apply Bool.negb_false_iff, Z.eqb_eq in Hnw.
  iDestruct "Hfields" as "(%L & Hfl & Hptr & Hfd & Hf2 & Htail)".
  iExists fb, fr, (fs_flags st), (fs_flags2 st). iSplit; [iPureIntro; unfold file_size in He; auto 9|].
  iFrame "Hl Hfl Hf2". iIntros "Hl Hfl Hf2". iExists fb, fr, st, nb, wd, w, tw, tm. iFrame "Hl Hrest".
  iSplit; [done|]. rewrite /file_fields. by iFrame.
Qed.

(** The local allocation starts with zero bytes and no capabilities.
    Initialization turns it into an active stage with room for 128 wide
    characters, independently of the state of the stream's buffers. *)
Local Lemma wp_fresh_file fr bb fp Φ :
  call_frame wprintf_file_init_fn [WPtr (obj bb); WPtr fp] = Some fr -> 0 < bb -> bb mod 8 = 0 -> bb+560 <= 2^48 ->
  FileInv.LG.obj bb (heap_req 8 560) -∗ ▷ (wide_stage bb (stage_reg bb) fp [] 0 true -∗ Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hb Ha He. iIntros "Hobj HK". iDestruct (obj_zero_block with "Hobj") as "(Hl & Hx & Hc)"; [compute; discriminate|].
  iAssert (live bb (stage_reg bb)) with "Hl" as "Hl".
  change (Z.to_nat (req_extent (heap_req 8 560))) with (8+(8+(8+(8+(8+(8+512))))))%nat.
  iDestruct (zero_cell_prefix with "Hx Hc") as "(H0 & Hx & Hc)". iDestruct (zero_cell_prefix with "Hx Hc") as "(H8 & Hx & Hc)".
  iDestruct (zero_cell_prefix with "Hx Hc") as "(H16 & Hx & Hc)". iDestruct (zero_cell_prefix with "Hx Hc") as "(H24 & Hx & Hc)".
  iEval (rewrite (replicate_add 8) (replicate_add 4 4) !byte_ps_app !pts_app) in "Hx".
  iDestruct "Hx" as "[[H32 _] Hx]". iEval (rewrite (replicate_add 8) aux_ps_app pts_app) in "Hc". iDestruct "Hc" as "[_ Hc]".
  iDestruct (zero_cell_prefix with "Hx Hc") as "(H40 & Hx & Hc)".
  iEval (rewrite /pcell /pts big_sepL_cons) in "H24". iDestruct "H24" as "[_ H24]".
  iApply (wp_wprintf_file_init _ bb (stage_reg bb) fp null null null 0 0 null with "Hl H0 H8 H16 H24 [H32] H40");
    [assumption|lia|assumption|cbn; lia|cbn; lia|iSplit; [done|iExact "H32"]|].
  iNext. iIntros "Hl H0 H8 H16 H24 H32 H40". iApply "HK". iExists (replicate 512 0), (replicate 512 CNone).
  change (4*size []) with 0. rewrite Z.add_0_r. iFrame. iPureIntro. rewrite !length_replicate. cbn [r_end length].
  split_and!; first [lia|assumption|change (Forall (fun b => 0 <= b < 256) (replicate 512 0)); apply Forall_replicate; lia|constructor].
Qed.

(** These names identify the compiled functions that the format and its
    unlocked stream wrapper call directly. *)
Class WideFormatCode : Prop := {
  wfc_orient : Defines ge "_IO_fwide" wprintf_fwide_fn;
  wfc_init : Defines ge "__wprintf_buffer_to_file_init" wprintf_file_init_fn;
  wfc_buffer : Defines ge "__wprintf_buffer" wprintf_buffer_fn;
  wfc_done : Defines ge "__wprintf_buffer_to_file_done" wprintf_file_done_fn;
  wfc_count : Defines ge "__wprintf_buffer_done" wprintf_count_fn;
  wfc_search : Defines ge "__wcschrnul" wprintf_chr_fn;
  wfc_scan : Defines ge "glibc_vfwprintf_internal#__find_specwc.gnu_inline" wprintf_scan_fn;
  wfc_write : Defines ge "__wprintf_buffer_write" wprintf_write_fn;
  wfc_length : Defines ge "__wcslen" wprintf_length_fn;
  wfc_pad : Defines ge "glibc_vfwprintf_internal#__wprintf_buffer_pad" wprintf_pad_inline_fn;
  wfc_failed : Defines ge "glibc_vfwprintf_internal#__wprintf_buffer_has_failed" wprintf_failed_fn
}.

Context (E W : iProp Σ) `{!WideFormatCode, !WideBufferCalls vb self E}.
Context (Hidle : wprintf_fwide_idle_spec W) (Hwide : wprintf_fwide_wide_spec W).

(** The integer result covers ordinary output, failure and count overflow.
    Refusing wide orientation is the only path that returns an idle stream. *)
Lemma wp_wprintf_internal fr fp fmt rr ap dq b r xs eb vr Φ :
  call_frame wprintf_internal_fn [WPtr fp; WPtr (mkPtr fmt (Ro fmt)); WPtr ap; WInt 0] = Some fr ->
  ow_errno w0 = Some (obj eb) -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (obj eb) ->
  (E ⊢ errno_any eb ∗ (errno_any eb -∗ E)) ->
  (E ⊢ W ∗ (W -∗ E)) ->
  0 < b -> b mod 8 = 0 -> b+4*size xs+4 <= r_end r -> r_end r <= 2^63 -> Forall (fun c => 0 < c < 256) xs ->
  wprintf_fmt_ro fmt rr -∗ wprintf_tables_ro -∗ printf_ro -∗ vtables_ro ge vb vr -∗ wvtables_ro ge vb -∗
  va_at ap 8 [WPtr (mkPtr fmt (Ro fmt)); WPtr (obj b)] -∗ file_idle vb self fp 1 -∗ E -∗
  liveq dq b r -∗ bytesq dq b 0 (stage_bytes (xs++[0])) -∗
  ▷ (∀ n, ⌜0 <= n < 2^32⌝ -∗ (file_idle vb self fp 1 ∨ file_wide ge vb self fp 1) -∗ E -∗
     liveq dq b r -∗ bytesq dq b 0 (stage_bytes (xs++[0])) -∗ Φ (Ret (WInt n))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Herr Hge Hlend Hconv Hb Ha He Hr V. injection Hfr as <-.
  iIntros "#Hfmt #Ht #Hro #Hvt #Hwv Hva HF HE Hl Hb HK". iDestruct (Hconv with "HE") as "[HW Hrestore]". step.
  Local Ltac alloc b H := iApply wp_alloc; [vm_compute; reflexivity|vm_compute; congruence|vm_compute; congruence|
    intros ? ? ? ? Hfresh Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hfresh Hw)|]; iNext; iIntros (b H) "Hobj".
  alloc bb Hbb. iRename "Hobj" into "Hstage". change (0 < bb /\ bb mod 16 = 0 /\ bb+560 <= 2^48) in Hbb.
  destruct Hbb as (Hbb & Hb16 & Hbe). assert (Hb8 : bb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  do 2 (let x := fresh in let Hx := fresh in alloc x Hx; clear Hx; iClear "Hobj").
  iApply wp_call_bind; [vx|exact wfc_orient|reflexivity|]. iNext. iApply (Hidle with "Hvt HF HW"); [reflexivity|].
  iNext. iIntros (n) "[[-> HF]|[-> HF]] HW"; resume; step; branch; step.
  { iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" $! 4294967295 with "[%] [HF] [HW Hrestore] Hl Hb"); [lia|by iLeft|by iApply "Hrestore"]. }
  iDestruct (wide_flags with "HF") as (fb sr fl f2 (-> & Hfb & Hfa & Hfe & Hsr & Hnw & _)) "(Hfl & [%Hfl Hflags] & Hf2 & Hback)".
  check "Hfl". load_s32 "Hfl" "Hflags". step. branch_symbolic. rewrite (Z.mod_small fl); [|lia]. change (8 mod 2^32) with 8.
  rewrite Hnw. cbn [edge_label]. step. do 3 step. iPoseProof "Hfmt" as "((%Hg & %Hfmt0 & %Hfmt8 & %Hfmte & %Hfmtr) & _)".
  branch_symbolic. rewrite (Z.mod_small fmt); [|lia]. change ((0 mod 2^64) mod 2^64) with 0.
  destruct (Z.eqb_spec fmt 0) as [Hz|_]; [lia|]. cbn [edge_label]. step. iDestruct ("Hback" with "Hfl [Hflags] Hf2") as "HF"; [by iSplit|].
  iApply wp_call_bind; [vx|exact wfc_orient|reflexivity|]. iNext. iApply (Hwide with "HF HW"); [reflexivity|].
  iNext. iIntros "HF HW". iDestruct ("Hrestore" with "HW") as "HE". resume. step. branch. step. step.
  iDestruct (wide_flags with "HF") as (fb' sr' fl' f2' (Hfp & Hfb' & Hfa' & Hfe' & Hsr' & _ & Hnl)) "(Hfl & Hflags & [%Hf2r Hf2] & Hback)".
  injection Hfp as <-. check "Hfl". load_s32 "Hfl" "Hf2". step_named. step_named. step_named. step.
  assert (Hx : x0 = fx_field f2') by (eapply fx_shift_field; eassumption).
  assert (Hx1 : x1 = 0).
  { rewrite E2 Hx (Z.mod_small (fx_field f2')); [|apply fx_field_range]. change (128 mod 2^32) with 128.
    change 128 with (Z.land 16777215 128) at 1. rewrite Z.land_assoc fx_field_low; [|exact Hf2r]. rewrite -Z.land_assoc. exact Hnl. }
  clear E0 E1 E2 Hx. subst x1. branch. step. iDestruct ("Hback" with "Hfl Hflags [Hf2]") as "HF"; [by iSplit|].
  iApply wp_call_bind; [vx|exact wfc_init|reflexivity|]. iNext. iApply (wp_fresh_file with "Hstage"); [reflexivity|assumption..|].
  iNext. iIntros "Hstage". resume. iAssert (wprintf_out vb self E bb (stage_reg bb) (obj fb)) with "[HF HE Hstage]" as "Ho".
  { iSplitR; [iExists vr; iFrame "#"|]. iFrame "HF HE". iExists [], 0, true. done. }
  iApply wp_call_bind; [vx|exact wfc_buffer|reflexivity|]. iNext.
  iApply (@wp_wprintf_buffer _ _ _ vb self E _ wfc_search wfc_scan wfc_write wfc_length wfc_pad wfc_failed
    _ _ _ _ _ _ _ dq b r xs eb with "Hfmt Ht Hro Hva Ho Hl Hb"); [reflexivity|assumption..|].
  iNext. iIntros "(_ & HF & HE & %cs & %w & %ok & Hstage) Hl Hb". resume.
  iApply wp_call_bind; [vx|exact wfc_done|reflexivity|]. iNext.
  iApply (wp_wprintf_file_done eb Herr Hge vb self E (wbc_xs_fn vb self E) (wbc_xs vb self E)
    (wbc_backend vb self E) wfc_count with "Hvt Hwv HF HE Hstage"); [reflexivity|exact Hlend|].
  iNext. iIntros (cs' w' ok' n Hn) "HF HE _". resume. iApply wp_ret; [reflexivity|vx|]. iNext.
  rewrite !Z.mod_mod; try lia. rewrite (Z.mod_small n (2^32) Hn). iApply ("HK" with "[%] [HF] HE Hl Hb"); [exact Hn|by iRight].
Qed.
End internal.
