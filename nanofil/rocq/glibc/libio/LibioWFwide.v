(** Hello's wide print call makes stdout wide with `c: _IO_fwide`. *)

From Glibc Require Import Unit_string_memset_os Unit_wcsmbs_wcsmbsload_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic HelloLeaf.
From Glibc Require Import CodePrelude HelloImageModule HelloImageLoad
  OsWorld OsBlocks OsRegistry FileInv FileIdle LibioLogic LibioWIdle MemFwdLogic Mbrtowc StartImageCpu StartImageEarly HelloImageMbsObjs HelloImageWFwideObjs LibioCloseSteps WPrintfInternal Fix.
From Glibc Require MemchrLast StartInitMisc.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).

Definition glibc_clone_conv := Unit_wcsmbs_wcsmbsload_os.fn___wcsmbs_clone_conv.

Local Abbreviation ts := (img_a "__libc_tsd_LOCALE").
Local Abbreviation ft := (img_a "__wcsmbs_gconv_fcts_c").
Local Abbreviation tw := (img_a "glibc_wcsmbsload#to_wc").
Local Abbreviation tm := (img_a "glibc_wcsmbsload#to_mb").
Local Abbreviation lk := (img_a "__gconv_lock").

Section objects.
Context `{!gen_heapGS piece pval Σ}.

(** The conversion lock is free between calls, so it holds zero. *)
Definition gconv_lock_free : iProp Σ := live lk (img_gd "__gconv_lock") ∗ int_cell lk 0 0.

(** Making a stream wide reads the thread's locale, the C locale's
    table of converters and both steps, and it takes and releases the
    conversion lock. The predicate [wfwide_res] dq owns all of these.
    Only the lock changes during the call, and it is free again at the
    end, so the call gives the predicate back unchanged. *)
Definition wfwide_res (dq : dfrac) : iProp Σ :=
  mbr_locale dq ∗ mbr_tables ∗ ptsq DfracDiscarded hello_wfwide_ps ∗ gconv_lock_free.

(** The copy reads the rest of the table and the second step's handle. *)
Lemma wfwide_tables : ptsq DfracDiscarded hello_wfwide_ps ⊢
  icellq DfracDiscarded ft 8 1 ∗ pcellq DfracDiscarded ft 16 (rop tm) ∗ icellq DfracDiscarded ft 24 1 ∗
  liveq DfracDiscarded tm (img_gd "glibc_wcsmbsload#to_mb") ∗ pcellq DfracDiscarded tm 0 null.
Proof using Type.
  rewrite /hello_wfwide_ps (ptsq_app _ (cell _ 8 1)) (ptsq_app _ (ptr_ps _ 16 _)) (ptsq_app _ (cell _ 24 1)).
  rewrite (ptsq_app _ [mbs_life _]). iIntros "($ & $ & $ & $ & $)".
Qed.
End objects.

Section clone.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (Hts : lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (objp ts))
  (Hlk : lookup (TAtom "__gconv_lock") (ge_globals ge) = Some (objp lk)).

(** The copy of the C locale's table names one step in each direction,
    and the conversion lock is free again when the copy returns. *)
Lemma wp_clone_conv fr dq cb creg x0 n8 x16 n24 Φ :
  call_frame glibc_clone_conv [WPtr (objp cb)] = Some fr ->
  cb mod 8 = 0 -> 0 < cb -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 ->
  wfwide_res dq -∗ live cb creg -∗ pcell cb 0 x0 -∗ icell cb 8 n8 -∗ pcell cb 16 x16 -∗ icell cb 24 n24 -∗
  ▷ (wfwide_res dq -∗ live cb creg -∗ pcell cb 0 (rop tw) -∗ icell cb 8 1 -∗ pcell cb 16 (rop tm) -∗ icell cb 24 1 -∗
     Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hts Hlk.
  intros Hfr Hca Hcb Hce Hcr. injection Hfr as <-.
  iIntros "((Hts & Hts0 & Hgl & Hgl0) & (#Hcc & #Hcc32 & #Hcd & #Hcd0 & #Hft & #Hft0 & #Hst & #Hst0 & #Hfn) & #Hw & Hlk)
    Hcl H0 H8 H16 H24 HK".
  iDestruct (wfwide_tables with "Hw") as "(#Hft8 & #Hft16 & #Hft24 & #Hml & #Hm0)".
  Local Ltac rd H := check_read_dq H by a2; iNext; iIntros "_".
  Local Ltac hrd H := iApply (MemchrLast.wp_half_check_read_dq registry (os_wi w0) ge with H);
    [reflexivity | reflexivity | reflexivity | right; reflexivity | a2 | a2 | lia | a2 | a2 |]; iNext; iIntros "_".
  Local Ltac rnw H := iApply (StartInitMisc.wp_renew_read_dq with H);
    [reflexivity | vx | reflexivity | right; reflexivity | a2 | a2 | a2 |]; iNext; iIntros "_".
  step. step_global Hts. check "Hts". load_pointer_dq "Hts Hts0 Hgl" by a2. iNext. iIntros "Hts Hts0 Hgl".
  check "Hgl". load_pointer_dq "Hgl Hgl0 Hcc" by a2. iNext. iIntros "Hgl Hgl0 _".
  step. rd "Hcc". load_pointer_dq "Hcc Hcc32 Hcd" by a2. iNext. iIntros "_ _ _".
  rd "Hcd". load_pointer_dq "Hcd Hcd0 Hft" by a2. iNext. iIntros "_ _ _". do 3 step. branch. step.
  rnw "Hcd". load_pointer_dq "Hcd Hcd0 Hft" by a2. iNext. iIntros "_ _ _". rd "Hft".
  load_pointer_dq "Hft Hft0 Hst" by a2. iNext. iIntros "_ _ _". check "Hcl". store "Hcl" "H0". step. step.
  hrd "Hft". iApply (wp_raw_load_read_dq with "Hft Hft8"); [reflexivity | vx | right; reflexivity | a2 |]. iNext. iIntros "_ _".
  check "Hcl". store_long "Hcl" "H8". step. step. hrd "Hft". load_pointer_dq "Hft Hft16 Hml" by a2. iNext. iIntros "_ _ _".
  check "Hcl". store "Hcl" "H16". step. step. hrd "Hft".
  iApply (wp_raw_load_read_dq with "Hft Hft24"); [reflexivity | vx | right; reflexivity | a2 |]. iNext. iIntros "_ _".
  check "Hcl". store_long "Hcl" "H24". iDestruct "Hlk" as "(Hll & % & Hlb)". step_global Hlk. check "Hll".
  iApply (wp_raw_cas_w with "Hll Hlb"); [left; reflexivity | reflexivity | reflexivity | vx | reflexivity | a2 | a2 |
    intros _; wi_store |]. iNext. iIntros "Hll Hlb".
  rewrite (_ : of_bytes (int_bytes 0) =? 0 mod 2 ^ 32 = true); [|reflexivity].
  rewrite (_ : of_bytes (int_bytes 0) mod 2 ^ 32 = 0); [|reflexivity].
  step. branch. step. step. branch. step. check "Hcl".
  load_pointer_dq "Hcl H0 Hst" by a2. iNext. iIntros "Hcl H0 _". rd "Hst".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 null (img_gd "glibc_wcsmbsload#to_wc")
    DfracDiscarded DfracDiscarded DfracDiscarded with "Hst Hst0 []");
    [reflexivity | vx | right; reflexivity | a2 | a2 | change (0 <= 0 < 2^64); lia | done |].
  iNext. iIntros "_ _ _". do 2 step. branch. step. step. check "Hcl".
  load_pointer_dq "Hcl H16 Hml" by a2. iNext. iIntros "Hcl H16 _". rd "Hml".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 null (img_gd "glibc_wcsmbsload#to_mb")
    DfracDiscarded DfracDiscarded DfracDiscarded with "Hml Hm0 []");
    [reflexivity | vx | right; reflexivity | a2 | a2 | change (0 <= 0 < 2^64); lia | done |].
  iNext. iIntros "_ _ _". do 2 step. branch. step. step_global Hlk. check "Hll".
  iAssert (bytes lk 0 (int_bytes 1)) with "Hlb" as "Hlb". assert (H1 : 0 <= 1 < 2 ^ 32) by lia.
  load_s32 "Hll" "Hlb". step. step. check "Hll".
  iApply (wp_raw_cas_w with "Hll Hlb"); [left; reflexivity | reflexivity | reflexivity | vx | reflexivity | a2 | a2 |
    intros _; wi_store |]. iNext. iIntros "Hll Hlb".
  rewrite (_ : of_bytes (int_bytes 1) =? ((1 mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32 = true); [|reflexivity].
  rewrite (_ : of_bytes (int_bytes 1) mod 2 ^ 32 = 1); [|reflexivity].
  step. branch. step. step. branch. step. branch. step.
  iApply wp_ret_void. iNext. iApply ("HK" with "[$Hts $Hts0 $Hgl $Hgl0 $Hll Hlb] Hcl H0 H8 H16 H24").
  iSplitL ""; [iFrame "#"|]. iSplit; [done|]. iSplit; [iPureIntro; lia|]. iExact "Hlb".
Qed.
End clone.

(** ## Cutting zero bytes into fields

    Glibc gives every stream 224 zero bytes for its wide state.
    Orientation stores pointers and flags into some of them and leaves
    the rest zero. A store needs ownership of one field at a time, so
    the proof first cuts the zero bytes into those fields. *)

Module WfVL := VariadicLogicOn R LG0.
Import WfVL.

Section split.
Context `{!gen_heapGS piece pval Σ}.

(** A conversion descriptor before orientation holds only zeros. The
    predicate [izero] b o owns its pointer and integer fields. *)
Definition izero (b o : Z) : iProp Σ := pcell b o null ∗ pcell b (o + 8) null ∗ pcell b (o + 16) null ∗
  bytes b (o + 24) (replicate 16 0) ∗ pcell b (o + 40) null ∗ bytes b (o + 48) (replicate 8 0).

(** Eight zero bytes with empty capability slots form a null pointer. *)
Lemma zp b o o2 n : o2 = o + 8 -> bytes b o (replicate (8 + n) 0) -∗ auxes b o (replicate (8 + n) CNone) -∗
  pcell b o null ∗ bytes b o2 (replicate n 0) ∗ auxes b o2 (replicate n CNone).
Proof using Type. intros ->. iIntros "Hb Ha". iApply (zero_cell_prefix with "Hb Ha"). Qed.

(** The first k zero bytes split off from the rest. *)
Lemma zb b o o2 k n : o2 = o + Z.of_nat k -> bytes b o (replicate (k + n) 0) -∗ auxes b o (replicate (k + n) CNone) -∗
  bytes b o (replicate k 0) ∗ auxes b o (replicate k CNone) ∗ bytes b o2 (replicate n 0) ∗ auxes b o2 (replicate n CNone).
Proof using Type. intros ->. rewrite !replicate_add bytes_app auxes_app !length_replicate. iIntros "[$ $] [$ $]". Qed.
(** Sixteen zero bytes of a descriptor hold its flags, its call count,
    its marker word and four bytes of padding. *)
Lemma zero16 b o : bytes b o (replicate 16 0) -∗
  bytes b o (int_bytes 0) ∗ bytes b (o + 4) (int_bytes 0) ∗ bytes b (o + 8) (int_bytes 0) ∗ bytes b (o + 12) [0; 0; 0; 0].
Proof using Type.
  rewrite (_ : replicate 16 0 = int_bytes 0 ++ int_bytes 0 ++ int_bytes 0 ++ [0; 0; 0; 0]); [|reflexivity].
  rewrite !bytes_app. change (length (int_bytes 0)) with 4%nat. rewrite -!Z.add_assoc. iIntros "($ & $ & $ & $)".
Qed.

Lemma wide_zero_split wb : bytes wb 0 (replicate 224 0) -∗ auxes wb 0 (replicate 224 CNone) -∗
  ([∗ list] i ↦ p ∈ replicate 11 null, pcell wb (woff_ptr i) p) ∗ bytes wb 88 (replicate 16 0) ∗
  auxes wb 88 (replicate 16 CNone) ∗ izero wb 104 ∗ izero wb 160 ∗ bytes wb 216 (replicate 8 0) ∗
  auxes wb 216 (replicate 8 CNone).
Proof using Type.
  iIntros "Hb Ha".
  Local Ltac zp1 o o2 n H := iDestruct (zp _ o o2 n with "Hb Ha") as H; [lia|].
  Local Ltac zb1 o o2 k n H := iDestruct (zb _ o o2 k n with "Hb Ha") as H; [lia|].
  zp1 0 8 216%nat "(P0 & Hb & Ha)". zp1 8 16 208%nat "(P1 & Hb & Ha)". zp1 16 24 200%nat "(P2 & Hb & Ha)".
  zp1 24 32 192%nat "(P3 & Hb & Ha)". zp1 32 40 184%nat "(P4 & Hb & Ha)". zp1 40 48 176%nat "(P5 & Hb & Ha)".
  zp1 48 56 168%nat "(P6 & Hb & Ha)". zp1 56 64 160%nat "(P7 & Hb & Ha)". zp1 64 72 152%nat "(P8 & Hb & Ha)".
  zp1 72 80 144%nat "(P9 & Hb & Ha)". zp1 80 88 136%nat "(P10 & Hb & Ha)".
  zb1 88 104 16%nat 120%nat "($ & $ & Hb & Ha)".
  zp1 104 112 112%nat "(C0 & Hb & Ha)". zp1 112 120 104%nat "(C1 & Hb & Ha)". zp1 120 128 96%nat "(C2 & Hb & Ha)".
  zb1 128 144 16%nat 80%nat "(C3 & _ & Hb & Ha)". zp1 144 152 72%nat "(C4 & Hb & Ha)".
  zb1 152 160 8%nat 64%nat "(C5 & _ & Hb & Ha)".
  zp1 160 168 56%nat "(D0 & Hb & Ha)". zp1 168 176 48%nat "(D1 & Hb & Ha)". zp1 176 184 40%nat "(D2 & Hb & Ha)".
  zb1 184 200 16%nat 24%nat "(D3 & _ & Hb & Ha)". zp1 200 208 16%nat "(D4 & Hb & Ha)".
  zb1 208 216 8%nat 8%nat "(D5 & _ & Hb & Ha)".
  iFrame "Hb Ha". iSplitL "P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10"; [iFrame; done|]. rewrite /izero.
  iSplitL "C0 C1 C2 C3 C4 C5"; iFrame.
Qed.
End split.

(** ## Orienting an idle stream

    Hello's wide print call asks `c: _IO_fwide` twice whether stdout is
    wide. The first call finds an idle stream and either refuses it,
    because an earlier narrow call oriented it, or makes it wide by
    filling its two conversion descriptors from the C locale's table.
    The second call finds the wide stream and returns at once. The two
    lemmas below prove the contracts that [WPrintfInternal](../stdio/WPrintfInternal.v)
    assumes for these calls, with [wfwide_res] as the resource W. *)

Section fwide.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (Hts : lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (objp ts))
  (Hlk : lookup (TAtom "__gconv_lock") (ge_globals ge) = Some (objp lk))
  (Htw : lookup (TAtom "glibc_wcsmbsload#to_wc") (ge_globals ge) = Some (rop tw))
  (Htm : lookup (TAtom "glibc_wcsmbsload#to_mb") (ge_globals ge) = Some (rop tm))
  (Hset : registry (TAtom "zmemset") = Some (void_only (memset_contract os_world)))
  (Hset_fn : find_fn ge (TAtom "zmemset") = None)
  (Hset_sym : lookup (TAtom "zmemset") (ge_globals ge) = None)
  `{!Defines ge "__wcsmbs_clone_conv" glibc_clone_conv, !Defines ge "__GI_memset" Unit_string_memset_os.fn___GI_memset}.
Context (vb : Z) (self : ptr).

(** A wide stream reads its mode, finds 1 and returns it, and nothing
    in the stream changes. *)
Lemma wprintf_fwide_wide dq : wprintf_fwide_wide_spec vb self (wfwide_res dq).
Proof using Type.
  intros fr fp Φ Hfr. injection Hfr as <-. iIntros "HF HW HK".
  iDestruct "HF" as "(%fb & %freg & %st & %nb & %wd & %w & %tw' & %tm' & %Hp & Hl & Hfields & Hrest)".
  pose proof Hp as (-> & Ha & Hb & He & Hr & _ & _ & Hm & _). unfold file_size in He.
  iDestruct "Hfields" as "(%L & Hfl & Hptr & Hfd & Hf2 & Hold & %Lc & Hcol & Hlock & Hoff & Hcv & Hwd & Hfl1 & Hfb &
    Hmode & Htot & Hvt)".
  step. iApply wp_alloc; [vm_compute; reflexivity|vm_compute; congruence|vm_compute; congruence|
    intros ? ? ? ? Hfresh Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hfresh Hw)|]. iNext. iIntros (cb _) "_".
  step. branch. step. step. branch. step. step. step. step. rewrite Hm. iDestruct "Hmode" as "[%Hmr Hmode]".
  check "Hl". load_s32 "Hl" "Hmode". step. branch. step. branch. step. step. load_s32 "Hl" "Hmode".
  iApply wp_ret; [reflexivity|vx|]. iNext. change (1 mod 2^32) with 1. iApply ("HK" with "[-HW] HW").
  iExists fb, freg, st, nb, wd, w, tw', tm'. iFrame. do 3 (iSplit; [done|]). rewrite Hm. by iFrame.
Qed.

(** An idle stream with mode minus one stays narrow. An unoriented
    stream asks [wp_clone_conv] for the locale's two steps and writes
    them into its descriptors, clears its conversion states, points its
    codecvt field at the input descriptor and its jump table at the wide
    one, and sets its mode to 1. Its wide buffer stays empty, so the
    result meets [file_wide] with no wide buffer. *)
Lemma wprintf_fwide_idle dq : wprintf_fwide_idle_spec vb self (wfwide_res dq).
Proof using Defines0 Defines1 Hlk Hset Hset_fn Hset_sym Htm Hts Htw.
  intros fr fp vr Φ Hfr. injection Hfr as <-. iIntros "#Hvt HF HW HK".
  iDestruct "HF" as "(%fb & %freg & %st & %nb & %Hp & Hl & Hfields & Hlock & Hbuf & Hwi)".
  pose proof Hp as (-> & Hfa & Hfb0 & He & Hr & Hfo & Hid & Hvtb & Hbp & Hsi). unfold file_size in He.
  iDestruct "Hfields" as "(%L & Hfl & Hptr & Hfd & Hf2 & Hold & %Lc & Hcol & Hlck & Hoff & Hcv & Hwd & Hfl1 & Hfb &
    Hmode & Htot & Hvtc)".
  step. iApply wp_alloc; [vm_compute; reflexivity|vm_compute; congruence|vm_compute; congruence|
    intros ? ? ? ? Hfresh Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hfresh Hw)|]. iNext. iIntros (cb Hcb) "Hcb".
  step. branch. step. step. branch. step. step. step. step. iDestruct "Hmode" as "[%Hmr Hmode]".
  check "Hl". load_s32 "Hl" "Hmode". step. pose proof Hid as (_ & _ & [Hm0|Hm1] & _).
  2: { rewrite Hm1 in Hmr |- *. branch. step. branch. step. step. load_s32 "Hl" "Hmode".
       iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" with "[-HW] HW"). iLeft. iSplit; [done|].
       iExists fb, freg, st, nb. iFrame. iSplit; [done|]. rewrite Hm1. by iFrame. }
  rewrite Hm0 in Hmr |- *. branch. step. step. step. step. branch. step. step. branch. step. step. step.
  iDestruct "Hwi" as (wb wreg (Hwd & Hcv0 & Hwb & Hwa & Hwe & Hwr)) "(Hwl & Hz & Ha0 & Hwv)".
  iDestruct (wide_zero_split with "Hz Ha0") as "(Hps & Hs & Has & Hci & Hco & Hsb & Hsba)". rewrite Hwd Hcv0.
  check "Hl". load "Hl" "Hwd" "Hwl". step. check "Hl". store "Hl" "Hcv".
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _)". rewrite /woff_ptr /=.
  check "Hl". load "Hl" "Hwd" "Hwl". load "Hl" "Hwd" "Hwl". step. check "Hwl". load_null "Hwl" "P1".
  check "Hwl". store "Hwl" "P0". check "Hl". load "Hl" "Hwd" "Hwl". step. load "Hl" "Hwd" "Hwl". step.
  check "Hwl". load_null "Hwl" "P3". check "Hwl". store "Hwl" "P4". check "Hl". load "Hl" "Hwd" "Hwl". step.
  iDestruct (zb wb 88 96 8 8 with "Hs Has") as "(Hs0 & Ha0 & Hs1 & Ha1)"; [done|].
  Local Ltac zset o H :=
    iApply (wp_call_glibc_memset Hset Hset_fn Hset_sym _ _ _ _ _ _ _ _ _ _ _ o (replicate 8 0) (replicate 8 CNone) 0
      with H); [vxu|apply defines|reflexivity|lia|cbn; lia|assumption|done|lia|cbn; lia|done|];
    iNext; iIntros H; change (clear_slots o (replicate 8 CNone)) with (replicate 8 CNone); cbn [length replicate].
  zset 88 "Hwl Hs0 Ha0". check "Hl". load "Hl" "Hwd" "Hwl". step. zset 96 "Hwl Hs1 Ha1".
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. destruct Hcb as (Hcb0 & Hcba & Hcbe).
  change (cb mod 16 = 0) in Hcba. change (cb + 32 <= 2^48) in Hcbe. assert (Hcb8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (obj_zero_block with "Hcb") as "(Hcl & Hx & Hc)"; [compute; discriminate|].
  iAssert (live cb (mkRegion cb (cb + 32) Heap Live)) with "Hcl" as "Hcl".
  change (Z.to_nat (req_extent (heap_req 8 32))) with (8 + (8 + (8 + (8 + 0))))%nat.
  iDestruct (zero_cell_prefix with "Hx Hc") as "(H0 & Hx & Hc)". iDestruct (zero_cell_prefix with "Hx Hc") as "(H8 & Hx & Hc)".
  iDestruct (zero_cell_prefix with "Hx Hc") as "(H16 & Hx & Hc)". iDestruct (zero_cell_prefix with "Hx Hc") as "(H24 & _ & _)".
  iEval (rewrite /pcell /pts big_sepL_cons) in "H8 H24". iDestruct "H8" as "[_ H8]". iDestruct "H24" as "[_ H24]".
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_clone_conv Hts Hlk with "HW Hcl H0 H8 H16 H24"); [reflexivity|exact Hcb8|exact Hcb0|cbn; lia|cbn; lia|].
  iNext. iIntros "HW Hcl H0 H8 H16 H24". resume.
  step. check "Hcl". iApply (wp_raw_load with "Hcl H8"); [reflexivity|vx|reflexivity|a2|]. iNext. iIntros "Hcl H8".
  step. branch. step. step. check "Hcl". iApply (wp_raw_load with "Hcl H24"); [reflexivity|vx|reflexivity|a2|].
  iNext. iIntros "Hcl H24". step. branch. step.
  iDestruct "HW" as "(Hloc & #Htab & #Hwf & Hglk)". iPoseProof "Htab" as "(_ & _ & _ & _ & _ & _ & Hstl & _ & _)".
  iDestruct (wfwide_tables with "Hwf") as "(_ & _ & _ & Hml & _)".
  check "Hcl". load_pointer_dq "Hcl H0 Hstl" by a2. iNext. iIntros "Hcl H0 _".
  iDestruct "Hci" as "(C0 & C1 & C2 & C3 & C4 & C5)". check "Hwl". store "Hwl" "C0". step. step. check "Hwl".
  iDestruct (zero16 with "C3") as "(N128 & N132 & N136 & N140)".
  store_int "Hwl" "N132". step. check "Hwl". store_int "Hwl" "N136". step. check "Hwl". store_int "Hwl" "N128".
  step. step. check "Hl". load "Hl" "Hwd" "Hwl". step. check "Hwl". store "Hwl" "C4".
  step. step. check "Hcl". load_pointer_dq "Hcl H16 Hml" by a2. iNext. iIntros "Hcl H16 _".
  iDestruct "Hco" as "(D0 & D1 & D2 & D3 & D4 & D5)". check "Hwl". store "Hwl" "D0". step. step.
  iDestruct (zero16 with "D3") as "(M184 & M188 & M192 & M196)". check "Hwl". store_int "Hwl" "M188". step.
  check "Hwl". store_int "Hwl" "M192". step. check "Hwl". store_int "Hwl" "M184". step.
  check "Hl". load "Hl" "Hwd" "Hwl". step. check "Hwl". store "Hwl" "D4". step.
  check "Hl". load "Hl" "Hwd" "Hwl". step. check "Hwl". iDestruct "Hvt" as "(%Hvtf & #Hvbl & _)".
  assert (Hvx : 0 <= vb + vt_wfile < 2^64)
    by (destruct Hvtf as (_ & Hve & _ & Hv0 & Hvr); change io_vtables_size with 2352 in Hve; unfold vt_wfile; lia).
  load_pointer_dq "Hwl Hwv Hvbl" by a2. iNext. iIntros "Hwl Hwv _". check "Hl". store "Hl" "Hvtc".
  step. step. step. check "Hl". store_int "Hl" "Hmode". iApply wp_ret; [reflexivity|vx|]. iNext.
  assert (E88 : (wb mod 2^64 + 88 mod 2^64) mod 2^64 = wb + 88) by (rewrite !(Z.mod_small _ (2^64)); lia).
  assert (E104 : (wb mod 2^64 + 104 mod 2^64) mod 2^64 = wb + 104) by (rewrite !(Z.mod_small _ (2^64)); lia).
  iEval (cbn [ptr_addr ptr_cap]; rewrite E88) in "C4 D4". iEval (rewrite E104) in "Hcv".
  change ((1 mod 2^32) mod 2^32) with 1. change (1 mod 2^32) with 1 in *. change (0 mod 2^32) with 0.
  change (9 mod 2^32) with 9. change (0 mod 256) with 0.
  destruct (idle_wide_rules fb nb st Hfo Hbp Hsi) as [Hwfo Hws]. pose proof (idle_ok_widle_ok _ _ Hid) as (Hw1 & Hw2 & _ & Hw3).
  iAssert (wfwide_res dq) with "[Hloc Hglk]" as "HW"; [iFrame "Hloc Hglk Htab Hwf"|].
  iApply ("HK" $! 1 with "[-HW] HW"). iRight. iSplit; [done|].
  iExists fb, freg, (mkFstate (fs_flags st) (fs_ptrs st) (fs_fileno st) (fs_flags2 st) (fs_old_offset st) (fs_column st)
    (fs_lock st) (fs_offset st) (mkPtr (wb + woff_cd_in) (Obj wb)) (fs_wide st) (fs_freeres_list st) (fs_freeres_buf st)
    1 (fs_total st) (mkPtr (vb + vt_wfile) (Ro vb))), nb, wb, WbNone, (rop tw), (rop tm).
  iSplit. { iPureIntro. split_and!; try done. exact (conj Hw1 (conj Hw2 (conj (or_introl eq_refl) Hw3))). }
  iFrame "Hl Hlock Hbuf". iSplitL "Hfl Hptr Hfd Hf2 Hold Hcol Hlck Hoff Hcv Hwd Hfl1 Hfb Hmode Htot Hvtc".
  { rewrite /file_fields /=. iFrame. rewrite Hwd. iFrame. iSplit; [done|]. iSplit; [done|]. iSplit; [iPureIntro; lia|]. done. }
  iExists wreg, (replicate 11 null), null, null, null, null, 1, 0, 9, 0, [0; 0; 0; 0], (replicate 8 CNone).
  iSplit. { iPureIntro. split_and!; try done; try lia. left; reflexivity. repeat constructor; lia. }
  iDestruct (zb wb 216 220 4 4 with "Hsb Hsba") as "(Hsb0 & Hsba0 & Hsb1 & Hsba1)"; [done|].
  rewrite /iconv_cell /woff_cd_in /woff_cd_out /woff_state /woff_shortbuf /woff_vtable /woff_ptr.
  iAssert (auxes wb 216 (replicate 8 CNone)) with "[Hsba0 Hsba1]" as "Hsba".
  { rewrite (_ : replicate 8 CNone = replicate 4 CNone ++ replicate 4 CNone); [|done]. rewrite auxes_app. iFrame. }
  iAssert (bytes wb 88 (replicate 16 0) ∗ auxes wb 88 (replicate 16 CNone))%I with "[Hs0 Hs1 Ha0 Ha1]" as "[Hs Has]".
  { rewrite (_ : replicate 16 0 = replicate 8 0 ++ replicate 8 0); [|done].
    rewrite (_ : replicate 16 CNone = replicate 8 CNone ++ replicate 8 CNone); [|done]. rewrite bytes_app auxes_app. iFrame. }
  rewrite /int_cell. iFrame. rewrite big_sepL_nil. iPureIntro. split_and!; try reflexivity; lia.
Qed.
End fwide.
