(** Hello's wide print call makes stdout wide with `c: _IO_fwide`. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic HelloLeaf.
From Glibc Require Import CodePrelude HelloImageCode125 HelloImageCode274 HelloImageModule HelloImageLoad
  OsWorld OsBlocks FileInv FileIdle LibioLogic LibioWIdle MemFwdLogic Mbrtowc StartImageCpu StartImageEarly HelloImageMbsObjs HelloImageWFwideObjs WPrintfInternal Fix.
From Glibc Require MemchrLast StartInitMisc.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).

Definition glibc_clone_conv := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_274])) "__wcsmbs_clone_conv".

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
Proof. intros ->. rewrite !replicate_add bytes_app auxes_app !length_replicate. iIntros "[$ $] [$ $]". Qed.
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
