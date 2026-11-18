(** When the wide buffer has no room, glibc sends one character to the
    stream's overflow function. A wide stream already has its orientation,
    so the dispatcher need not set it again. It checks the jump table
    and calls its overflow slot with the original character. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude HelloImageCode137 HelloImageCode143 Fix OsWorld FileInv
  LibioLogic LibioCloseSteps LibioPutsInv LibioWIdle LibioOverflowBase.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Definition woverflow_fn := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_143])) "__GI___woverflow".
Definition wfile_overflow_fn := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_137])) "__GI__IO_wfile_overflow".

Section dispatch.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context (vb : Z) (self : ptr) (E : iProp Σ).

(** The stream returns the character it accepted or WEOF on failure.
    WEOF as input requests a flush; success then returns zero. *)
Definition woverflow_spec (fn : func) : Prop := forall fr fp ch Φ,
  0 <= ch < 2^32 -> call_frame fn [WPtr fp; WInt ch] = Some fr ->
  file_wide ge vb self fp 1 -∗ E -∗
  ▷ (∀ r, ⌜ovf_ret ch r⌝ -∗ file_wide ge vb self fp 1 -∗ E -∗ Φ (Ret (WInt r))) -∗ WP (ERun fr : sexpr) {{ Φ }}.

(** The dispatcher reads the mode and the table pointer, then hands the
    whole stream back before it calls the chosen function. *)
Local Lemma mode_table fp : file_wide ge vb self fp 1 ⊢ ∃ fb freg,
  ⌜fp = obj fb /\ 0 < fb /\ fb mod 8 = 0 /\ fb + 224 <= r_end freg /\ r_end freg <= 2^63⌝ ∗
  live fb freg ∗ int_cell fb off_mode 1 ∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) ∗
  (live fb freg -∗ int_cell fb off_mode 1 -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ file_wide ge vb self fp 1).
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %wd & %w & %tw & %tm & %Hp & Hl & Hfields & Hrest)".
  pose proof Hp as (Hfp & Hal & Hfb & Hend & Hreg & _ & _ & Hmode & Hvt & _).
  iDestruct "Hfields" as "(%Hlen & Hfl & Hptr & Hfd & Hf2 & Ho & %Hcol & Hc & Hlk & Hof & Hcv & Hwd & Hfr & Hbuf & Hm & Htw & Hvt)".
  rewrite Hmode Hvt. iExists fb, freg. iSplit; [iPureIntro; unfold file_size in *; auto|].
  iFrame "Hl Hm Hvt". iIntros "Hl Hm Hvt". iExists fb, freg, st, nb, wd, w, tw, tm.
  iFrame "Hl Hrest". iSplit; [done|]. rewrite /file_fields Hmode Hvt. by iFrame.
Qed.

(** The public overflow entry uses the same rule as the file method in
    the table. Reading the table consumes no part of the stream. *)
Lemma woverflow_dispatch_spec vr :
  ge_fn ge "__GI__IO_wfile_overflow" wfile_overflow_fn ->
  (E ⊢ vtables_ro ge vb vr ∗ wvtables_ro ge vb ∗ E) ->
  woverflow_spec wfile_overflow_fn -> woverflow_spec woverflow_fn.
Proof using Type*.
  intros Hfn Htables Hcall fr fp ch Φ Hch Hfr. injection Hfr as <-. iIntros "HF HE HK".
  iDestruct (Htables with "HE") as "(#Hvt & #Hwv & HE)".
  iDestruct (mode_table with "HF") as (fb br (-> & Hfb & Hfa & Hend & Hr)) "(Hl & [%Hm Hm] & Hvtp & Hclose)".
  iPoseProof (wvtables_slot ge vb slot_overflow "__GI__IO_wfile_overflow" with "Hwv") as "#Hslot"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "__GI__IO_wfile_overflow")) vr) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfn). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvr) & Hvl & _)". unfold io_vtables_size in Hvend.
  step. step. check "Hl". load_s32 "Hl" "Hm". step. branch. step. step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity|vx|left; reflexivity|a2|a2|cbn; unfold vt_wfile; lia|].
  iNext. iIntros "Hl Hvtp _". step. step_global Hvg. do 3 step. unfold vt_wfile. norm.
  replace (vb+840-vb) with 840 by lia. branch. step. step. check_read_dq "Hvl" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl Hslot Hfc");
    [reflexivity|vx|right; reflexivity|a2|a2|apply (ge_fn_addr _ _ _ Hfn)|].
  iNext. iIntros "_ _ _". iDestruct ("Hclose" with "Hl [Hm] Hvtp") as "HF"; [by iSplit|].
  iApply wp_check_function; [vx|apply (ge_fn_check _ _ _ Hfn)|]. iNext.
  iApply wp_raw_call_bind; [vx|apply (ge_fn_cap _ _ _ Hfn)|apply (ge_fn_check _ _ _ Hfn)|vx|
    apply (ge_fn_find _ _ _ Hfn)|reflexivity|reflexivity|]. iNext.
  rewrite (Z.mod_small ch (2^32) Hch). iApply (Hcall with "HF HE"); [exact Hch|reflexivity|].
  iNext. iIntros (r Hret) "HF HE". resume. iApply wp_ret; [reflexivity|vx|]. iNext.
  assert (Hr32 : 0 <= r < 2^32) by (destruct Hret as [-> | ->]; [lia|destruct (ch =? 2^32-1); lia]).
  rewrite !Z.mod_mod; try lia. rewrite (Z.mod_small r (2^32) Hr32). by iApply ("HK" with "[%] HF HE").
Qed.
End dispatch.
