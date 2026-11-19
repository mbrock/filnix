(** The wide formatter's append loop flushes the staging array when it runs
    out of room. The dispatcher checks the mode before and after the call
    to the file backend. A short write leaves the buffer failed; a complete
    write leaves all 128 character positions available for the next append. *)

From Glibc Require Import Unit_stdioZ2dcommon_wprintf_buffer_flush_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic WordBits.
From Glibc Require Import CodePrelude Fix OsWorld FileInv LibioLogic
  LibioCloseSteps LibioPutsInv LibioWIdle PrintfOut WPrintfFileFlush.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Definition wprintf_dispatch_fn := Unit_stdioZ2dcommon_wprintf_buffer_flush_os.fn___wprintf_buffer_flush.

(** The stream counts characters, but the array stores four bytes per character. *)
Definition stage_bytes (cs : list Z) := flat_map (fun c => le_bytes c 4) cs.
Lemma stage_bytes_length cs : length (stage_bytes cs) = (4 * length cs)%nat.
Proof. induction cs as [|c cs IH]; [done|]. change (length (le_bytes c 4 ++ stage_bytes cs) = (4 * S (length cs))%nat).
  rewrite length_app length_le_bytes IH. lia. Qed.

Lemma stage_bytes_valid cs : Forall (fun b => 0 <= b < 256) (stage_bytes cs).
Proof. induction cs as [|c cs IH]; [constructor|]. apply Forall_app. split; [|exact IH].
  apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (i & <- & _). apply byte_of_range. Qed.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section dispatch.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The prefix holds the characters that the next flush will offer the
    stream. The unused suffix need not be zero: a successful flush rewinds
    the cursor without clearing any bytes or [[capability]] slots. *)
Definition wide_stage bb br fp cs written (active : bool) : iProp Σ :=
  ∃ tail slots,
    ⌜0 < bb /\ bb mod 8 = 0 /\ bb + 560 <= r_end br /\ r_end br <= 2^63 /\
      0 <= written < 2^64 /\ Forall (fun c => 0 <= c < 2^32) cs /\
      (4 * length cs + length tail = 512)%nat /\ length slots = 512%nat /\
      Forall (fun b => 0 <= b < 256) tail⌝ ∗
    live bb br ∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) ∗
    pcell bb 8 (mkPtr (bb + 48 + 4 * Z.of_nat (length cs)) (Obj bb)) ∗
    pcell bb 16 (mkPtr (bb + 560) (Obj bb)) ∗ icell bb 24 written ∗
    int_cell bb 32 (if active then 2 else 0) ∗ pcell bb 40 fp ∗
    bytes bb 48 (stage_bytes cs ++ tail) ∗ auxes bb 48 slots.

Context (vb : Z) (self : ptr) (E : iProp Σ)
  (Hfn : ge_fn ge "__GI__IO_wfile_xsputn" wprintf_xsputn_fn)
  (Hcall : wprintf_xsputn_call_spec vb self E).

(** The file backend puts the old prefix back in the unused suffix when
    it rewinds the cursor. It keeps the prefix pending on failure. *)
Lemma wp_wprintf_stage_flush fr bb br fp vreg cs written Φ :
  call_frame wprintf_file_flush_fn [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ file_wide ge vb self fp 1 -∗ E -∗
  wide_stage bb br fp cs written true -∗
  ▷ (∀ ok : bool, file_wide ge vb self fp 1 -∗ E -∗
    wide_stage bb br fp (if ok then [] else cs)
      (if ok then (written + Z.of_nat (length cs)) mod 2^64 else written) ok -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  iIntros (Hfr) "#Hvt #Hwv HF HE (%tail & %slots & %H & Hl & Hbase & Hcur & Hstop & Hw & Hm & Hfp & Hbs & Ha) HK".
  destruct H as (Hbb & Hal & Hend & Hreg & Hwr & Hvalid & Hlen & Hslots & Htail).
  iEval (rewrite bytes_app) in "Hbs". iDestruct "Hbs" as "[Hcs Htail]".
  iApply (wp_wprintf_file_flush vb self E Hfn Hcall with "Hvt Hwv HF HE Hl Hcur Hfp Hcs Hw Hm");
    try assumption; [lia|]. iNext. iIntros (ok) "HF HE Hl Hcur Hfp Hcs Hw Hm".
  iApply ("HK" $! ok with "HF HE"). destruct ok.
  - iExists (stage_bytes cs ++ tail)%list, slots. rewrite /stage_bytes /= !Z.add_0_r bytes_app.
    iFrame. iPureIntro. rewrite length_app stage_bytes_length. repeat split; try assumption;
      try lia; try apply Z.mod_pos_bound; try lia; try constructor. apply Forall_app. auto using stage_bytes_valid.
  - iExists tail, slots. rewrite bytes_app. iFrame. done.
Qed.

Context (Hflush : find_fn ge (TAtom "__wprintf_buffer_flush_to_file") = Some (Defined wprintf_file_flush_fn)).

(** The return value tells the append loop whether the next character
    fits. A failed buffer returns zero without retrying the stream. *)
Lemma wp_wprintf_dispatch fr bb br fp vreg cs written active Φ :
  call_frame wprintf_dispatch_fn [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ file_wide ge vb self fp 1 -∗ E -∗
  wide_stage bb br fp cs written active -∗
  ▷ (∀ ok : bool, file_wide ge vb self fp 1 -∗ E -∗
    wide_stage bb br fp (if ok then [] else cs)
      (if ok then (written + Z.of_nat (length cs)) mod 2^64 else written) ok -∗
    Φ (Ret (WInt (if ok then 1 else 0)))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr. injection Hfr as <-.
  iIntros "#Hvt #Hwv HF HE (%tail & %slots & %H & Hl & Hbase & Hcur & Hstop & Hw & Hm & Hfp & Hbs & Ha) HK".
  pose proof H as (Hbb & Hal & Hend & Hreg & _). step. step. check "Hl". load_mode "Hl" "Hm". step.
  destruct active; branch; step.
  - step. clear Hmode_range. load_mode "Hl" "Hm". step. branch. step. step. branch. step.
    iApply wp_call_bind; [vx | exact Hflush | reflexivity |]. iNext.
    iApply (wp_wprintf_stage_flush with "Hvt Hwv HF HE [Hl Hbase Hcur Hstop Hw Hm Hfp Hbs Ha]"); [reflexivity | iExists tail, slots; iFrame; done |].
    iNext. iIntros (ok) "HF HE (%tl & %sl & %H' & Hl & Hbase & Hcur & Hstop & Hw & Hm & Hfp & Hbs & Ha)".
    resume. step. step. step. check "Hl". clear Hmode_range. load_mode "Hl" "Hm". step. destruct ok; branch; step.
    + step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur". step.
      load_self_using wp_raw_load_pointer_self "Hl Hstop". do 3 step. branch_as false. step.
      iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" $! true with "HF HE"). iExists tl, sl. by iFrame.
    + iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" $! false with "HF HE"). iExists tl, sl. by iFrame.
  - iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" $! false with "HF HE"). iExists tail, slots. by iFrame.
Qed.
End dispatch.
