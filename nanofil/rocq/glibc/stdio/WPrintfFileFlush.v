(** The wide formatter flushes its private array by calling the stream's
    xsputn slot, even when the array is empty. An exact write resets the
    cursor. A short write leaves the cursor in place and marks the buffer
    failed, so later appends stop. *)

From Glibc Require Import HelloImageTypedIO HelloImageTypedWP.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld FileInv
  LibioLogic LibioCloseSteps LibioPutsInv LibioWIdle.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

(** The first function reads the stream's jump table. The second takes
    the array pointer and the number of characters to write. *)
Definition wprintf_file_flush_fn := hello_image_fn___wprintf_buffer_flush_to_file.
Definition wprintf_xsputn_fn := hello_image_fn___GI__IO_wfile_xsputn.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section flush.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context (vb : Z) (self : ptr) (E : iProp Σ).

(** The stream borrows the staged characters without taking ownership of
    the rest of the array. It may accept fewer characters than requested. *)
Definition wprintf_xsputn_call_spec : Prop := forall fr fp bb breg dq cs Φ,
  0 < bb -> bb mod 8 = 0 -> bb + 560 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Z.of_nat (length cs) <= 128 -> Forall (fun c => 0 <= c < 2 ^ 32) cs ->
  call_frame wprintf_xsputn_fn
    [WPtr fp; WPtr (mkPtr (bb + 48) (Obj bb)); WInt (Z.of_nat (length cs))] = Some fr ->
  file_wide ge vb self fp 1 -∗ E -∗ liveq dq bb breg -∗ bytesq dq bb 48 (flat_map (fun c => le_bytes c 4) cs) -∗
  ▷ (∀ r, ⌜0 <= r <= Z.of_nat (length cs)⌝ -∗ file_wide ge vb self fp 1 -∗ E -∗
    liveq dq bb breg -∗ bytesq dq bb 48 (flat_map (fun c => le_bytes c 4) cs) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

(** Loading a slot requires access to the stream and its vtable pointer.
    The formatter returns both before it calls the stream. *)
Local Lemma wide_vtable_loan fp :
  file_wide ge vb self fp 1 -∗ ∃ fb freg,
    ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + 224 <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗
    live fb freg ∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) ∗
    (live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ file_wide ge vb self fp 1).
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %wd & %w & %tw & %tm & %Hp & Hl & Hfields & Hrest)".
  pose proof Hp as (Hfp & Hal & Hfb & Hend & Hreg & _ & _ & _ & Hvt & _).
  iDestruct "Hfields" as "(%Hlen & Hfl & Hptrs & Hfd & Hf2 & Ho & %Hcol & Hc & Hlk & Hof & Hcv & Hwd & Hfr & Hbuf & Hm & Htw & Hvt)".
  rewrite Hvt. iExists fb, freg. iSplit; [iPureIntro; unfold file_size in *; auto|].
  iFrame "Hl Hvt". iIntros "Hl Hvt". iExists fb, freg, st, nb, wd, w, tw, tm.
  iFrame "Hl Hrest". iSplit; [done|]. rewrite /file_fields Hvt. by iFrame.
Qed.

Context (Hfn : ge_fn ge "__GI__IO_wfile_xsputn" wprintf_xsputn_fn)
  (Hcall : wprintf_xsputn_call_spec).

(** A successful flush counts the characters and rewinds the cursor. A
    failed flush changes only the mode. Both paths return the source bytes. *)
Lemma wp_wprintf_file_flush fr bb breg fp vreg cs written Φ :
  let n := Z.of_nat (length cs) in
  call_frame wprintf_file_flush_fn [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 560 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  n <= 128 -> Forall (fun c => 0 <= c < 2 ^ 32) cs -> 0 <= written < 2 ^ 64 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ file_wide ge vb self fp 1 -∗ E -∗
  live bb breg -∗ pcell bb 8 (mkPtr (bb + 48 + 4*n) (Obj bb)) -∗ pcell bb 40 fp -∗
  bytes bb 48 (flat_map (fun c => le_bytes c 4) cs) -∗ icell bb 24 written -∗ int_cell bb 32 2 -∗
  ▷ (∀ ok : bool, file_wide ge vb self fp 1 -∗ E -∗ live bb breg -∗
     pcell bb 8 (mkPtr (if ok then bb + 48 else bb + 48 + 4*n) (Obj bb)) -∗ pcell bb 40 fp -∗
     bytes bb 48 (flat_map (fun c => le_bytes c 4) cs) -∗
     icell bb 24 (if ok then (written + n) mod 2 ^ 64 else written) -∗ int_cell bb 32 (if ok then 2 else 0) -∗
     Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros n Hfr Hbb Hal Hend Hreg Hn Hcs Hw. injection Hfr as <-.
  assert (Hn0 : 0 <= n) by (unfold n; lia).
  iIntros "#Hvt #Hwv HF HE Hb Hcur Hfp Hcs Hw Hm HK".
  iDestruct (wide_vtable_loan with "HF") as (fb freg (-> & Hfb & Hfa & Hfe & Hfrg)) "(Hf & Hvtp & Hclose)".
  iPoseProof (wvtables_slot ge vb slot_xsputn "__GI__IO_wfile_xsputn" with "Hwv") as "#Hslot"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "__GI__IO_wfile_xsputn")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfn). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)".
  unfold io_vtables_size in Hvend.
  step. step. check "Hb". load_self_using wp_raw_load_pointer_self "Hb Hcur".
  do 6 step. check "Hb". load "Hb" "Hfp" "Hf". step. check "Hf".
  iApply (wp_raw_load_pointer_dq with "Hf Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_wfile; lia |].
  iNext. iIntros "Hf Hvtp _". step. step_global Hvg. do 3 step. unfold vt_wfile. norm.
  replace (bb + 48 + 4*n - (bb + 48)) with (n * 4) by lia.
  replace (vb + 840 - vb) with 840 by lia. norm.
  change (sign_extension (2^64) (2^63) 4) with 4. unfold sign_extension. change (4 =? 0) with false.
  rewrite (Z.mod_small (n*4) (2^64)); [|lia]. rewrite (proj2 (Z.leb_gt (2^63) (n*4)) ltac:(lia)).
  rewrite Z.quot_mul; [|lia]. norm. branch. step. step.
  check_read_dq "Hvl" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl Hslot Hfc");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hfn) |].
  iNext. iIntros "_ _ _". step. check "Hb". load "Hb" "Hfp" "Hf". step.
  iDestruct ("Hclose" with "Hf Hvtp") as "HF".
  norm. iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfn) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfn) | apply (ge_fn_check _ _ _ Hfn) |
    vx | apply (ge_fn_find _ _ _ Hfn) | reflexivity | reflexivity |]. iNext.
  rewrite (Z.mod_small n (2^64)); [|lia]. iApply (Hcall with "HF HE Hb Hcs"); try assumption; [reflexivity|].
  iNext. iIntros (r Hr) "HF HE Hb Hcs". resume. fold n in Hr. step. norm.
  destruct (Z.eq_dec r n) as [-> | Hneq].
  - rewrite Z.eqb_refl. branch. step. step. check "Hb".
    iApply (wp_raw_load with "Hb Hw"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Hb Hw".
    step. check "Hb". store_long "Hb" "Hw". step. step. check "Hb". store "Hb" "Hcur".
    iApply wp_ret_void. iNext. norm. iApply ("HK" $! true with "HF HE Hb Hcur Hfp Hcs [Hw] Hm").
    rewrite Z.mod_mod; [iExact "Hw"|lia].
  - rewrite (proj2 (Z.eqb_neq r n) Hneq). branch. step. step. check "Hb".
    iDestruct "Hm" as "[_ Hm]". store_int "Hb" "Hm". iApply wp_ret_void. iNext.
    iApply ("HK" $! false with "HF HE Hb Hcur Hfp Hcs Hw [Hm]"). iSplit; [done|iExact "Hm"].
Qed.
End flush.
