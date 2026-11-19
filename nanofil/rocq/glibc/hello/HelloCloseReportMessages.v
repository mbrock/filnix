(** Glibc returns a pointer to an error message or null. Reading
    the table supplies that pointer, but printing the message also
    requires permission to read its bytes. This module takes both
    permissions from Hello's initial error table, using the same
    index for the pointer and its target. *)

From Glibc Require Import Unit_stdioZ2dcommon_errlist_os.
From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import List String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Run Machine Pieces Heap Logic Language.
From Glibc Require Import FileInv WordString HelloGetoptTable StartImageEarly HelloImageLoad
  HelloCloseReportImage HelloCloseReportLookup Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Definition err_at (k : Z) := nth (Z.to_nat k) err_messages None.
Definition err_ptr (m : option (Z * region * list Z)) :=
  match m with Some (b, _, _) => mkPtr b (Ro b) | None => null end.

(** For every non-null slot, the allocated words cover the terminator
    and the address stored in the slot starts the message. *)
Lemma err_shape i b r s : err_messages !! i = Some (Some (b, r, s)) ->
  str_shape (mkPtr b (Ro b)) b r (lit_words s) s.
Proof.
  intros Hi. apply str_shape_b_sound.
  assert (H : forallb (fun m => match m with Some (b, r, s) =>
    str_shape_b (mkPtr b (Ro b)) b r (lit_words s) s | None => true end) err_messages = true)
    by (vm_compute; reflexivity).
  apply forallb_forall with (x := Some (b, r, s)) in H; [exact H|].
  apply list_elem_of_In, (list_elem_of_lookup_2 _ i). exact Hi.
Qed.

Lemma err_count : List.length err_messages = 134%nat.
Proof. reflexivity. Qed.

#[local] Opaque err_messages err_table err_length.

Section messages.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation gexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation dq := DfracDiscarded.

Definition err_text (m : option (Z * region * list Z)) : iProp Σ :=
  match m with Some (b, _, s) => word_string dq (mkPtr b (Ro b)) s | None => True end%I.

Local Lemma err_concat pss : ptsq dq (List.concat pss) ⊣⊢ [∗ list] ps ∈ pss, ptsq dq ps.
Proof using Type. induction pss as [|ps pss IH]; cbn [List.concat]; rewrite ?ptsq_app ?IH; done. Qed.

Lemma err_slot_own i m : err_messages !! i = Some m ->
  ptsq dq (List.concat (imap err_slot_ps err_messages)) ⊢
  pcellq dq err_table.1 (8 * Z.of_nat i) (err_ptr m) ∗ err_text m ∗
  live_capq dq (ptr_cap (err_ptr m)) (match m with Some (_, r, _) => r | None => err_table.2 end).
Proof using Type.
  intros Hi. rewrite err_concat. iIntros "#H".
  iPoseProof (big_sepL_lookup _ _ i with "H") as "Hslot"; [rewrite list_lookup_imap Hi; reflexivity|].
  iEval (rewrite /err_slot_ps ptsq_app) in "Hslot". iDestruct "Hslot" as "[Hp Ht]". iSplit; first iExact "Hp".
  destruct m as [[[b r] s]|]; last done. pose proof (err_shape i b r s Hi) as Hs.
  iEval (rewrite /lit_ps (ptsq_app _ [_])) in "Ht". iDestruct "Ht" as "[Hl Hw]".
  iSplit; last iExact "Hl". iExists b, r, (lit_words s). iSplit; first done.
  replace (wstart (mkPtr b (Ro b)) - b) with 0 by
    (unfold wstart; cbn; rewrite (ss_align _ _ _ _ _ Hs); lia). iSplit; [iExact "Hl"|iExact "Hw"].
Qed.

(** A caller of strerror gets the actual read-only string when glibc
    finds one. A hole or a number outside the table yields null and
    grants no permission to read from it. *)
Lemma wp_hello_get_errlist fr k Φ : ge_globals ge = img_globals ->
  call_frame Unit_stdioZ2dcommon_errlist_os.fn___get_errlist [WInt k] = Some fr -> 0 <= k < 2^32 ->
  ptsq dq hello_errlist_ps -∗ ▷ (err_text (err_at k) -∗ Φ (Ret (WPtr (err_ptr (err_at k))))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hg Hfr Hk. rewrite /hello_errlist_ps (ptsq_app _ [_;_]) (ptsq_app _ (cell _ _ _))
    (ptsq_app _ (List.concat _)) (ptsq_app _ [_]).
  iIntros "([#Hl #Ht] & #Hlen & #Hs & _) HK".
  assert (Hlen : Term.lookup (TAtom "_sys_errlist_internal_len") (ge_globals ge) =
    Some (mkPtr err_length.1 (Ro err_length.1))) by (rewrite Hg; vm_compute; reflexivity).
  assert (Htab : Term.lookup (TAtom "_sys_errlist_internal") (ge_globals ge) =
    Some (mkPtr err_table.1 (Ro err_table.1))) by (rewrite Hg; vm_compute; reflexivity).
  destruct (Z.ltb_spec k 134) as [Hin|Hout].
  - destruct (lookup_lt_is_Some_2 err_messages (Z.to_nat k)) as [m Hm]; [rewrite err_count; lia|].
    rewrite /err_at nth_lookup Hm. cbn [default].
    iDestruct (err_slot_own _ _ Hm with "Hs") as "(Hp & Htext & Htgt)".
    rewrite Z2Nat.id; last lia.
    iApply (wp_close_get_errlist fr k _ err_length.2 _ err_table.2 (err_ptr m) _ Φ Hfr Hk Hlen Htab with "Hl Hlen Ht [Hp Htgt]");
      [reflexivity|discriminate|discriminate|reflexivity|reflexivity|discriminate|discriminate| | | ].
    + destruct m as [[[b r] s]|]; last (cbn; lia). pose proof (err_shape _ _ _ _ Hm) as HS.
      pose proof (ss_fit _ _ _ _ _ HS) as Hfit. pose proof (ss_align _ _ _ _ _ HS).
      pose proof (ss_base _ _ _ _ _ HS). pose proof (ss_space _ _ _ _ _ HS).
      unfold wstart in Hfit. cbn [ptr_addr err_ptr] in Hfit |- *. lia.
    + rewrite (proj2 (Z.ltb_lt _ _) Hin). iSplit; [iExact "Hp"|iExact "Htgt"].
    + rewrite (proj2 (Z.ltb_lt _ _) Hin). iNext. iApply ("HK" with "Htext").
  - rewrite /err_at nth_overflow; last (rewrite err_count; lia).
    iApply (wp_close_get_errlist fr k _ err_length.2 _ err_table.2 null err_table.2 Φ Hfr Hk Hlen Htab with "Hl Hlen Ht []");
      [reflexivity|discriminate|discriminate|reflexivity|reflexivity|discriminate|discriminate|cbn; lia| | ].
    + rewrite (proj2 (Z.ltb_ge _ _) Hout). done.
    + rewrite (proj2 (Z.ltb_ge _ _) Hout). iNext. iApply "HK". done.
Qed.
End messages.
