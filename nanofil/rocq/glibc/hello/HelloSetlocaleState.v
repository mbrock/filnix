(** When Hello selects the C locale, setlocale looks up environment
    variables such as LC_TIME and LC_PAPER. Getopt already holds part
    of each of those names. This proof puts the bytes back together so
    setlocale can read the names, and shows that it returns the global
    locale and the character tables to Hello. *)

From Glibc Require Import LiteralWords.
From Glibc Require Import GlibcProgram GlibcTactics.
From iris.program_logic Require Import language weakestpre.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv StrlenLogic WordString HelloImageLoad
  StartCtypeInitSpec StartEarlyInitSpec HelloImageEarly StartImageEarly HelloImageLocaleObjs
  HelloImageModule HelloImageCLocaleObjs HelloGettextLocaleConst HelloStartGetopt HelloLocaleState HelloSetlocalePostload HelloSetlocaleAll.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section window.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** ## Strings inside frozen words

    Glibc reads a name one word at a time, even when the name starts
    halfway through a word. To extract a name from a table, we keep the
    aligned words that contain its first byte through its terminator. *)
Lemma ws_window b reg ws (k n : nat) p s :
  (k <= length ws)%nat -> wstart p - b = 8 * Z.of_nat k -> str_shape p b reg (take n (drop k ws)) s ->
  liveq DfracDiscarded b reg -∗ ptsq DfracDiscarded (words_ps b 0 ws) -∗ word_string DfracDiscarded p s.
Proof using Type.
  intros Hk Hw Hs.
  assert (E : ws = take k ws ++ take n (drop k ws) ++ drop n (drop k ws)) by (by rewrite !take_drop).
  rewrite {1}E words_ps_app words_ps_app !ptsq_app. iIntros "#Hl (_ & #Hm & _)". iExists b, reg, (take n (drop k ws)). iSplit; [done|].
  rewrite /wwin Hw length_take_le; [|exact Hk]. iSplit; [iExact "Hl"|]. iExact "Hm".
Qed.

(** For concrete pointers and words, a computation finds the window and
    checks the string. *)
Definition ws_ok (b : Z) (reg : region) (ws : list Z) (p : ptr) (s : list Z) : bool :=
  let k := Z.to_nat ((wstart p - b) / 8) in
  let n := Z.to_nat ((ptr_addr p mod 8 + Z.of_nat (length s) + 8) / 8) in
  Nat.leb k (length ws) && (wstart p - b =? 8 * Z.of_nat k) && str_shape_b p b reg (take n (drop k ws)) s.

Lemma ws_window_b b reg ws p s : ws_ok b reg ws p s = true ->
  liveq DfracDiscarded b reg -∗ ptsq DfracDiscarded (words_ps b 0 ws) -∗ word_string DfracDiscarded p s.
Proof using Type.
  unfold ws_ok. intros H. apply andb_prop in H as [H Hs]. apply andb_prop in H as [Hk Hw].
  exact (ws_window b reg ws _ _ p s (proj1 (Nat.leb_le _ _) Hk) (proj1 (Z.eqb_eq _ _) Hw) (str_shape_b_sound _ _ _ _ _ Hs)).
Qed.

(** ## Smaller frozen shares

    A frozen share can be copied, so it holds every list of pieces that
    it contains, in any order. Whether one concrete list contains
    another is decided by computation, which needs equality of pieces
    and their values. *)
Local Instance ss_life_eq : EqDecision life.
Proof. intros x y. change ({x = y} + {x <> y}). decide equality. Defined.
Local Instance ss_kind_eq : EqDecision kind.
Proof. intros x y. change ({x = y} + {x <> y}). decide equality. Defined.
Local Instance ss_region_eq : EqDecision region.
Proof. intros x y. change ({x = y} + {x <> y}). decide equality; first [apply Z.eq_dec | apply ss_life_eq | apply ss_kind_eq]. Defined.
Local Instance ss_term_eq : EqDecision term.
Proof.
  intros x y. destruct (term_eqb x y) eqn:E; [left; apply term_eqb_eq; exact E|].
  right. intros ->. rewrite term_eqb_refl in E. discriminate.
Defined.
Local Instance ss_cap_eq : EqDecision cap.
Proof. intros x y. change ({x = y} + {x <> y}). decide equality; first [apply ss_term_eq | apply Z.eq_dec]. Defined.
Local Instance ss_ptr_eq : EqDecision ptr.
Proof. intros x y. change ({x = y} + {x <> y}). decide equality; first [apply ss_cap_eq | apply Z.eq_dec]. Defined.
Local Instance ss_pval_eq : EqDecision pval.
Proof. solve_decision. Defined.
Local Instance ss_piece_eq : EqDecision piece.
Proof. intros x y. change ({x = y} + {x <> y}). decide equality; apply Z.eq_dec. Defined.

(** A reader who can read a whole table can also read any selection of
    its entries, even if the reader visits them in a different order. *)
Lemma ptsq_incl ps qs : Forall (fun x => x ∈ ps) qs -> ptsq DfracDiscarded ps ⊢ ptsq DfracDiscarded qs.
Proof using Type.
  intros H. iIntros "#H". rewrite /ptsq. iApply big_sepL_intro. iIntros "!>" (k x Hk).
  apply list_elem_of_lookup_2 in Hk. rewrite Forall_forall in H.
  apply list_elem_of_In in Hk. specialize (H x Hk).
  iApply (big_sepL_elem_of (fun lv => pointsto lv.1 DfracDiscarded lv.2) _ _ H with "H").
Qed.

(** The inclusion of concrete lists follows by computation. *)
Lemma ptsq_incl_b ps qs : bool_decide (Forall (fun x => x ∈ ps) qs) = true ->
  ptsq DfracDiscarded ps ⊢ ptsq DfracDiscarded qs.
Proof using Type. intros H. apply ptsq_incl. exact (bool_decide_eq_true_1 _ H). Qed.

(** ## The frozen locale tables

    Startup and getopt own different parts of the same table. The
    strings passed to getenv need whole aligned words, including the
    bytes before and after each category name. *)

Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance bridge_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation nb := (img_a "_nl_category_names").
Local Abbreviation nr := (img_gd "_nl_category_names").
Local Abbreviation ib := (img_a "_nl_category_name_idxs").
Local Abbreviation ir := (img_gd "_nl_category_name_idxs").
Local Abbreviation gl := (img_a "_nl_global_locale").
Local Abbreviation cc := (img_a "_nl_C_LC_CTYPE").
Local Abbreviation cv := (mkPtr (img_a "_nl_C_name") (Ro (img_a "_nl_C_name"))).
Local Abbreviation empty_name := (mkPtr (img_a "hello#str.80") (Ro (img_a "hello#str.80"))).

(** These words contain all the names up to the terminator of the
    last one. The inclusion check below also checks their padding. *)
Local Definition name_words := Eval vm_compute in
  lit_words (take 136 (hello_names_head ++ lc_window ++ hello_names_tail)).

Local Definition table_ps := hello_clocale_objs_ps ++ lc_name_ps nb nr ++ lc_idx_ps ib ir ++
  [(PLive cc, VLive (img_gd "_nl_C_LC_CTYPE"))].

Local Ltac frozen H := iApply (ptsq_incl_b with H); vm_compute; reflexivity.

(** A call can read every category name and the tables that the
    character-type update consults. It needs only discarded shares. *)
Local Lemma locale_tables : word_string DfracDiscarded empty_name [] -∗
  ptsq DfracDiscarded hello_clocale_objs_ps -∗ ct_ro hello_ct_objs -∗ hello_getopt_ro -∗ sl_ro ∗ pl_ro.
Proof using Type.
  iIntros "#H80 #Hcl #Hct #(_ & _ & _ & (_ & Hnames) & Hi & H5 & HC & _)".
  iDestruct "Hct" as "(Hcc & H56 & H64 & H80c & Hxl & Hxu & Htl)".
  iAssert (ptsq DfracDiscarded table_ps) as "#T".
  { iEval (rewrite /table_ps (ptsq_app _ hello_clocale_objs_ps) (ptsq_app _ (lc_name_ps _ _)) (ptsq_app _ (lc_idx_ps _ _))).
    iSplit; [iExact "Hcl"|]. iSplit; [iExact "Hnames"|]. iSplit; last iExact "Hcc".
    iEval (rewrite /lc_idx_ps (ptsq_app _ [_])). iSplit; [iExact "Hi"|iExact "H5"]. }
  iAssert (liveq DfracDiscarded nb nr) as "#Nl". { frozen "T". }
  iAssert (ptsq DfracDiscarded (words_ps nb 0 name_words)) as "#Nw". { frozen "T". }
  iSplit.
  - unfold sl_ro. iSplit; [iExact "H80"|]. iSplit; [iExact "HC"|].
    Local Ltac literal reg := iSplit; [lazymatch goal with |- environments.envs_entails _ (word_string _ (mkPtr ?b _) ?s) =>
      iApply (ws_window_b b reg (lit_words s)); [vm_compute; reflexivity | frozen "T" | frozen "T"] end|].
    literal (img_gd "_nl_POSIX_name"). literal (img_gd "glibc_findlocale#str.243").
    literal (img_gd "glibc_findlocale#str.244"). literal (img_gd "glibc_setlocale#str.234").
    do 5 (iSplit; [frozen "T"|]).
    iApply big_sepL_intro. iIntros "!>" (i x Hx).
    apply list_elem_of_lookup_2, list_elem_of_In in Hx.
    repeat destruct Hx as [<-|Hx]; [..|destruct Hx].
    all: unfold sl_cat_ro; do 4 (iSplit; [frozen "T"|]); iSplit;
      [iApply (ws_window_b with "Nl Nw"); vm_compute; reflexivity | frozen "T"].
  - unfold pl_ro. iFrame "Hcc H56 H64 H80c Hxl Hxu Htl". repeat (iSplit; [frozen "T"|]). frozen "T".
Qed.

(** ## Returning the writable cells

    The body groups the global cells by category and the character
    tables by their use after a locale change. Startup groups them by
    object. These are the same pieces with the same ownership shares. *)

Local Definition shared_pieces (xs : list (dfrac * (piece * pval))) : iProp Σ :=
  [∗ list] x ∈ xs, pointsto x.2.1 x.1 x.2.2.

Local Lemma shared_app xs ys : shared_pieces (xs ++ ys) ⊣⊢ shared_pieces xs ∗ shared_pieces ys.
Proof using Type. apply big_sepL_app. Qed.

Local Lemma shared_q dq ps : ptsq dq ps ⊣⊢ shared_pieces (map (pair dq) ps).
Proof using Type. rewrite /shared_pieces big_sepL_fmap. reflexivity. Qed.

Local Lemma shared_join P Q xs ys : (P ⊣⊢ shared_pieces xs) -> (Q ⊣⊢ shared_pieces ys) ->
  P ∗ Q ⊣⊢ shared_pieces (xs ++ ys).
Proof using Type. intros -> ->. symmetry. apply shared_app. Qed.

Local Lemma shared_perm xs ys : bool_decide (xs ≡ₚ ys) = true -> shared_pieces xs ⊣⊢ shared_pieces ys.
Proof using Type. intros H. apply big_opL_permutation. exact (bool_decide_eq_true_1 _ H). Qed.

Local Ltac pack := lazymatch goal with
  | |- _ ∗ _ ⊣⊢ _ => eapply shared_join; pack
  | |- pts ?ps ⊣⊢ _ => exact (shared_q (DfracOwn 1) ps)
  | |- ptsq ?dq ?ps ⊣⊢ _ => exact (shared_q dq ps)
  | |- emp ⊣⊢ _ => exact (reflexivity (shared_pieces []))
  end.

(** Setlocale gets the same cells back in a different order. Getopt's
    name slot must remain read-only, so the comparison checks both the
    contents and the permission of each cell. *)
Local Lemma locale_cells_view :
  pcell gl 0 (mkPtr cc (Ro cc)) ∗ pts hello_locale_objs_ps ∗ ct_lives hello_ct_objs ∗ ct_cells_set hello_ct_objs ∗
  pcellq DfracDiscarded gl 168 cv ⊣⊢ sl_gl_cells ∗ pl_cells ∗ pcell gl 176 cv.
Proof using Type.
  unfold sl_gl_cells, sl_rows, pl_cells, ct_lives, ct_cells_set. rewrite !big_sepL_cons big_sepL_nil.
  unfold pcell, pcellq, live.
  etransitivity; first pack. etransitivity; last (symmetry; pack). apply shared_perm. vm_compute. reflexivity.
Qed.

(** The call can change the catalog counter. Once it returns the locale
    slots and character table pointers, those cells and the new counter
    restore Hello's private locale state. *)
Lemma hello_setlocale_lend : locale_c w fr ∗ hello_getopt_ro ⊢
  sl_ro ∗ pl_ro ∗ sl_gl_cells ∗ pl_cells ∗ pcell gl 176 cv ∗ hello_cat_cntr ∗
  (sl_gl_cells -∗ pl_cells -∗ pcell gl 176 cv -∗ hello_cat_cntr -∗ locale_c w fr).
Proof using Type.
  iIntros "[(D & G & L & C & #K & #R & N & #H80) #Get]".
  iDestruct (locale_tables with "H80 K R Get") as "[Sr Pr]".
  iSplitL "Sr"; [iExact "Sr"|]. iSplitL "Pr"; [iExact "Pr"|].
  iDestruct "Get" as "(_ & _ & _ & _ & _ & _ & _ & _ & H5 & _)".
  iCombine "D G L C H5" as "V". iEval (rewrite locale_cells_view) in "V".
  iDestruct "V" as "(S & P & A)". iSplitL "S"; [iExact "S"|]. iSplitL "P"; [iExact "P"|].
  iSplitL "A"; [iExact "A"|]. iSplitL "N"; [iExact "N"|].
  iIntros "S P A N". iCombine "S P A" as "V". iEval (rewrite -locale_cells_view) in "V".
  iDestruct "V" as "(D & G & L & C & _)". iFrame "D G L C K R N H80".
Qed.

End window.
