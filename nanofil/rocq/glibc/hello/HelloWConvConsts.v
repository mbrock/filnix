(** Hello startup owns the read-only objects used by wide-character conversion.
    Their placement and contents give the conversion the individual cells and
    table bounds that it reads. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Values Memory Pieces Heap MemLogic StringLogic.
From Glibc Require Import FileInv HelloImageLoad HelloImageWFwideObjs HelloImageWConvObjs
  ImageObjectPieces Mbrtowc LibioWConvConsts HelloImagePlacement.
Import ListNotations FileInv.ML FileInv.LG.
Open Scope Z_scope.
Open Scope list_scope.

Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation img_r n := (ltac:(let v := eval vm_compute in (snd (img_obj n%string)) in exact v)) (only parsing).
Local Abbreviation cc := (img_a "_nl_C_LC_CTYPE").
Local Abbreviation tmb := (img_a "glibc_wcsmbsload#to_mb").
Local Abbreviation s280 := (img_a "glibc_C_ctype#str.280").
Local Abbreviation fia := (img_a "glibc_C_ctype#translit_from_idx").
Local Abbreviation fta := (img_a "glibc_C_ctype#translit_from_tbl").
Local Abbreviation tia := (img_a "glibc_C_ctype#translit_to_idx").
Local Abbreviation tta := (img_a "glibc_C_ctype#translit_to_tbl").
Local Abbreviation fct := (mkPtr (img_a "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii"))).

(** Every generated address and region end agrees with the linked loader. *)
Lemma hello_conversion_placement :
  map (fun row : string * Z * Z => let '(n, _, _) := row in
    (n, img_addr n, r_end (snd (img_obj n)))) placement = placement.
Proof. vm_compute. reflexivity. Qed.

Section consts.
Context `{!gen_heapGS piece pval Σ}.

(** The conversion reads these read-only objects. They include the
    converter path that `c: mbrtowc` reads and the output step's
    handle. They also include the transliteration tables, the zero
    word after each table of strings, and the words that lead to the
    tables. *)
Definition wconv_ro : iProp Σ :=
  mbr_tables ∗ ptsq DfracDiscarded hello_wfwide_ps ∗ ptsq DfracDiscarded hello_wc_tables_ps ∗
  ptsq DfracDiscarded hello_wc_words_ps ∗ ptsq DfracDiscarded hello_wc_tails_ps.

Global Instance wconv_ro_persistent : Persistent wconv_ro.
Proof using Type. unfold wconv_ro, mbr_tables, liveq, pcellq. apply _. Qed.

(** A discarded share of a list of pieces gives a share of any list
    whose pieces it contains. *)
Lemma ptsq_disc_incl ps qs : incl qs ps -> ptsq DfracDiscarded ps ⊢ ptsq DfracDiscarded qs.
Proof using Type.
  intros Hi. rewrite /ptsq. iIntros "#H". iApply big_sepL_intro. iIntros "!>" (k x Hk).
  apply list_elem_of_lookup_2, list_elem_of_In, Hi, list_elem_of_In, list_elem_of_lookup in Hk as [i Hi'].
  iApply (big_sepL_lookup with "H"). exact Hi'.
Qed.

(** The tactic [incl_seg] finds a list among the parts of a longer one. *)
Local Ltac incl_seg := first [apply incl_refl | apply incl_appl; incl_seg | apply incl_appr; incl_seg].

(** The startup shares give the constants one by one. *)
Lemma wconv_ro_consts : wconv_ro ⊢ wconv_consts.
Proof using Type.
  assert (Ew : hello_wc_words_ps = byte_ps cc 544 (le_bytes 1659 4) ++ ptr_ps cc 552 (rop fia) ++ ptr_ps cc 560 (rop fta) ++
    ptr_ps cc 568 (rop tia) ++ ptr_ps cc 576 (rop tta) ++ byte_ps cc 584 (le_bytes 1 4) ++ ptr_ps cc 592 (rop s280) ++
    byte_ps cc 600 (le_bytes 0 4) ++ [(PLive s280, VLive (img_r "glibc_C_ctype#str.280"))] ++
    byte_ps s280 0 (le_bytes 63 4) ++ ptr_ps tmb 40 fct) by (vm_compute; reflexivity).
  assert (Ef : hello_wfwide_ps = cell (img_a "__wcsmbs_gconv_fcts_c") 8 1 ++
    ptr_ps (img_a "__wcsmbs_gconv_fcts_c") 16 (rop tmb) ++ cell (img_a "__wcsmbs_gconv_fcts_c") 24 1 ++
    [(PLive tmb, VLive (img_r "glibc_wcsmbsload#to_mb"))] ++ ptr_ps tmb 0 null) by (vm_compute; reflexivity).
  assert (Et : hello_wc_tables_ps =
    [(PLive fia, VLive (img_r "glibc_C_ctype#translit_from_idx"))] ++ byte_ps fia 0 (le_words wc_from_idx) ++
    [(PLive fta, VLive (img_r "glibc_C_ctype#translit_from_tbl"))] ++ byte_ps fta 0 (le_words wc_from_tbl) ++
    [(PLive tia, VLive (img_r "glibc_C_ctype#translit_to_idx"))] ++ byte_ps tia 0 (le_words wc_to_idx) ++
    [(PLive tta, VLive (img_r "glibc_C_ctype#translit_to_tbl"))] ++ byte_ps tta 0 (le_words wc_to_tbl))
    by (vm_compute; reflexivity).
  assert (Etl : hello_wc_tails_ps = byte_ps fta (4 * 3317) (le_bytes 0 4) ++ byte_ps tta (4 * 5886) (le_bytes 0 4))
    by (vm_compute; reflexivity).
  assert (Eft : byte_ps fta 0 (le_words wc_ft) = byte_ps fta 0 (le_words wc_from_tbl) ++ byte_ps fta (4 * 3317) (le_bytes 0 4))
    by (vm_compute; reflexivity).
  assert (Ett : byte_ps tta 0 (le_words wc_tt) = byte_ps tta 0 (le_words wc_to_tbl) ++ byte_ps tta (4 * 5886) (le_bytes 0 4))
    by (vm_compute; reflexivity).
  rewrite /wconv_ro /wconv_consts /mbr_tables Ew Ef. unfold liveq, pcellq, bytesq. rewrite Eft Ett Et Etl.
  remember (le_words wc_from_idx) as A1 eqn:E1. remember (le_words wc_from_tbl) as A2 eqn:E2.
  remember (le_words wc_to_idx) as A3 eqn:E3. remember (le_words wc_to_tbl) as A4 eqn:E4.
  clear E1 E2 E3 E4 Ew Ef Et Etl Eft Ett.
  change (ptsq DfracDiscarded ((PAux ?b ?o, VAux (ptr_cap ?p)) :: cell ?b ?o (ptr_addr ?p))) with (ptsq DfracDiscarded (ptr_ps b o p)).
  iIntros "#(H1 & H2 & H3 & H4 & H5)". iDestruct "H1" as "(Hcc & _)".
  iCombine "Hcc H2 H3 H4 H5" as "H". rewrite -!ptsq_app.
  iApply (ptsq_disc_incl with "H"). repeat apply incl_app. all: solve [incl_seg].
Qed.
End consts.
