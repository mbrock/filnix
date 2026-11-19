(** When a wide character has no ASCII byte, glibc looks for a
    replacement in tables that the C locale keeps. The proof of that
    search needs to know what each table holds and where it is.
    Startup proves all of these constants at once, as one share that
    nobody can write. This file breaks that share into the separate
    facts that the search reads. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude HelloImageLoad HelloImageMbsObjs HelloImageWFwideObjs HelloImageWConvObjs
  ImageObjectPieces OsWorld FileInv LibioLogic LibioDefaultXsputnBuf LibioWIdle Mbrtowc CBlocks Fix LibioWConvAscii.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.
Open Scope list_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
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

(** ## The constants that transliteration reads *)

Section consts.
Context `{!gen_heapGS piece pval Σ}.

(** These lists hold the source and replacement tables. Each list
    ends with the zero word that ends the table's last string. *)
Definition wc_ft : list Z := wc_from_tbl ++ [0].
Definition wc_tt : list Z := wc_to_tbl ++ [0].

(** This assertion lists the read-only constants of [wconv_ro] one by one. *)
Definition wconv_consts : iProp Σ :=
  liveq DfracDiscarded tmb (img_r "glibc_wcsmbsload#to_mb") ∗ pcellq DfracDiscarded tmb 0 null ∗
  pcellq DfracDiscarded tmb 40 fct ∗ liveq DfracDiscarded cc (img_gd "_nl_C_LC_CTYPE") ∗
  bytesq DfracDiscarded cc 544 (le_bytes 1659 4) ∗
  pcellq DfracDiscarded cc 552 (rop fia) ∗ pcellq DfracDiscarded cc 560 (rop fta) ∗
  pcellq DfracDiscarded cc 568 (rop tia) ∗ pcellq DfracDiscarded cc 576 (rop tta) ∗
  bytesq DfracDiscarded cc 584 (le_bytes 1 4) ∗ pcellq DfracDiscarded cc 592 (rop s280) ∗
  bytesq DfracDiscarded cc 600 (le_bytes 0 4) ∗
  liveq DfracDiscarded s280 (img_r "glibc_C_ctype#str.280") ∗ bytesq DfracDiscarded s280 0 (le_bytes 63 4) ∗
  liveq DfracDiscarded fia (img_r "glibc_C_ctype#translit_from_idx") ∗ bytesq DfracDiscarded fia 0 (le_words wc_from_idx) ∗
  liveq DfracDiscarded fta (img_r "glibc_C_ctype#translit_from_tbl") ∗ bytesq DfracDiscarded fta 0 (le_words wc_ft) ∗
  liveq DfracDiscarded tia (img_r "glibc_C_ctype#translit_to_idx") ∗ bytesq DfracDiscarded tia 0 (le_words wc_to_idx) ∗
  liveq DfracDiscarded tta (img_r "glibc_C_ctype#translit_to_tbl") ∗ bytesq DfracDiscarded tta 0 (le_words wc_tt).

Global Instance wconv_consts_persistent : Persistent wconv_consts.
Proof using Type. unfold wconv_consts, liveq, pcellq, bytesq. apply _. Qed.

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
