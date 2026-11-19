(** When a wide character has no ASCII byte, glibc looks for a
    replacement in tables that the C locale keeps. The proof of that
    search needs to know what each table holds and where it is.
    The assertion below lists the read-only cells the search borrows. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Values Memory Pieces Heap MemLogic.
From Glibc Require Import FileInv CLocaleCells CtypeTranslitTables.
Import ListNotations FileInv.ML FileInv.LG.
Open Scope Z_scope.
Open Scope list_scope.

Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation cc := (conv_addr "_nl_C_LC_CTYPE").
Local Abbreviation tmb := (conv_addr "glibc_wcsmbsload#to_mb").
Local Abbreviation s280 := (conv_addr "glibc_C_ctype#str.280").
Local Abbreviation fia := (conv_addr "glibc_C_ctype#translit_from_idx").
Local Abbreviation fta := (conv_addr "glibc_C_ctype#translit_from_tbl").
Local Abbreviation tia := (conv_addr "glibc_C_ctype#translit_to_idx").
Local Abbreviation tta := (conv_addr "glibc_C_ctype#translit_to_tbl").
Local Abbreviation fct := (mkPtr (conv_addr "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii"))).

(** ## The constants that transliteration reads *)

Section consts.
Context `{!gen_heapGS piece pval Σ}.

(** These lists hold the source and replacement tables. Each list
    ends with the zero word that ends the table's last string. *)
Definition wc_ft : list Z := wc_from_tbl ++ [0].
Definition wc_tt : list Z := wc_to_tbl ++ [0].

(** This assertion lists the read-only constants that transliteration reads. *)
Definition wconv_consts : iProp Σ :=
  liveq DfracDiscarded tmb (conv_region "glibc_wcsmbsload#to_mb") ∗ pcellq DfracDiscarded tmb 0 null ∗
  pcellq DfracDiscarded tmb 40 fct ∗ liveq DfracDiscarded cc (conv_region "_nl_C_LC_CTYPE") ∗
  bytesq DfracDiscarded cc 544 (le_bytes 1659 4) ∗
  pcellq DfracDiscarded cc 552 (rop fia) ∗ pcellq DfracDiscarded cc 560 (rop fta) ∗
  pcellq DfracDiscarded cc 568 (rop tia) ∗ pcellq DfracDiscarded cc 576 (rop tta) ∗
  bytesq DfracDiscarded cc 584 (le_bytes 1 4) ∗ pcellq DfracDiscarded cc 592 (rop s280) ∗
  bytesq DfracDiscarded cc 600 (le_bytes 0 4) ∗
  liveq DfracDiscarded s280 (conv_region "glibc_C_ctype#str.280") ∗ bytesq DfracDiscarded s280 0 (le_bytes 63 4) ∗
  liveq DfracDiscarded fia (conv_region "glibc_C_ctype#translit_from_idx") ∗ bytesq DfracDiscarded fia 0 (le_words wc_from_idx) ∗
  liveq DfracDiscarded fta (conv_region "glibc_C_ctype#translit_from_tbl") ∗ bytesq DfracDiscarded fta 0 (le_words wc_ft) ∗
  liveq DfracDiscarded tia (conv_region "glibc_C_ctype#translit_to_idx") ∗ bytesq DfracDiscarded tia 0 (le_words wc_to_idx) ∗
  liveq DfracDiscarded tta (conv_region "glibc_C_ctype#translit_to_tbl") ∗ bytesq DfracDiscarded tta 0 (le_words wc_tt).

Global Instance wconv_consts_persistent : Persistent wconv_consts.
Proof using Type. unfold wconv_consts, liveq, pcellq, bytesq. apply _. Qed.

End consts.
