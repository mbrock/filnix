(** Before GNU Hello prints its help text, it asks
    `c: setlocale (LC_MESSAGES, NULL)` for the name of the message
    locale. To answer, glibc reads two things: whether the global locale
    object is alive, and the cell that names the message category. A
    warning from the option parser reads the same two things through
    gettext, so the private state that startup leaves already holds
    them. This module opens that state the way a warning does, lends
    the two cells to the query, and closes the state again. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv FileIdle WordString LocalenameLogic
  SetlocaleCode SetlocaleQuery StartCtypeInitSpec StartImageEarly HelloGlibcDebts HelloGetoptDiagLock
  HelloImageModule HelloImageLoad HelloImageLayout HelloImageEarly HelloImageDiagObjs
  HelloStartGetopt HelloStartGetoptRules HelloStartHdGetopt.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section query.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).

Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance query_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation gl := (ct_gl hello_ct_objs).
Local Abbreviation glreg := (ct_glreg hello_ct_objs).
Local Abbreviation cb := (img_a "_nl_C_name").
Local Abbreviation cv := (mkPtr cb (Ro cb)).

(** Opening the private state needs the address tb of the thread's
    own object and an open stderr, because a warning writes to it. *)
Context (tb : Z) (Hfd2 : In 2 (ow_fds w)).

(** The image links `c: setlocale` to glibc's function. *)
Lemma hello_setlocale_found : find_fn hge (TAtom "setlocale") = Some (Defined glibc_setlocale).
Proof using Type. vm_compute. reflexivity. Qed.

(** Startup leaves the C locale in place, so the query returns the
    name "C". It works for any private state priv that holds the
    warnings' state, whatever else priv holds beside it, and it gives
    back the streams and priv unchanged. *)
Lemma hello_setlocale_query (N X priv : iProp Σ) :
  (priv ⊣⊢ N ∗ hello_hd_getopt w fr tb ∗ X) ->
  fn_triple w hge (TAtom "setlocale") [WInt 5; WPtr null]
    (hello_ro hge ob ∗ hello_stdio w hge ob ∗ priv)%I
    (fun r => ∃ q, ⌜r = Ret (WPtr q)⌝ ∗ hello_stdio w hge ob ∗ priv ∗ (⌜ptr_addr q = 0⌝ ∨ str_ro q))%I.
Proof using Hfd2.
  intros Hpriv. exists glibc_setlocale. split; [exact hello_setlocale_found|]. split; [eexists; reflexivity|].
  intros f Φ Hf. iIntros "(_ & Hio & Hp) HK". iDestruct (Hpriv with "Hp") as "Hp".
  iDestruct (hello_hd_lend w fr tb Hfd2 N X with "[$Hio $Hp]") as "[[HN (%x & %Hx & HG)] Hback]".
  rewrite /hello_dgx /hello_dg_G.
  iDestruct (dlk_locale with "HG") as "(#Hcv & (Hgl & Hgp & Hll & Hlc & Hlt) & HG)".
  assert (E : ptr_addr (mkPtr gl (Obj gl)) - gl + 128 + 8 * 5 = 168) by (cbn [ptr_addr]; lia).
  iEval (rewrite E) in "Hlc".
  iApply (wp_setlocale_query f gl glreg (DfracOwn 1) DfracDiscarded cv x.2 DfracDiscarded with "Hll Hlc Hlt").
  1: exact Hf. 1: vm_compute; reflexivity.
  1-4: (vm_compute; try reflexivity; try congruence). 1: (cbn; lia).
  iNext. iIntros "Hll Hlc Hlt". iApply "HK". iExists cv. iSplit; [done|].
  iEval (rewrite -E) in "Hlc".
  iAssert (hello_stdio w hge ob ∗ (N ∗ hello_hd_getopt w fr tb ∗ X))%I with "[-]" as "[Hio Hp]".
  { iApply "Hback". iFrame "HN". iExists x. iSplit; [done|]. iApply "HG". iFrame. }
  iFrame "Hio". iSplitL "Hp"; [iApply Hpriv; iExact "Hp"|]. iRight. iExists [67]. iExact "Hcv".
Qed.

End query.
