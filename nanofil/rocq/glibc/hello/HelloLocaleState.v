(** Hello's library calls share one private state, and a contract that
    holds for any private state could never reach the locale or the
    conversion objects. So this module says exactly what the part of
    the private state outside getopt's warnings holds. It has three
    components: the locale cells that setlocale writes, the constants
    that the conversion to wide characters reads, and what is left for
    close_stdout and the error reports. It then builds them from what
    startup leaves.

    Hello's main first sets the locale named by the environment, which
    is the C locale. Setting the C locale stores the values that the
    locale cells already hold. So this state fixes each of those values,
    and setlocale leaves them as they were. One cell does change: a
    counter that setlocale increments, so the state leaves it open.

    Getopt's warnings read the locale under the same lock that setlocale
    takes. That lock therefore lives in their state, and setlocale
    borrows it from there. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv WordString StartCtypeInitSpec StartEarlyInitSpec
  StartImageCpu HelloImageModule HelloImageLoad HelloImageEarly HelloImageCloseObjs HelloImageLocaleObjs
  HelloImageMbsObjs HelloImageCLocaleObjs HelloStartGetopt HelloStartHdBuild HelloCloseReportImage.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section state.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).

Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance hl_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation gl := (ct_gl hello_ct_objs).
Local Abbreviation cc := (ct_cc hello_ct_objs).

(** ## The three components

    A proof of setlocale should not have to know about close_stdout's
    globals, and a proof of the conversion should not have to know
    about setlocale's cells. So the state comes in three parts, one for
    each group of calls, and a proof takes out its own part and puts it
    back. The parts share no object. *)

(** Setlocale adds one to the catalog counter, and gettext compares the
    counter with the one it saw last. Nothing needs its value, so the
    counter holds some 32-bit integer. *)
Definition hello_cat_cntr : iProp Σ :=
  ∃ n, pts (obj_ps (img_ob "_nl_msg_cat_cntr") (le_bytes n 4)).

(** Setlocale in the C locale writes each locale cell with the value it
    already holds, so this part of the state fixes those values. It
    holds the locale's category pointers and names, the table pointers
    and the old table globals. It also holds the counter that setlocale
    increments. Setlocale reads its constants as frozen shares, so
    getenv can look up each category name as a frozen string. *)
Definition locale_c : iProp Σ :=
  pcell gl 0 (mkPtr cc (Ro cc)) ∗ pts hello_locale_objs_ps ∗ ct_lives hello_ct_objs ∗
  ct_cells_set hello_ct_objs ∗ ptsq DfracDiscarded hello_clocale_objs_ps ∗ ct_ro hello_ct_objs ∗ hello_cat_cntr.

(** The conversion to wide characters only reads its constants: the
    character type data, the converter's step and the names "C" and
    "POSIX". So the private state holds them as shares that never
    change. *)
Definition hello_conv_ro : iProp Σ := ptsq DfracDiscarded hello_mbs_objs_ps.

(** This list holds close_stdout's writable globals and the conversion
    lock. It leaves out the catalog counter, which the locale part holds. *)
Definition hello_close_rest_ps : list (piece * pval) :=
  obj_ps (img_ob "exit_failure") [1; 0; 0; 0] ++
  obj_ps (img_ob "closeout#ignore_EPIPE") [0] ++
  obj_ps (img_ob "closeout#file_name") (repeat 0 8%nat) ++
  obj_ps (img_ob "__gconv_lock") (repeat 0 4%nat).

(** When close_stdout reports a write error, it reads the formatter's
    tables and its own globals. If errno is nonzero, it also reads
    glibc's error messages. The latter remain readable after the call. *)
Definition hello_priv_residual : iProp Σ :=
  hello_getopt_ro ∗ pts hello_close_rest_ps ∗ pts hello_close_ro_ps ∗ ptsq DfracDiscarded hello_errlist_ps.

(** The part of the private state outside getopt's warnings is the
    three components. *)
Definition hello_priv_rest : iProp Σ := locale_c ∗ hello_conv_ro ∗ hello_priv_residual.

(** ## Building the components

    Hello's theorem should not assume that the private state exists, so
    this section builds it from the objects that startup leaves unused.
    Those objects split into the three parts, once the conversion's
    constants are frozen as read-only shares. *)

(** The catalog counter is the last of close_stdout's writable
    globals, and it starts at 0. *)
Lemma hello_close_split :
  pts hello_close_objs_ps ⊣⊢ pts hello_close_rest_ps ∗ pts (obj_ps (img_ob "_nl_msg_cat_cntr") (le_bytes 0 4)) ∗
    pts hello_close_ro_ps.
Proof using Type.
  assert (E : hello_close_objs_ps =
    hello_close_rest_ps ++ obj_ps (img_ob "_nl_msg_cat_cntr") (le_bytes 0 4) ++ hello_close_ro_ps).
  { rewrite /hello_close_objs_ps /hello_close_rw_ps /hello_close_rest_ps -!app_assoc. reflexivity. }
  rewrite E !pts_app. done.
Qed.

(** What startup leaves is enough for the three components. *)
Lemma hello_priv_build : hello_hd_rest w fr ==∗ hello_priv_rest.
Proof using Type.
  iIntros "(Pgl & #Ro & Hco & Hlo & Hcl & Hcc & Hmb & Hcx & Hel & #Hct)".
  rewrite hello_close_split. iDestruct "Hco" as "(Hcr & Hn & Hcro)".
  iEval (rewrite pts_ptsq) in "Hmb". iMod (ptsq_persist with "Hmb") as "#Hmb".
  iEval (rewrite pts_ptsq) in "Hcx". iMod (ptsq_persist with "Hcx") as "#Hcx".
  iEval (rewrite pts_ptsq) in "Hel". iMod (ptsq_persist with "Hel") as "#Hel".
  iModIntro. iSplitL "Pgl Hlo Hcl Hcc Hn".
  { iFrame "Pgl Hlo Hcl Hcc Hcx Hct". iExists 0. iExact "Hn". }
  iSplitR; [iExact "Hmb"|]. iSplitR; [iExact "Ro"|].
  iSplitL "Hcr"; [iExact "Hcr"|]. iSplitL "Hcro"; [iExact "Hcro"|iExact "Hel"].
Qed.

End state.
