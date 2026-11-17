(** When a user gives GNU Hello an option it does not know, getopt
    prints a warning to standard error. To print it, gettext looks up a
    translation and glibc's formatter writes the text. These calls read
    some objects that only they use. They also borrow standard error,
    errno and the thread's cleanup fields, which every library call
    shares. This module says which objects the warnings keep between
    calls, and how they borrow the shared ones for one warning. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv FileIdle WordString RdlockLogic TfindEmpty LocalenameLogic
  DcgettextLocale DcgettextRwlock DcgettextRealV DcigettextRouteV PrintfSpec PrintfStreamInv FxprintfStream
  GetoptDiag GetoptLongDiag GetenvEntry GetenvStatic StartCtypeInitSpec StartGetenv
  HelloGlibcDebts HelloGetoptDiagGettext HelloGetoptDiagTcb HelloGetoptDiagLock HelloGetoptDiagMsgs HelloGettextLink
  HelloImageModule HelloImageLoad HelloImageLayout HelloImageEarly HelloGetoptDiagImage HelloImageDiagObjs
  HelloStartGetopt HelloStartGetoptRules.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section hd.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).

Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance hd_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation self := (ow_self w).

(** ## Where the reports read the locale *)

(** Gettext reads the thread's locale pointer, which points at the
    global locale, and the name of its message category, which is "C". *)
Local Abbreviation lt := (ct_lt hello_ct_objs).
Local Abbreviation ltreg := (ct_ltreg hello_ct_objs).
Local Abbreviation gl := (ct_gl hello_ct_objs).
Local Abbreviation glreg := (ct_glreg hello_ct_objs).
Local Abbreviation cb := (img_a "_nl_C_name").
Local Abbreviation lp := (mkPtr gl (Obj gl)).
Local Abbreviation cv := (mkPtr cb (Ro cb)).

(** The thread's object lies at tb. *)
Context (tb : Z).

(** ## The part of hd_priv that the reports need *)

(** A warning needs these resources. Their state depends on the flag v,
    the thread's id tid and the region treg of the string "C". *)
Definition hello_dgx (v tid : Z) (treg : region) : iProp Σ :=
  hello_dg_G w fr lt 0 ltreg (DfracOwn 1) lp gl glreg (DfracOwn 1) (DfracOwn 1) DfracDiscarded treg cv
    (DfracOwn (1/2)) (DfracOwn (1/2/2)) (DfracOwn (1/2/2)) tb (DfracOwn 1) v tid.

(** The reports print to stderr while it is narrow and its lock has room
    for one more holder. *)
Definition hello_err_view : iProp Σ :=
  ∃ mode flags2 held, ⌜(mode = 0 \/ mode = 2 ^ 32 - 1) /\ (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32)⌝ ∗
    printf_stream (ho_vb ob) self (ho_err ob) mode flags2 held ∗ fx_owner self held.

(** Between two calls, Hello's open streams keep the thread's cleanup
    fields, errno and stderr. The private state keeps everything else
    that a warning needs, and it gets those three back for each
    warning. *)
Definition hello_hd_getopt : iProp Σ :=
  ∃ x : Z * Z * region, ⌜0 <= x.1.1 < 2 ^ 32⌝ ∗
    (tcb_cleanup_inv self ∗ errno_any eb ∗ hello_err_view -∗ hello_dgx x.1.1 x.1.2 x.2).

(** A caller does not know the flag, the id or that region, so the
    resource that the warnings borrow hides all three. *)
Definition hello_getopt_E : iProp Σ := ∃ x : Z * Z * region, ⌜0 <= x.1.1 < 2 ^ 32⌝ ∗ hello_dgx x.1.1 x.1.2 x.2.

(** ## Lending the streams *)

(** A narrow view of stderr is still one of Hello's open streams. *)
Lemma hello_err_view_back : hello_err_view ⊢ file_inv (ho_vb ob) self (ho_err ob).
Proof using Type.
  iIntros "(%mode & %flags2 & %held & %Hm & (%fb & %freg & %st & %nb & %vt & %Hs & Hl & Hf & Hk & Hb) & _)".
  destruct Hs as (Hp & H8 & H0 & He & Ht & Hok & Hmo & Hmv & Hvt & Hbuf & Hf2).
  iExists fb, freg, st, nb, vt, held. iFrame. iPureIntro. subst mode. split_and!; assumption.
Qed.

(** G lends the thread's cleanup fields, errno and stderr together, and
    it takes them back in any state that Hello's streams allow. *)
Lemma hello_dgx_lend v tid treg :
  hello_dgx v tid treg ⊢ tcb_cleanup_inv self ∗ errno_any eb ∗ hello_err_view ∗
    (tcb_cleanup_inv self ∗ errno_any eb ∗ hello_err_view -∗ hello_dgx v tid treg).
Proof using Type.
  rewrite /hello_dgx /hello_dg_G /dlk_G /dlk_G0 /dtx_G /dtx_G0 /dgx_G /dgx_before /dcg_before_v /rw_held /rw_self /dgx_stream.
  iIntros "(%s1 & %s2 & %s3 & %Hr & %tbreg & %jb & %Hc & Hcl & Hj & Hx & ((%bs & H1 & (Hk1 & Hl1 & Hi1) &
    (Hk2 & Hl2 & Hi2) & (Hk3 & Hl3 & Hi3) & H5 & H6 & H7 & He) & (#Hso & %mode & %flags2 & %held & %Hm & Hps & Hfo & #HF)
    & HL))".
  iAssert (live tb tbreg) with "[Hl1 Hl2 Hl3]" as "Hl".
  { iPoseProof (dtx_live_split (glibc_program := hd_program) tb tbreg) as "[_ Hb]". iApply "Hb". iFrame "Hl1 Hl2 Hl3". }
  iSplitL "Hcl Hj Hx Hl".
  { iExists tb, tbreg, jb. iSplit; [iPureIntro; exact Hc|]. iFrame "Hcl Hj Hx Hl". }
  iSplitL "He"; [iExists bs; iExact "He"|].
  iSplitL "Hps Hfo"; [iExists mode, flags2, held; iFrame "Hps Hfo"; done|].
  iIntros "((%tb2 & %tbreg2 & %jb2 & %Hc2 & Hl & Hcl & Hj & Hx) & (%bs2 & He) &
    (%mode2 & %flags22 & %held2 & %Hm2 & Hps & Hfo))".
  destruct Hc as (Hs & Hc). destruct Hc2 as (Hs2 & Hc2). rewrite Hs in Hs2. injection Hs2 as <-.
  iPoseProof (dtx_live_split (glibc_program := hd_program) tb tbreg2) as "[Hb _]".
  iDestruct ("Hb" with "Hl") as "(Hl1 & Hl2 & Hl3)".
  iExists s1, s2, s3. iSplit; [done|]. iExists tbreg2, jb2. iSplit; [iPureIntro; split; [exact Hs | exact Hc2]|].
  iSplitL "Hcl"; [iExact "Hcl"|]. iSplitL "Hj"; [iExact "Hj"|]. iSplitL "Hx"; [iExact "Hx"|].
  iSplitL "H1 Hk1 Hl1 Hi1 Hk2 Hl2 Hi2 Hk3 Hl3 Hi3 H5 H6 H7 He".
  { iExists bs2. iSplitL "H1"; [iExact "H1"|]. iSplitL "Hk1 Hl1 Hi1"; [iFrame "Hk1 Hl1 Hi1"|].
    iSplitL "Hk2 Hl2 Hi2"; [iFrame "Hk2 Hl2 Hi2"|]. iSplitL "Hk3 Hl3 Hi3"; [iFrame "Hk3 Hl3 Hi3"|].
    iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|]. iSplitL "H7"; [iExact "H7"|]. iExact "He". }
  iSplitL "Hps Hfo"; [|iExact "HL"]. iSplit; [iExact "Hso"|].
  iExists mode2, flags22, held2. iSplit; [done|]. iSplitL "Hps"; [iExact "Hps"|]. iSplitL "Hfo"; [iExact "Hfo"|].
  iExact "HF".
Qed.

(** Main keeps stderr in a tidy state between calls. A warning prints
    to stderr and may leave it untidy. Two unproved facts link the two
    forms. The first says a tidy stderr gives the warnings their view.
    The second says the view they return is tidy again, which needs a
    better printing contract. Both are hypotheses for now. *)
Context (hello_stderr_lend : file_idle (ho_vb ob) self (ho_err ob) 2 ⊢ hello_err_view).
Context (hello_stderr_back : hello_err_view ⊢ file_idle (ho_vb ob) self (ho_err ob) 2).

(** Main lends the warnings what they need from its streams and its
    private state. After a warning, main gets both back, whatever the
    warning wrote. N and X are other parts that main keeps. *)
Lemma hello_hd_lend (N X : iProp Σ) :
  hello_stdio w hge ob ∗ (N ∗ hello_hd_getopt ∗ X) ⊢
    (N ∗ hello_getopt_E) ∗ (N ∗ hello_getopt_E -∗ hello_stdio w hge ob ∗ (N ∗ hello_hd_getopt ∗ X)).
Proof using hello_stderr_lend hello_stderr_back.
  iIntros "[(Ho & He & Hi & Hl & Ht & Hn) (HN & (%x & %Hx & Hw) & HX)]".
  iDestruct (hello_stderr_lend with "He") as "Hv".
  iDestruct ("Hw" with "[Ht Hn Hv]") as "HG"; [iFrame "Ht Hv"; iExact "Hn"|].
  iSplitL "HN HG"; [iFrame "HN"; iExists x; iSplit; [done | iExact "HG"]|].
  iIntros "[HN (%y & %Hy & HG)]". iDestruct (hello_dgx_lend with "HG") as "(Ht & Hn & Hv & Hb)".
  iSplitR "HN Hb HX".
  { iSplitL "Ho"; [iExact "Ho"|]. iSplitL "Hv"; [iApply hello_stderr_back; iExact "Hv"|].
    iSplitL "Hi"; [iExact "Hi"|]. iSplitL "Hl"; [iExact "Hl"|]. iSplitL "Ht"; [iExact "Ht" | iExact "Hn"]. }
  iSplitL "HN"; [iExact "HN"|]. iSplitR "HX"; [iExists y; iSplit; [done | iExact "Hb"] | iExact "HX"].
Qed.

End hd.
