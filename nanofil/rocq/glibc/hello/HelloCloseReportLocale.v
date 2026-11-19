(** Glibc disables cancellation before it reports a write error. Its
    translation still takes three read locks, but none of the locks
    reads the cancellation flag. This module separates the flag from
    the resources that gettext borrows. The report can then translate
    any error message while keeping the disabled flag for the restore. *)

From Glibc Require Import HelloObjects GlibcTactics GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine Pieces Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv FileIdle StartCtypeInitSpec StartImageEarly
   HelloGetoptDiagGettext HelloGetoptDiagTcb HelloGetoptDiagLock HelloGettextLocaleConst
  HelloGettextDomain HelloGetoptDiagImage HelloStartGetoptRules HelloStartHdGetopt HelloStartHdRules
  HelloImageModule HelloImageLoad HelloImageLayout HelloImageEarly LibioCleanupExit DcgettextRealV DcgettextRwlock.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section report.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance report_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation eb := (img_a "__libc_errno").
Local Abbreviation gl := (ct_gl hello_ct_objs).
Local Abbreviation ts := (ct_lt hello_ct_objs).
Local Abbreviation cv := (mkPtr (img_a "_nl_C_name") (Ro (img_a "_nl_C_name"))).
Local Notation full := (DfracOwn 1).
Local Notation half := (DfracOwn (1/2)%Qp).
Local Notation quarter := (DfracOwn (1/2/2)%Qp).
Local Notation dq := DfracDiscarded.
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** The three locks collectively own the thread's lifetime. The state
    also owns stderr and errno, so a translation need not borrow them
    a second time. *)
Definition report_locale tb tr v tid treg : iProp Σ :=
  ∃ s1 s2 s3, ⌜dlk_ready tid s1 /\ dlk_ready tid s2 /\ dlk_ready tid s3⌝ ∗
    dtx_G0 eb hello_dom libc_domain_text dq (ptr_addr hello_nb) (ptr_cap hello_nb) lc_messages_off lc_messages
      dq cv hello_p276 hello_p277 hello_db.1 full hello_db.2 hello_ib.1 dq hello_ib.2 hello_sec.1 full hello_sec.2
      ob full hello_root.1 0 hello_root.2 ts 0 (ct_ltreg hello_ct_objs) full (mkPtr gl (Obj gl)) gl
      (ct_glreg hello_ct_objs) full dq dq treg
      hello_lk1.1 hello_lk1.2 (dl_r s1) (dl_cw s1) (dl_sh s1) (dl_fl s1) half
      hello_lk2.1 hello_lk2.2 (dl_r s2) (dl_cw s2) (dl_sh s2) (dl_fl s2) quarter
      hello_lkt.1 hello_lkt.2 (dl_r s3) (dl_cw s3) (dl_sh s3) (dl_fl s3) quarter
      tb tid (ho_vb ob) (ho_sb ob) (ho_sreg ob) (ho_err ob) (hello_dg_F w fr) (hello_dg_Lm w fr) tr v.

(** Opening getopt's private state exposes the enabled cancellation
    flag once. The reverse direction rebuilds that state after error
    has restored the flag. *)
Lemma report_locale_open tb v tid treg : hello_dgx w fr tb v tid treg ⊣⊢
  ∃ tr jb, ⌜dtx_tcb_at tb tr⌝ ∗ pcell tb off_cleanup null ∗ pcell tb off_cleanup_jmp jb ∗
    int_cell tb off_cancelhandling 0 ∗ report_locale tb tr v tid treg.
Proof using Type.
  rewrite /hello_dgx /hello_dg_G /dlk_G /dlk_G0 /dtx_G /report_locale. iSplit.
  - iIntros "(%a & %b & %c & %Hr & %tr & %jb & %Ht & Hc & Hj & Hf & HG)".
    iExists tr,jb. iSplit; [done|]. iFrame "Hc Hj Hf". iExists a,b,c. by iFrame.
  - iIntros "(%tr & %jb & %Ht & Hc & Hj & Hf & %a & %b & %c & %Hr & HG)".
    iExists a,b,c. iSplit; [done|]. iExists tr,jb. by iFrame.
Qed.

(** The print and the flush borrow the whole thread lifetime, stderr
    and errno. They may change errno or the idle stream state. The
    translation accepts both back without asking about cancellation. *)
Lemma report_locale_lend tb tr v tid treg : report_locale tb tr v tid treg ⊢
  live tb tr ∗ errno_any eb ∗ file_idle (ho_vb ob) (ow_self w) (ho_err ob) 2 ∗
  (live tb tr -∗ errno_any eb -∗ file_idle (ho_vb ob) (ow_self w) (ho_err ob) 2 -∗
    report_locale tb tr v tid treg).
Proof using Type.
  rewrite /report_locale /dtx_G0 /dgx_G /dgx_before /dcg_before_v /rw_held /dgx_stream.
  iIntros "(%a & %b & %c & %Hr & (%bs & Hreads & (H1 & L1 & I1) & (H2 & L2 & I2) &
    (H3 & L3 & I3) & Hroot & Hlocale & Hcache & He) & (#Hs & %Hfd & Herr & HF) & Hmsgs)".
  iSplitL "L1 L2 L3"; [rewrite (dtx_live_split (glibc_program := report_program) tb tr); iFrame|].
  iSplitL "He"; [iExists bs; iExact "He"|].
  iFrame "Herr". iIntros "Hl (%bs' & He) Herr".
  iDestruct (dtx_live_split (glibc_program := report_program) tb tr with "Hl") as "(L1 & L2 & L3)".
  iExists a,b,c. iSplit; [done|]. iSplitR "Herr HF Hmsgs".
  { iExists bs'. iFrame "Hreads Hroot Hlocale Hcache He". iFrame "H1 L1 I1 H2 L2 I2 H3 L3 I3". }
  iSplitR "Hmsgs"; [|iExact "Hmsgs"]. iSplit; [iExact "Hs"|]. iSplit; [done|].
  iSplitL "Herr"; [iExact "Herr"|iExact "HF"].
Qed.

(** Both strerror branches call gettext with the libc domain and the
    message category. In the C locale the result is the input pointer,
    whether it names an error from the table or the unknown-error prefix. *)
Lemma wp_report_translate (Hfr : frees_heap fr) (Herr : ow_errno w = Some (mkPtr eb (Obj eb)))
    tb tr v tid treg f e ls l d args rest j mid Φ :
  dtx_tcb_at tb tr -> 0 <= v < 2^32 -> 0 < ptr_addr mid < 2^64 ->
  map_option (arg_x hge e) args = Some [WPtr hello_dom; WPtr mid; WInt 5] ->
  report_locale tb tr v tid treg -∗
  ▷ (report_locale tb tr v tid treg -∗
      WP (ERun (mkFrame f (put d (WPtr mid) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Htr Hv Hmid Hargs. iIntros "(%a & %b & %c & (%H1 & %H2 & %H3) & HG) HK".
  iApply (dgx_translate (glibc_program := report_program) eb Herr holds_os_glibc with "HG").
  - eapply dgx_premises_of_e, dtx_premises_at; last exact Htr.
    eapply dlk_premises_at; [|exact H1|exact H2|exact H3].
    eapply hello_dg_premises; [exact Hfr|apply hello_locale_cells|exact Hv].
  - exact (fun m (H : 0 < ptr_addr m < 2^64) => H).
  - exact Hmid.
  - exact Hargs.
  - iNext. iIntros (q) "HT". iDestruct (dtx_T0_G with "HT") as "[-> HG]".
    iApply "HK". iExists a,b,c. iFrame "HG". done.
Qed.

End report.
