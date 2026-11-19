(** Hello prints its greeting with `c: wprintf`, which writes wide
    characters to stdout. While it runs, the call also uses errno, the
    allocator and some constant tables, and it gives them all back.
    Main keeps these in its other streams and its private state. This
    file shows that main can lend them to the call and still keep its
    own contract. *)

From Glibc Require Import HelloObjects.
From Glibc Require Fix.
From Glibc Require Import Unit_string_memset_os GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic LibioWIdle PrintfSpec HelloImageModule
  HelloImageLoad HelloImageLayout HelloGlibcDebts HelloGlibcLibsT HelloStartHdGetopt HelloLocaleState
  HelloWideState HelloImageWFwideObjs HelloImageWReleaseObjs HelloImageWConvObjs HelloImageWideObjs HelloImageWPrintfObjs AllocCall LibioWOverflowWrite WPrintfScan WPrintfParse WPrintfInternal
  WPrintfWrap WPrintfStreamImage LibioWFwide.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section call.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance call_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation o := hello_image_objs.
Local Abbreviation fmt := (img_a "hello#str.83").

(** The call needs the linked program, errno and stdout's descriptor. *)
Context (tb : Z) (Hlink : hello_link hge o) (Herr : ow_errno w = Some (mkPtr (ho_eb o) (Obj (ho_eb o))))
  (Hfd1 : In 1 (ow_fds w)) (Hfd2 : In 2 (ow_fds w)).

(** The formatter's jump tables are constants of the image, and the
    private state holds the entries it reads. *)
Lemma hello_wprintf_tables : ptsq DfracDiscarded hello_wprintf_tables_ps ⊢ wprintf_tables_ro.
Proof using Type.
  unfold hello_wprintf_tables_ps, wprintf_tables_ro. iIntros "H".
  iExists (img_addr "glibc_vfwprintf_internal#jump_table"), (img_obj "glibc_vfwprintf_internal#jump_table").2,
    (img_addr "glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278"),
    (img_obj "glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278").2,
    (img_addr "glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282"),
    (img_obj "glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282").2.
  iSplit; [iPureIntro; vm_compute; repeat split; (reflexivity || discriminate)|].
  rewrite /liveq /bytesq -!ptsq_app. iExact "H".
Qed.

(** When stdout is wide, its calls go through a second table of
    methods. Main can read every slot of that table. *)
Lemma hello_ro_wvtables : hello_ro hge o ⊢ wvtables_ro hge (ho_vb o).
Proof using Type. iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _)". iExact "H". Qed.

(** The formatter reads all twenty bytes of the greeting's format.
    Main's read-only promise holds them, at the address that the image
    gives the format. *)
Lemma hello_ro_greet_fmt : hello_ro hge o ⊢ ∃ rr, wprintf_fmt_ro fmt rr.
Proof using Type.
  iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H)".
  iDestruct "H" as (b br [Hl Hb]) "[Hlv Hby]".
  assert (Ef : lookup (TAtom "hello#str.83") (ge_globals hge) = Some (mkPtr fmt (Ro fmt))) by (vm_compute; reflexivity).
  rewrite Ef in Hl. injection Hl as <-. iExists br. rewrite /wprintf_fmt_ro.
  iSplit; [iPureIntro; split; [exact Ef|exact Hb]|]. iSplit; [iExact "Hlv"|iExact "Hby"].
Qed.

(** The call borrows main's streams without stdout, its private state
    and its read-only promise. *)
Definition wprintf_E (priv : iProp Σ) : iProp Σ := hello_stdio_wide w hge o emp ∗ priv ∗ hello_ro hge o.

(** The greeting's buffer is the one that main allocated and filled.
    The call returns stdout in either orientation, and every other part
    of main's state unchanged. *)
Lemma hello_wprintf_greet (N priv : iProp Σ) :
  (priv ⊣⊢ N ∗ hello_hd_getopt w fr tb ∗ (N ∗ hello_priv_rest w fr)) ->
  wdo_pending_spec (ho_vb o) (ow_self w) 1 (wprintf_E priv) ->
  forall bd n ws, 0 < bd -> bd mod 16 = 0 -> bd + req_extent (wreq n) <= 2 ^ 48 -> wide_text ws ->
  HelloGlibcDebts.fn_triple w hge (TAtom "wprintf") [WPtr (sym_ptr hge "hello#str.83"); WPtr (mkPtr bd (Obj bd))]
    (hello_ro hge o ∗ hello_stdio w hge o ∗ priv ∗ wbuf bd n ws)%I
    (ret_int (hello_stdio_wide w hge o (wprintf_out w hge o) ∗ priv ∗ wbuf bd n ws))%I.
Proof using Type*.
  intros HP Hwr bd n ws Hb Ha He Hw.
  set (E := wprintf_E priv). set (W := wfwide_res (DfracOwn (1/2))).
  assert (Hlend : E ⊢ W ∗ (W -∗ E)).
  { iIntros "(Hio & Hp & #Hro)". iDestruct (hello_wfwide_lend w fr tb Hfd2 N priv emp HP with "[$Hio $Hp]") as "[HW Hb]".
    iSplitL "HW"; [iExact "HW"|]. iIntros "HW". iDestruct ("Hb" with "HW") as "[Hio Hp]".
    rewrite /E /wprintf_E. iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Hp"; [iExact "Hp"|iExact "Hro"]. }
  assert (Herr2 : E ⊢ errno_any (ho_eb o) ∗ (errno_any (ho_eb o) -∗ E)).
  { rewrite /E /wprintf_E. iIntros "((Ho & Hs & Hi & Hl & Ht & He & Hc) & Hp & #Hro)". iSplitL "He"; [iExact "He"|].
    iIntros "He". iSplitR "Hp"; [iFrame "Ho Hs Hi Hl Ht He Hc"|]. iSplitL "Hp"; [iExact "Hp"|iExact "Hro"]. }
  assert (Loan : E ⊢ vtables_ro hge (ho_vb o) (ho_vreg o) ∗ wvtables_ro hge (ho_vb o) ∗
    malloc_call_state DfracDiscarded (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o) ∗
    errno_any (ho_eb o) ∗ (errno_any (ho_eb o) -∗ E)).
  { iIntros "HE". iAssert (hello_ro hge o) as "#Hro". { rewrite /E /wprintf_E. iDestruct "HE" as "(_ & _ & Hro)". iExact "Hro". }
    iPoseProof (hello_ro_wvtables with "Hro") as "#Hwv". iPoseProof "Hro" as "(Hvt & _ & _ & _ & _ & _ & _ & Hm & _)".
    iDestruct (Herr2 with "HE") as "[He HK]". iSplitR; [iExact "Hvt"|]. iSplitR; [iExact "Hwv"|].
    iSplitR; [rewrite /malloc_call_state; iExact "Hm"|]. iSplitL "He"; [iExact "He"|iExact "HK"]. }
  pose proof (hello_wprintf_xsputn_image w fr E Hlink Herr Hfd1 Loan Hwr) as Hxs.
  destruct (hk_zmemset _ _ Hlink) as [Hzf Hzs].
  assert (Hset : glibc_os_registry (TAtom "zmemset") = Some (void_only (ExternalCalls.memset_contract os_world))) by reflexivity.
  assert (Dcl : Defines hge "__wcsmbs_clone_conv" glibc_clone_conv) by (vm_compute; reflexivity).
  assert (Dms : Defines hge "__GI_memset" Unit_string_memset_os.fn___GI_memset) by (vm_compute; reflexivity).
  assert (Hidle : wprintf_fwide_idle_spec (ho_vb o) (ow_self w) W).
  { refine (@wprintf_fwide_idle _ _ call_program _ _ _ _ Hset Hzf Hzs Dcl Dms _ _ _); vm_compute; reflexivity. }
  pose proof (@wprintf_fwide_wide _ _ call_program (ho_vb o) (ow_self w) (DfracOwn (1/2))) as Hwide.
  pose proof (fun rr => hello_wprintf_has_spec w fr E W bd n ws (ho_out o) DfracDiscarded rr (ho_vreg o)
    Hidle Hwide Hxs Hw Hb Ha He Herr Herr2 Hlend) as T.
  destruct (T (img_gd "hello#str.83")) as (gf & Hfind & Hcall & _). exists gf. split; [exact Hfind|]. split; [exact Hcall|].
  intros f Φ Hf. iIntros "(#Hro & (Hout & Hrest) & Hp & Hwb) HK".
  iDestruct (HP with "Hp") as "(HN & HG & HN2 & Hloc & Hcv & Hres)".
  (* Proof search for this persistence runs away, so the instance is given. *)
  assert (Hcvp : Persistent (hello_conv_ro (Σ := Σ))) by exact (bi.sep_persistent _ _ (ptsq_persistent _) (ptsq_persistent _)).
  iDestruct (@bi.persistent_persistently_2 _ _ _ Hcvp with "Hcv") as "#Hc".
  (* The format's region is not fixed in advance, so the call's contract is taken at the region that the promise names. *)
  iDestruct (hello_ro_greet_fmt with "Hro") as (rr) "#Hfm".
  destruct (T rr) as (gf' & Hfind' & _ & T'). rewrite Hfind in Hfind'. injection Hfind' as <-.
  iAssert wprintf_tables_ro as "Htb".
  { iDestruct "Hc" as "[_ Hw]". iEval (rewrite /hello_wide_objs_ps (ptsq_app _ hello_wfwide_ps)
      (ptsq_app _ hello_wrelease_ps) (ptsq_app _ hello_wc_tables_ps) (ptsq_app _ hello_wc_words_ps)
      (ptsq_app _ hello_wc_tails_ps)) in "Hw".
    iDestruct "Hw" as "(_ & _ & _ & _ & _ & Hw)". iApply (hello_wprintf_tables with "Hw"). }
  iAssert priv with "[HN HG HN2 Hloc Hcv Hres]" as "Hp".
  { iApply HP. iSplitL "HN"; [iExact "HN"|]. iSplitL "HG"; [iExact "HG"|]. iSplitL "HN2"; [iExact "HN2"|].
    iSplitL "Hloc"; [iExact "Hloc"|]. iSplitL "Hcv"; [iExact "Hcv"|iExact "Hres"]. }
  iPoseProof (hello_ro_wvtables with "Hro") as "#Hwv".
  iPoseProof "Hro" as "(Hvt & _ & Hsl & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _)".
  iApply (T' f Φ Hf with "[Hout Hrest Hp Hwb] [HK]").
  - iSplitR; [iExact "Hfm"|]. iSplitR; [iExact "Htb"|]. iSplitR; [iExact "Hpr"|]. iSplitR; [iExact "Hvt"|].
    iSplitR; [iExact "Hwv"|].
    iSplitR. { iExists (ho_so o), (ho_soreg o). iSplit; [iPureIntro; vm_compute; repeat split; (reflexivity || discriminate)|].
      iSplit; [iExact "Hsl"|iExact "Hsp"]. }
    iSplitL "Hout"; [iExact "Hout"|]. iSplitR "Hwb"; [|iExact "Hwb"]. rewrite /E /wprintf_E.
    iSplitL "Hrest"; [iSplitR; [done|iExact "Hrest"]|]. iSplitL "Hp"; [iExact "Hp"|iExact "Hro"].
  - iIntros (r) "(%k & %Hk & _ & Hout & ((_ & Hrest) & Hp & _) & Hwb)". iApply "HK". iExists k. iSplit; [done|].
    iSplitR "Hp Hwb"; [|iSplitL "Hp"; [iExact "Hp"|iExact "Hwb"]]. iSplitL "Hout"; [iExact "Hout"|iExact "Hrest"].
Qed.

End call.
