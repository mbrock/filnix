(** When startup calls main, some objects have not been used yet. They
    include Hello's private start list, the flag that marks a privileged
    process, the thread's id and the thread's locale pointer. This module
    builds from them what getopt's warnings need between calls. Gettext's
    three locks start free and the thread's id is positive, so this
    thread holds none of the locks for writing. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv WordString RdlockLogic TfindEmpty LocalenameLogic
  DcgettextRwlock DcgettextRealV DcigettextRouteV StartCtypeInitSpec HelloGlibcDebts HelloGetoptDiagGettext
  HelloGetoptDiagTcb HelloGetoptDiagLock HelloGettextLink HiAtexitAlloc HelloImageModule HelloImageLoad HelloImageLayout
  HelloImageEarly HelloGetoptDiagImage HelloImageDiagObjs HelloGetoptStart HelloStartGetopt HelloStartGetoptRules HelloStartHdGetopt HelloImageCloseObjs HelloImageLocaleObjs StartEarlyInitSpec
  AllocRo LibioFputsSpec.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** A stored 32-bit integer keeps only the low 32 bits of a number. *)
Lemma byte_of_mod32 v i : 0 <= i < 4 -> byte_of (v mod 2 ^ 32) i = byte_of v i.
Proof.
  intros Hi. unfold byte_of. change 256 with (2 ^ 8). apply Z.bits_inj'. intros n Hn.
  destruct (Z.lt_ge_cases n 8).
  - rewrite (Z.mod_pow2_bits_low (v mod 2 ^ 32 / 2 ^ (8 * i))); [|lia].
    rewrite (Z.mod_pow2_bits_low (v / 2 ^ (8 * i))); [|lia].
    rewrite !Z.div_pow2_bits; [|lia..]. rewrite Z.mod_pow2_bits_low; [reflexivity|lia].
  - rewrite !Z.mod_pow2_bits_high; [reflexivity|lia..].
Qed.

Lemma le_bytes_mod32 v : le_bytes v 4 = le_bytes (v mod 2 ^ 32) 4.
Proof. unfold le_bytes. cbn. rewrite !byte_of_mod32; [reflexivity|lia..]. Qed.

Section build.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).

Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance hb_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation gl := (ct_gl hello_ct_objs).
Local Abbreviation cc := (ct_cc hello_ct_objs).

(** The thread's object lies at tb, and the world names it as the
    calling thread. *)
Context (tb : Z) (Hself : ow_self w = mkPtr tb (Obj tb)) (Hfd2 : In 2 (ow_fds w)).

(** A thread id's cell splits into a half and two quarters, one for
    each lock. *)
Lemma bytes_thirds b o xs :
  bytes b o xs ⊢ bytesq (DfracOwn (1/2)) b o xs ∗ bytesq (DfracOwn (1/2/2)) b o xs ∗ bytesq (DfracOwn (1/2/2)) b o xs.
Proof using Type.
  rewrite /bytes /bytesq pts_ptsq -(ptsq_split (1 / 2 / 2) (1 / 2 / 2)) Qp.div_2 -ptsq_split Qp.div_2. done.
Qed.

(** The formatter reads the stream jump tables, the flag that says
    the process has one thread and the allocator's idle state. Startup
    leaves all three among Hello's read-only objects, and the image
    names the allocator's two globals where the read-only promise puts
    them. *)
Lemma hello_fx_ro : hello_ro_rest hge ob ⊢ fputs_ro (ho_vb ob) ∗ malloc_ro.
Proof using Type.
  destruct hello_image_memory as (g & m & Hi). destruct (hello_loaded_tables g m Hi) as [Eg _]. subst g.
  destruct (hello_image_link_objects _ _ fr Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmp & Htc & _).
  iIntros "#H". iSplitR.
  - iDestruct "H" as "(V & S & _)". iExists (ho_vreg ob), (ho_sb ob), (ho_sreg ob). iFrame "V S".
  - iDestruct "H" as "(_ & _ & _ & _ & _ & _ & _ & T & _)".
    iExists (ho_mp ob), (ho_tc ob), (ho_dm ob), (ho_mpreg ob), (ho_tcreg ob), (ho_dmreg ob).
    iSplit; [iPureIntro; split; [exact Hmp | exact Htc] | iExact "T"].
Qed.

(** The private state keeps what the reports do not need: the first
    word of the global locale, Hello's read-only objects, the globals of
    close_stdout and `c: error` with the conversion lock and the catalog
    counter, and the locale cells that setlocale writes. Those include
    the thread's three table pointers, which early init has set. *)
Definition hello_hd_rest : iProp Σ :=
  pcell gl 0 (mkPtr cc (Ro cc)) ∗ hello_getopt_ro ∗ pts hello_close_objs_ps ∗ pts hello_locale_objs_ps ∗
  ct_lives hello_ct_objs ∗ ct_cells_set hello_ct_objs.

(** Startup leaves these objects, and they become the reports' part of
    the private state and the rest. *)
Lemma hello_hd_build v t : 0 < t < 2 ^ 32 ->
  pts hello_getopt_priv_ps -∗ pts hello_close_objs_ps -∗ pts hello_locale_objs_ps -∗
  ct_lives hello_ct_objs -∗ ct_cells_set hello_ct_objs -∗ live hello_sec.1 hello_sec.2 -∗ bytes hello_sec.1 0 (le_bytes v 4) -∗
  bytes tb 720 (le_bytes t 4) -∗ hello_ro_rest hge ob -∗ ct_locale hello_ct_objs ==∗
  hello_hd_getopt w fr tb ∗ hello_hd_rest.
Proof using Hself Hfd2.
  intros Ht. iIntros "Hp Hco Hlo Hcl Hcc Ls Bs Bt #Hro (Llt & Plt & Lgl & Pgl)".
  iMod (hello_getopt_own (glibc_program := hb_program) with "Hp") as "[#Ro (K1 & K2 & K3 & Rt & Ldb & Pdb & Pms)]";
    [reflexivity|].
  iModIntro. iSplitR "Pgl Hco Hlo Hcl Hcc".
  2: { iSplitL "Pgl"; [iExact "Pgl"|]. iSplitR; [iExact "Ro"|]. iSplitL "Hco"; [iExact "Hco"|].
       iSplitL "Hlo"; [iExact "Hlo"|]. iSplitL "Hcl"; [iExact "Hcl" | iExact "Hcc"]. }
  iPoseProof "Ro" as "(_ & _ & _ & _ & _ & _ & (%cbb & %creg & %cws & %Csh & Cl & _) & _)".
  destruct Csh as [[Hc|Hc] _ _ _ _ _ _ _ _]; [discriminate|]. injection Hc as <-.
  iEval (rewrite le_bytes_mod32) in "Bs". iDestruct (bytes_thirds with "Bt") as "(B1 & B2 & B3)".
  iExists (v mod 2 ^ 32, t, creg). iSplit; [iPureIntro; cbn; apply Z.mod_pos_bound; lia|].
  iIntros "((%tb2 & %tbreg & %jb & %Hc & Hl & Hcl & Hj & Hx) & (%bs & He) & Hps)".
  destruct Hc as (Hs & Hc). rewrite Hself in Hs. injection Hs as <-.
  iPoseProof (dtx_live_split (glibc_program := hb_program) tb tbreg) as "[Hb _]".
  iDestruct ("Hb" with "Hl") as "(Hl1 & Hl2 & Hl3)".
  rewrite /hello_dgx /hello_dg_G /dlk_G /dlk_G0 /dtx_G /dtx_G0 /dgx_G /dgx_before /dcg_before_v /rw_held /rw_self /dgx_stream.
  iExists (mkDlk 0 0 0 0), (mkDlk 0 0 0 0), (mkDlk 0 0 0 0). cbn [fst snd dl_r dl_cw dl_sh dl_fl].
  iSplit; [iPureIntro; unfold dlk_ready; cbn [dl_r dl_cw]; split_and!; first [lia | vm_compute; reflexivity]|].
  iExists tbreg, jb. iSplit; [iPureIntro; split; [exact Hself | exact Hc]|]. iFrame "Hcl Hj Hx".
  rewrite /hello_lk1 /hello_lk2 /hello_lkt /hello_root /hello_db /hello_ib /hello_sec /locale_name_res /dci_reads_v
    /int_cellq. cbn [fst snd].
  iEval (rewrite /hello_sec /bytes pts_ptsq; cbn [fst snd]) in "Bs".
  iEval (rewrite /hello_sec /live pts_ptsq; cbn [fst snd]) in "Ls".
  iEval (rewrite /live pts_ptsq) in "Llt Lgl". iEval (rewrite /pcell pts_ptsq) in "Plt Pms".
  iSplitR "Hps".
  { iExists bs. iPoseProof "Ro" as "(_ & H276 & H277 & Hcat & Hil & Hib & Hcc & Hdm & _)".
    iSplitL "Ldb Pdb Ls Bs".
    { iSplit; [iExact "Hdm"|]. iSplit; [iExact "Hcat"|]. iSplit; [iExact "Hcc"|]. iSplit; [iExact "H276"|].
      iSplit; [iExact "H277"|]. iSplitL "Ldb"; [iExact "Ldb"|]. iSplitL "Pdb"; [iExact "Pdb"|].
      iSplit; [iExact "Hil"|]. iSplit; [iExact "Hib"|]. iSplitL "Ls"; [iExact "Ls"|].
      iSplit; [iPureIntro; apply Z.mod_pos_bound; lia | iExact "Bs"]. }
    iSplitL "K1 Hl1 B1"; [iSplitL "K1"; [iExact "K1"|]; iSplitL "Hl1"; [iExact "Hl1"|];
      iSplit; [iPureIntro; lia | iExact "B1"]|].
    iSplitL "K2 Hl2 B2"; [iSplitL "K2"; [iExact "K2"|]; iSplitL "Hl2"; [iExact "Hl2"|];
      iSplit; [iPureIntro; lia | iExact "B2"]|].
    iSplitL "K3 Hl3 B3"; [iSplitL "K3"; [iExact "K3"|]; iSplitL "Hl3"; [iExact "Hl3"|];
      iSplit; [iPureIntro; lia | iExact "B3"]|].
    iSplitL "Rt"; [iExact "Rt"|].
    iSplitL "Llt Plt Lgl Pms".
    { iSplitL "Llt"; [iExact "Llt"|]. iSplitL "Plt"; [iExact "Plt"|]. iSplitL "Lgl"; [iExact "Lgl"|].
      iSplitL "Pms"; [iExact "Pms" | iExact "Cl"]. }
    iSplitR "He"; [|iExact "He"]. rewrite /hello_gettext_cache /hi_malloc_state.
    iPoseProof "Hro" as "(_ & _ & _ & _ & _ & _ & _ & $ & _)". }
  iSplitL "Hps"; [|iPoseProof "Ro" as "($ & _)"].
  iSplit; [iPoseProof "Hro" as "(_ & $ & _)"|].
  iSplit; [done|]. iSplitL "Hps"; [iExact "Hps"|]. iSplit; [iExact "Ro" | iApply (hello_fx_ro with "Hro")].
Qed.

End build.
