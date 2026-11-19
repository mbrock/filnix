(** Hello's main first calls `c: setlocale (LC_ALL, "")`, and the call
    must leave Hello's private state as it found it. Another module
    proves the call over glibc's code, given the constants that setlocale
    reads and the cells that it writes. This module takes those out of
    the private state, runs the call and puts them back.

    Setlocale holds a lock while it works, and it reads the thread's
    current locale. Main keeps the lock and that pointer in the state
    it lends to getopt's error messages, so this proof borrows them
    from there. Main keeps everything else that setlocale reads or
    writes with its copy of the C locale. *)

From Glibc Require Fix.
From Glibc Require Import Unit_locale_setlocale_os.
From Glibc Require Import GlibcProgram GlibcTactics.
From iris.program_logic Require Import language weakestpre.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv StrlenLogic WordString GlibcSpec
  StartGetenv GetenvEntry GetenvStatic GetenvScan LocaleEnv
  HelloGlibcDebts HelloGetoptDiagLock HelloImageModule HelloImageLoad HelloImageLayout
  HelloStartGetopt HelloStartGetoptRules HelloStartHdGetopt HelloLocaleState
  HelloSetlocalePostload HelloSetlocaleAll.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section wrap.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).

Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance sa_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation ob := hello_image_objs.
Local Abbreviation gl := (img_a "_nl_global_locale").
Local Abbreviation cv := (mkPtr (img_a "_nl_C_name") (Ro (img_a "_nl_C_name"))).

(** The warnings' state names the thread's own object at tb, and it
    needs stderr open, because a warning writes to it. *)
Context (tb : Z) (Hfd2 : In 2 (ow_fds w)).

(** ## The call

    Setlocale reads constants of the C locale and rewrites a few cells
    with the values they already have. The proof needs a way to lend
    those out of main's state and to take the cells back afterwards. *)
Definition setlocale_bridge : Prop :=
  locale_c w fr ∗ hello_getopt_ro ⊢ sl_ro ∗ pl_ro ∗ sl_gl_cells ∗ pl_cells ∗ pcell gl 176 cv ∗ hello_cat_cntr ∗
    (sl_gl_cells -∗ pl_cells -∗ pcell gl 176 cv -∗ hello_cat_cntr -∗ locale_c w fr).

(** After the call, main's state is the same as before. This holds for
    any state that keeps the environment, the warnings' things and the
    C locale, whatever else it also keeps. *)
Lemma hello_setlocale_all (Y priv : iProp Σ) dq dqa dqe bc rc be re counter ep es :
  setlocale_bridge -> getenv_image_ok hge bc rc be re -> c_locale_env (map entry_text es) -> frees_heap fr ->
  (priv ⊣⊢ (getenv_globals dq bc rc be re counter ep ∗ getenv_storage dqa dqe ep es) ∗ hello_hd_getopt w fr tb ∗
    (Y ∗ hello_priv_rest w fr)) ->
  setlocale_all w hge ob priv.
Proof using Hfd2.
  intros Hbr Himg Henv Hfh Hpriv. exists Unit_locale_setlocale_os.fn___GI_setlocale. split; [vm_compute; reflexivity|].
  split; [eexists; reflexivity|]. intros f Φ Hf.
  assert (E80 : sym_ptr hge "hello#str.80" = mkPtr (img_a "hello#str.80") (Ro (img_a "hello#str.80")))
    by (vm_compute; reflexivity).
  rewrite E80 in Hf. iIntros "(_ & Hio & Hp) HK". iDestruct (Hpriv with "Hp") as "(HN & Hgo & HY & Hrest)".
  iDestruct (hello_hd_lend w fr tb Hfd2 (getenv_globals dq bc rc be re counter ep ∗ getenv_storage dqa dqe ep es) Y with "[Hio HN Hgo HY]") as "[[[HGg HGs] (%x & %Hx & HG)] Hback]";
    [iFrame "Hio HN Hgo HY"|].
  rewrite /hello_dgx /hello_dg_G.
  iDestruct (dlk_setlocale with "HG") as "(_ & (Hlt & Hlc & Hgl & H168 & #Hcap) & %s & %tr & [%Hs %Htc] & [Hlk Hself] & Hlb)".
  iDestruct "Hrest" as "(Hl0 & Hconv & #Hgro & Hres)".
  iDestruct (Hbr with "[$Hl0 $Hgro]") as "(Hsl & Hpl & Hgc & Hpc & H176 & Hn & Hbk)".
  destruct s as [r cw sh fl]. destruct Hs as (Hr & Hfl & Hcw). cbn [dl_r dl_cw dl_sh dl_fl] in *. subst r fl.
  destruct Htc as (Hself & Htb & Htb8 & Htbe & Htbr). change off_cancelhandling with 792 in Htbe.
  iApply (sl_explore w fr dq dqa dqe bc rc be re counter ep es Himg Henv Hfh f tb tr _ _ x.1.2 cw sh _ (DfracOwn 1)
    with "Hlk Hself Hgl H176 Hcap Hsl Hpl HGg HGs Hgc Hlt Hlc Hpc Hn [-]").
  1: exact Hf. 1: (split_and!; [reflexivity | lia | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence
    | exact Hself | lia | lia | lia]).
  1: exact Hcw.
  iIntros "HGg HGs Hgl H176 Hgc Hlt Hlc Hpc Hn Hlk Hself". iApply "HK". iExists cv. iSplit; [done|].
  iDestruct ("Hbk" with "Hgc Hpc H176 Hn") as "Hl0".
  iDestruct ("Hlb" $! (mkDlk 0 0 sh 0) with "[%] [$Hlt $Hlc $Hgl $H168 $Hcap] [$Hlk $Hself]") as "HG".
  { unfold dlk_ready. cbn. split_and!; lia. }
  iDestruct ("Hback" with "[HGg HGs HG]") as "[Hio (HN & Hgo & HY)]".
  { iFrame "HGg HGs". iExists x. iSplit; [done | iExact "HG"]. }
  iFrame "Hio". iApply Hpriv. rewrite /hello_priv_rest /hello_priv_residual.
  iSplitL "HN"; [iExact "HN"|]. iSplitL "Hgo"; [iExact "Hgo"|]. iSplitL "HY"; [iExact "HY"|].
  iSplitL "Hl0"; [iExact "Hl0"|]. iSplitL "Hconv"; [iExact "Hconv"|]. iSplitR; [iExact "Hgro" | iExact "Hres"].
Qed.

End wrap.
