(** We want Hello's main to start from what startup leaves behind,
    rather than from memory that a caller describes. When startup calls
    `c: main`, [HelloStartPost](HelloStartPost.v) has already turned its
    memory into [hello_start_main_res]. Main's contract in
    [HelloStartBridge](HelloStartBridge.v) asks for a little more: the
    option parser's state with the promise that each call keeps it, the
    exit handlers' initial state and Hello's private state. This module
    builds main's precondition from those pieces.

    ## What the parser borrows

    getopt reads the environment through `c: getenv`, so it borrows a
    share of the environment's objects for each call. It also reads the
    thread's stack size through the alloca cutoff. Startup wrote that
    size in `c: __tls_init_tp`, so the thread object holds it, and the
    proof freezes those eight bytes. The parser's own objects and Hello's
    option table come from the image's start lists. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Language Logic StringLogic
  MemLogic HelloLeaf HelloMain.
From Glibc Require Import GlibcProgram GlibcSpec OsWorld OsRegistry WordString FileInv
  GetoptModule GetoptState GetoptDiag GetoptLongDiag GetoptLongPfxAlloc GetoptInitial
  HelloGlibcLibsT HelloGetoptTable HelloGetoptState HelloGlibcDebts HelloGlibcMainLoop HelloGetoptCall
  HelloGetoptStart HelloGetoptBackend GetenvCode GetenvScan GetenvEntry GetenvStatic GetenvCall StrchrCode StrcmpCode
  StrncmpCode StrlenLogic MemFwdCode HelloImageModule HelloImageLoad HelloImageLayout HelloImageStart
  HelloStartBridge HelloStartPost StartGetenv.
From Glibc Require HelloGlibcJoin CutoffCode CutoffLogic.
Import ListNotations GetoptState FileInv FileInv.ML FileInv.LG FileInv.L HelloGlibcDebts.
Open Scope Z_scope.
Open Scope list_scope.

(** This tactic proves a closed fact about the image's numbers. It
    avoids congruence, which would also search the large hypotheses
    about the image's functions. *)
Local Ltac num := first [vm_compute; reflexivity | vm_compute; intros ?H; discriminate H].

Section entry.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w : os_world) (m : mem).
Context (fr : word -> mem -> option (res unit * mem)) (Hi : initial_memory hello_image_module = Some (img_globals, m)).

(** This is the linked Hello program, run in the world w that startup
    ends in. *)
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
Local Abbreviation Pw := (program_of w glibc_os_registry hge).
Local Abbreviation o := hello_image_objs.

Context (Hk : hello_link hge o) (Hos : hello_os_layout w o).

(** The exit handlers start with no callback and a free lock. *)
Definition hello_exit0 : iProp Σ :=
  HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] 0 ∗ HelloGlibcJoin.Libs.exit_lock o.

(** The parser reads two frozen objects between calls: the name of its
    environment variable and the thread's stack size sz. *)
Definition hello_entry_ro (sz : Z) : iProp Σ :=
  □ (word_string DfracDiscarded (sym_ptr hge "glibc_getopt#str.145") [80;79;83;73;88;76;89;95;67;79;82;82;69;67;84] ∗
     CutoffLogic.stack_size_cell (glibc_program := Pw) (ow_self w) DfracDiscarded sz).

(** The parser keeps this state between calls: its private object, its
    flags with the strings and the table it reads, and the frozen
    objects. *)
Definition hello_entry_state (av : Z) (ar : region) (sz : Z) : list ptr -> Z -> iProp Σ :=
  fun ps i => (hello_getopt_state (img_a "glibc_getopt#getopt_data") (img_gd "glibc_getopt#getopt_data") av ar ps i ∗
    hello_getopt_globals hge (img_a "opterr") (img_gd "opterr") (img_a "optopt") (img_gd "optopt")
      (mkPtr (img_a "glibc_getopt#str.146") (Ro (img_a "glibc_getopt#str.146")))
      (mkPtr (img_a "glibc_getopt#str.147") (Ro (img_a "glibc_getopt#str.147")))
      (mkPtr (img_a "glibc_getopt#str.150") (Ro (img_a "glibc_getopt#str.150")))
      [45; 45] [45] [45; 87; 32]
      (mkPtr (img_a "hello#str.65") (Ro (img_a "hello#str.65"))) (mkPtr (img_a "hello#str.66") (Ro (img_a "hello#str.66")))
      (mkPtr (img_a "hello#str.67") (Ro (img_a "hello#str.67"))) (mkPtr (img_a "hello#str.68") (Ro (img_a "hello#str.68"))) ∗
    hello_entry_ro sz)%I.

(** Main starts with the arguments p0 :: ps in the vector av, the
    parser at index 1, no option argument, and the two names y and z. *)
Definition hello_main_x (av : Z) (ar : region) (p0 : ptr) (ps : list ptr) (y z : ptr) (sz : Z) : hello_main_binder :=
  (av, ar, p0, ps, null, y, z, null, 1, hello_entry_state av ar sz).

(** When startup calls main, it holds what main's contract asks for,
    once the open contracts supply Hello's private state. The option
    parser also needs to borrow half of what `c: getenv` reads, together
    with some resource E that the open contracts choose. That bundle can
    lend the thread's cleanup fields, and Hello's streams and private
    state can lend the bundle. *)
Lemma hello_main_entry debt (E : iProp Σ) T dom envp es sz tb av ar p0 ps y z :
  let G := (getenv_globals (glibc_program := Pw) (DfracOwn (1/2)) (img_a "__environ_counter") (img_gd "__environ_counter")
      (img_a "__environ") (img_gd "__environ") 0 envp ∗ getenv_storage (DfracOwn (1/2)) DfracDiscarded envp es ∗ E)%I in
  ow_self w = mkPtr tb (Obj tb) ->
  getopt_diag_rule w glibc_os_registry hge G T (ho_err o) dom ->
  getopt_ldiag_rule w glibc_os_registry hge G T (ho_err o) dom ->
  (G ⊢ tcb_cleanup_inv (ow_self w) ∗ (tcb_cleanup_inv (ow_self w) -∗ G)) ->
  (hello_stdio w hge o ∗ hd_priv w hge o debt ⊢ G ∗ (G -∗ hello_stdio w hge o ∗ hd_priv w hge o debt)) ->
  hello_start_main_res img_globals fr w av ar p0 ps y z -∗ icell tb CutoffLogic.off_stackblock_size sz -∗
  hd_priv w hge o debt -∗ hello_printf_ro hge ==∗
  fs_pre (hello_main_spec w hge o debt hello_exit0) (hello_main_x av ar p0 ps y z sz).
Proof using Hi Hk.
  intros G Hself Hdg Hld Hln Hg.
  pose proof (hello_image_layout img_globals m fr Hi) as Hy.
  destruct (hk_cookie _ _ Hk) as [Hcf Hcs].
  assert (Hgl : find_fn hge (TAtom "getopt_long") = Some (Defined glibc_getopt_long)) by num.
  assert (Hgi : find_fn hge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal)) by num.
  assert (Hgr : find_fn hge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r)) by num.
  assert (Hplo : find_fn hge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option))
    by num.
  assert (Hcmp : find_fn hge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp)) by num.
  assert (Hchr : find_fn hge (TAtom "__GI_strchr") = Some (Defined glibc_strchr)) by num.
  assert (Hchrn : find_fn hge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul)) by num.
  assert (Hncmp : find_fn hge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp)) by num.
  assert (Hgetfn : find_fn hge (TAtom "__GI_getenv") = Some (Defined glibc_getenv)) by num.
  assert (Hgms : find_fn hge (TAtom "__GI_memset") = Some (Defined glibc_memset)) by num.
  assert (Hcut : find_fn hge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined CutoffCode.glibc_libc_alloca_cutoff))
    by num.
  pose proof (hk_gi_strlen _ _ Hk) as Hlen.
  set (N := word_string DfracDiscarded (sym_ptr hge "glibc_getopt#str.145") [80;79;83;73;88;76;89;95;67;79;82;82;69;67;84] : iProp Σ).
  set (C := CutoffLogic.stack_size_cell (glibc_program := Pw) (ow_self w) DfracDiscarded sz).
  assert (Hnamed : getenv_at_rule w glibc_os_registry hge ((G ∗ N) ∗ □ C) (sym_ptr hge "glibc_getopt#str.145")).
  { apply getenv_at_rule_sep. apply (getenv_name_at_rule (glibc_program := Pw)).
    apply (getenv_static_name_contract (glibc_program := Pw)); num. }
  assert (Hloan : (G ∗ N) ∗ □ C ⊢
    CutoffLogic.cutoff_loan (glibc_program := Pw) DfracDiscarded ∗
    (CutoffLogic.cutoff_loan (glibc_program := Pw) DfracDiscarded -∗ (G ∗ N) ∗ □ C)).
  { iIntros "[[HG #HN] #HC]". iDestruct (Hln with "HG") as "[Ht Hb]".
    iSplitL "Ht"; [iFrame "Ht"; iExists sz; iExact "HC"|].
    iIntros "[Ht _]". iSplitL; [iSplitL; [iApply ("Hb" with "Ht")|iExact "HN"]|iExact "HC"]. }
  assert (HgC : hello_stdio w hge o ∗ hd_priv w hge o debt ∗ □ (N ∗ C) ⊢
    ((G ∗ N) ∗ □ C) ∗ (((G ∗ N) ∗ □ C) -∗ hello_stdio w hge o ∗ hd_priv w hge o debt ∗ □ (N ∗ C))).
  { iIntros "(Hio & Hpv & #HX)". iDestruct "HX" as "[#HN #HC]".
    iDestruct (Hg with "[$Hio $Hpv]") as "[HG Hb]".
    iSplitL "HG"; [iFrame "HG HN HC"|]. iIntros "[[HG _] _]".
    iDestruct ("Hb" with "HG") as "[Hio Hpv]". iFrame "Hio Hpv". iModIntro. iFrame "HN HC". }
  assert (Hloop : loop_getopt w hge o debt av ar (hello_entry_state av ar sz)).
  { exact (hello_getopt_ix_ro_sep_at w hge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hlen
      (img_a "glibc_getopt#getopt_data") (img_gd "glibc_getopt#getopt_data") ltac:(num) ltac:(num) ltac:(num)
      ltac:(num) ltac:(num)
      (img_a "opterr") (img_gd "opterr") (img_a "optopt") (img_gd "optopt") ltac:(num) ltac:(num) ltac:(num)
      ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num)
      (mkPtr (img_a "glibc_getopt#str.146") (Ro (img_a "glibc_getopt#str.146")))
      (mkPtr (img_a "glibc_getopt#str.147") (Ro (img_a "glibc_getopt#str.147")))
      (mkPtr (img_a "glibc_getopt#str.150") (Ro (img_a "glibc_getopt#str.150")))
      (sym_ptr hge "glibc_getopt#str.145") (sym_ptr hge "glibc_getopt#str.149") (sym_ptr hge "glibc_getopt#str.148")
      (sym_ptr hge "glibc_getopt#str.138") (sym_ptr hge "glibc_getopt#str.139") (sym_ptr hge "glibc_getopt#str.140")
      (sym_ptr hge "glibc_getopt#str.141") (sym_ptr hge "glibc_getopt#str.142") (sym_ptr hge "glibc_getopt#str.143")
      (sym_ptr hge "glibc_getopt#str.144") dom
      [45; 45] [45] [45; 87; 32] ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num)
      ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num) ltac:(num)
      ((G ∗ N) ∗ □ C) (hello_tcache o) (fun mid q => (T mid q ∗ N) ∗ □ C)%I
      (getopt_diag_rule_sep w glibc_os_registry hge (G ∗ N) (□ C) (fun mid q => T mid q ∗ N)%I (ho_err o) dom
        (getopt_diag_rule_sep w glibc_os_registry hge G N T (ho_err o) dom Hdg))
      (getopt_ldiag_rule_sep w glibc_os_registry hge (G ∗ N) (□ C) (fun mid q => T mid q ∗ N)%I (ho_err o) dom
        (getopt_ldiag_rule_sep w glibc_os_registry hge G N T (ho_err o) dom Hld))
      (hello_malloc_rule w hge o Hk) (hello_memset_rule w hge o Hk Hgms) (hello_free_rule w hge o Hk)
      (mkPtr (img_a "hello#str.65") (Ro (img_a "hello#str.65"))) (mkPtr (img_a "hello#str.66") (Ro (img_a "hello#str.66")))
      (mkPtr (img_a "hello#str.67") (Ro (img_a "hello#str.67"))) (mkPtr (img_a "hello#str.68") (Ro (img_a "hello#str.68")))
      (hello_ro_tcache hge o) (□ (N ∗ C))%I av ar Hnamed
      (getopt_cutoff_rule_with_loan (glibc_program := Pw) ((G ∗ N) ∗ □ C) DfracDiscarded
        ltac:(reflexivity) Hcf Hcs Hcut Hloan) HgC). }
  assert (E69 : sym_ptr hge "hello#str.69" = mkPtr (img_a "hello#str.69") (Ro (img_a "hello#str.69"))) by num.
  assert (Etb : sym_ptr hge "hello#parse_options.longopts.64" =
    mkPtr (img_a "hello#parse_options.longopts.64") (Ro (img_a "hello#parse_options.longopts.64"))) by num.
  rewrite /hello_start_main_res.
  iIntros "(Hro & #HN & _ & Hst & #Hargs & Hav & Hnc & HX0 & Hio & Hgo) Hsz Hpv #Hpr".
  iMod (CutoffLogic.stack_size_own (glibc_program := Pw) tb sz Hself with "Hsz") as "#HC".
  rewrite /hello_start_ps /hello_image_tab_ps /hello_image_getopt_ps /hello_tab_ps /getopt_start_ps.
  iDestruct (pts_app with "Hst") as "[Ht Hst]". iDestruct (pts_app with "Ht") as "[Ht L]".
  iDestruct (pts_app with "L") as "[L1 L]". iDestruct (pts_app with "L") as "[L2 L]".
  iDestruct (pts_app with "L") as "[L3 L]". iDestruct (pts_app with "L") as "[L4 L5]".
  iDestruct (pts_app with "Hst") as "[Hz Hst]". iDestruct (pts_app with "Hst") as "[He Hst]".
  iDestruct (pts_app with "Hst") as "[Ho Hst]". iDestruct (pts_app with "Hst") as "[Hdd Hst]".
  iDestruct (pts_app with "Hst") as "[H7 H0]".
  iMod (hello_table_own_ro with "Ht L1 L2 L3 L4 L5") as "(#Htab & #Hos & #Hts)"; [num..|].
  iMod (getopt_lits_own with "Hdd H7 H0") as "(#Hdd & #H7 & #H0)"; [num..|].
  iDestruct (int_global_own with "He") as "[Hel Hec]"; [lia|].
  iDestruct (int_global_own with "Ho") as "[Hol Hoc]"; [lia|].
  iDestruct "Hav" as "(%Hav & Havl & Hcl)". destruct Hav as (Hav0 & Hav8 & Hn & Hfit & Har).
  iModIntro. rewrite /hello_main_x. cbn [fs_pre hello_main_spec hello_main_pre].
  iSplit; [iPureIntro; split; [cbn [length] in *; lia|exact Hloop]|].
  iSplitL "Hro"; [iApply hello_ro_join; rewrite E69 Etb; iSplitL "Hro"; [iExact "Hro"|];
    iSplitR; [iExists s_optstring; iExact "Hos"|]; iSplitR; [iExact "Hts" | iExact "Hpr"]|].
  iSplitR; [iExact "Hargs"|].
  iSplitL "Havl Hcl"; [iSplit; [iPureIntro; split_and!; assumption|]; iSplitL "Havl"; [iExact "Havl"|iExact "Hcl"]|].
  iSplitL "Hnc"; [iExact "Hnc"|]. iSplitL "HX0"; [iExact "HX0"|]. iSplitL "Hio"; [iExact "Hio"|].
  iSplitL "Hpv"; [iExact "Hpv"|]. iSplitL "Hgo"; [iExact "Hgo"|].
  rewrite /hello_entry_state. iSplitL "Hz".
  { iApply (hello_getopt_state_pieces with "Hz"); [lia|num|num|num|cbn [length] in *; lia..]. }
  iSplitL "Hel Hec Hol Hoc".
  { iExists 1, 63. iSplitL "Hel"; [iExact "Hel"|]. iSplitL "Hec"; [iExact "Hec"|].
    iSplitL "Hol"; [iExact "Hol"|]. iSplitL "Hoc"; [iExact "Hoc"|]. rewrite E69 Etb. iSplitR; [iExact "Hos"|].
    iSplitR; [iExact "Htab"|]. iSplitR; [iExact "Hdd"|]. iSplitR; [iExact "H7" | iExact "H0"]. }
  rewrite /hello_entry_ro. iModIntro. iFrame "HN HC".
Qed.

End entry.
