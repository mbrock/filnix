(** This file states and proves Hello's safety theorem: GNU Hello,
    linked with userland glibc, never panics, gets stuck or breaks a
    contract when it runs from main. It is the one endpoint of the Hello
    proof, and its premises are what remains open.

    Most of Hello's library calls run glibc's own proved code: the option
    parser getopt_long with its string, allocation and alloca-cutoff
    callees, getenv, and the calls in HelloGlibcJoin.v. The calls that
    print, convert or read the locale are still contracts, the fields of
    [HelloCore], and so are the two printers of getopt's warnings.

    Nobody has proved yet what glibc does before main, so the caller
    describes the memory that main starts with. Some of it is just what
    the loader writes into the program image, such as the parser's
    globals and Hello's table of long options. The rest is what startup
    would have set up, such as the streams and the arguments. Each object
    also needs an address, which the caller names. A script in
    nanofil/tests lists and counts all these premises, and CI prints the
    count. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloMain.
From Glibc Require Import GlibcProgram OsWorld OsRegistry WordString FileInv
  GetoptModule GetoptState GetoptInitialize GetoptDiag GetoptLongDiag GetoptLongPfxAlloc
  GetoptLongStr GetoptInitial AtexitLogic HelloGlibcLibsT HelloGetoptTable HelloGetoptState
  HelloGlibcDebts HelloGlibcMainLoop HelloGlibcMainFull HelloGetoptCall HelloGetoptStart
  HelloGetoptBackend GetenvCode GetenvEntry GetenvScan GetenvStatic GetenvCall
  StrchrCode StrcmpCode StrncmpCode StrlenLogic MemFwdCode.
From Glibc Require HelloGlibcJoin CutoffCode CutoffLogic.
Import ListNotations GetoptState FileInv FileInv.ML FileInv.LG FileInv.L HelloGlibcDebts.
Open Scope Z_scope.
Open Scope list_scope.

(** These bytes spell the parser's environment key, without the terminator.
    The existing literal representation adds the terminator and word padding. *)
Definition posixly_correct_bytes : list Z := [80;79;83;73;88;76;89;95;67;79;82;82;69;67;84].

(** Every allowed execution of Hello's main function avoids panics, stuck
    steps and contract failures. Initial memory must contain the name,
    its terminator, and the thread's stack size at the addresses chosen
    by the linked program, beside glibc's parser objects and Hello's
    option table. The caller
    also supplies readable environment globals, an array, and its strings.
    Neither the stack-size value nor the parser's valid index is fixed here. *)
Theorem hello_never_panics Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo bdd rdd b7 r7 b0 r0
    bn rn mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ts sz
    entries ep dq dqa dqt bc rc be re counter :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  find_fn ge (TAtom "getopt_long") = Some (Defined glibc_getopt_long) ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_getenv") = Some (Defined glibc_getenv) ->
  find_fn ge (TAtom "__GI_memset") = Some (Defined glibc_memset) ->
  find_fn ge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined CutoffCode.glibc_libc_alloca_cutoff) ->
  find_fn ge (TAtom "zthread_self_cookie") = None -> Term.lookup (TAtom "zthread_self_cookie") (ge_globals ge) = None ->
  ow_self w0 = mkPtr ts (Obj ts) ->
  Term.lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 56 <= r_end greg -> r_end greg <= 2 ^ 48 ->
  Term.lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)) ->
  0 < oe -> oe + 4 <= r_end roe -> r_end roe <= 2 ^ 48 ->
  Term.lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)) ->
  0 < oo -> oo + 4 <= r_end roo -> r_end roo <= 2 ^ 48 ->
  0 < ho_oa o -> 0 < ho_oi o -> 0 < ho_se o ->
  Term.lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some (mkPtr bdd (Ro bdd)) ->
  0 < bdd -> bdd mod 8 = 0 -> bdd + 8 <= r_end rdd -> r_end rdd <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some (mkPtr b7 (Ro b7)) ->
  0 < b7 -> b7 mod 8 = 0 -> b7 + 8 <= r_end r7 -> r_end r7 <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some (mkPtr b0 (Ro b0)) ->
  0 < b0 -> b0 mod 8 = 0 -> b0 + 8 <= r_end r0 -> r_end r0 <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#parse_options.longopts.64") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  0 < tb -> tb mod 8 = 0 -> tb + 136 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#str.69") (ge_globals ge) = Some (mkPtr b5 (Ro b5)) ->
  0 < b1 -> b1 mod 8 = 0 -> b1 + 16 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 16 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  0 < b4 -> b4 mod 8 = 0 -> b4 + 8 <= r_end r4 -> r_end r4 <= 2 ^ 48 ->
  0 < b5 -> b5 mod 8 = 0 -> b5 + 8 <= r_end r5 -> r_end r5 <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some (mkPtr bn (Ro bn)) ->
  0 < bn -> bn mod 8 = 0 -> bn + 16 <= r_end rn -> r_end rn <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  Term.lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  Term.lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  Term.lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  Term.lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  Term.lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  Term.lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  Term.lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  Term.lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Term.lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  Term.lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m ->
  agrees m (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 ++
    lit_ps bn rn (lit_words posixly_correct_bytes) ++ cell ts CutoffLogic.off_stackblock_size sz)) ->
  os_wi w0 m w (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 ++
    lit_ps bn rn (lit_words posixly_correct_bytes) ++ cell ts CutoffLogic.off_stackblock_size sz)) ->
  NoDup (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 ++
    lit_ps bn rn (lit_words posixly_correct_bytes) ++ cell ts CutoffLogic.off_stackblock_size sz).*1 ->
  map_disjoint h1 (list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 ++
    lit_ps bn rn (lit_words posixly_correct_bytes) ++ cell ts CutoffLogic.off_stackblock_size sz)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : HelloCore w0 ge o) (E : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    let G := (getenv_globals (glibc_program := program_of w0 glibc_os_registry ge)
      dq bc rc be re counter ep ∗ getenv_storage dqa dqt ep entries ∗ E)%I in
    getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    (G ⊢ tcb_cleanup_inv (ow_self w0) ∗ (tcb_cleanup_inv (ow_self w0) -∗ G)) /\
    (hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ⊢ G ∗ (G -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o debt)) /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ==∗
      hello_ro_rest ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hgetfn Hgms Hcf Hsf Hss Hts
    Hgb Hgb0 Hgb8 Hgbe Hgbr Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    H146 Hd0 Hd8 Hde Hdr H147 H70 H78 H7e H7r H150 H00 H08 H0e H0r
    Htb Htb0 Htb8 Htbe Htbr H69 Hb10 Hb18 Hb1e Hb1r Hb20 Hb28 Hb2e Hb2r Hb30 Hb38 Hb3e Hb3r
    Hb40 Hb48 Hb4e Hb4r Hb50 Hb58 Hb5e Hb5r H145 Hbn Hbn8 Hbne Hbnr
    H148 H149 H138 H139 H140 H141 H142 H143 H144 Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal
    Hargc Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  apply (hello_getopt_table_core_sep Σ w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo
    bdd rdd b7 r7 b0 r0 tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5
    (lit_ps bn rn (lit_words posixly_correct_bytes) ++ cell ts CutoffLogic.off_stackblock_size sz)); try assumption.
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & E & T & Hdg & Hld & Hln & Hg & Hpre).
  set (G := (getenv_globals (glibc_program := program_of w0 glibc_os_registry ge)
    dq bc rc be re counter ep ∗ getenv_storage dqa dqt ep entries ∗ E)%I) in *.
  set (N := word_string DfracDiscarded (mkPtr bn (Ro bn)) posixly_correct_bytes : iProp Σ).
  set (C := CutoffLogic.stack_size_cell (glibc_program := program_of w0 glibc_os_registry ge)
    (ow_self w0) DfracDiscarded sz).
  exists debt, (N ∗ C)%I. split.
  { iIntros "Hpieces". iDestruct (pts_app with "Hpieces") as "[HN HC]".
    iMod (lit_own bn rn posixly_correct_bytes with "HN") as "#HN";
      [exact Hbn|exact Hbn8|exact Hbne|exact Hbnr|vm_compute; reflexivity|].
    iMod (CutoffLogic.stack_size_own (glibc_program := program_of w0 glibc_os_registry ge) ts sz Hts with "HC") as "#HC".
    iModIntro. iModIntro. iFrame "HN HC". }
  split; [|exact Hpre].
  pose proof (hk_gi_strlen _ _ Hk) as Hstrlen.
  assert (Hnamed : getenv_at_rule w0 glibc_os_registry ge ((G ∗ N) ∗ □ C) (mkPtr bn (Ro bn))).
  { apply getenv_at_rule_sep. apply (getenv_name_at_rule (glibc_program := program_of w0 glibc_os_registry ge)).
    apply (getenv_static_name_contract (glibc_program := program_of w0 glibc_os_registry ge));
      try assumption; exact (hk_gi_strlen _ _ Hk). }
  assert (Hloan : (G ∗ N) ∗ □ C ⊢
    CutoffLogic.cutoff_loan (glibc_program := program_of w0 glibc_os_registry ge) DfracDiscarded ∗
    (CutoffLogic.cutoff_loan (glibc_program := program_of w0 glibc_os_registry ge) DfracDiscarded -∗ (G ∗ N) ∗ □ C)).
  { iIntros "[[HG #HN] #HC]". iDestruct (Hln with "HG") as "[Ht Hb]".
    iSplitL "Ht"; [iFrame "Ht"; iExists sz; iExact "HC"|].
    iIntros "[Ht _]". iSplitL; [iSplitL; [iApply ("Hb" with "Ht")|iExact "HN"]|iExact "HC"]. }
  assert (HgC : hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ □ (N ∗ C) ⊢
    ((G ∗ N) ∗ □ C) ∗ (((G ∗ N) ∗ □ C) -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ □ (N ∗ C))).
  { iIntros "(Hio & Hpv & #HX)". iDestruct "HX" as "[#HN #HC]".
    iDestruct (Hg with "[$Hio $Hpv]") as "[HG Hb]".
    iSplitL "HG"; [iFrame "HG HN HC"|]. iIntros "[[HG _] _]".
    iDestruct ("Hb" with "HG") as "[Hio Hpv]". iFrame "Hio Hpv". iModIntro. iFrame "HN HC". }
  exact (hello_getopt_ix_ro_sep_at w0 ge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp (hk_gi_strlen _ _ Hk)
    gb greg Hgb Hgb0 Hgb8 Hgbe Hgbr oe roe oo roo Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0)) (mkPtr bn (Ro bn)) mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom
    [45;45] [45] [45;87;32] H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    ((G ∗ N) ∗ □ C) (hello_tcache o) (fun mid q => (T mid q ∗ N) ∗ □ C)%I
    (getopt_diag_rule_sep w0 glibc_os_registry ge (G ∗ N) (□ C) (fun mid q => T mid q ∗ N)%I (ho_err o) dom
      (getopt_diag_rule_sep w0 glibc_os_registry ge G N T (ho_err o) dom Hdg))
    (getopt_ldiag_rule_sep w0 glibc_os_registry ge (G ∗ N) (□ C) (fun mid q => T mid q ∗ N)%I (ho_err o) dom
      (getopt_ldiag_rule_sep w0 glibc_os_registry ge G N T (ho_err o) dom Hld))
    (hello_malloc_rule w0 ge o Hk) (hello_memset_rule w0 ge o Hk Hgms) (hello_free_rule w0 ge o Hk)
    (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4))
    (hello_ro_tcache ge o) (□ (N ∗ C))%I av ar Hnamed
    (getopt_cutoff_rule_with_loan (glibc_program := program_of w0 glibc_os_registry ge) ((G ∗ N) ∗ □ C) DfracDiscarded
      ltac:(reflexivity) Hsf Hss Hcf Hloan) HgC).
Qed.
