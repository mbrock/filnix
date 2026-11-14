From Glibc Require Import GlibcProgram.
(** Hello's safety theorem with glibc's getopt_long, in HelloGetoptCall.v,
    lets the streams and the callees' private state lend the parser its
    globals, its strings and Hello's option table. A reader then cannot
    tell where those objects come from at startup. This file states the
    theorem so that the loop carries those objects next to the parser's
    private object, and the loan covers only the backends' resources G
    and M.

    glibc's own objects come from the program's starting memory. That
    memory holds the zeroed parser object, opterr with the value 1,
    optopt with the value 63 and the three strings "--", "-" and "-W ".
    The rest of the memory must supply everything else. Hello's option
    table and option string stay in that rest, because Hello's read-only
    literals already share them. The addresses of all these objects are
    parameters, and the caller states that their fields are distinct
    from each other and from the rest. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv StrchrCode StrcmpCode StrncmpCode StrlenLogic
  GetoptModule GetoptState GetoptInitialize GetoptDiag GetoptLongExact GetoptLongStore GetoptLongDiag
  GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSite GetoptWrapParse GetoptLongStr GetoptInitial
  AtexitLogic HelloGlibcLibsT HelloGetoptTable HelloGetoptState HelloGlibcDebts HelloGlibcMainLoop
  HelloGlibcMainFull HelloGetoptCall.
From Glibc Require FileInv HelloGlibcDebts HelloGlibcMainFull HelloGlibcJoin HelloGetoptCall.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L HelloGlibcDebts.

(** ## glibc's objects at startup

    Before Hello's first call, glibc's parser has written nothing. Its
    private object holds zeroes, opterr holds 1 and optopt holds the
    question mark. The strings are constant. *)

(** These are the fields of glibc's objects that the parser uses, at the
    bases that the linked program chose. *)
Definition getopt_start_ps (gb : Z) (greg : region) (oe : Z) (roe : region) (oo : Z) (roo : region)
    (bdd : Z) (rdd : region) (b7 : Z) (r7 : region) (b0 : Z) (r0 : region) : list (piece * pval) :=
  getopt_zero_ps gb greg ++ int_global_ps oe roe 1 ++ int_global_ps oo roo 63 ++
  lit_ps bdd rdd (lit_words [45; 45]) ++ lit_ps b7 r7 (lit_words [45]) ++ lit_ps b0 r0 (lit_words [45; 87; 32]).

(** If no starting memory could satisfy the theorem's assumptions, the
    theorem would say nothing. When the getopt module is loaded on its
    own, its memory holds exactly these values, each in its own place.
    So suitable memory exists, though the linked program may put the
    objects elsewhere. *)
Lemma getopt_start_fixture :
  let ps := getopt_start_ps 65584 getopt_private_region 65696 (gd 65696 65704) 65760 (gd 65760 65768)
    66176 (gd 66176 66184) 66208 (gd 66208 66216) 66352 (gd 66352 66360) in
  all_agree getopt_memory ps /\ NoDup ps.*1.
Proof.
  cbn zeta. split.
  - apply checked_pieces_all_agree. unfold getopt_memory. vm_compute. reflexivity.
  - apply (NoDup_fmap_1 (fun p => match p with
      | PLive b => 4 * 512 * b | PByte b o => 4 * (512 * b + o) + 1
      | PAux b o => 4 * (512 * b + o) + 2 | _ => 3 end)).
    apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(** ## The theorem

    Hello should be safe when glibc's option parser starts the way the
    loader leaves it, not only when a caller hands the parser a suitable
    state. The theorem below starts glibc's objects from the starting
    memory. It still asks where the linked program put them, and it asks
    for the rest of the program's resources as before. Read-only text
    must be frozen before it is shared, so that last request may freeze
    it. It also supplies Hello's option table and option string. *)

(** Every allowed execution of Hello with glibc's getopt_long avoids
    panics, stuck steps and contract failures when glibc's objects start
    with their initial values beside the rest of the program. *)
Theorem hello_never_panics_getopt_start Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo bdd rdd b7 r7 b0 r0
    penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom n1 n2 n3 n4 :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  find_fn ge (TAtom "getopt_long") = Some (Defined glibc_getopt_long) ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
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
  Term.lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  Term.lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  Term.lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  Term.lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  Term.lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  Term.lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  Term.lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  Term.lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  Term.lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  Term.lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m ->
  agrees m (h1 ∪ list_to_map (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  os_wi w0 m w (h1 ∪ list_to_map (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  NoDup (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0).*1 ->
  map_disjoint h1 (list_to_map (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : HelloCore w0 ge o) (G M : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    getenv_rule w0 glibc_os_registry ge G /\ getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\ getopt_cutoff_rule w0 glibc_os_registry ge /\
    getopt_malloc_rule w0 glibc_os_registry ge M /\ getopt_memset_rule w0 glibc_os_registry ge /\
    getopt_free_rule w0 glibc_os_registry ge /\
    (hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ⊢ (G ∗ M) ∗ (G ∗ M -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o debt)) /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ==∗
      hello_ro ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i ∗
      opt_table (sym_ptr ge "hello#parse_options.longopts.64") (hello_los n1 n2 n3 n4) ∗
      word_string DfracDiscarded (sym_ptr ge "hello#str.69") s_optstring)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hgb Hgb0 Hgb8 Hgbe Hgbr Hoe Hoe0 Hoee Hoer
    Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0 H146 Hd0 Hd8 Hde Hdr H147 H70 H78 H7e H7r H150 H00 H08 H0e H0r
    H145 H148 H149 H138 H139 H140 H141 H142 H143 H144 -> Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  apply (heap_labelled_safe Σ glibc_os_registry (os_wi w0) ge _ m s w _ (fun _ => True) Hr Hd Ha Hw).
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & G & M & T & Hge & Hdg & Hld & Hcu & Hma & Hms & Hfr & Hgm & Hpre).
  pose proof (hello_getopt_ix_own w0 ge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp (hk_gi_strlen _ _ Hk)
    gb greg Hgb Hgb0 Hgb8 Hgbe Hgbr oe roe oo roo Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0)) penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom
    [45; 45] [45] [45; 87; 32] H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    G M T Hge Hdg Hld Hcu Hma Hms Hfr n1 n2 n3 n4 Hgm av ar) as Hix.
  rewrite big_sepM_union; [|exact Hdisj].
  rewrite (big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v)); [|exact Hnd].
  iIntros "[H1 HP]".
  iAssert (pts (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) with "[HP]" as "HP";
    [rewrite /pts; iExact "HP"|].
  rewrite /getopt_start_ps. iDestruct (pts_app with "HP") as "[Hz HP]".
  iDestruct (pts_app with "HP") as "[He HP]". iDestruct (pts_app with "HP") as "[Ho HP]".
  iDestruct (pts_app with "HP") as "[Hdd HP]". iDestruct (pts_app with "HP") as "[H7 H0]".
  iMod (Hpre with "H1") as "(#Hro & #Hps & (%Hav & Havl & Hcl) & Hn & HX & Hio & Hpv & Hgo & #Ht & #H69)".
  iMod (getopt_lits_own with "Hdd H7 H0") as "(#Hdd & #H7 & #H0)"; try assumption.
  iDestruct (int_global_own with "He") as "[Hel Hec]"; [lia|].
  iDestruct (int_global_own with "Ho") as "[Hol Hoc]"; [lia|].
  destruct Hav as (Hav0 & Hav8 & Hn & Hfit & Har).
  iApply (HelloGlibcMainFull.main_full_state w0 ge o debt _ _
    (HelloGlibcJoin.Libs.hello_libs w0 ge o Hk Hos debt c) Hy av ar p0 ps x y z a i _ _ Hi Hix
    with "Hro Hps [Havl Hcl] Hn HX Hio Hpv Hgo [Hz Hel Hec Hol Hoc]").
  - iSplit; [iPureIntro; split_and!; assumption|]. iSplitL "Havl"; [iExact "Havl" | iExact "Hcl"].
  - iSplitL "Hz".
    { iApply (hello_getopt_state_pieces with "Hz"); try assumption; cbn [length] in *; lia. }
    iExists 1, 63. iSplitL "Hel"; [iExact "Hel"|]. iSplitL "Hec"; [iExact "Hec"|].
    iSplitL "Hol"; [iExact "Hol"|]. iSplitL "Hoc"; [iExact "Hoc"|]. iSplitR; [iExact "H69"|].
    iSplitR; [iExact "Ht"|]. iSplitR; [iExact "Hdd"|]. iSplitR; [iExact "H7" | iExact "H0"].
Qed.
