From Glibc Require Import GlibcProgram.
(** Hello's safety theorem with glibc's getopt_long, in HelloGetoptCall.v,
    lets the streams and the callees' private state lend the parser its
    globals, its strings and Hello's option table. A reader then cannot
    tell where those objects come from at startup. This file states the
    theorem so that the loop carries those objects next to the parser's
    private object, and the loan covers only the backends' resources G
    and M.

    When Hello starts, glibc's option parser has not run, so its objects
    still hold what the loader wrote. The theorems here take those objects
    from the program's starting memory: the zeroed parser object, the
    error flag holding 1, the option character holding 63, and the three
    strings "--", "-" and "-W ". The second theorem also takes Hello's
    option table, its names and its option string from there. The rest
    of memory supplies everything else. Every address is a parameter,
    and the caller states that all these pieces have distinct keys. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloMain HelloName.
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

(** This checks glibc's own pieces and nothing else. When the getopt
    module is loaded on its own, its memory holds exactly these values,
    each at its own key. It does not show that Hello's, the backends' and
    startup's other assumptions can hold in the same memory, and the
    linked program may put these objects elsewhere. *)
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

(** ## The startup argument

    The startup theorems in this file and in HelloGetoptBackend.v differ
    only in how they obtain the loop's contract for getopt_long. The two
    lemmas below take that contract as an assumption and do the rest of
    the work: they split the starting memory, build glibc's objects and
    Hello's table from it, and run Hello's main function. *)

(** Hello runs safely when each call to getopt_long keeps the loop's
    promise, and glibc's objects start zeroed beside the rest of memory. *)
Lemma hello_getopt_start_core Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 n1 n2 n3 n4 :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  0 < gb -> gb mod 8 = 0 -> gb + 56 <= r_end greg -> r_end greg <= 2 ^ 48 ->
  0 < bdd -> bdd mod 8 = 0 -> bdd + 8 <= r_end rdd -> r_end rdd <= 2 ^ 48 ->
  0 < b7 -> b7 mod 8 = 0 -> b7 + 8 <= r_end r7 -> r_end r7 <= 2 ^ 48 ->
  0 < b0 -> b0 mod 8 = 0 -> b0 + 8 <= r_end r0 -> r_end r0 <= 2 ^ 48 ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m -> agrees m (h1 ∪ list_to_map (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  os_wi w0 m w (h1 ∪ list_to_map (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) -> NoDup (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0).*1 ->
  map_disjoint h1 (list_to_map (getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists debt : HelloCore w0 ge o,
    loop_getopt w0 ge o debt av ar (fun ps i => hello_getopt_state gb greg av ar ps i ∗
      hello_getopt_globals ge oe roe oo roo (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0))
        [45; 45] [45] [45; 87; 32] n1 n2 n3 n4)%I /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ==∗
      hello_ro ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i ∗
      opt_table (sym_ptr ge "hello#parse_options.longopts.64") (hello_los n1 n2 n3 n4) ∗
      word_string DfracDiscarded (sym_ptr ge "hello#str.69") s_optstring)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgb0 Hgb8 Hgbe Hgbr Hd0 Hd8 Hde Hdr H70 H78 H7e H7r H00 H08 H0e H0r
    -> Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  apply (heap_labelled_safe Σ glibc_os_registry (os_wi w0) ge _ m s w _ (fun _ => True) Hr Hd Ha Hw).
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & Hix & Hpre).
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
    H145 H148 H149 H138 H139 H140 H141 H142 H143 H144 Hargc Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  apply (hello_getopt_start_core Σ w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo
    bdd rdd b7 r7 b0 r0 n1 n2 n3 n4); try assumption.
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & G & M & T & Hge & Hdg & Hld & Hcu & Hma & Hms & Hfr & Hgm & Hpre).
  exists debt. split; [|exact Hpre].
  exact (hello_getopt_ix_own w0 ge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp (hk_gi_strlen _ _ Hk)
    gb greg Hgb Hgb0 Hgb8 Hgbe Hgbr oe roe oo roo Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0)) penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom
    [45; 45] [45] [45; 87; 32] H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    G M T Hge Hdg Hld Hcu Hma Hms Hfr n1 n2 n3 n4 Hgm av ar).
Qed.

(** ## Reading Hello's table from memory

    The theorem above asks the rest of memory for Hello's option table
    and option string, although Hello's read-only literals already share
    the same bytes as plain strings. A proof of Hello's startup could not
    supply both from separate memory. The theorem below therefore reads
    the table, its names and the option string from the starting memory.
    It freezes those bytes once and derives the table and both strings
    from them, so the rest of memory supplies only the other literals. *)

(** These are Hello's literals other than its option string and its table. *)
Definition hello_lits_rest : list string :=
  ["hello#str.54"; "hello#str.55"; "hello#str.56"; "hello#str.57"; "hello#str.58"; "hello#str.59";
   "hello#str.60"; "hello#str.61"; "hello#str.62"; "hello#str.63";
   "hello#str.70"; "hello#str.71"; "hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75";
   "hello#str.76"; "hello#str.77"; "hello#str.78"; "hello#str.79"; "hello#str.80"; "hello#str.81";
   "hello#str.82"; "hello#str.83"]%string.

Section rest.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** This is Hello's read-only promise without the shares of its option
    string and its table. *)
Definition hello_ro_rest (ge : genv) (o : hello_objs) : iProp Σ :=
  vtables_ro ge (ho_vb o) (ho_vreg o) ∗ single_ro ge (ho_sb o) (ho_sreg o) ∗
  liveq DfracDiscarded (ho_so o) (ho_soreg o) ∗ pcellq DfracDiscarded (ho_so o) 0 (ho_out o) ∗
  liveq DfracDiscarded (ho_se o) (ho_sereg o) ∗ pcellq DfracDiscarded (ho_se o) 0 (ho_err o) ∗
  liveq DfracDiscarded (ho_eb o) (ho_ereg o) ∗
  HelloGlibcDebts.AL.tcache_idle DfracDiscarded (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o) ∗
  word_string DfracDiscarded (ho_lp o) libs_bytes ∗ word_string DfracDiscarded (ho_tp o) lt_bytes ∗
  [∗ list] s ∈ hello_lits_rest, str_ro (sym_ptr ge s).

(** The two missing shares complete Hello's read-only promise. *)
Lemma hello_ro_join ge o :
  hello_ro_rest ge o ∗ str_ro (sym_ptr ge "hello#str.69") ∗ str_ro (sym_ptr ge "hello#parse_options.longopts.64") ⊢
  hello_ro ge o.
Proof.
  rewrite /hello_ro_rest /hello_ro.
  iIntros "((#A & #B & #C & #D & #E & #F & #G & #H & #I & #J & #L) & #S & #T)".
  iSplitR; [iExact "A"|]. iSplitR; [iExact "B"|]. iSplitR; [iExact "C"|]. iSplitR; [iExact "D"|].
  iSplitR; [iExact "E"|]. iSplitR; [iExact "F"|]. iSplitR; [iExact "G"|]. iSplitR; [iExact "H"|].
  iSplitR; [iExact "I"|]. iSplitR; [iExact "J"|].
  iEval (rewrite -(take_drop 10 hello_lits_rest)) in "L". iEval (rewrite big_sepL_app) in "L".
  iDestruct "L" as "[L1 L2]".
  change hello_lits with (take 10 hello_lits_rest ++ ["hello#str.69"%string; "hello#parse_options.longopts.64"%string] ++
    drop 10 hello_lits_rest)%list.
  rewrite !big_sepL_app. iFrame "L1 L2". cbn. iFrame "S T".
Qed.

End rest.

(** Hello runs safely when each call to getopt_long keeps the loop's
    promise, and Hello's table and glibc's objects start as loaded. *)
Lemma hello_getopt_table_core Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo bdd rdd b7 r7 b0 r0
    tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  0 < gb -> gb mod 8 = 0 -> gb + 56 <= r_end greg -> r_end greg <= 2 ^ 48 ->
  0 < bdd -> bdd mod 8 = 0 -> bdd + 8 <= r_end rdd -> r_end rdd <= 2 ^ 48 ->
  0 < b7 -> b7 mod 8 = 0 -> b7 + 8 <= r_end r7 -> r_end r7 <= 2 ^ 48 ->
  0 < b0 -> b0 mod 8 = 0 -> b0 + 8 <= r_end r0 -> r_end r0 <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#parse_options.longopts.64") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  0 < tb -> tb mod 8 = 0 -> tb + 136 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#str.69") (ge_globals ge) = Some (mkPtr b5 (Ro b5)) ->
  0 < b1 -> b1 mod 8 = 0 -> b1 + 16 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 16 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  0 < b4 -> b4 mod 8 = 0 -> b4 + 8 <= r_end r4 -> r_end r4 <= 2 ^ 48 ->
  0 < b5 -> b5 mod 8 = 0 -> b5 + 8 <= r_end r5 -> r_end r5 <= 2 ^ 48 ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m -> agrees m (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++ getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  os_wi w0 m w (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++ getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) -> NoDup (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++ getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0).*1 -> map_disjoint h1 (list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++ getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists debt : HelloCore w0 ge o,
    loop_getopt w0 ge o debt av ar (fun ps i => hello_getopt_state gb greg av ar ps i ∗
      hello_getopt_globals ge oe roe oo roo (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0))
        [45; 45] [45] [45; 87; 32] (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4)))%I /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ==∗
      hello_ro_rest ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgb0 Hgb8 Hgbe Hgbr Hd0 Hd8 Hde Hdr H70 H78 H7e H7r H00 H08 H0e H0r
    Htb Htb0 Htb8 Htbe Htbr H69 Hb10 Hb18 Hb1e Hb1r Hb20 Hb28 Hb2e Hb2r Hb30 Hb38 Hb3e Hb3r
    Hb40 Hb48 Hb4e Hb4r Hb50 Hb58 Hb5e Hb5r -> Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  set (tab := hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5) in *.
  set (st := getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0) in *.
  rewrite list_to_map_app map_union_assoc in Ha, Hw.
  rewrite list_to_map_app map_disjoint_union_r in Hdisj. destruct Hdisj as [Hd1 Hd2].
  rewrite fmap_app NoDup_app in Hnd. destruct Hnd as (Hn1 & Hn12 & Hn2).
  assert (Hd12 : map_disjoint (list_to_map tab : gmap piece pval) (list_to_map st)).
  { apply map_disjoint_list_to_map_l, Forall_forall. intros [k v] Hin.
    apply not_elem_of_list_to_map_1, Hn12, list_elem_of_fmap. exists (k, v). split; [reflexivity | exact Hin]. }
  assert (E69 : sym_ptr ge "hello#str.69" = mkPtr b5 (Ro b5)) by (rewrite /sym_ptr H69; reflexivity).
  assert (Etb : sym_ptr ge "hello#parse_options.longopts.64" = mkPtr tb (Ro tb)) by (rewrite /sym_ptr Htb; reflexivity).
  apply (hello_getopt_start_core Σ w0 ge o m s w (h1 ∪ list_to_map tab) _ av ar p0 ps x y z a i c fuel
    gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4)));
    try (assumption || reflexivity).
  - by apply map_disjoint_union_l_2.
  - intros HinvG HheapG.
    destruct (Hstart HinvG HheapG) as (debt & Hix & Hpre).
    exists debt. split; [exact Hix|].
    rewrite big_sepM_union; [|exact Hd1].
    rewrite (big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v)); [|exact Hn1].
    iIntros "[H1 HT]". iAssert (pts tab) with "[HT]" as "HT"; [rewrite /pts; iExact "HT"|].
    rewrite /tab /hello_tab_ps. iDestruct (pts_app with "HT") as "[Ht HT]".
    iDestruct (pts_app with "HT") as "[L1 HT]". iDestruct (pts_app with "HT") as "[L2 HT]".
    iDestruct (pts_app with "HT") as "[L3 HT]". iDestruct (pts_app with "HT") as "[L4 L5]".
    iMod (Hpre with "H1") as "(#Hro & Hps & Hav & Hn & HX & Hio & Hpv & Hgo)".
    iMod (hello_table_own_ro with "Ht L1 L2 L3 L4 L5") as "(#Htab & #Hos & #Hts)"; try assumption.
    iModIntro. rewrite E69 Etb.
    iSplitR; [iApply hello_ro_join; rewrite E69 Etb; iSplitR; [iExact "Hro"|];
      iSplitR; [iExists s_optstring; iExact "Hos" | iExact "Hts"]|].
    iSplitL "Hps"; [iExact "Hps"|]. iSplitL "Hav"; [iExact "Hav"|]. iSplitL "Hn"; [iExact "Hn"|].
    iSplitL "HX"; [iExact "HX"|]. iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Hpv"; [iExact "Hpv"|].
    iSplitL "Hgo"; [iExact "Hgo"|]. iSplitR; [iExact "Htab" | iExact "Hos"].
Qed.

(** Every allowed execution of Hello with glibc's getopt_long avoids
    panics, stuck steps and contract failures when glibc's objects and
    Hello's option table start in their loader state beside the rest of
    the program. *)
Theorem hello_never_panics_getopt_table Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo bdd rdd b7 r7 b0 r0
    penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 :
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
  Term.lookup (TAtom "hello#parse_options.longopts.64") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  0 < tb -> tb mod 8 = 0 -> tb + 136 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#str.69") (ge_globals ge) = Some (mkPtr b5 (Ro b5)) ->
  0 < b1 -> b1 mod 8 = 0 -> b1 + 16 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 16 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  0 < b4 -> b4 mod 8 = 0 -> b4 + 8 <= r_end r4 -> r_end r4 <= 2 ^ 48 ->
  0 < b5 -> b5 mod 8 = 0 -> b5 + 8 <= r_end r5 -> r_end r5 <= 2 ^ 48 ->
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
  agrees m (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++ getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  os_wi w0 m w (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++ getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  NoDup (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++ getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0).*1 ->
  map_disjoint h1 (list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++ getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : HelloCore w0 ge o) (G M : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    getenv_rule w0 glibc_os_registry ge G /\ getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\ getopt_cutoff_rule w0 glibc_os_registry ge /\
    getopt_malloc_rule w0 glibc_os_registry ge M /\ getopt_memset_rule w0 glibc_os_registry ge /\
    getopt_free_rule w0 glibc_os_registry ge /\
    (hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ⊢ (G ∗ M) ∗ (G ∗ M -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o debt)) /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ==∗
      hello_ro_rest ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hgb Hgb0 Hgb8 Hgbe Hgbr Hoe Hoe0 Hoee Hoer
    Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0 H146 Hd0 Hd8 Hde Hdr H147 H70 H78 H7e H7r H150 H00 H08 H0e H0r
    Htb Htb0 Htb8 Htbe Htbr H69 Hb10 Hb18 Hb1e Hb1r Hb20 Hb28 Hb2e Hb2r Hb30 Hb38 Hb3e Hb3r
    Hb40 Hb48 Hb4e Hb4r Hb50 Hb58 Hb5e Hb5r
    H145 H148 H149 H138 H139 H140 H141 H142 H143 H144 Hargc Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  apply (hello_getopt_table_core Σ w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo
    bdd rdd b7 r7 b0 r0 tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5); try assumption.
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & G & M & T & Hge & Hdg & Hld & Hcu & Hma & Hms & Hfr & Hgm & Hpre).
  exists debt. split; [|exact Hpre].
  exact (hello_getopt_ix_own w0 ge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp (hk_gi_strlen _ _ Hk)
    gb greg Hgb Hgb0 Hgb8 Hgbe Hgbr oe roe oo roo Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0)) penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom
    [45; 45] [45] [45; 87; 32] H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    G M T Hge Hdg Hld Hcu Hma Hms Hfr (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4)) Hgm av ar).
Qed.
