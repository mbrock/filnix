From Glibc Require Import GlibcProgram.
(** Hello calls getopt_long once per option, and glibc remembers its
    place between calls in a private object. The safety theorem in
    HelloGlibcJoinIx.v lets each call borrow that object while it matches
    argv and optind. This file proves that contract from the proof of
    glibc's own getopt_long, so the theorem no longer has to assume it. The proof only moves resources: it lends the
    call what the parser rule in GetoptLongStr.v asks for and gives the
    caller back what the rule returns.

    The call also writes opterr and optopt, prints through stderr and
    reads Hello's option table, but Hello's loop does not hold those.
    The callees keep them in their private state, so this file asks that
    the streams and that state lend them to the call and take them back.
    The streams are part of the loan because a warning printed to stderr
    uses the stream that Hello owns.

    This file does not decide where the linker puts glibc's objects.
    It takes each address as a parameter, along with the fact that the
    linked program finds the symbol there. It also takes the rules for
    getenv, the warning printers, the alloca cutoff, malloc, memset and
    free as premises. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv StrchrCode StrcmpCode StrncmpCode StrlenLogic
  GetoptModule GetoptState GetoptInitialize GetoptDiag GetoptLongExact GetoptLongStore GetoptLongDiag
  GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSite GetoptWrapParse GetoptLongStr
  AtexitLogic HelloGlibcLibsT HelloGetoptTable GetoptInitial HelloGetoptState HelloGlibcDebts HelloGlibcMainLoop HelloGlibcJoinIx.
From Glibc Require FileInv GetoptLongStr GetoptLongStore HelloGlibcDebts HelloGetoptState HelloGlibcJoin
  HelloGlibcJoinIx.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L HelloGlibcDebts.

Section call.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloCore w0 ge o) (Hy : hello_layout ge o).

(** ## The linked program

    The parser rule names the functions it calls and the globals it
    reads, so the linked program must define them. These facts describe
    the linked program, not the standalone images of Hello or glibc.
    Each object the rule writes also needs its bounds. *)

(** The program defines getopt_long and the functions that it calls. *)
Context (Hgl : find_fn ge (TAtom "getopt_long") = Some (Defined glibc_getopt_long))
  (Hgi : find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal))
  (Hgr : find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r))
  (Hplo : find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option))
  (Hcmp : find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp))
  (Hchr : find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr))
  (Hchrn : find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul))
  (Hncmp : find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp))
  (Hlen : find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen)).

(** The parser keeps its progress in the object gb with region greg. *)
Context (gb : Z) (greg : region)
  (Hgb : Term.lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr gb (Obj gb)))
  (Hgb0 : 0 < gb) (Hgb8 : gb mod 8 = 0) (Hgbe : gb + 56 <= r_end greg) (Hgbr : r_end greg <= 2 ^ 48).

(** The globals opterr and optopt are integer objects. *)
Context (oe : Z) (roe : region) (oo : Z) (roo : region)
  (Hoe : Term.lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)))
  (Hoe0 : 0 < oe) (Hoee : oe + 4 <= r_end roe) (Hoer : r_end roe <= 2 ^ 48)
  (Hoo : Term.lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)))
  (Hoo0 : 0 < oo) (Hooe : oo + 4 <= r_end roo) (Hoor : r_end roo <= 2 ^ 48).

(** Hello's layout bounds optarg, optind and stderr from below by zero.
    The parser rule needs them strictly above zero. *)
Context (Hoa0 : 0 < ho_oa o) (Hoi0 : 0 < ho_oi o) (Hse0 : 0 < ho_se o).

(** These are glibc's own strings: the separator "--", the prefixes "-"
    and "-W ", the getenv key and the diagnostic formats. *)
Context (pdd pfx7 pfx0 penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom : ptr) (sdd pxs7 pxs0 : list Z)
  (H146 : Term.lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd)
  (H147 : Term.lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx7)
  (H150 : Term.lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx0)
  (H145 : Term.lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv)
  (H148 : Term.lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid')
  (H149 : Term.lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid)
  (H138 : Term.lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138)
  (H139 : Term.lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139)
  (H140 : Term.lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140)
  (H141 : Term.lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141)
  (H142 : Term.lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid)
  (H143 : Term.lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3)
  (H144 : Term.lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4).

(** ## The rules that remain premises

    The parser reads the environment and prints warnings. It may also
    allocate a small buffer and free it again. Other milestones prove
    those functions, so this file assumes each of their rules. *)

(** G serves getenv and the diagnostics, and M serves malloc. *)
Context (G M : iProp Σ) (T : ptr -> ptr -> iProp Σ)
  (Hgetenv : getenv_rule w0 glibc_os_registry ge G)
  (Hdiag : getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom)
  (Hldiag : getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom)
  (Hcut : getopt_cutoff_rule w0 glibc_os_registry ge)
  (Hmalloc : getopt_malloc_rule w0 glibc_os_registry ge M)
  (Hmemset : getopt_memset_rule w0 glibc_os_registry ge)
  (Hfree : getopt_free_rule w0 glibc_os_registry ge).

(** ## The resources that the call borrows

    Each call needs a few things that only the callees hold. It writes
    opterr and optopt, and it reads Hello's option string, its table of
    four long options and glibc's own strings. The definition below
    gathers them, and the split after it says where they come from. *)

(** The option names lie at these pointers. *)
Context (n1 n2 n3 n4 : ptr).

(** The call borrows opterr and optopt at any values, the backends'
    resources, and shares of the strings and the table. *)
Definition hello_getopt_priv : iProp Σ :=
  ∃ err c0, live oe roe ∗ int_cell oe 0 err ∗ live oo roo ∗ int_cell oo 0 c0 ∗ G ∗ M ∗
    word_string DfracDiscarded (sym_ptr ge "hello#str.69") s_optstring ∗
    opt_table (sym_ptr ge "hello#parse_options.longopts.64") (hello_los n1 n2 n3 n4) ∗
    word_string DfracDiscarded pdd sdd ∗ word_string DfracDiscarded pfx7 pxs7 ∗
    word_string DfracDiscarded pfx0 pxs0.

(** The streams and the private state lend these resources and take
    them back after the call. *)
Context (Hsplit : hello_stdio w0 ge o ∗ hd_priv w0 ge o D ⊢
  hello_getopt_priv ∗ (hello_getopt_priv -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o D)).

(** ## The contract

    Each call starts with optind and the parser's object in a matching
    state. The wrapper copies optind into the object, and the parser
    runs. It leaves a session at the new optind, which is again a
    matching state, and a return of 103 leaves a string at optarg. *)

(** This is the contract of one call. The call starts from a state that
    matches argv and optind. It gives back the resources it borrowed,
    together with a new matching state. While the parser searches for a
    long option, the alloca cutoff borrows G and returns it. *)
Lemma hello_getopt_lend_with av ar ps a i :
  getopt_cutoff_rule_with w0 glibc_os_registry ge G ->
  fn_triple w0 ge (TAtom "getopt_long")
    [WInt (Z.of_nat (length ps)); WPtr (mkPtr av (Obj av)); WPtr (sym_ptr ge "hello#str.69");
     WPtr (sym_ptr ge "hello#parse_options.longopts.64"); WPtr null]
    (hello_ro ge o ∗ hello_getopt_priv ∗ argv_own av ar ps ∗ ([∗ list] q ∈ ps, str_ro q) ∗
     getopt_cells o a i ∗ hello_getopt_state gb greg av ar ps i)%I
    (fun r => ∃ code ps' a' i', ⌜r = Ret (WInt code) /\ 0 <= code < 2 ^ 32 /\ Permutation ps ps' /\
                                 0 <= i' <= Z.of_nat (length ps)⌝ ∗
                hello_getopt_priv ∗ argv_own av ar ps' ∗ getopt_cells o a' i' ∗
                hello_getopt_state gb greg av ar ps' i' ∗ (if code =? 103 then str_ro a' else True))%I.
Proof.
  intros Hcw.
  exists glibc_getopt_long. split; [exact Hgl|].
  split; [eexists; apply getopt_long_call_frame|]. intros fr Φ Hfr.
  destruct (hello_los_facts n1 n2 n3 n4 []) as (Hfl & Hlos & Hneg & Hcode).
  pose proof (hy_oa _ _ Hy) as Hoa. pose proof (hy_oa_at _ _ Hy) as (_ & Hoa8 & Hoae & Hoar).
  pose proof (hy_oi _ _ Hy) as Hoi. pose proof (hy_oi_at _ _ Hy) as (_ & Hoie & Hoir).
  pose proof (hy_se _ _ Hy) as Hse. pose proof (hy_se_at _ _ Hy) as (_ & Hse8 & Hsee & Hser).
  iIntros "(#Hro & Hp & (%Hav & Havl & Hcl) & #Hps & (Hoal & Hoac & Hoil & Hoic) & HS) HQ".
  destruct Hav as (Hav0 & Hav8 & Hn & Hfit & Har).
  iDestruct "Hp" as (err c0) "(Hoel & Hoec & Hool & Hooc & HG & HM & #Hos & #Ht & #Hdd & #H7 & #H0)".
  iPoseProof "Hro" as "(_ & _ & _ & _ & #Hsel & #Hsec & _)".
  iPoseProof (hello_getopt_state_copy_in (glibc_program := program_of w0 glibc_os_registry ge)
    gb greg av ar ps i err with "HS") as "Hci".
  iEval (rewrite /HelloGlibcDebts.str_ro) in "Hps".
  iApply (wp_getopt_long_str_call_with (glibc_program := program_of w0 glibc_os_registry ge) fr av ar
    (sym_ptr ge "hello#str.69") s_optstring (sym_ptr ge "hello#parse_options.longopts.64") null gb greg ps i err
    (ho_oi o) (ho_oireg o) oe roe (ho_oa o) (ho_oareg o) oo roo a c0 G T (ho_err o) dom (ho_se o) (ho_sereg o)
    mid mid' pdd sdd M f138 f139 f140 f141 lmid mid3 mid4 (hello_los n1 n2 n3 n4) [] pfx7 pxs7 pfx0 pxs0 penv 103 Φ
    with "Hci Hoil Hoic Hoel Hoec Hoal Hoac Hool Hooc Hos HG Hsel Hsec Havl Hcl Hps Hdd Ht H7 H0 [] HM [] [HQ]");
    try (assumption || reflexivity || lia).
  - rewrite /GetoptLongStore.flags_own. iSplit; [iPureIntro; apply NoDup_nil_2 | done].
  - rewrite /GetoptLongStore.longind_own. iLeft. done.
  - iIntros (x i' c' a' ps' [Hp Hx]) "Hw Hoil Hoic Hoel Hoec Hoal Hoac Hool Hooc Havl Hcl _ HG _ HM _ _ Hstr".
    iDestruct (getopt_session_index with "Hw") as "[%Hi' Hw]".
    pose proof (Permutation_length Hp) as Hl.
    iAssert hello_getopt_priv with "[Hoel Hoec Hool Hooc HG HM]" as "Hp".
    { iExists err, c'. iFrame "Hoel Hoec Hool Hooc HG HM Hos Ht Hdd H7 H0". }
    iApply "HQ". iExists x, ps', a', i'.
    iSplit; [iPureIntro; split_and!; [reflexivity | lia | lia | exact Hp | lia | rewrite Hl; lia]|].
    iFrame "Hp". iSplitL "Havl Hcl".
    { iSplit; [iPureIntro; rewrite -Hl; split_and!; assumption | iFrame "Havl Hcl"]. }
    iSplitL "Hoal Hoac Hoil Hoic"; [iFrame "Hoal Hoac Hoil Hoic"|].
    iSplitL "Hw"; [iApply (hello_getopt_state_session with "Hw")|].
    iEval (rewrite /GetoptLongStr.arg_str) in "Hstr". destruct (x =? 103); [|done].
    rewrite /HelloGlibcDebts.str_ro. iDestruct "Hstr" as (s) "Hs". iExists s. iExact "Hs".
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma hello_getopt_lend av ar ps a i :
  fn_triple w0 ge (TAtom "getopt_long")
    [WInt (Z.of_nat (length ps)); WPtr (mkPtr av (Obj av)); WPtr (sym_ptr ge "hello#str.69");
     WPtr (sym_ptr ge "hello#parse_options.longopts.64"); WPtr null]
    (hello_ro ge o ∗ hello_getopt_priv ∗ argv_own av ar ps ∗ ([∗ list] q ∈ ps, str_ro q) ∗
     getopt_cells o a i ∗ hello_getopt_state gb greg av ar ps i)%I
    (fun r => ∃ code ps' a' i', ⌜r = Ret (WInt code) /\ 0 <= code < 2 ^ 32 /\ Permutation ps ps' /\
                                 0 <= i' <= Z.of_nat (length ps)⌝ ∗
                hello_getopt_priv ∗ argv_own av ar ps' ∗ getopt_cells o a' i' ∗
                hello_getopt_state gb greg av ar ps' i' ∗ (if code =? 103 then str_ro a' else True))%I.
Proof. exact (hello_getopt_lend_with av ar ps a i (getopt_cutoff_rule_with_any w0 glibc_os_registry ge G Hcut)). Qed.

(** glibc's getopt_long meets the loop's contract with the admissible
    states of the parser's object. *)
Lemma hello_getopt_ix av ar : loop_getopt w0 ge o D av ar (hello_getopt_state gb greg av ar).
Proof.
  intros ps a i. destruct (hello_getopt_lend av ar ps a i) as (gf & Hg & Hfr & Ht).
  exists gf. split; [exact Hg|]. split; [exact Hfr|]. intros fr Φ Hf.
  iIntros "(#Hro & Hio & Hpv & Hav & #Hps & Hc & HS) HQ".
  iDestruct (Hsplit with "[Hio Hpv]") as "[Hp Hback]"; [iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]|].
  iApply (Ht fr Φ Hf with "[Hp Hav Hc HS]").
  { iSplitR; [iExact "Hro"|]. iSplitL "Hp"; [iExact "Hp"|]. iSplitL "Hav"; [iExact "Hav"|].
    iSplitR; [iExact "Hps"|]. iSplitL "Hc"; [iExact "Hc" | iExact "HS"]. }
  iIntros (r) "(%x & %ps' & %a' & %i' & %Hx & Hp & Hav & Hc & HS & Hstr)".
  iDestruct ("Hback" with "Hp") as "[Hio Hpv]".
  iApply "HQ". iExists x, ps', a', i'. iSplit; [iPureIntro; exact Hx|].
  iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Hpv"; [iExact "Hpv"|]. iSplitL "Hav"; [iExact "Hav"|].
  iSplitL "Hc"; [iExact "Hc"|]. iSplitL "HS"; [iExact "HS" | iExact "Hstr"].
Qed.

(** This record packs the other contracts with the proved call. *)
Definition hello_debts_ix : HelloDebtsIx w0 ge o := mkHelloDebtsIx w0 ge o D gb greg hello_getopt_ix.

(** ## The parser's own resources

    Hello's other calls never touch opterr, optopt, the option table or
    getopt's strings; only getopt_long uses them. So the loop can keep
    them next to the parser's private object. Then the streams and the
    private state need to lend each call only what getenv, the warning
    printers and malloc use. *)

(** These are the resources that only the parser uses: opterr and optopt
    at any values, and shares of the strings and the table. *)
Definition hello_getopt_globals : iProp Σ :=
  ∃ err c0, live oe roe ∗ int_cell oe 0 err ∗ live oo roo ∗ int_cell oo 0 c0 ∗
    word_string DfracDiscarded (sym_ptr ge "hello#str.69") s_optstring ∗
    opt_table (sym_ptr ge "hello#parse_options.longopts.64") (hello_los n1 n2 n3 n4) ∗
    word_string DfracDiscarded pdd sdd ∗ word_string DfracDiscarded pfx7 pxs7 ∗
    word_string DfracDiscarded pfx0 pxs0.

(** What a call borrows splits into the parser's own objects and what the backends use. *)
Lemma hello_getopt_priv_split : hello_getopt_priv ⊣⊢ hello_getopt_globals ∗ G ∗ M.
Proof.
  iSplit.
  - iIntros "(%err & %c0 & Hel & Hec & Hol & Hoc & HG & HM & #H69 & #Ht & #Hdd & #H7 & #H0)".
    iSplitR "HG HM"; [|iSplitL "HG"; [iExact "HG" | iExact "HM"]].
    iExists err, c0. iSplitL "Hel"; [iExact "Hel"|]. iSplitL "Hec"; [iExact "Hec"|].
    iSplitL "Hol"; [iExact "Hol"|]. iSplitL "Hoc"; [iExact "Hoc"|]. iSplitR; [iExact "H69"|].
    iSplitR; [iExact "Ht"|]. iSplitR; [iExact "Hdd"|]. iSplitR; [iExact "H7" | iExact "H0"].
  - iIntros "((%err & %c0 & Hel & Hec & Hol & Hoc & #H69 & #Ht & #Hdd & #H7 & #H0) & HG & HM)".
    iExists err, c0. iSplitL "Hel"; [iExact "Hel"|]. iSplitL "Hec"; [iExact "Hec"|].
    iSplitL "Hol"; [iExact "Hol"|]. iSplitL "Hoc"; [iExact "Hoc"|]. iSplitL "HG"; [iExact "HG"|].
    iSplitL "HM"; [iExact "HM"|]. iSplitR; [iExact "H69"|].
    iSplitR; [iExact "Ht"|]. iSplitR; [iExact "Hdd"|]. iSplitR; [iExact "H7" | iExact "H0"].
Qed.

(** The streams and the private state still lend what the backends use. *)
Context (Hgm : hello_stdio w0 ge o ∗ hd_priv w0 ge o D ⊢ (G ∗ M) ∗ (G ∗ M -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o D)).

(** glibc's getopt_long meets the loop's contract when the loop carries
    the parser's own resources beside its object. *)
Lemma hello_getopt_ix_own av ar :
  loop_getopt w0 ge o D av ar (fun ps i => hello_getopt_state gb greg av ar ps i ∗ hello_getopt_globals)%I.
Proof.
  intros ps a i. destruct (hello_getopt_lend av ar ps a i) as (gf & Hg & Hfr & Ht).
  exists gf. split; [exact Hg|]. split; [exact Hfr|]. intros fr Φ Hf.
  iIntros "(#Hro & Hio & Hpv & Hav & #Hps & Hc & HS & Hgo) HQ".
  iDestruct (Hgm with "[Hio Hpv]") as "[Hb Hback]"; [iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]|].
  iApply (Ht fr Φ Hf with "[Hgo Hb Hav Hc HS]").
  { iSplitR; [iExact "Hro"|]. iSplitL "Hgo Hb".
    { iApply hello_getopt_priv_split. iSplitL "Hgo"; [iExact "Hgo" | iExact "Hb"]. }
    iSplitL "Hav"; [iExact "Hav"|]. iSplitR; [iExact "Hps"|]. iSplitL "Hc"; [iExact "Hc" | iExact "HS"]. }
  iIntros (r) "(%x & %ps' & %a' & %i' & %Hx & Hp & Hav & Hc & HS & Hstr)".
  iDestruct (hello_getopt_priv_split with "Hp") as "(Hgo & Hb)".
  iDestruct ("Hback" with "Hb") as "[Hio Hpv]".
  iApply "HQ". iExists x, ps', a', i'. iSplit; [iPureIntro; exact Hx|].
  iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Hpv"; [iExact "Hpv"|]. iSplitL "Hav"; [iExact "Hav"|].
  iSplitL "Hc"; [iExact "Hc"|]. iSplitL "HS Hgo"; [iSplitL "HS"; [iExact "HS" | iExact "Hgo"] | iExact "Hstr"].
Qed.

(** Hello already shares the memory that malloc reads, so nobody needs
    to lend it. Only getenv and the warning printers still borrow from the
    streams and the private state. *)
Context (Hro_m : hello_ro ge o ⊢ M)
  (Hg : hello_stdio w0 ge o ∗ hd_priv w0 ge o D ⊢ G ∗ (G -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o D)).

(** With that, each call to glibc's getopt_long does what the loop
    expects of it, also when the cutoff borrows G. *)
Lemma hello_getopt_ix_ro_with av ar :
  getopt_cutoff_rule_with w0 glibc_os_registry ge G ->
  loop_getopt w0 ge o D av ar (fun ps i => hello_getopt_state gb greg av ar ps i ∗ hello_getopt_globals)%I.
Proof.
  intros Hcw.
  intros ps a i. destruct (hello_getopt_lend_with av ar ps a i Hcw) as (gf & Hgf & Hfr & Ht).
  exists gf. split; [exact Hgf|]. split; [exact Hfr|]. intros fr Φ Hf.
  iIntros "(#Hro & Hio & Hpv & Hav & #Hps & Hc & HS & Hgo) HQ".
  iDestruct (Hg with "[Hio Hpv]") as "[HG Hback]"; [iSplitL "Hio"; [iExact "Hio" | iExact "Hpv"]|].
  iDestruct (Hro_m with "Hro") as "HM".
  iApply (Ht fr Φ Hf with "[Hgo HG HM Hav Hc HS]").
  { iSplitR; [iExact "Hro"|]. iSplitL "Hgo HG HM".
    { iApply hello_getopt_priv_split. iSplitL "Hgo"; [iExact "Hgo"|]. iSplitL "HG"; [iExact "HG" | iExact "HM"]. }
    iSplitL "Hav"; [iExact "Hav"|]. iSplitR; [iExact "Hps"|]. iSplitL "Hc"; [iExact "Hc" | iExact "HS"]. }
  iIntros (r) "(%x & %ps' & %a' & %i' & %Hx & Hp & Hav & Hc & HS & Hstr)".
  iDestruct (hello_getopt_priv_split with "Hp") as "(Hgo & HG & _)".
  iDestruct ("Hback" with "HG") as "[Hio Hpv]".
  iApply "HQ". iExists x, ps', a', i'. iSplit; [iPureIntro; exact Hx|].
  iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Hpv"; [iExact "Hpv"|]. iSplitL "Hav"; [iExact "Hav"|].
  iSplitL "Hc"; [iExact "Hc"|]. iSplitL "HS Hgo"; [iSplitL "HS"; [iExact "HS" | iExact "Hgo"] | iExact "Hstr"].
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma hello_getopt_ix_ro av ar :
  loop_getopt w0 ge o D av ar (fun ps i => hello_getopt_state gb greg av ar ps i ∗ hello_getopt_globals)%I.
Proof. exact (hello_getopt_ix_ro_with av ar (getopt_cutoff_rule_with_any w0 glibc_os_registry ge G Hcut)). Qed.

End call.

(** ## Hello with glibc's getopt_long

    A reader of Hello's safety theorem wants to know that the option
    parser is glibc's real code, not a promise about it. The theorem
    below gives that answer. When Hello calls getopt_long, the program
    runs glibc's parser, whose proof is above. What remains for the
    caller is the rest of the C library, the places of glibc's data, and
    the parser's object at the start, matching argv and optind. Facts
    about memory are stated for every [[ghost-state]] that the proof may
    create, because the proof creates it only when it starts. *)

(** Every allowed execution of Hello with glibc's getopt_long avoids
    panics, stuck steps and contract failures. *)
Theorem hello_never_panics_getopt Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h0 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo
    pdd pfx7 pfx0 penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom sdd pxs7 pxs0 n1 n2 n3 n4 :
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
  Term.lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  Term.lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx7 ->
  Term.lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx0 ->
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
  R.ready s m -> live_disjoint m -> agrees m h0 -> os_wi w0 m w h0 ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : HelloCore w0 ge o) (G M : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    getenv_rule w0 glibc_os_registry ge G /\ getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\ getopt_cutoff_rule w0 glibc_os_registry ge /\
    getopt_malloc_rule w0 glibc_os_registry ge M /\ getopt_memset_rule w0 glibc_os_registry ge /\
    getopt_free_rule w0 glibc_os_registry ge /\
    (hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ⊢
      hello_getopt_priv ge oe roe oo roo pdd pfx7 pfx0 sdd pxs7 pxs0 G M n1 n2 n3 n4 ∗
      (hello_getopt_priv ge oe roe oo roo pdd pfx7 pfx0 sdd pxs7 pxs0 G M n1 n2 n3 n4 -∗
         hello_stdio w0 ge o ∗ hd_priv w0 ge o debt)) /\
    (([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
      hello_ro ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i ∗
      hello_getopt_state gb greg av ar (p0 :: ps) i)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hgb Hgb0 Hgb8 Hgbe Hgbr Hoe Hoe0 Hoee Hoer
    Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0 H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    Hargc Hi Hr Hd Ha Hw Hstart.
  apply (hello_never_panics_ix Σ w0 ge o m s w h0 argc av ar p0 ps x y z a i c fuel Hk Hy Hos Hargc Hi Hr Hd Ha Hw).
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & G & M & T & Hge & Hdg & Hld & Hcu & Hma & Hms & Hfr & Hsp & Hpre).
  exists (hello_debts_ix w0 ge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp (hk_gi_strlen _ _ Hk)
    gb greg Hgb Hgb0 Hgb8 Hgbe Hgbr oe roe oo roo Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    pdd pfx7 pfx0 penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom sdd pxs7 pxs0
    H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    G M T Hge Hdg Hld Hcu Hma Hms Hfr n1 n2 n3 n4 Hsp).
  exact Hpre.
Qed.

(** ## Starting from the zeroed object

    Someone checking Hello's safety should not have to supply glibc's
    private parser state by hand. When Hello starts, it has not asked
    for an option yet, and the parser's memory still holds zeroes. The
    result below reads that zeroed memory out of the program's starting
    memory. The rest of the starting memory must provide everything else
    that the previous result needs, and Hello may still begin at any
    index from zero to argc. *)

(** Hello with glibc's getopt_long stays safe when the starting heap
    holds the parser's zeroed object beside the rest of the program. *)
Theorem hello_never_panics_getopt_zero Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo
    pdd pfx7 pfx0 penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom sdd pxs7 pxs0 n1 n2 n3 n4 :
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
  Term.lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  Term.lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx7 ->
  Term.lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx0 ->
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
  R.ready s m -> live_disjoint m -> agrees m (h1 ∪ list_to_map (getopt_zero_ps gb greg)) ->
  os_wi w0 m w (h1 ∪ list_to_map (getopt_zero_ps gb greg)) -> map_disjoint h1 (list_to_map (getopt_zero_ps gb greg)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : HelloCore w0 ge o) (G M : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    getenv_rule w0 glibc_os_registry ge G /\ getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\ getopt_cutoff_rule w0 glibc_os_registry ge /\
    getopt_malloc_rule w0 glibc_os_registry ge M /\ getopt_memset_rule w0 glibc_os_registry ge /\
    getopt_free_rule w0 glibc_os_registry ge /\
    (hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ⊢
      hello_getopt_priv ge oe roe oo roo pdd pfx7 pfx0 sdd pxs7 pxs0 G M n1 n2 n3 n4 ∗
      (hello_getopt_priv ge oe roe oo roo pdd pfx7 pfx0 sdd pxs7 pxs0 G M n1 n2 n3 n4 -∗
         hello_stdio w0 ge o ∗ hd_priv w0 ge o debt)) /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ⊢
      hello_ro ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hgb Hgb0 Hgb8 Hgbe Hgbr Hoe Hoe0 Hoee Hoer
    Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0 H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    Hargc Hi Hr Hd Ha Hw Hdisj Hstart.
  apply (hello_never_panics_getopt Σ w0 ge o m s w (h1 ∪ list_to_map (getopt_zero_ps gb greg)) argc av ar
    p0 ps x y z a i c fuel gb greg oe roe oo roo pdd pfx7 pfx0 penv mid mid' f138 f139 f140 f141 lmid mid3 mid4
    dom sdd pxs7 pxs0 n1 n2 n3 n4); try assumption.
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & G & M & T & Hge & Hdg & Hld & Hcu & Hma & Hms & Hfr & Hsp & Hpre).
  exists debt, G, M, T. split_and!; try assumption.
  rewrite big_sepM_union; [|exact Hdisj].
  rewrite (big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v)); [|apply getopt_zero_ps_distinct].
  iIntros "[H1 Hz]".
  iAssert (pts (getopt_zero_ps gb greg)) with "[Hz]" as "Hz"; [rewrite /pts; iExact "Hz"|].
  iDestruct (Hpre with "H1") as "(Hro & Hs & (%Hav & Havl & Hcl) & Hn & Hx & Hio & Hpv & Hc)".
  destruct Hav as (Hav0 & Hav8 & Hn & Hfit & Har).
  iFrame "Hro Hs Hn Hx Hio Hpv Hc".
  iSplitL "Havl Hcl"; [iSplit; [iPureIntro; split_and!; assumption | iFrame "Havl Hcl"]|].
  iApply (hello_getopt_state_pieces with "Hz"); try assumption; cbn [length] in *; lia.
Qed.
