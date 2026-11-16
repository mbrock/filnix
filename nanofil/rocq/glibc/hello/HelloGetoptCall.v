From Glibc Require Import GlibcProgram.
(** Hello calls getopt_long once per option, and glibc remembers its
    place between calls in a private object. Hello's main loop lets each
    call borrow that object while it matches argv and optind. This file
    proves that contract from the proof of glibc's own getopt_long, so
    Hello's safety theorem in HelloNeverPanics.v does not assume it. The
    proof only moves resources: it lends the call what the parser rule in
    GetoptLongStr.v asks for and gives the caller back what the rule
    returns.

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
    free as premises, which the safety theorem discharges except for the
    two warning printers. *)

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
  AtexitLogic HelloGlibcLibsT HelloGetoptTable GetoptInitial HelloGetoptState HelloGlibcDebts HelloGlibcMainLoop.
From Glibc Require FileInv GetoptLongStr GetoptLongStore HelloGlibcDebts HelloGetoptState.
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

    The parser prints warnings. It may also allocate a small buffer and
    free it again. Other files prove some of those functions, so this
    file assumes each of their rules. *)

(** G serves getenv, the cutoff and the diagnostics, and M serves malloc. *)
Context (G M : iProp Σ) (T : ptr -> ptr -> iProp Σ)
  (Hdiag : getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom)
  (Hldiag : getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom)
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

(** ## The contract

    Each call starts with optind and the parser's object in a matching
    state. The wrapper copies optind into the object, and the parser
    runs. It leaves a session at the new optind, which is again a
    matching state, and a return of 103 leaves a string at optarg. *)

(** This is the contract of one call. The call starts from a state that
    matches argv and optind. It gives back the resources it borrowed,
    together with a new matching state. While the parser searches for a
    long option, the alloca cutoff borrows G and returns it. *)
Lemma hello_getopt_lend_with_at av ar ps a i :
  GetenvCall.getenv_at_rule w0 glibc_os_registry ge G penv ->
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
  intros Hnamed Hcw.
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
  iApply (wp_getopt_long_str_call_with_at (glibc_program := program_of w0 glibc_os_registry ge) fr av ar
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

(** Hello already shares the memory that malloc reads, so nobody needs
    to lend it. *)
Context (Hro_m : hello_ro ge o ⊢ M).

(** The parser needs to read memory that Hello keeps between calls.
    Hello carries its read permissions in R beside the parser's object,
    and lends them with the streams and private state. Each call returns
    everything it borrows. This supports both the environment name and
    the stack-size cell read by the cutoff. *)
Lemma hello_getopt_ix_ro_sep_at (R : iProp Σ) av ar :
  GetenvCall.getenv_at_rule w0 glibc_os_registry ge G penv ->
  getopt_cutoff_rule_with w0 glibc_os_registry ge G ->
  (hello_stdio w0 ge o ∗ hd_priv w0 ge o D ∗ R ⊢ G ∗ (G -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o D ∗ R)) ->
  loop_getopt w0 ge o D av ar (fun ps i => hello_getopt_state gb greg av ar ps i ∗ hello_getopt_globals ∗ R)%I.
Proof.
  intros Hnamed Hcw HgR.
  intros ps a i. destruct (hello_getopt_lend_with_at av ar ps a i Hnamed Hcw) as (gf & Hgf & Hfr & Ht).
  exists gf. split; [exact Hgf|]. split; [exact Hfr|]. intros fr Φ Hf.
  iIntros "(#Hro & Hio & Hpv & Hav & #Hps & Hc & HS & Hgo & HR) HQ".
  iDestruct (HgR with "[$Hio $Hpv $HR]") as "[HG Hback]".
  iDestruct (Hro_m with "Hro") as "HM".
  iApply (Ht fr Φ Hf with "[Hgo HG HM Hav Hc HS]").
  { iSplitR; [iExact "Hro"|]. iSplitL "Hgo HG HM".
    { iApply hello_getopt_priv_split. iSplitL "Hgo"; [iExact "Hgo"|]. iSplitL "HG"; [iExact "HG" | iExact "HM"]. }
    iSplitL "Hav"; [iExact "Hav"|]. iSplitR; [iExact "Hps"|]. iSplitL "Hc"; [iExact "Hc" | iExact "HS"]. }
  iIntros (r) "(%x & %ps' & %a' & %i' & %Hx & Hp & Hav & Hc & HS & Hstr)".
  iDestruct (hello_getopt_priv_split with "Hp") as "(Hgo & HG & _)".
  iDestruct ("Hback" with "HG") as "(Hio & Hpv & HR)".
  iApply "HQ". iExists x, ps', a', i'. iSplit; [iPureIntro; exact Hx|].
  iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Hpv"; [iExact "Hpv"|]. iSplitL "Hav"; [iExact "Hav"|].
  iSplitL "Hc"; [iExact "Hc"|]. iSplitL "HS Hgo HR"; [iFrame "HS Hgo HR" | iExact "Hstr"].
Qed.

End call.
