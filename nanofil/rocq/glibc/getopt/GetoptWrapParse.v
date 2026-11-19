From Glibc Require Import Unit_string_strchr_os Unit_string_strchrnul_os Unit_string_strcmp_os Unit_string_strncmp_os.
From Glibc Require Import GlibcProgram.
(** A program calls getopt through the wrapper _getopt_internal. The
    wrapper copies optind and opterr into a private object and runs the
    parser on it. Then it copies the new index, argument and option back
    to optind, optarg and optopt. The wrapper's rule takes the parser as
    a premise. This file fills that premise with the proved parser call,
    so the program assumes nothing about the parser. *)

From Glibc Require Import GlibcTactics OsTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require OsWorld FileInv LibioLogic WordString StrchrnulLogic StrlenLogic StrlenWord StrncmpLogic GetoptModule GetoptState ByteRead GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptDiag GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongPfxCmp GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSite GetoptDashRet GetoptWExit GetoptCallParse GetoptWrapper GetoptEntryPre GetoptEntryScanRet GetoptShortCap GetoptCharRet.
Import OsWorld FileInv LibioLogic WordString StrchrnulLogic StrlenLogic StrlenWord StrncmpLogic GetoptModule GetoptState ByteRead GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptDiag GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongPfxCmp GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSite GetoptDashRet GetoptWExit GetoptCallParse GetoptWrapper GetoptEntryPre GetoptEntryScanRet GetoptEntryPre GetoptDiag GetoptShortCap GetoptEntry GetoptCharRet.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptLongSite GetoptShortCap GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic ByteRead GetoptArgv.

(** ## The answer is a 32-bit value

    The wrapper copies the parser's answer as a 32-bit value, so every
    return must say that it fits. The lemmas below read the bound from
    the facts each path already proves. *)

(** The scan returns -1 or 1. *)
Lemma scan_ret_x n i0 o ps' x i' a' : scan_ret_case n i0 o ps' x i' a' -> 0 <= x < 2 ^ 32.
Proof. intros [(-> & _) | [(-> & _) | (-> & _)]]; lia. Qed.

(** A short option returns '?', ':' or the widened option byte. *)
Lemma char_ret_x ps n i oo cur a t so x i' oo' a' c' :
  char_ret_case ps n i oo cur a t so x i' oo' a' c' -> 0 <= x < 2 ^ 32.
Proof.
  intros [(-> & _) | (k & _ & _ & _ & _ & H)]; [lia|].
  destruct H as [(_ & -> & _) | [(_ & _ & -> & _) | [(_ & _ & _ & -> & _) | [(_ & _ & _ & _ & -> & _) |
    (_ & _ & _ & _ & -> & _)]]]]; try apply chr_w_range. destruct (_ =? _); lia.
Qed.

(** The long-option parser states the bound itself. *)
Lemma plo_ret_x ps i n cur s a os x i' a' c' : plo_ret_case ps i n cur s a os x i' a' c' -> 0 <= x < 2 ^ 32.
Proof. intros (_ & _ & _ & Hx & _). exact Hx. Qed.

Import ProgramAbbreviations.
Section wrap_parse.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance wrapparse_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A shared view of the stream's liveness can be copied. *)
Local Instance wrapparse_liveq_persistent b0 reg : Persistent (liveq DfracDiscarded b0 reg).
Proof using Type. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance wrapparse_pcellq_persistent b0 o x : Persistent (pcellq DfracDiscarded b0 o x).
Proof using Type. unfold pcellq. apply _. Qed.
(** A shared view of the argument's object life can be copied. *)
Local Instance wrapparse_capq_persistent c reg : Persistent (live_capq DfracDiscarded c reg).
Proof using Type. destruct c; cbn; apply _. Qed.

(** ## What the wrapper receives from the parser

    The wrapper copies three private fields and needs proof that the
    argument is live. Everything else that the parser gives back must
    wait until the copy is done. The definitions below name that rest
    and the whole return in the form the wrapper's rule asks for. *)

(** The wrapper copies three fields and leaves the rest alone until it
    is done. The rest holds the cursor, the reordered words and what the
    caller lent. It also holds a wand that makes a session from the
    fields, and a copy of the proof that the argument is live. *)
Definition wrap_rest (b : Z) (r : region) (av : Z) (ar : region) (ps : list ptr) (G : iProp Σ) (F : list ptr)
    (M : iProp Σ) (li : ptr) (x i' c' : Z) (a' : ptr) : iProp Σ :=
  ∃ ps' cur, ⌜Permutation ps ps' /\ 0 <= x < 2 ^ 32⌝ ∗ pcell b 32 cur ∗
    (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 c' -∗ pcell b 16 a' -∗ pcell b 32 cur -∗
       getopt_session b r av ar ps' i') ∗
    live av ar ∗ argv_cells av ps' ∗ argv_strs ps' ∗ G ∗ flags_own F ∗ M ∗ longind_own li ∗ arg_cap a'.

(** This is the return that the wrapper's rule asks of the parser. *)
Definition wrap_post (b : Z) (r : region) (Ψ : Z -> Z -> Z -> ptr -> iProp Σ)
    (o : language.val (nanofil_lang registry ge)) : iProp Σ :=
  ∃ x i' c' a' ra, ⌜o = Ret (WInt x) /\ 0 <= x < 2 ^ 32 /\ 0 <= ptr_addr a' < 2 ^ 64⌝ ∗
    live b r ∗ int_cell b 0 i' ∗ int_cell b 8 c' ∗ pcell b 16 a' ∗ live_capq DfracDiscarded (ptr_cap a') ra ∗
    Ψ x i' c' a'.

(** Every path returns the same pieces, so one lemma packs them. *)
Lemma wrap_ret b r av ar ps ps' (G : iProp Σ) F (M : iProp Σ) li x i' oo' a' c' :
  0 <= x < 2 ^ 32 -> Permutation ps ps' ->
  live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
  (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     getopt_session b r av ar ps' i') -∗
  live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
  wrap_post b r (wrap_rest b r av ar ps G F M li) (Ret (WInt x)).
Proof using Type.
  intros Hx Hp. iIntros "Hl Hi Ho Hab Hcur Hw Ha Hcl #Hs HG HF HM Hli [[%ra #Hcap] %Hra]".
  iExists x, i', oo', a', ra. iSplit; [iPureIntro; split_and!; [reflexivity | lia | lia | lia | lia] |].
  iSplitL "Hl"; [done|]. iSplitL "Hi"; [done|]. iSplitL "Ho"; [done|]. iSplitL "Hab"; [done|].
  iSplitR; [iExact "Hcap"|]. iExists ps', c'. iSplit; [iPureIntro; split; [exact Hp | lia]|].
  iSplitL "Hcur"; [done|]. iSplitL "Hw"; [done|]. iSplitL "Ha"; [done|]. iSplitL "Hcl"; [done|].
  iSplitR; [done|]. iSplitL "HG"; [done|]. iSplitL "HF"; [done|]. iSplitL "HM"; [done|].
  iSplitL "Hli"; [done|]. iSplit; [by iExists ra | iPureIntro; lia].
Qed.

(** The three ends of the W option all fit the wrapper. *)
Lemma w_ret_exits_wrap b r av ar ps ps' los li F (G M : iProp Σ) i n c a so q sq k0 :
  Permutation ps ps' -> argv_strs ps' -∗
  w_ret_exits b r av ar ps' los li F G M i n c a so q sq k0 (wrap_post b r (wrap_rest b r av ar ps G F M li)).
Proof using Type.
  intros Hp. iIntros "#Hs". unfold w_ret_exits. iSplit; [|iSplit].
  - iIntros (x i' oo' a' c' (_ & Hc)) "Hl Hi Ho Hab Hcur Hw Ha Hcl HG HF HM Hli Hca".
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca"); [exact (plo_ret_x _ _ _ _ _ _ _ _ _ _ _ Hc) | exact Hp].
  - iIntros (s2 x i' oo' a' c' (_ & _ & Hc)) "_ Hl Hi Ho Hab Hcur Hw Ha Hcl HG HF HM Hli Hca".
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca"); [exact (plo_ret_x _ _ _ _ _ _ _ _ _ _ _ Hc) | exact Hp].
  - iIntros "_ Hl Hi Ho Hab Hcur Hw Ha Hcl HG HF HM Hli Hca".
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca"); [destruct (_ =? _); lia | exact Hp].
Qed.

(** ## How each return reaches the wrapper

    The call rule names nine kinds of return, and the wrapper needs the
    same few things from each. Every kind already holds the fields, the
    proof for the argument and the wand. So the lemma below only checks
    that the answer fits in 32 bits and that the words were reordered. *)

(** All nine returns of the call give the wrapper what it needs. A
    resumed call leaves the words in place, so the caller lends their
    strings. *)
Lemma call_parse_rets_wrap n av ar p os li lonly b r ps j (G : iProp Σ) se sereg fp los F (M : iProp Σ) :
  argv_strs ps -∗
  call_parse_rets n av ar p os li lonly b r ps j G se sereg fp los F M
    (wrap_post b r (wrap_rest b r av ar ps G F M li)).
Proof using Type.
  iIntros "#Hs0". unfold call_parse_rets.
  iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
  - iIntros (s s' ps' x i' a' (_ & _ & Hp & Hc)) "Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl Hs HG Hca HF HM Hli".
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca"); [exact (scan_ret_x _ _ _ _ _ _ _ Hc) | exact Hp].
  - iIntros (s s' w ps' i' f' l' x i'' oo' a' c' (Hf & _ & Hc)) "Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl Hs HG HF HM Hli Hca".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & _).
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca"); [exact (plo_ret_x _ _ _ _ _ _ _ _ _ _ _ Hc) | exact Hp].
  - iIntros (s s' w ps' i' f' l' x i'' oo' a' c' (Hf & _ & _ & _ & Hc))
      "Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl Hs HG HF HM Hli Hca".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & _).
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca"); [exact (plo_ret_x _ _ _ _ _ _ _ _ _ _ _ Hc) | exact Hp].
  - iIntros (s s' w ps' i' f' l' oo' a' x i'' oo'' a'' c'' (Hf & _ & _ & _ & Hc))
      "Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl Hs HG HF HM Hli Hca".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & _).
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca");
      [exact (char_ret_x _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) | exact Hp].
  - iIntros (s s' w ps' i' f' l' a' (Hf & _)) "_ #Hs".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & _). iApply (w_ret_exits_wrap with "Hs"). exact Hp.
  - iIntros (s s' w ps' i' f' l' x i'' oo' a' c' (Hf & Hc)) "Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl Hs HG Hca HF HM Hli".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & _).
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca");
      [exact (char_ret_x _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) | exact Hp].
  - iIntros (s s' w ps' i' f' l' Hf) "_ #Hs".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & _). iApply (w_ret_exits_wrap with "Hs"). exact Hp.
  - iIntros (s q sq k0 _). iApply (w_ret_exits_wrap with "Hs0"). reflexivity.
  - iIntros (s q sq k0 x i' oo' a' c' (_ & Hc)) "Hl Hi Ho Hab Hcur Hw Ha Hcl HG Hca HF HM Hli".
    iApply (wrap_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs0 HG HF HM Hli Hca");
      [exact (char_ret_x _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) | reflexivity].
Qed.

(** ## The copy into the private object

    Before the parser runs, the wrapper writes optind and opterr into the
    index and error fields. The program must lend those two fields and
    show that the parser may start from the result. The definition below
    names that view, and the two lemmas after it build it from a session
    or from fresh zeroed storage. *)

(** The wrapper borrows the index and error fields. When it gives them
    back holding j and err, the parser may start. *)
Definition copy_in_view (b : Z) (r : region) (av : Z) (ar : region) (ps : list ptr) (j err : Z) : iProp Σ :=
  ∃ i0 e0, live b r ∗ int_cell b 0 i0 ∗ int_cell b 4 e0 ∗
    (live b r -∗ int_cell b 0 j -∗ int_cell b 4 err -∗ getopt_entry_pre b r av ar ps j).

(** A session at index i admits the public index i, or 0 to start over. *)
Lemma session_copy_in b r av ar ps i j err :
  j = i \/ j = 0 -> getopt_session b r av ar ps i ⊢ copy_in_view b r av ar ps j err.
Proof using Type. intros Hj. apply (session_entry_pre b r av ar ps i j err Hj). Qed.

(** Fresh zeroed storage admits any public index within the count. *)
Lemma zero_copy_in b r av ar ps j err :
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (List.length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  1 <= Z.of_nat (List.length ps) < 2 ^ 31 -> 0 <= j <= Z.of_nat (List.length ps) ->
  getopt_state_own b r getopt_zero ⊢ copy_in_view b r av ar ps j err.
Proof using Type.
  intros Hav Hal Hfit Har Hn Hj. iIntros "H". iExists 0, 0.
  iApply (zero_entry_pre b r av ar ps j err Hav Hal Hfit Har Hn Hj with "H").
Qed.

(** ## The whole wrapper call

    The rule below runs the wrapper with the proved call of the parser.
    The parser's answer, index, option and argument reach the public
    cells. Then the wand gives the session back over the reordered words,
    and the caller gets every resource it lent. *)

(** A program can call getopt through the wrapper safely. The wrapper
    puts optind i and opterr err into the private object and runs the
    parser. When it returns, optind holds the new index i', optarg holds
    a' and optopt holds c'. The program gets a session at i' over the
    reordered words ps'. It also gets proof that a' is live, and the
    flags, M and longind that it lent. *)
Lemma wp_getopt_wrap_parse e n av ar p os lo li lonly pc penv b r ps i err oi roi oe roe oa roa oo roo a0 c0
    (G : iProp Σ) T fp dom se sereg mid mid' pdd sdd (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 Φ :
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WInt pc) -> 0 <= pc < 2 ^ 32 ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr b (Obj b)) ->
  lookup (TAtom "optind") (ge_globals ge) = Some (mkPtr oi (Obj oi)) ->
  lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)) ->
  lookup (TAtom "optarg") (ge_globals ge) = Some (mkPtr oa (Obj oa)) ->
  lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < oi -> oi + 4 <= r_end roi -> r_end roi <= 2 ^ 48 ->
  0 < oe -> oe + 4 <= r_end roe -> r_end roe <= 2 ^ 48 ->
  0 < oa -> oa mod 8 = 0 -> oa + 8 <= r_end roa -> r_end roa <= 2 ^ 48 ->
  0 < oo -> oo + 4 <= r_end roo -> r_end roo <= 2 ^ 48 ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined Unit_string_strcmp_os.fn___GI_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  GetoptInitialize.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx7 ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx0 ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> no_neg1_val los ->
  0 <= lonly < 2 ^ 32 -> Z.of_nat (List.length ps) = n -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  copy_in_view b r av ar ps i err -∗
  live oi roi -∗ int_cell oi 0 i -∗ live oe roe -∗ int_cell oe 0 err -∗
  live oa roa -∗ pcell oa 0 a0 -∗ live oo roo -∗ int_cell oo 0 c0 -∗
  word_string DfracDiscarded p os -∗ G -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  opt_table lo los -∗ word_string DfracDiscarded pfx7 pxs7 -∗ word_string DfracDiscarded pfx0 pxs0 -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ x i' c' a' ps', ⌜Permutation ps ps' /\ 0 <= x < 2 ^ 32⌝ -∗ getopt_session b r av ar ps' i' -∗
     live oi roi -∗ int_cell oi 0 i' -∗ live oe roe -∗ int_cell oe 0 err -∗
     live oa roa -∗ pcell oa 0 a' -∗ live oo roo -∗ int_cell oo 0 c' -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
     Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type.
  intros H0 H2 H4 H6 H8 H10 H12 Hpc Hfn Hgd Hgi Hge Hga Hgo Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer
    Hoa Hoaa Hoae Hoar Hoo Hooe Hoor Hgc Hdd Hget Hpenv Hg Hgn Hdiag Hse Hmid' Hmid Hgp Hp7 Hp0 Hcut Hmal Hset
    Hlrule Hfree Hgsn Hgl H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hneg Hlo Hlen Hn Hse0 Hsea Hsee Hser.
  iIntros "(%i0 & %e0 & Hl & Hb0 & Hb4 & Hpre) Hoi Hi Hoe He Hoa Hpa Hoo Hc #Hos HG #Hsl #Hsc Ha Hcl #Hs #Hdd
    #Ht #Hp7 #Hp0 HF HM Hli HK".
  iApply (wp_getopt_internal e n (mkPtr av (Obj av)) p lo li lonly pc b r oi roi oe roe oa roa oo roo i err a0 c0
            i0 e0 (wrap_rest b r av ar ps G F M li) Φ
            with "Hoi Hi Hoe He Hoa Hpa Hoo Hc Hl Hb0 Hb4 [Hpre HG Ha Hcl HF HM Hli] [HK]"); try (assumption || lia).
  - iIntros (cf Hcf) "Hl Hb0 Hb4". iSpecialize ("Hpre" with "Hl Hb0 Hb4").
    iApply (wp_getopt_call_parse cf n av ar p os lo li lonly pc penv b r ps i G T fp dom se sereg mid mid' pdd sdd M
              f138 f139 f140 f141 lmid mid3 mid4 los F pfx7 pxs7 pfx0 pxs0 (wrap_post b r (wrap_rest b r av ar ps G F M li))
              with "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd Ht Hp7 Hp0 HF HM Hli [ ]"); try assumption.
    iApply (call_parse_rets_wrap with "Hs").
  - iIntros (x i' c' a') "Hrest Hl Hb0 Hb8 Hb16 Hoi Hi Hoe He Hoa Hpa Hoo Hc".
    iDestruct "Hrest" as (ps' cur) "(%Hp & Hcur & Hw & Ha & Hcl & #Hs' & HG & HF & HM & Hli & Hca)".
    iSpecialize ("Hw" with "Hl Hb0 Hb8 Hb16 Hcur").
    iApply ("HK" with "[%] Hw Hoi Hi Hoe He Hoa Hpa Hoo Hc Ha Hcl Hs' HG HF HM Hli Hca"). exact Hp.
Qed.

End wrap_parse.
