(** In long-only mode, glibc's getopt first tries a word with one dash,
    such as "-name", as a long option. When the long-option parser says
    no by answering -1, getopt reads the word again as short options.
    This file proves both outcomes of that call. A return hands over the
    fields that getopt copies to its public variables, with proof that
    the argument can be read, and a way to restore the session. A fall
    back hands the short options the argument the parser chose. *)

From Glibc Require Import AllocCall OsMemLogic LongOption LongOptionTable Unit_string_strchr_os
  Unit_string_strchrnul_os Unit_string_strncmp_os GlibcProgram GlibcTactics OsTactics GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require OsWorld WordString StrchrnulLogic StrlenLogic StrlenWord StrcmpBits StrncmpLogic GetoptModule GetoptState ByteRead GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptLongScan GetoptLongDiag GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSession GetoptLongSite GetoptLongCap GetoptDashRet GetoptShortCap GetoptColon GetoptEntryScan GetoptEntryChar GetoptScanChar.
Import OsWorld WordString StrchrnulLogic StrlenLogic StrlenWord StrcmpBits StrncmpLogic GetoptModule GetoptState ByteRead GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptLongScan GetoptLongDiag GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSession GetoptLongSite GetoptLongCap GetoptDashRet GetoptShortCap GetoptColon GetoptEntry GetoptEntryScan GetoptEntryChar GetoptScanChar.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptLongSite GetoptLongSession GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongDiag GetoptLongCap GetoptShortCap GetoptExchange GetoptState Fix.ML0 Fix.LG0 Fix.LG0.L ByteRead GetoptArgv.

Section arg.
Context `{!gen_heapGS piece pval Σ}.

(** The parser may leave the argument a, point it after the equals sign
    of the string s at cur, or point it at the next word. Each choice
    is usable when a is: the text after the equals sign lies in the
    shared string, and the next word comes from the vector or is null. *)
Lemma arg_cap_long ps i cur s a a' :
  a' = a \/ a' = ptr_add cur (Z.of_nat (eq_len s) + 1) \/ a' = nth (Z.to_nat (i + 1)) ps null ->
  word_string DfracDiscarded cur s -∗ argv_strs ps -∗ arg_cap a -∗ arg_cap a'.
Proof using Type.
  intros [-> | [-> | ->]]; iIntros "#Hws #Hs Ha".
  - iExact "Ha".
  - iDestruct (ws_shape with "Hws") as %(_ & Hc0 & Hce). pose proof (eq_len_le s).
    iDestruct (argv_str_cap with "Hws") as (rc) "[Hc _]".
    iSplitL "Hc"; [by iExists rc | iPureIntro; unfold ptr_add; cbn; lia].
  - by iApply arg_cap_nth.
Qed.
End arg.

Import ProgramAbbreviations.
Section long_only_ret.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance loret_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A shared view of the stream's liveness can be copied. *)
Local Instance loret_liveq_persistent b0 reg : Persistent (liveq DfracDiscarded b0 reg).
Proof using Type. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance loret_pcellq_persistent b0 o x : Persistent (pcellq DfracDiscarded b0 o x).
Proof using Type. unfold pcellq. apply _. Qed.

(** ## The call for a single-dash word

    Both the wrapper and the short options read what the parser wrote,
    so those values must stay visible. The rule below runs the call and
    keeps them visible. The caller lends the strings, the table, the
    flags, the longind cell and the allocator resource M. The argument
    starts out null, because the entry blocks clear it. *)

(** A single-dash word sq at index i either returns the parser's answer
    x, or falls back to the short options when x is -1. A return hands
    over the fields that the parser wrote, the evidence for the new
    argument and a wand that gives the session back. The fallback keeps
    the index and the cursor, keeps the names in ks, and hands over every
    field with the evidence for the argument that the parser chose. *)
Lemma wp_getopt_long_only_ret_with ks e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq n lonly pe i oo b r li er ord fst lst Φ :
  avoids ks long_only_site_names = true ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx -> no_neg1_val os ->
  getopt_cutoff_rule_with w0 registry ge G -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  0 <= pe < 2 ^ 32 -> 0 <= lonly < 2 ^ 32 ->
  ps !! Z.to_nat i = Some q -> sbyte sq 0 = 45 -> sbyte sq 1 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 null -∗ int_cell b 24 1 -∗
  pcell b 32 (ptr_add q 1) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  ((∀ x i' oo' a' c', ⌜x <> 4294967295 /\ plo_ret_case ps i n (ptr_add q 1) (drop 1 sq) null os x i' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (∀ e' oo' a', ⌜keeps ks e e' /\ (a' = null \/ a' = ptr_add (ptr_add q 1) (Z.of_nat (eq_len (drop 1 sq)) + 1) \/
        a' = nth (Z.to_nat (i + 1)) ps null)⌝ -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 4 er -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ int_cell b 24 1 -∗
      pcell b 32 (ptr_add q 1) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L338") (Some (TAtom "L376")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L376") long_only_call long_only_jump)) : gexpr)
    {{ Φ }}.
Proof using Type.
  intros Hks Hgp H0 H2 H1 H6 H8 H10 H12 H3 Hstr Hneg Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140
    H141 Hmid Hmid3 Hmid4 Hfl Hos Hpe Hlo Hq Hq0 Hq1 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser
    Hord Hfst Hlst.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli HK".
  pose proof (sbyte_in_len sq 1 Hq1) as Hl1.
  iDestruct (ws_suffix q sq 1 with "Hwq") as "#Hws"; [lia|].
  iApply (wp_getopt_long_only_call_keep_with ks e G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F
            pfx pxs po so q sq (ptr_add q 1) (drop 1 sq) n lonly pe i oo null b r li Φ
            with "Ht Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli [-]");
    try (assumption || lia).
  iSplit.
  - iDestruct "HK" as "[HK _]". iIntros (x Hx) "Hres".
    iDestruct (plo_res_capped_null with "Hws Hs Hres") as "Hres".
    iDestruct "Hres" as (i' oo' a' c') "(Hl & Hib & Hoob & Hab & Hcur & Ha & Hcl & HG & HF & HM & Hli & Hcap & %Hra' & %Hp)".
    pose proof Hp as (Hi' & Hc' & _ & _ & _).
    iApply ("HK" $! x i' oo' a' c' with "[%] Hl Hib Hoob Hab Hcur [Her Hini Hor Hfi Hla] Ha Hcl HG HF HM Hli [Hcap]");
      [exact (conj Hx Hp) | | by iSplitL "Hcap"].
    iIntros "Hl Hib Hoob Hab Hcur".
    assert (Hnq : nth (Z.to_nat i) ps null = q) by (by rewrite (nth_lookup_Some _ _ _ _ Hq)).
    iPoseProof (GetoptScanChar.scan_cluster_cursor ps i sq er oo ord fst lst with "[]") as "Hcu";
      [rewrite Hnq; exact Hq | lia | lia | exact Hq1 | rewrite Hnq; iExact "Hwq" |].
    rewrite Hnq.
    iApply (GetoptLongSession.long_session b r av ar ps (mkGetoptState i er oo null 1 (ptr_add q 1) ord fst lst)
              i' oo' a' c' (drop 1 sq) with "Hcu Hws Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla");
      try (unfold getopt_bounds; cbn; lia); try (cbn; lia); try reflexivity; try exact Hc'.
  - iDestruct "HK" as "[_ HK]". iIntros (e' oo' a' (Hk & Ha')) "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli".
    iApply ("HK" $! e' oo' a' with "[%] Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl HG HF HM Hli [-]");
      [exact (conj Hk Ha') |].
    iApply (arg_cap_long ps i (ptr_add q 1) (drop 1 sq) null a' Ha' with "Hws Hs []"). iApply arg_cap_null.
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma wp_getopt_long_only_ret ks e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq n lonly pe i oo b r li er ord fst lst Φ :
  avoids ks long_only_site_names = true ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx -> no_neg1_val os ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  0 <= pe < 2 ^ 32 -> 0 <= lonly < 2 ^ 32 ->
  ps !! Z.to_nat i = Some q -> sbyte sq 0 = 45 -> sbyte sq 1 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 null -∗ int_cell b 24 1 -∗
  pcell b 32 (ptr_add q 1) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  ((∀ x i' oo' a' c', ⌜x <> 4294967295 /\ plo_ret_case ps i n (ptr_add q 1) (drop 1 sq) null os x i' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (∀ e' oo' a', ⌜keeps ks e e' /\ (a' = null \/ a' = ptr_add (ptr_add q 1) (Z.of_nat (eq_len (drop 1 sq)) + 1) \/
        a' = nth (Z.to_nat (i + 1)) ps null)⌝ -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 4 er -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ int_cell b 24 1 -∗
      pcell b 32 (ptr_add q 1) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L338") (Some (TAtom "L376")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L376") long_only_call long_only_jump)) : gexpr)
    {{ Φ }}.
Proof using Type.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 Hcut.
  exact (wp_getopt_long_only_ret_with ks e G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq n lonly pe i oo b r li er ord fst lst Φ H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

(** ## The exit after the scan

    The scan file left a promise for single-dash words in long-only mode,
    and this part keeps it. The caller lends the parser's resources and
    handles the two outcomes: a return, or a fall back to short options
    when the parser answers -1. *)

(** This lemma proves the long-only exit of the scan from two promises
    of the caller. The word is at index i' of the reordered vector, and
    text follows its dash. One promise handles a return, with the fields,
    the proof for the argument and a way to restore the session. The
    other handles a fall back to the short options, with every field and
    the proof for the argument that the parser chose. *)
Lemma scan_long_only_exit_with ks ks4 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 pfx pxs los F Φ :
  avoids ks long_only_site_names = true -> incl entry_scan_keys ks4 ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx -> no_neg1_val los ->
  getopt_cutoff_rule_with w0 registry ge G -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z ->
  0 <= lonly < 2 ^ 32 -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  flags_own F -∗ M -∗ longind_own li -∗
  ((∀ s s' w ps' i' f' l' x i'' oo' a' c',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
        x <> 4294967295 /\
        plo_ret_case ps' i' n (ptr_add (nth (Z.to_nat i') ps' null) 1) (drop 1 w) null los x i'' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      arg_cap a' -∗ Φ (Ret (WInt x))) ∧
   (∀ e1 e2 s s' w ps' i' f' l' oo' a',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
        entry_env e1 n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\ keeps ks e1 e2 /\
        (a' = null \/ a' = ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) (Z.of_nat (eq_len (drop 1 w)) + 1) \/
         a' = nth (Z.to_nat (i' + 1)) ps' null)⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗
      int_cell b 24 1 -∗ pcell b 32 (ptr_add (nth (Z.to_nat i') ps' null) 1) -∗ int_cell b 40 (gs_order s') -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      arg_cap a' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L338") (Some (TAtom "L376")))) : gexpr)
        {{ Φ }})) -∗
  ∀ e' e1 s s' w ps' i' f' l',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b))) /\ keeps ks4 e' e1 /\
        lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 null -∗
      int_cell b 24 1 -∗ pcell b 32 (ptr_add (nth (Z.to_nat i') ps' null) 1) -∗ int_cell b 40 (gs_order s') -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e1 [] None (Exec (TAtom "L376") long_only_call long_only_jump))
            : gexpr) {{ Φ }}.
Proof using Type.
  intros Hks Hin4 Hgp Hstr Hneg Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3 Hmid4 Hfl
    Hos Hlo Hn Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hos HF HM Hli HK".
  iIntros (e' e1 s s' w ps' i' f' l' (Hfacts & Henv & H100 & Hk1 & Hlo0 & H45))
    "#Hws Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla #Hsl #Hsc Ha Hcl #Hs HG".
  pose proof (GetoptEntryScan.entry_env_keeps ks4 e' e1 _ _ _ _ _ _ _ _ Hk1 Hin4 Henv) as Henv1.
  pose proof Henv1 as (H0 & H2 & H6 & H8 & H10 & H12 & Hpr1 & Hpr3 & _).
  pose proof Hfacts as (Hst & Hj & Hini1 & Hord & Harg & Hp & Hlen & Hfl' & Hli' & Hii & Hw0 & Hw1 & Hb & Hal & Hend &
    Hr & Hav & Hala & Hda & Hra).
  destruct (lookup_lt_is_Some_2 ps' (Z.to_nat i')) as [q Hq]; [lia|].
  assert (Hnq : ps' !! Z.to_nat i' = Some (nth (Z.to_nat i') ps' null)) by (by rewrite (nth_lookup_Some _ _ _ _ Hq)).
  iDestruct "He" as "[%Herr0 He]". rewrite (GetoptScanChar.entry_state_err _ _ Hst) in Herr0.
  iDestruct (ws_suffix p os (opt_skip os) (GetoptColon.opt_skip_le os) with "Hos") as "#Hpo".
  iApply (wp_getopt_long_only_ret_with ks e1 G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps' lo los F
            pfx pxs (ptr_add p (Z.of_nat (opt_skip os))) (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w n
            lonly (print_errors os (gs_err s)) i' (gs_opt s') b r li (gs_err s') (gs_order s') f' l' Φ
            with "Ht Hws Hpo Hpfx Hsl Hsc Hl Hi [He] Hoo Hab Hini Hcur Ho Hf Hla Ha Hcl Hs HG HF HM Hli [HK]");
    try (assumption || lia || exact (print_errors_range os (gs_err s) Herr0)).
  { rewrite (GetoptScanChar.entry_state_err _ _ Hst). by iSplit. }
  iSplit.
  - iDestruct "HK" as "[HK _]". iIntros (x i'' oo' a' c' Hc) "Hl Hi Hoo Hab Hcur Hw Ha Hcl HG HF HM Hli Hca".
    iApply ("HK" $! s s' w ps' i' f' l' x i'' oo' a' c'
              with "[%] Hl Hi Hoo Hab Hcur Hw Hsl Hsc Ha Hcl Hs HG HF HM Hli Hca").
    exact (conj Hfacts (conj Hlo0 (conj H45 Hc))).
  - iDestruct "HK" as "[_ HK]". iIntros (e2 oo' a' (Hk & Ha'))
      "Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla Ha Hcl HG HF HM Hli Hca".
    iApply ("HK" $! e1 e2 s s' w ps' i' f' l' oo' a'
              with "[%] Hws Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla Hsl Hsc Ha Hcl Hs HG HF HM Hli Hca").
    exact (conj Hfacts (conj Hlo0 (conj H45 (conj Henv1 (conj Hk Ha'))))).
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma scan_long_only_exit ks ks4 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 pfx pxs los F Φ :
  avoids ks long_only_site_names = true -> incl entry_scan_keys ks4 ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx -> no_neg1_val los ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z ->
  0 <= lonly < 2 ^ 32 -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  flags_own F -∗ M -∗ longind_own li -∗
  ((∀ s s' w ps' i' f' l' x i'' oo' a' c',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
        x <> 4294967295 /\
        plo_ret_case ps' i' n (ptr_add (nth (Z.to_nat i') ps' null) 1) (drop 1 w) null los x i'' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      arg_cap a' -∗ Φ (Ret (WInt x))) ∧
   (∀ e1 e2 s s' w ps' i' f' l' oo' a',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
        entry_env e1 n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\ keeps ks e1 e2 /\
        (a' = null \/ a' = ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) (Z.of_nat (eq_len (drop 1 w)) + 1) \/
         a' = nth (Z.to_nat (i' + 1)) ps' null)⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗
      int_cell b 24 1 -∗ pcell b 32 (ptr_add (nth (Z.to_nat i') ps' null) 1) -∗ int_cell b 40 (gs_order s') -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      arg_cap a' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L338") (Some (TAtom "L376")))) : gexpr)
        {{ Φ }})) -∗
  ∀ e' e1 s s' w ps' i' f' l',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b))) /\ keeps ks4 e' e1 /\
        lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 null -∗
      int_cell b 24 1 -∗ pcell b 32 (ptr_add (nth (Z.to_nat i') ps' null) 1) -∗ int_cell b 40 (gs_order s') -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e1 [] None (Exec (TAtom "L376") long_only_call long_only_jump))
            : gexpr) {{ Φ }}.
Proof using Type.
  intros H0 H1 H2 H3 H4 Hcut.
  exact (scan_long_only_exit_with ks ks4 n av ar p os lo li lonly b r ps j G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 pfx pxs los F Φ H0 H1 H2 H3 H4 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

End long_only_ret.
