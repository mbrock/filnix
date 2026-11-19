From Glibc Require Import Unit_string_strchr_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcProgram.
(** In long-only mode, glibc's getopt reads a single-dash word such as
    "-ab" as short options when the long-option parser rejects it. The
    parser may already have changed the bad-option field and chosen an
    argument before it answered -1, and the short options start from
    those values. This file follows that path: it stores the cursor one
    byte into the word, runs one character of the cluster to its return,
    and restores the session. The form W; keeps its own exit. *)

From Glibc Require Import GlibcTactics OsTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require OsWorld FileInv LibioLogic WordString StrchrnulLogic StrlenLogic StrlenWord StrcmpBits StrncmpLogic GetoptModule GetoptState ByteRead GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongPfxCmp GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSite GetoptKnownCap GetoptShort GetoptOptArg GetoptShortRet GetoptShortCap GetoptColon GetoptEntryScan GetoptCharRet GetoptEntryChar GetoptScanChar.
Import OsWorld FileInv LibioLogic WordString StrchrnulLogic StrlenLogic StrlenWord StrcmpBits StrncmpLogic GetoptModule GetoptState ByteRead GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongPfxCmp GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSite GetoptKnownCap GetoptDiag GetoptReqTail GetoptShort GetoptOptArg GetoptShortRet GetoptShortCap GetoptColon GetoptEntry GetoptEntryScan GetoptCharRet GetoptEntryChar GetoptScanChar.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptLongSite GetoptShortCap GetoptKnownCap GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic ByteRead GetoptArgv.

(** One list of names can serve the whole path. The setup's names avoid
    the names that the long-only call and the short cursor assign, so a
    caller can keep them across both blocks. *)
Lemma entry_scan_keys_fallback : avoids entry_scan_keys long_only_site_names = true /\
  avoids entry_scan_keys short_names = true.
Proof. split; vm_compute; reflexivity. Qed.

Import ProgramAbbreviations.
Section long_only_short.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance los_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A shared view of the stream's liveness can be copied. *)
Local Instance los_liveq_persistent b0 reg : Persistent (liveq DfracDiscarded b0 reg).
Proof using Type. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance los_pcellq_persistent b0 o x : Persistent (pcellq DfracDiscarded b0 o x).
Proof using Type. unfold pcellq. apply _. Qed.

(** ## The exits of the fallback

    The caller has to know how the fallback ends. It either stops at W;
    with every field in hand, or it returns one character of the
    cluster. The definitions below say what the caller holds in each
    case. Both start from the bad-option field oo' and the argument a'
    that the parser left, and both pass the parser's resources back. *)

(** This is the fallback exit of [scan_long_only_exit], word for word. *)
Definition long_only_fallback_exit (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr)
    (lonly b : Z) (r : region) (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr)
    (ks : list name) (F : list ptr) (M : iProp Σ) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ e1 e2 s s' w ps' i' f' l' oo' a',
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
        {{ Φ }}.

(** The short-option step can end in two ways, and the caller has to
    handle both. If the option is W followed by a semicolon, the code
    jumps to its own block and the caller gets every field. Otherwise
    the code returns one character. Then the caller gets the copied
    fields, proof that the argument is live, and a wand that restores
    the session. Both ways start from the values that the parser left. *)
Definition long_only_short_exits (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr)
    (lonly b : Z) (r : region) (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr)
    (kc kr : list name) (F : list ptr) (M : iProp Σ) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ)
    : iProp Σ :=
  (∀ e3 e4 e5 s s' w ps' i' f' l' oo' a' k,
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
        (a' = null \/ a' = ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) (Z.of_nat (eq_len (drop 1 w)) + 1) \/
         a' = nth (Z.to_nat (i' + 1)) ps' null) /\
        entry_env e3 n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        keeps kc e3 e4 /\ keeps kr e4 e5 /\ lookup (TAtom "v455") e4 = Some (WInt (chr_w (sbyte (drop 1 w) 0))) /\
        (k < List.length (drop (opt_skip os) os))%nat /\ sbyte (drop (opt_skip os) os) k = sbyte (drop 1 w) 0 /\
        lookup (TAtom "v459") e4 = Some (WPtr (ptr_add (ptr_add p (Z.of_nat (opt_skip os))) (Z.of_nat k))) /\
        lookup (TAtom "chk137") e4 = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        sbyte (drop (opt_skip os) os) k = 87 /\ sbyte (drop (opt_skip os) os) (S k) = 59 /\
        ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 (if sbyte (drop 1 w) 1 =? 0 then i' + 1 else i') -∗ int_cell b 4 (gs_err s') -∗
      int_cell b 8 oo' -∗ pcell b 16 a' -∗ int_cell b 24 1 -∗
      pcell b 32 (ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) 1) -∗ int_cell b 40 (gs_order s') -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e5 [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
  (∀ s s' w ps' i' f' l' oo' a' x i'' oo'' a'' c'',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
        (a' = null \/ a' = ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) (Z.of_nat (eq_len (drop 1 w)) + 1) \/
         a' = nth (Z.to_nat (i' + 1)) ps' null) /\
        char_ret_case ps' n i' oo' (ptr_add (nth (Z.to_nat i') ps' null) 1) a' (drop 1 w)
          (drop (opt_skip os) os) x i'' oo'' a'' c''⌝ -∗
      live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo'' -∗ pcell b 16 a'' -∗ pcell b 32 c'' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo'' -∗ pcell b 16 a'' -∗ pcell b 32 c'' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      arg_cap a'' -∗ Φ (Ret (WInt x))).

(** ## From the fallback to a return

    When the long-option parser gives up, getopt reads the word as a
    group of short options. It puts the cursor after the dash and reads
    the first letter. The fields still hold what the parser left there.
    After the letter is handled, the caller can rebuild the session over
    the reordered words. *)

(** This lemma lets the caller treat a rejected long option as short
    options. The caller handles the two endings above, and in return it
    gets the exit that the long-only call leaves open. The call keeps the
    names in ks and the cursor keeps the names in kz. Both lists must
    hold the setup's names, and [entry_scan_keys_fallback] shows that
    they can. *)
Lemma long_only_fallback_char ks kz kc kr n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom se sereg mid mid'
    F (M : iProp Σ) Φ :
  incl entry_scan_keys ks -> avoids kz short_names = true -> incl entry_scan_keys kz ->
  avoids kc char_names = true -> incl char_ret_keys kc ->
  avoids kr opt_names = true -> avoids kr req_names = true -> avoids kr diag_names = true ->
  avoids kr ret_names = true -> incl known_req_keys kr ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded p os -∗
  long_only_short_exits n av ar p os lo li lonly b r ps j G se sereg fp kc kr F M Φ -∗
  long_only_fallback_exit n av ar p os lo li lonly b r ps j G se sereg fp ks F M Φ.
Proof using Type.
  intros Hks Hkz Hinz Hkc Hkin Hop Hrq Hdg Hrt Hinc Hg Hgn Hdiag Hse Hmid' Hmid Hn Hse0 Hsea Hsee Hser.
  iIntros "#Hos HK".
  iIntros (e1 e2 s s' w ps' i' f' l' oo' a' (Hfacts & Hlo0 & H45 & Henv1 & Hk2 & Ha'))
    "#Hws Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla #Hsl #Hsc Ha Hcl #Hs HG HF HM Hli Hca".
  pose proof Hfacts as (Hst & Hj & Hini1 & Hord & Harg & Hp & Hlen & Hfl' & Hli' & Hii & Hw0 & Hw1 & Hb & Hal & Hend &
    Hr & Hav & Hala & Hda & Hra).
  pose proof (GetoptEntryScan.entry_env_keeps ks e1 e2 _ _ _ _ _ _ _ _ Hk2 Hks Henv1) as Henv2.
  pose proof Henv2 as (_ & H2 & _ & _ & _ & H12 & _ & _ & _ & _ & Hc2 & _ & Hc20 & _).
  pose proof (sbyte_in_len w 1 Hw1) as Hlw.
  iDestruct (ws_suffix _ w 1 with "Hws") as "#Hws1"; [lia|].
  assert (Ht0 : sbyte (drop 1 w) 0 <> 0) by (rewrite sbyte_drop; [exact Hw1 | lia]).
  iDestruct "He" as "[%Herr0 He]". rewrite (GetoptScanChar.entry_state_err _ _ Hst) in Herr0.
  iDestruct (ws_suffix p os (opt_skip os) (GetoptColon.opt_skip_le os) with "Hos") as "#Hpo".
  iApply (wp_getopt_short_cursor kz e2 (TAtom "L376") i' n (ptr_add (nth (Z.to_nat i') ps' null) 1) b r av ar ps' Φ
            with "Hl Hi Hcur Ha Hcl Hs [-]"); try (assumption || lia).
  iIntros (e3 Hk3) "Hl Hi Hcur Ha Hcl".
  pose proof (GetoptEntryScan.entry_env_keeps kz e2 e3 _ _ _ _ _ _ _ _ Hk3 Hinz Henv2) as Henv3.
  iApply (wp_getopt_char_ret kc kr e3 (TAtom "L338") i' n (print_errors os (gs_err s))
            (ptr_add (nth (Z.to_nat i') ps' null) 1) (drop 1 w) (ptr_add p (Z.of_nat (opt_skip os)))
            (drop (opt_skip os) os) oo' a' lo li lonly b r av ar ps' G T fp dom se sereg mid mid' Φ
            with "Hws1 Hpo Hsl Hsc Hl Hi Hoo Hab Hcur Ha Hcl Hs HG Hca [-]");
    try (assumption || lia || exact (print_errors_range os (gs_err s) Herr0)).
  iSplit.
  - iDestruct "HK" as "[HW _]". iIntros (e4 e5 k Hw) "Hl Hi Hoo Hab Hcur Ha Hcl HG Hca".
    iApply ("HW" $! e3 e4 e5 s s' w ps' i' f' l' oo' a' k
              with "[%] Hws Hl Hi [He] Hoo Hab Hini Hcur Ho Hf Hla Hsl Hsc Ha Hcl Hs HG HF HM Hli Hca");
      [exact (conj Hfacts (conj Hlo0 (conj H45 (conj Ha' (conj Henv3 Hw))))) |].
    rewrite (GetoptScanChar.entry_state_err _ _ Hst). by iSplit.
  - iDestruct "HK" as "[_ HR]". iIntros (x i'' oo'' a'' c'' Hcase) "Hl Hi Hoo Hab Hcur Ha Hcl HG Hca".
    iApply ("HR" $! s s' w ps' i' f' l' oo' a' x i'' oo'' a'' c''
              with "[%] Hl Hi Hoo Hab Hcur [He Hini Ho Hf Hla] Hsl Hsc Ha Hcl Hs HG HF HM Hli Hca");
      [exact (conj Hfacts (conj Hlo0 (conj H45 (conj Ha' Hcase)))) |].
    iIntros "Hl Hi Hoo Hab Hcur".
    assert (Hnq : ps' !! Z.to_nat i' = Some (nth (Z.to_nat i') ps' null)).
    { destruct (lookup_lt_is_Some_2 ps' (Z.to_nat i')) as [q Hq]; [lia|]. by rewrite (nth_lookup_Some _ _ _ _ Hq). }
    iPoseProof (GetoptScanChar.scan_cluster_cursor ps' i' w (gs_err s') oo' (gs_order s') f' l' Hnq with "Hws")
      as "Hcu"; [lia | lia | exact Hw1 |].
    iAssert (int_cell b 4 (gs_err s')) with "[He]" as "He".
    { rewrite (GetoptScanChar.entry_state_err _ _ Hst). by iSplit. }
    subst n.
    iApply (char_ret_session b r av ar ps'
              (mkGetoptState i' (gs_err s') oo' null 1 (ptr_add (nth (Z.to_nat i') ps' null) 1) (gs_order s') f' l')
              oo' (drop 1 w) (drop (opt_skip os) os) x i'' oo'' a' a'' c''
              with "Hcu Hws1 Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla");
      cbn [gs_ind gs_initialized gs_order gs_next]; try (assumption || lia).
    unfold getopt_bounds. cbn. lia.
Qed.

End long_only_short.
