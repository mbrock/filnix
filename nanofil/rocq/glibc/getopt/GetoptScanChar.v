From Glibc Require Import Unit_string_strchr_os Unit_string_strchrnul_os Unit_string_strcmp_os.
From Glibc Require Import GlibcProgram.
(** When glibc's scanner finds a word that starts with a dash, it decides
    whether the word is a long option or a cluster of short options. A
    cluster such as "-ab" goes straight to the character step, with the
    cursor on the byte after the dash. This file proves that decision on
    the path from the scan, runs the character step of a new cluster to
    its returns, and restores the session over the permuted argument
    vector. The two calls of the long-option parser and the form W; keep
    their own exits. *)

From Glibc Require Import GlibcTactics OsTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrnulLogic GetoptModule
  GetoptState ByteRead GetoptInitialize GetoptColon GetoptEntry GetoptEntryPre GetoptArgv
  GetoptExchange GetoptCursor GetoptIdlePath GetoptScanEnd GetoptEntryScan GetoptScanChoice
  GetoptDispatch GetoptDiag GetoptReqTail GetoptShort GetoptOptArg GetoptShortRet GetoptShortCap GetoptKnownCap
  GetoptCharRet GetoptEntryChar GetoptEntryScanRet.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** A report goes out only when the caller asked for reports. The flag
    that says so was computed before the scan, and the scan leaves the
    error field alone, so the flag fits in a word as the field does. *)
Lemma entry_state_err s s' : entry_state s s' -> gs_err s' = gs_err s.
Proof. intros [(_ & o & _ & ->) | (_ & ->)]; reflexivity. Qed.

(** ## What the scan found

    A step must not read past the word it works on, so the later blocks
    need to know which word the scan found. The fact below records it:
    where the call started, how the vector was reordered, which word w
    the scan stopped at, and where the waiting words lie. *)

(** The scan stopped at a word w that starts with a dash and goes on
    past it. The word sits at index i' of the reordered vector. *)
Definition scan_cluster_facts (n av : Z) (ar : region) (b : Z) (r : region) (ps : list ptr) (j : Z)
    (s s' : getopt_state) (w : list Z) (ps' : list ptr) (i' f' l' : Z) : Prop :=
  entry_state s s' /\ gs_ind s = j /\ gs_initialized s' = 1 /\ 0 <= gs_order s' <= 2 /\ gs_arg s' = null /\
  Permutation ps ps' /\ Z.of_nat (List.length ps') = n /\ 0 <= f' <= l' /\ l' <= i' /\ gs_ind s' <= i' < n /\
  sbyte w 0 = 45 /\ sbyte w 1 <> 0 /\
  0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
  0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48.

(** The word "-" alone has no second byte, so the bytes after its dash
    are empty and could not hold a cursor. The scan rules it out before
    the choice. *)
Lemma scan_cluster_ctl_dash : drop 1 [45] = [] /\ sbyte [45] 1 = 0.
Proof. split; reflexivity. Qed.

Section cursor.
Context `{!gen_heapGS piece pval Σ}.

(** The next call must resume inside the same word. A cursor just after
    the dash does point inside that word, because the word goes on past
    the dash. The state that holds the cursor keeps the waiting block. *)
Lemma scan_cluster_cursor (ps' : list ptr) i' w err oo o f' l' :
  ps' !! Z.to_nat i' = Some (nth (Z.to_nat i') ps' null) -> 0 <= i' < Z.of_nat (List.length ps') ->
  l' <= i' -> sbyte w 1 <> 0 ->
  word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
  getopt_cursor ps' i' (mkGetoptState i' err oo null 1 (ptr_add (nth (Z.to_nat i') ps' null) 1) o f' l').
Proof using Type.
  intros Hq Hi Hli Hw1. iIntros "#Hw". pose proof (sbyte_in_len w 1 Hw1) as Hlw.
  iRight. iRight. iExists (nth (Z.to_nat i') ps' null), (take 1 w), (drop 1 w). rewrite take_drop. iFrame "Hw".
  iPureIntro. cbn [gs_next gs_last]. rewrite length_take_le; [|lia].
  split_and!; [lia | lia | by apply entry_char_nth_error | | reflexivity | exact Hli].
  intros E. apply (f_equal List.length) in E. rewrite length_drop in E. cbn in E. lia.
Qed.
End cursor.

Import GetoptShortCap GetoptKnownCap GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic ByteRead GetoptArgv.

Import ProgramAbbreviations.
Section scan_char.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance scanchar_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A shared view of the stream's liveness can be copied. *)
Local Instance scanchar_liveq_persistent b reg : Persistent (liveq DfracDiscarded b reg).
Proof using Type. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance scanchar_pcellq_persistent b o x : Persistent (pcellq DfracDiscarded b o x).
Proof using Type. unfold pcellq. apply _. Qed.

(** ## The exits after the choice

    Each way out of the choice must say exactly what the caller holds, or
    the caller could not finish it. A word can go to the long-option
    parser in two ways, and a new cluster can stop at W; or return. The
    definitions below spell out what the caller holds in each case. They
    always read the word from the vector as the scan left it. *)

(** This is the option-choice exit of [entry_scan_ret], word for word. *)
Definition scan_choice_exit (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr)
    (lonly b : Z) (r : region) (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr)
    (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ e' s s' w ps' i' f' l',
      ⌜entry_state s s' /\ gs_ind s = j /\ gs_initialized s' = 1 /\ 0 <= gs_order s' <= 2 /\ gs_arg s' = null /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b))) /\
        Permutation ps ps' /\ Z.of_nat (List.length ps') = n /\ 0 <= f' <= l' /\ l' <= i' /\
        gs_ind s' <= i' < n /\ ps' !! Z.to_nat i' = Some (nth (Z.to_nat i') ps' null) /\
        sbyte w 0 = 45 /\ sbyte w 1 <> 0 /\
        0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
        0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 null -∗
      int_cell b 24 1 -∗ pcell b 32 (gs_next s') -∗ int_cell b 40 (gs_order s') -∗ int_cell b 44 f' -∗
      int_cell b 48 l' -∗ (⌜gs_next s' = null⌝ ∨ word_string DfracDiscarded (gs_next s') []) -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L291") (Some (TAtom "L303")))) : gexpr)
        {{ Φ }}.

(** A word that starts with two dashes, or a single-dash word in
    long-only mode, goes to the long-option parser. The cursor is two
    bytes or one byte into the word, as the exits at L342 and L376 say. *)
Definition scan_long_exits (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr)
    (lonly b : Z) (r : region) (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr)
    (ks4 : list name) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  (∀ e' e1 s s' w ps' i' f' l',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b))) /\ keeps ks4 e' e1 /\ sbyte w 1 = 45⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 null -∗
      int_cell b 24 1 -∗ pcell b 32 (ptr_add (nth (Z.to_nat i') ps' null) 2) -∗ int_cell b 40 (gs_order s') -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e1 [] None (Exec (TAtom "L342") long_call long_jump)) : gexpr)
        {{ Φ }}) ∧
  (∀ e' e1 s s' w ps' i' f' l',
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
            : gexpr) {{ Φ }}).

(** The caller needs to know how a new cluster ends. It either stops at
    W; with every field in hand, or it returns. After a return, the caller
    gets the fields that the wrapper copies, the evidence that the
    argument is usable, and a wand that gives the session back. *)
Definition scan_char_exits (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr)
    (lonly b : Z) (r : region) (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr)
    (ks ks2 : list name) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  (∀ e1 e2 e3 s s' w ps' i' f' l' k,
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        entry_env e1 n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        keeps ks e1 e2 /\ keeps ks2 e2 e3 /\ lookup (TAtom "v455") e2 = Some (WInt (chr_w (sbyte (drop 1 w) 0))) /\
        (k < List.length (drop (opt_skip os) os))%nat /\ sbyte (drop (opt_skip os) os) k = sbyte (drop 1 w) 0 /\
        lookup (TAtom "v459") e2 = Some (WPtr (ptr_add (ptr_add p (Z.of_nat (opt_skip os))) (Z.of_nat k))) /\
        lookup (TAtom "chk137") e2 = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        sbyte (drop (opt_skip os) os) k = 87 /\ sbyte (drop (opt_skip os) os) (S k) = 59 /\
        ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 (if sbyte (drop 1 w) 1 =? 0 then i' + 1 else i') -∗ int_cell b 4 (gs_err s') -∗
      int_cell b 8 (gs_opt s') -∗ pcell b 16 null -∗ int_cell b 24 1 -∗
      pcell b 32 (ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) 1) -∗ int_cell b 40 (gs_order s') -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e3 [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        char_ret_case ps' n i' (gs_opt s') (ptr_add (nth (Z.to_nat i') ps' null) 1) null (drop 1 w)
          (drop (opt_skip os) os) x i'' oo' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x))).

(** These are the same exits, except that a return also gives the
    string of the word. *)
Definition scan_char_exits_ws (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr)
    (lonly b : Z) (r : region) (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr)
    (ks ks2 : list name) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  (∀ e1 e2 e3 s s' w ps' i' f' l' k,
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        entry_env e1 n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        keeps ks e1 e2 /\ keeps ks2 e2 e3 /\ lookup (TAtom "v455") e2 = Some (WInt (chr_w (sbyte (drop 1 w) 0))) /\
        (k < List.length (drop (opt_skip os) os))%nat /\ sbyte (drop (opt_skip os) os) k = sbyte (drop 1 w) 0 /\
        lookup (TAtom "v459") e2 = Some (WPtr (ptr_add (ptr_add p (Z.of_nat (opt_skip os))) (Z.of_nat k))) /\
        lookup (TAtom "chk137") e2 = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        sbyte (drop (opt_skip os) os) k = 87 /\ sbyte (drop (opt_skip os) os) (S k) = 59 /\
        ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗
      live b r -∗ int_cell b 0 (if sbyte (drop 1 w) 1 =? 0 then i' + 1 else i') -∗ int_cell b 4 (gs_err s') -∗
      int_cell b 8 (gs_opt s') -∗ pcell b 16 null -∗ int_cell b 24 1 -∗
      pcell b 32 (ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) 1) -∗ int_cell b 40 (gs_order s') -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e3 [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        char_ret_case ps' n i' (gs_opt s') (ptr_add (nth (Z.to_nat i') ps' null) 1) null (drop 1 w)
          (drop (opt_skip os) os) x i'' oo' a' c'⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x))).

(** A caller that handles the exits without the string also handles
    them with it. *)
Lemma scan_char_exits_weaken n av ar p os lo li lonly b r ps j (G : iProp Σ) se sereg fp ks ks2 Φ :
  scan_char_exits n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ ⊢
  scan_char_exits_ws n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ.
Proof using Type.
  iIntros "H". unfold scan_char_exits, scan_char_exits_ws.
  iSplit; [iDestruct "H" as "[H _]"; iExact "H"|]. iDestruct "H" as "[_ H]".
  iIntros (s s' w ps' i' f' l' x i'' oo' a' c' Hc) "_".
  iApply ("H" $! s s' w ps' i' f' l' x i'' oo' a' c' with "[%]"). exact Hc.
Qed.

(** ## The choice and a new cluster

    The scan left the caller with a promise to finish the option choice.
    The lemma below keeps that promise for short options. It decides what
    kind of word the scan found and, for a cluster, reads its first
    character and returns. After each return, the caller can rebuild the
    session from the fields it holds. *)

(** To finish the choice, the caller only has to handle the long options
    and W;. Everything else returns here. The choice must keep the names
    that the setup computed, so that the character step can still read
    them afterwards. A return also gives the string of the word. *)
Lemma scan_choice_char_ws ks ks2 ks4 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom se sereg mid mid' Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  avoids ks4 choice_names = true -> incl entry_scan_keys ks4 ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded p os -∗
  (scan_long_exits n av ar p os lo li lonly b r ps j G se sereg fp ks4 Φ ∧
   scan_char_exits_ws n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ) -∗
  scan_choice_exit n av ar p os lo li lonly b r ps j G se sereg fp Φ.
Proof using Type.
  intros Hks Hkin Hop Hrq Hdg Hrt Hinc Hk4 Hin4 Hg Hgn Hdiag Hse Hmid' Hmid Hn Hse0 Hsea Hsee Hser.
  iIntros "#Hos HK".
  iIntros (e' s s' w ps' i' f' l' (Hst & Hj & Hin & Hord & Harg & Henv & H100 & Hp & Hlen & Hfl & Hli & Hii & Hq &
    Hw0 & Hw1 & Hb & Hal & Hend & Hr & Hav & Hala & Hda & Hra))
    "#Hws Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla #Hc #Hsl #Hsc Ha Hcl #Hs HG".
  assert (Hfacts : scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l') by (split_and!; first [assumption | lia]).
  pose proof (scan_choice_env _ _ _ _ _ _ _ _ _ Henv H100)
    as (H0 & H2 & Hpr1 & H6 & H8 & H10 & H12 & Hpr3 & Hc2 & Hc20 & _).
  pose proof (entry_state_err _ _ Hst) as Herr.
  iDestruct (ws_suffix p os (opt_skip os) (opt_skip_le os) with "Hos") as "#Hpo".
  iApply (wp_getopt_choice ks4 e' i' n (gs_next s') lo lonly (ptr_add p (Z.of_nat (opt_skip os)))
            (drop (opt_skip os) os) b r av ar ps' w Φ with "Hws Hpo Hl Hi Hcur Ha Hcl Hs [-]");
    try (assumption || lia).
  iSplit; [|iSplit].
  - iIntros (e1 Hk1) "Hl Hi Hcur Ha Hcl".
    pose proof (GetoptEntryScan.entry_env_keeps ks4 e' e1 _ _ _ _ _ _ _ _ Hk1 Hin4 Henv) as Henv1.
    pose proof (sbyte_in_len w 1 Hw1) as Hlw.
    iDestruct (ws_suffix _ w 1 with "Hws") as "#Hws1"; [lia|].
    assert (Ht0 : sbyte (drop 1 w) 0 <> 0) by (rewrite sbyte_drop; [exact Hw1 | lia]).
    iDestruct "He" as "[%Herr0 He]". rewrite Herr in Herr0.
    iPoseProof arg_cap_null as "Hnull".
    iApply (wp_getopt_char_ret ks ks2 e1 (TAtom "L338") i' n (print_errors os (gs_err s))
              (ptr_add (nth (Z.to_nat i') ps' null) 1) (drop 1 w) (ptr_add p (Z.of_nat (opt_skip os)))
              (drop (opt_skip os) os) (gs_opt s') null lo li lonly b r av ar ps' G T fp dom se sereg mid mid' Φ
              with "Hws1 Hpo Hsl Hsc Hl Hi Hoo Hab Hcur Ha Hcl Hs HG Hnull [-]");
      try (assumption || lia || exact (print_errors_range os (gs_err s) Herr0)).
    iSplit.
    + iDestruct "HK" as "[_ [HW _]]". iIntros (e2 e3 k Hw) "Hl Hi Hoo Hab Hcur Ha Hcl HG _".
      iApply ("HW" $! e1 e2 e3 s s' w ps' i' f' l' k
                with "[%] Hws Hl Hi [He] Hoo Hab Hini Hcur Ho Hf Hla Hsl Hsc Ha Hcl Hs HG");
        [exact (conj Hfacts (conj Henv1 Hw)) | rewrite Herr; by iSplit].
    + iDestruct "HK" as "[_ [_ HR]]". iIntros (x i'' oo' a' c' Hcase) "Hl Hi Hoo Hab Hcur Ha Hcl HG Hca".
      iApply ("HR" $! s s' w ps' i' f' l' x i'' oo' a' c'
                with "[%] Hws Hl Hi Hoo Hab Hcur [He Hini Ho Hf Hla] Hsl Hsc Ha Hcl Hs HG Hca");
        [exact (conj Hfacts Hcase) |].
      iIntros "Hl Hi Hoo Hab Hcur".
      iPoseProof (scan_cluster_cursor ps' i' w (gs_err s') (gs_opt s') (gs_order s') f' l' Hq with "Hws")
        as "Hcu"; [lia | lia | exact Hw1 |].
      iAssert (int_cell b 4 (gs_err s')) with "[He]" as "He"; [rewrite Herr; by iSplit|].
      subst n.
      iApply (char_ret_session b r av ar ps'
                (mkGetoptState i' (gs_err s') (gs_opt s') null 1 (ptr_add (nth (Z.to_nat i') ps' null) 1)
                   (gs_order s') f' l')
                (gs_opt s') (drop 1 w) (drop (opt_skip os) os) x i'' oo' null a' c'
                with "Hcu Hws1 Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla");
        cbn [gs_ind gs_initialized gs_order gs_next]; try (assumption || lia).
      unfold getopt_bounds. cbn. lia.
  - iDestruct "HK" as "[[HL _] _]". iIntros (e1 (Hk1 & H45)) "Hl Hi Hcur Ha Hcl".
    iApply ("HL" $! e' e1 s s' w ps' i' f' l'
              with "[%] Hws Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla Hsl Hsc Ha Hcl Hs HG").
    split_and!; first [assumption | lia].
  - iDestruct "HK" as "[[_ HL] _]". iIntros (e1 (Hk1 & Hlo & H45)) "Hl Hi Hcur Ha Hcl".
    iApply ("HL" $! e' e1 s s' w ps' i' f' l'
              with "[%] Hws Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla Hsl Hsc Ha Hcl Hs HG").
    split_and!; first [assumption | lia].
Qed.

(** The same choice serves a caller that needs no string of the word. *)
Lemma scan_choice_char ks ks2 ks4 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom se sereg mid mid' Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  avoids ks4 choice_names = true -> incl entry_scan_keys ks4 ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded p os -∗
  (scan_long_exits n av ar p os lo li lonly b r ps j G se sereg fp ks4 Φ ∧
   scan_char_exits n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ) -∗
  scan_choice_exit n av ar p os lo li lonly b r ps j G se sereg fp Φ.
Proof using Type.
  intros. iIntros "Hos HK".
  iApply (scan_choice_char_ws ks ks2 ks4 n av ar p os lo li lonly b r ps j G T fp dom se sereg mid mid' Φ with "Hos");
    try eassumption.
  iSplit; [iDestruct "HK" as "[H _]"; iExact "H" | iDestruct "HK" as "[_ H]"; iApply scan_char_exits_weaken; iExact "H"].
Qed.

(** ## A call up to the long-option parser

    A caller of getopt wants one rule for a whole call, with as little
    left open as possible. The rule below joins the choice with the
    call-level rule of the scan file. Only the long options and W; remain
    open. *)

(** Every call of the parser either returns here or reaches a long option
    or W;. It returns after a scan that finds no option, or after one
    character of a cluster, whether the cluster is new or resumed. Every
    return gives back the copied fields, the evidence for the argument and
    a wand that restores the session. A return after one character also
    gives the string of the word. *)
Lemma wp_getopt_entry_dispatch_ws_at ks ks2 ks3 ks4 cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) T fp dom
    se sereg mid mid' pdd sdd Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  avoids ks3 idle_names = true -> avoids ks3 scan_end_names = true -> incl entry_scan_keys ks3 ->
  avoids ks4 choice_names = true -> incl entry_scan_keys ks4 ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined Unit_string_strcmp_os.fn___GI_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  call_frame glibc_getopt_internal_r
    [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] = Some cf ->
  GetenvCall.getenv_at_rule w0 registry ge G penv -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  Z.of_nat (List.length ps) = n -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  getopt_entry_pre b r av ar ps j -∗ word_string DfracDiscarded p os -∗ G -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  ((∀ s s' ps' x i' a', ⌜entry_state s s' /\ gs_ind s = j /\ Permutation ps ps' /\
        scan_ret_case n (gs_ind s') (gs_order s') ps' x i' a'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
         getopt_session b r av ar ps' i') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x))) ∧
   (scan_long_exits n av ar p os lo li lonly b r ps j G se sereg fp ks4 Φ ∧
    scan_char_exits_ws n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ) ∧
   (∀ e' e2 e3 s q sq k0 k,
      ⌜entry_resume_facts n av ar b r ps j s q sq k0 /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        keeps ks e' e2 /\ keeps ks2 e2 e3 /\ lookup (TAtom "v455") e2 = Some (WInt (chr_w (sbyte (drop k0 sq) 0))) /\
        (k < List.length (drop (opt_skip os) os))%nat /\ sbyte (drop (opt_skip os) os) k = sbyte (drop k0 sq) 0 /\
        lookup (TAtom "v459") e2 = Some (WPtr (ptr_add (ptr_add p (Z.of_nat (opt_skip os))) (Z.of_nat k))) /\
        lookup (TAtom "chk137") e2 = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        sbyte (drop (opt_skip os) os) k = 87 /\ sbyte (drop (opt_skip os) os) (S k) = 59 /\
        ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      word_string DfracDiscarded q sq -∗ word_string DfracDiscarded (gs_next s) (drop k0 sq) -∗
      live b r -∗ int_cell b 0 (if sbyte (drop k0 sq) 1 =? 0 then j + 1 else j) -∗ int_cell b 4 (gs_err s) -∗
      int_cell b 8 (gs_opt s) -∗ pcell b 16 null -∗ int_cell b 24 1 -∗ pcell b 32 (ptr_add (gs_next s) 1) -∗
      int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗ int_cell b 48 (gs_last s) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e3 [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
   (∀ s q sq k0 x i' oo' a' c',
      ⌜entry_resume_facts n av ar b r ps j s q sq k0 /\
        char_ret_case ps n j (gs_opt s) (gs_next s) null (drop k0 sq) (drop (opt_skip os) os) x i' oo' a' c'⌝ -∗
      word_string DfracDiscarded q sq -∗ live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x)))) -∗
  WP (ERun cf : gexpr) {{ Φ }}.
Proof using Type.
  intros Hks Hkin Hop Hrq Hdg Hrt Hinc Hki3 Hks3 Hin3 Hk4 Hin4 Hgc Hdd Hcf Hget Hpenv Hg Hgn Hdiag Hse Hmid' Hmid
    Hlen Hn Hse0 Hsea Hsee Hser.
  iIntros "Hpre #Hos HG Hsl Hsc Ha Hcl #Hs #Hdd HK".
  iApply (wp_getopt_entry_scan_char_ws_at ks ks2 ks3 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom se sereg
            mid mid' pdd sdd Φ with "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd [HK]"); try assumption.
  iSplit; [iDestruct "HK" as "[H _]"; iExact "H" |].
  iSplit; [|iDestruct "HK" as "(_ & _ & H)"; iExact "H"].
  iDestruct "HK" as "(_ & H & _)".
  iApply (scan_choice_char_ws ks ks2 ks4 n av ar p os lo li lonly b r ps j G T fp dom se sereg mid mid' Φ
            with "Hos H"); assumption.
Qed.

(** The legacy dispatch rule adapts to the same instruction proof. *)
Definition wp_getopt_entry_dispatch_ws ks ks2 ks3 ks4 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom
    se sereg mid mid' pdd sdd Φ Hks Hkin Hop Hrq Hdg Hrt Hinc Hki3 Hks3 Hin3 Hk4 Hin4 Hgc Hdd Hcf
    (Hget : GetoptInitialize.getenv_rule w0 registry ge G) :=
  wp_getopt_entry_dispatch_ws_at ks ks2 ks3 ks4 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom
    se sereg mid mid' pdd sdd Φ Hks Hkin Hop Hrq Hdg Hrt Hinc Hki3 Hks3 Hin3 Hk4 Hin4 Hgc Hdd Hcf
    (GetoptInitialize.getenv_rule_at w0 registry ge G penv Hget).

(** The same call serves a caller that needs no string of the word. *)
Lemma wp_getopt_entry_dispatch ks ks2 ks3 ks4 cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) T fp dom
    se sereg mid mid' pdd sdd Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  avoids ks3 idle_names = true -> avoids ks3 scan_end_names = true -> incl entry_scan_keys ks3 ->
  avoids ks4 choice_names = true -> incl entry_scan_keys ks4 ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined Unit_string_strcmp_os.fn___GI_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  call_frame glibc_getopt_internal_r
    [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] = Some cf ->
  GetoptInitialize.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  Z.of_nat (List.length ps) = n -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  getopt_entry_pre b r av ar ps j -∗ word_string DfracDiscarded p os -∗ G -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  ((∀ s s' ps' x i' a', ⌜entry_state s s' /\ gs_ind s = j /\ Permutation ps ps' /\
        scan_ret_case n (gs_ind s') (gs_order s') ps' x i' a'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
         getopt_session b r av ar ps' i') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x))) ∧
   (scan_long_exits n av ar p os lo li lonly b r ps j G se sereg fp ks4 Φ ∧
    scan_char_exits n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ) ∧
   (∀ e' e2 e3 s q sq k0 k,
      ⌜entry_resume_facts n av ar b r ps j s q sq k0 /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        keeps ks e' e2 /\ keeps ks2 e2 e3 /\ lookup (TAtom "v455") e2 = Some (WInt (chr_w (sbyte (drop k0 sq) 0))) /\
        (k < List.length (drop (opt_skip os) os))%nat /\ sbyte (drop (opt_skip os) os) k = sbyte (drop k0 sq) 0 /\
        lookup (TAtom "v459") e2 = Some (WPtr (ptr_add (ptr_add p (Z.of_nat (opt_skip os))) (Z.of_nat k))) /\
        lookup (TAtom "chk137") e2 = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        sbyte (drop (opt_skip os) os) k = 87 /\ sbyte (drop (opt_skip os) os) (S k) = 59 /\
        ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      word_string DfracDiscarded q sq -∗ word_string DfracDiscarded (gs_next s) (drop k0 sq) -∗
      live b r -∗ int_cell b 0 (if sbyte (drop k0 sq) 1 =? 0 then j + 1 else j) -∗ int_cell b 4 (gs_err s) -∗
      int_cell b 8 (gs_opt s) -∗ pcell b 16 null -∗ int_cell b 24 1 -∗ pcell b 32 (ptr_add (gs_next s) 1) -∗
      int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗ int_cell b 48 (gs_last s) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e3 [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
   (∀ s q sq k0 x i' oo' a' c',
      ⌜entry_resume_facts n av ar b r ps j s q sq k0 /\
        char_ret_case ps n j (gs_opt s) (gs_next s) null (drop k0 sq) (drop (opt_skip os) os) x i' oo' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x)))) -∗
  WP (ERun cf : gexpr) {{ Φ }}.
Proof using Type.
  intros. iIntros "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd HK".
  iApply (wp_getopt_entry_dispatch_ws ks ks2 ks3 ks4 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom se sereg mid mid' pdd sdd Φ with "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd");
    try eassumption.
  iSplit; [iDestruct "HK" as "[H _]"; iExact "H"|].
  iSplit.
  { iDestruct "HK" as "(_ & H & _)". iSplit; [iDestruct "H" as "[H _]"; iExact "H"|].
    iDestruct "H" as "[_ H]". iApply scan_char_exits_weaken. iExact "H". }
  iSplit; [iDestruct "HK" as "(_ & _ & H & _)"; iExact "H"|].
  iDestruct "HK" as "(_ & _ & _ & H)". iIntros (s q sq k0 x i' oo' a' c' Hc) "_".
  iApply ("H" $! s q sq k0 x i' oo' a' c' with "[%]"). exact Hc.
Qed.

End scan_char.
