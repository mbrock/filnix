From Glibc Require Import GlibcProgram.
(** When a call of glibc's scanner has no cluster to resume, it looks
    for the next word. It may return before it parses an option, because
    no word is left or because the word is a nonoption that the ordering
    mode returns. Otherwise it finds a word that starts with a dash and
    hands it to the option choice. The getopt wrapper copies the private
    index, the bad-option field and the argument after every return, so
    the early returns must hand over those fields together with the
    evidence that the argument is usable. This file runs the scanner on
    the path that the entry blocks leave, closes its early returns, and
    joins the result with the resumed-cluster rule of the entry blocks.
    The option choice and the form W; keep their own exits. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrcmpCode StrchrCode StrchrnulLogic GetoptModule
  GetoptState GetoptBytes GetoptInitialize GetoptColon GetoptEntry GetoptEntryPre GetoptEntryCall GetoptArgv
  GetoptExchange GetoptReturn GetoptIdlePath GetoptScanEnd GetoptScan GetoptScanSession GetoptEntryScan
  GetoptDiag GetoptReqTail GetoptShort GetoptOptArg GetoptShortRet GetoptShortCap GetoptKnownCap GetoptCharRet
  GetoptEntryChar.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptCharRet GetoptEntry GetoptEntryCall GetoptEntryChar
  GetoptEntryScan GetoptExchange GetoptInitialize GetoptScan GetoptScanSession GetoptShortCap GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The ways a scan returns early

    An early return ends the call with -1 or 1. The relation below names
    the returned value x, the new index i' and the new argument a'. The
    count is n, the scan starts at index i0 and o is the ordering mode.
    When no word is left, the index points at the first waiting
    nonoption, or at the count when none waits, and the scanner returns
    -1. In strict order a nonoption at index i' stops the scan with -1.
    In the returning order the scanner returns 1, takes the nonoption at
    index k of the permuted vector ps' as the argument, and steps past it. *)
Definition scan_ret_case (n i0 o : Z) (ps' : list ptr) (x i' : Z) (a' : ptr) : Prop :=
  (x = 4294967295 /\ a' = null /\ exists f' l', 0 <= f' <= l' /\ l' <= n /\ i' = (if f' =? l' then n else f')) \/
  (x = 4294967295 /\ a' = null /\ o = 0 /\ i0 <= i' < n) \/
  (x = 1 /\ o <> 0 /\ exists k, i0 <= k < n /\ i' = k + 1 /\ a' = nth (Z.to_nat k) ps' null).

(** Strict order never returns 1, because only the returning order
    hands back a nonoption. *)
Lemma scan_ret_ctl_strict n i0 ps' x i' a' : scan_ret_case n i0 0 ps' x i' a' -> x = 4294967295.
Proof. intros [H | [H | H]]; tauto. Qed.

(** In the returning order, the nonoption at index 1 of the permuted
    vector [p; q] is q, and the index moves to 2. *)
Lemma scan_ret_ctl_inorder p q : scan_ret_case 2 1 1 [p; q] 1 2 q.
Proof. right. right. split; [reflexivity|]. split; [lia|]. exists 1. cbn. repeat split; lia. Qed.

Import GetoptShortCap GetoptKnownCap GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML
  FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section entry_scan_ret.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance esr_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## Scanning from the entry blocks

    The entry blocks leave the scan path with the private object set up
    and its argument cleared. The rule below proves that path for the
    entry rule. It runs the scanner, finishes each early return, and
    hands a word that starts with a dash to the caller's option choice.
    The caller lends the argument vector, the stream for reports, the
    resource G and the string "--" that the scanner compares against. *)

(** A caller who looks for the next word must handle two outcomes, and
    this lemma asks for nothing else. After an early return, the caller
    gets the index, the bad option, the argument and its evidence, and
    the cursor. It also gets a wand that packs these back into a session
    over the permuted vector. A word that starts with a dash goes to the
    option choice at L291, with the whole object, the permuted vector,
    the setup's environment and the pointer that the scanner stored. *)
Lemma entry_scan_ret ks n av ar p os lo li lonly b r ps j (G : iProp Σ) pdd sdd se sereg fp Φ :
  avoids ks idle_names = true -> avoids ks scan_end_names = true -> incl entry_scan_keys ks ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  Z.of_nat (List.length ps) = n ->
  word_string DfracDiscarded pdd sdd -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((∀ s s' ps' x i' a', ⌜entry_state s s' /\ gs_ind s = j /\ Permutation ps ps' /\
        scan_ret_case n (gs_ind s') (gs_order s') ps' x i' a'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
         getopt_session b r av ar ps' i') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x))) ∧
   (∀ e' s s' w ps' i' f' l',
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
        {{ Φ }})) -∗
  entry_scan_exit n av ar p os lo li lonly b r ps j G Φ.
Proof.
  intros Hki Hks Hin Hg Hdd Hlen. iIntros "#Hdd Hsl Hsc Ha Hcl #Hs HK".
  iIntros (e0 s s' (Hst & Henv & Hj & Hini & Hord & Hbd & Harg & Hix & Hb & Hal & Hend & Hr & Hav & Hala & Hda & Hra))
    "Hl Hi He Hoo Hab Hin1 Hcur Ho Hf Hla #Hc HG".
  pose proof (GetoptEntryScan.entry_scan_env _ _ _ _ _ _ _ _ _ Henv) as (H0 & H2 & H12 & Hc0 & Hc1 & Hc2).
  pose proof Hbd as Hbd'. unfold getopt_bounds in Hbd'.
  iEval (rewrite Harg) in "Hab". iEval (rewrite Hini) in "Hin1".
  iApply (GetoptScan.wp_getopt_scan ks e0 (TAtom "L83") n (gs_ind s') (gs_order s') (gs_first s') (gs_last s') null
            b r av ar ps pdd sdd with "Hl Hi Hab Ho Hf Hla Ha Hcl Hs Hdd [-]"); try (assumption || lia).
  iSplit; [|iSplit; [|iSplit]].
  - iIntros (e' fr ps' i' f' l' (Hp & _ & Hfl & Hli & ->)) "Hl Hi Hab Ho Hf Hla Ha Hcl #Hs'".
    assert (Hlen' : Z.of_nat (List.length ps') = n) by (rewrite -(Permutation_length Hp); exact Hlen).
    step. iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt 4294967295)); [reflexivity | reflexivity |].
    iNext. iDestruct "HK" as "[HK _]".
    iApply ("HK" $! s s' ps' 4294967295 (if f' =? l' then n else f') null
              with "[%] Hl Hi Hoo Hab Hcur [He Hin1 Ho Hf Hla] Hsl Hsc Ha Hcl Hs' HG []").
    + split_and!; [exact Hst | exact Hj | exact Hp |]. left. split_and!; [reflexivity | reflexivity |].
      exists f', l'. split_and!; lia.
    + iIntros "Hl Hi Hoo Hab Hcur".
      iApply (scan_session with "Hc Hl Hi He Hoo Hab Hin1 Hcur Ho Hf Hla");
        rewrite ?Hlen'; try lia; destruct (Z.eqb_spec f' l'); lia.
    + iApply arg_cap_null.
  - iIntros (e' ps' i' f' l' (Hp & _ & Hfl & Hli & Hii & Ho0)) "Hl Hi Hab Ho Hf Hla Ha Hcl #Hs'".
    assert (Hlen' : Z.of_nat (List.length ps') = n) by (rewrite -(Permutation_length Hp); exact Hlen).
    step. iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt 4294967295)); [reflexivity | reflexivity |].
    iNext. iDestruct "HK" as "[HK _]".
    iApply ("HK" $! s s' ps' 4294967295 i' null
              with "[%] Hl Hi Hoo Hab Hcur [He Hin1 Ho Hf Hla] Hsl Hsc Ha Hcl Hs' HG []").
    + split_and!; [exact Hst | exact Hj | exact Hp |]. right. left. split_and!; first [reflexivity | lia].
    + iIntros "Hl Hi Hoo Hab Hcur".
      iApply (scan_session with "Hc Hl Hi He Hoo Hab Hin1 Hcur Ho Hf Hla"); rewrite ?Hlen'; lia.
    + iApply arg_cap_null.
  - iIntros (e' ps' i' f' l' (Hp & _ & Hfl & Hli & Hii & Ho0)) "Hl Hi Hab Ho Hf Hla Ha Hcl #Hs'".
    assert (Hlen' : Z.of_nat (List.length ps') = n) by (rewrite -(Permutation_length Hp); exact Hlen).
    unfold getopt_blk318; cbn [b_jump].
    iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt 1)); [reflexivity | reflexivity |].
    iNext. iDestruct "HK" as "[HK _]".
    iApply ("HK" $! s s' ps' 1 (i' + 1) (nth (Z.to_nat i') ps' null)
              with "[%] Hl Hi Hoo Hab Hcur [He Hin1 Ho Hf Hla] Hsl Hsc Ha Hcl Hs' HG []").
    + split_and!; [exact Hst | exact Hj | exact Hp |]. right. right. split_and!; [reflexivity | exact Ho0 |].
      exists i'. split_and!; first [reflexivity | lia].
    + iIntros "Hl Hi Hoo Hab Hcur".
      iApply (scan_session with "Hc Hl Hi He Hoo Hab Hin1 Hcur Ho Hf Hla"); rewrite ?Hlen'; lia.
    + by iApply arg_cap_nth.
  - iIntros (e' w ps' i' f' l' (Hp & Hk & Hfl & Hli & Hii & H0w & H1w & H100)) "Hws Hl Hi Hab Ho Hf Hla Ha Hcl #Hs'".
    pose proof (GetoptEntryScan.entry_env_keeps ks e0 e' _ _ _ _ _ _ _ _ Hk Hin Henv) as Henv'.
    assert (Hlen' : Z.of_nat (List.length ps') = n) by (rewrite -(Permutation_length Hp); exact Hlen).
    destruct (lookup_lt_is_Some_2 ps' (Z.to_nat i')) as [q Hq]; [lia|].
    iDestruct "HK" as "[_ HK]".
    iApply ("HK" $! e' s s' w ps' i' f' l' with "[%] Hws Hl Hi He Hoo Hab Hin1 Hcur Ho Hf Hla Hc Hsl Hsc Ha Hcl Hs' HG").
    rewrite (nth_lookup_Some _ _ _ _ Hq). split_and!; first [assumption | lia].
Qed.

(** ## The whole entry of a call

    A caller of the parser wants one rule for a whole call. The rule
    below joins the scan above with the resumed cluster of the last file.
    It covers a call from its start up to every early return and every
    short return. The caller still owes the option choice at L291 and the
    form W;. *)

(** Every call of the parser either returns here or stops where the
    caller takes over. It returns after a scan that finds no option, or
    after one character of a cluster. It stops early at the option choice
    or at the form W;, and the caller proves those two parts. Every
    return gives the copied fields, the evidence for the argument and a
    wand that restores the session. A return after a resumed character
    also gives the string of the word. *)
Lemma wp_getopt_entry_scan_char_ws ks ks2 ks3 cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) T fp dom
    se sereg mid mid' pdd sdd Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  avoids ks3 idle_names = true -> avoids ks3 scan_end_names = true -> incl entry_scan_keys ks3 ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  call_frame glibc_getopt_internal_r
    [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] = Some cf ->
  GetoptInitialize.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
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
   (∀ e' s s' w ps' i' f' l',
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
        {{ Φ }}) ∧
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
Proof.
  intros Hks Hkin Hop Hrq Hdg Hrt Hinc Hki3 Hks3 Hin3 Hgc Hdd Hcf Hget Hpenv Hg Hgn Hdiag Hse Hmid' Hmid Hlen Hn
    Hse0 Hsea Hsee Hser.
  iIntros "Hpre #Hos HG Hsl Hsc Ha Hcl #Hs #Hdd HK".
  iApply (wp_getopt_entry_char_ws ks ks2 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom se sereg mid mid' Φ
            with "Hpre Hos HG Hsl Hsc Ha Hcl Hs [HK]"); try assumption.
  iSplit.
  - iIntros "Hsl Hsc Ha Hcl".
    iApply (entry_scan_ret ks3 n av ar p os lo li lonly b r ps j G pdd sdd se sereg fp Φ
              with "Hdd Hsl Hsc Ha Hcl Hs [HK]"); try assumption.
    iSplit; [iDestruct "HK" as "[H _]"; iExact "H" | iDestruct "HK" as "(_ & H & _)"; iExact "H"].
  - iSplit; [iDestruct "HK" as "(_ & _ & H & _)"; iExact "H" | iDestruct "HK" as "(_ & _ & _ & H)"; iExact "H"].
Qed.

(** The same call serves a caller that needs no string of the word. *)
Lemma wp_getopt_entry_scan_char ks ks2 ks3 cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) T fp dom
    se sereg mid mid' pdd sdd Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  avoids ks3 idle_names = true -> avoids ks3 scan_end_names = true -> incl entry_scan_keys ks3 ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  call_frame glibc_getopt_internal_r
    [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] = Some cf ->
  GetoptInitialize.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
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
   (∀ e' s s' w ps' i' f' l',
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
        {{ Φ }}) ∧
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
Proof.
  intros. iIntros "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd HK".
  iApply (wp_getopt_entry_scan_char_ws ks ks2 ks3 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom se sereg mid mid' pdd sdd Φ with "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd");
    try eassumption.
  iSplit; [iDestruct "HK" as "[H _]"; iExact "H"|].
  iSplit; [iDestruct "HK" as "(_ & H & _)"; iExact "H"|].
  iSplit; [iDestruct "HK" as "(_ & _ & H & _)"; iExact "H"|].
  iDestruct "HK" as "(_ & _ & _ & H)". iIntros (s q sq k0 x i' oo' a' c' Hc) "_".
  iApply ("H" $! s q sq k0 x i' oo' a' c' with "[%]"). exact Hc.
Qed.

End entry_scan_ret.
