From Glibc Require Import GlibcProgram.
(** A call of glibc's getopt either resumes a group of short options or
    scans for the next word, and the scan sends the word down one of
    several paths. Earlier files proved each path up to the point where
    it handed control to another one. This file joins those paths into
    one rule for the call, from its entry to its returns. The caller
    still says what each kind of return means, because the getopt
    wrapper copies different fields after each. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrcmpCode StrchrnulLogic StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec GetoptLongMissOnly
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint GetoptLongAmbItem GetoptLongAmbList
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch GetoptLongSession GetoptLongDash GetoptLongSite GetoptLongCap GetoptDashRet GetoptLongOnlyRet GetoptLongOnlyShort GetoptWTail GetoptWOpt GetoptLongW GetoptWOptSession GetoptWRet GetoptWExit GetoptWExitRet GetoptIdlePath GetoptScanEnd GetoptEntryScanRet GetoptEntryPre GetoptKnownCap GetoptDiag GetoptReqTail GetoptShort GetoptOptArg GetoptShortRet
  GetoptShortCap GetoptColon GetoptEntry GetoptEntryScan GetoptScanChoice GetoptCharRet GetoptEntryChar GetoptScanChar.
From Glibc Require GetoptEntryScanRet GetoptIdlePath GetoptScanEnd GetoptWExit GetoptWExitRet GetoptLongOnlyShort GetoptWRet GetoptWOptSession GetoptLongOnlyRet GetoptCharRet GetoptLongSite GetoptDashRet GetoptLongDash GetoptLongCap GetoptShortCap GetoptEntryScan GetoptScanChar FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongCall GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongPfxAlloc GetoptLongSession GetoptLongStore GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptLongCall GetoptLongSite GetoptLongSession GetoptLongJoinMiss GetoptLongCap GetoptShortCap GetoptKnownCap
  GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic
  GetoptBytes GetoptArgv.

(** ## The names each block keeps

    Each block of the parser may assign some names and must keep others.
    The character step keeps the names below, which add the option table
    and the longind pointer to the ones it needs itself. Every other
    block keeps the names that the setup assigned. *)

(** The character step keeps these names before it reads the option string. *)
Definition call_char_keys : list name := char_ret_keys ++ [TAtom "v8"].
(** The option and return blocks after it keep these names. *)
Definition call_req_keys : list name := known_req_keys ++ [TAtom "v6"; TAtom "v8"].

(** The setup's names survive every block that the scan and the long
    paths run, because none of those blocks assigns them. *)
Lemma call_scan_keys : avoids entry_scan_keys idle_names = true /\ avoids entry_scan_keys scan_end_names = true /\
  avoids entry_scan_keys choice_names = true /\ avoids entry_scan_keys long_only_site_names = true /\
  avoids entry_scan_keys short_names = true.
Proof. split_and!; vm_compute; reflexivity. Qed.

(** This tactic proves a premise about a key list and leaves other goals alone. *)
Ltac call_keys :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- avoids _ _ = true => vm_compute; reflexivity
  | |- incl ?l ?l => apply incl_refl
  | |- incl _ _ => apply incl_appl, incl_refl
  | |- In _ _ => apply in_or_app; right; cbn [In]; repeat first [left; reflexivity | right]
  end.

Import ProgramAbbreviations.
Section call_parse.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance callparse_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A shared view of the stream's liveness can be copied. *)
Local Instance callparse_liveq_persistent b0 reg : Persistent (liveq DfracDiscarded b0 reg).
Proof. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance callparse_pcellq_persistent b0 o x : Persistent (pcellq DfracDiscarded b0 o x).
Proof. unfold pcellq. apply _. Qed.

(** ## The returns of a call

    The getopt wrapper treats each return differently, so the rule keeps
    them apart. The definition below lists nine kinds, in the order the
    paths are proved. They are the early returns of the scan, the two
    long paths, the long-only fallback and its W, a new group and its W,
    and a resumed group and its W. Every kind gives back the option
    table's flags, the resource M and the longind cell. *)

(** These are the nine kinds of return of a call, each as its own rule
    states it. *)
Definition call_parse_rets (n av : Z) (ar : region) (p : ptr) (os : list Z) (li : ptr) (lonly b : Z) (r : region)
    (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr) (los : list lopt) (F : list ptr)
    (M : iProp Σ) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  (∀ s s' ps' x i' a', ⌜entry_state s s' /\ gs_ind s = j /\ Permutation ps ps' /\
        scan_ret_case n (gs_ind s') (gs_order s') ps' x i' a'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
         getopt_session b r av ar ps' i') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))) ∧
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
     ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ sbyte w 1 = 45 /\
       plo_ret_case ps' i' n (ptr_add (nth (Z.to_nat i') ps' null) 2) (drop 2 w) null los x i'' a' c'⌝ -∗
     live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
        getopt_session b r av ar ps' i'') -∗
     liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
     arg_cap a' -∗ Φ (Ret (WInt x))) ∧
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
        x <> 4294967295 /\
        plo_ret_case ps' i' n (ptr_add (nth (Z.to_nat i') ps' null) 1) (drop 1 w) null los x i'' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      arg_cap a' -∗ Φ (Ret (WInt x))) ∧
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
      arg_cap a'' -∗ Φ (Ret (WInt x))) ∧
  (∀ s s' w ps' i' f' l' a',
     ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
       (a' = null \/ a' = ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) (Z.of_nat (eq_len (drop 1 w)) + 1) \/
        a' = nth (Z.to_nat (i' + 1)) ps' null)⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits b r av ar ps' los li F G M i' n 87 a' (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) ∧
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        char_ret_case ps' n i' (gs_opt s') (ptr_add (nth (Z.to_nat i') ps' null) 1) null (drop 1 w)
          (drop (opt_skip os) os) x i'' oo' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))) ∧
  (∀ s s' w ps' i' f' l', ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l'⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits b r av ar ps' los li F G M i' n 87 null (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) ∧
  (∀ s q sq k0, ⌜entry_resume_facts n av ar b r ps j s q sq k0⌝ -∗
     w_ret_exits b r av ar ps los li F G M j n 87 null (drop (opt_skip os) os) q sq k0 Φ) ∧
  (∀ s q sq k0 x i' oo' a' c',
      ⌜entry_resume_facts n av ar b r ps j s q sq k0 /\
        char_ret_case ps n j (gs_opt s) (gs_next s) null (drop k0 sq) (drop (opt_skip os) os) x i' oo' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a' -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))).

(** A caller that reads the argument needs more from some returns. In
    the form below, a long return also says which entry chose the
    argument. A long return and a short return also give the string of
    the word that the argument comes from. *)
Definition call_parse_rets_arg (n av : Z) (ar : region) (p : ptr) (os : list Z) (li : ptr) (lonly b : Z) (r : region)
    (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr) (los : list lopt) (F : list ptr)
    (M : iProp Σ) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  (∀ s s' ps' x i' a', ⌜entry_state s s' /\ gs_ind s = j /\ Permutation ps ps' /\
        scan_ret_case n (gs_ind s') (gs_order s') ps' x i' a'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 (gs_opt s') -∗ pcell b 16 a' -∗ pcell b 32 (gs_next s') -∗
         getopt_session b r av ar ps' i') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))) ∧
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
     ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ sbyte w 1 = 45 /\
       plo_ret_case ps' i' n (ptr_add (nth (Z.to_nat i') ps' null) 2) (drop 2 w) null los x i'' a' c' /\
       plo_arg_case ps' i' n (ptr_add (nth (Z.to_nat i') ps' null) 2) (drop 2 w) null los x i'' a'⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
        getopt_session b r av ar ps' i'') -∗
     liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
     arg_cap a' -∗ Φ (Ret (WInt x))) ∧
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
        x <> 4294967295 /\
        plo_ret_case ps' i' n (ptr_add (nth (Z.to_nat i') ps' null) 1) (drop 1 w) null los x i'' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      arg_cap a' -∗ Φ (Ret (WInt x))) ∧
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
      arg_cap a'' -∗ Φ (Ret (WInt x))) ∧
  (∀ s s' w ps' i' f' l' a',
     ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
       (a' = null \/ a' = ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) (Z.of_nat (eq_len (drop 1 w)) + 1) \/
        a' = nth (Z.to_nat (i' + 1)) ps' null)⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits b r av ar ps' los li F G M i' n 87 a' (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) ∧
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
      ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\
        char_ret_case ps' n i' (gs_opt s') (ptr_add (nth (Z.to_nat i') ps' null) 1) null (drop 1 w)
          (drop (opt_skip os) os) x i'' oo' a' c'⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps' i'') -∗
      liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ arg_cap a' -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))) ∧
  (∀ s s' w ps' i' f' l', ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l'⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits_arg b r av ar ps' los li F G M i' n 87 null (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) ∧
  (∀ s q sq k0, ⌜entry_resume_facts n av ar b r ps j s q sq k0⌝ -∗ word_string DfracDiscarded q sq -∗
     w_ret_exits_arg b r av ar ps los li F G M j n 87 null (drop (opt_skip os) os) q sq k0 Φ) ∧
  (∀ s q sq k0 x i' oo' a' c',
      ⌜entry_resume_facts n av ar b r ps j s q sq k0 /\
        char_ret_case ps n j (gs_opt s) (gs_next s) null (drop k0 sq) (drop (opt_skip os) os) x i' oo' a' c'⌝ -∗
      word_string DfracDiscarded q sq -∗ live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a' -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))).

(** A caller that handles the nine kinds without the relation also
    handles them with it. *)
Lemma call_parse_rets_weaken n av ar p os li lonly b r ps j (G : iProp Σ) se sereg fp los F (M : iProp Σ) Φ :
  call_parse_rets n av ar p os li lonly b r ps j G se sereg fp los F M Φ ⊢
  call_parse_rets_arg n av ar p os li lonly b r ps j G se sereg fp los F M Φ.
Proof.
  iIntros "H". unfold call_parse_rets, call_parse_rets_arg.
  iSplit; [iDestruct "H" as "(H & _)"; iExact "H"|].
  iSplit.
  { iDestruct "H" as "(_ & H & _)". iIntros (s s' w ps' i' f' l' x i'' oo' a' c' (Hf & H45 & Hc & _)) "_".
    iApply ("H" $! s s' w ps' i' f' l' x i'' oo' a' c' with "[%]"). exact (conj Hf (conj H45 Hc)). }
  iSplit; [iDestruct "H" as "(_ & _ & H & _)"; iExact "H"|].
  iSplit; [iDestruct "H" as "(_ & _ & _ & H & _)"; iExact "H"|].
  iSplit; [iDestruct "H" as "(_ & _ & _ & _ & H & _)"; iExact "H"|].
  iSplit.
  { iDestruct "H" as "(_ & _ & _ & _ & _ & H & _)". iIntros (s s' w ps' i' f' l' x i'' oo' a' c' Hc) "_".
    iApply ("H" $! s s' w ps' i' f' l' x i'' oo' a' c' with "[%]"). exact Hc. }
  iSplit.
  { iDestruct "H" as "(_ & _ & _ & _ & _ & _ & H & _)". iIntros (s s' w ps' i' f' l' Hf) "Hws Hs".
    iApply w_ret_exits_weaken. iApply ("H" $! s s' w ps' i' f' l' with "[%] Hws Hs"). exact Hf. }
  iSplit.
  { iDestruct "H" as "(_ & _ & _ & _ & _ & _ & _ & H & _)". iIntros (s q sq k0 Hf) "_".
    iApply w_ret_exits_weaken. iApply ("H" $! s q sq k0 with "[%]"). exact Hf. }
  iDestruct "H" as "(_ & _ & _ & _ & _ & _ & _ & _ & H)". iIntros (s q sq k0 x i' oo' a' c' Hc) "_".
  iApply ("H" $! s q sq k0 x i' oo' a' c' with "[%]"). exact Hc.
Qed.

(** ## One rule for the call

    The rule below starts at the call of the parser and ends at one of
    the nine kinds of return. It runs the entry, the scan and the option
    choice through the dispatch rule, and it finishes each path that the
    dispatch leaves open with the rule for that path. The caller lends
    the long-option resources once, and every path gets them, because
    only one path runs. *)

(** A call of the parser is safe, and it ends in one of the returns of
    [call_parse_rets_arg]. The count of words must stay below 2^31, and
    the option table must not use -1 as a value with a null flag. *)
Lemma wp_getopt_call_parse_arg cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) T fp dom se sereg mid mid'
    pdd sdd (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 los F pfx7 pxs7 pfx0 pxs0 Φ :
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
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx7 ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx0 ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
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
  getopt_entry_pre b r av ar ps j -∗ word_string DfracDiscarded p os -∗ G -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  opt_table lo los -∗ word_string DfracDiscarded pfx7 pxs7 -∗ word_string DfracDiscarded pfx0 pxs0 -∗
  flags_own F -∗ M -∗ longind_own li -∗
  call_parse_rets_arg n av ar p os li lonly b r ps j G se sereg fp los F M Φ -∗
  WP (ERun cf : gexpr) {{ Φ }}.
Proof.
  intros Hgc Hdd Hcf Hget Hpenv Hg Hgn Hdiag Hse Hmid' Hmid Hgp Hp7 Hp0 Hcut Hmal Hset Hlrule Hfree Hgsn Hgl
    H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hneg Hlo Hlen Hn Hse0 Hsea Hsee Hser.
  iIntros "Hpre #Hos HG #Hsl #Hsc Ha Hcl #Hs #Hdd #Ht #Hp7 #Hp0 HF HM Hli HK".
  unfold call_parse_rets_arg.
  iApply (wp_getopt_entry_dispatch_ws call_char_keys call_req_keys entry_scan_keys entry_scan_keys cf n av ar p os lo li
            lonly pc penv b r ps j G T fp dom se sereg mid mid' pdd sdd Φ
            with "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd [-]"); try call_keys; try assumption.
  iSplit.
  { iDestruct "HK" as "(H1 & _)". iIntros (s s' ps' x i' a' Hc) "Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl Hs' HG Hca".
    iApply ("H1" with "[%] Hl Hi Ho Hab Hcur Hw Hsl Hsc Ha Hcl Hs' HG Hca HF HM Hli"). exact Hc. }
  iSplit; [iSplit|].
  - unfold scan_long_exits. iSplit.
    + iDestruct "HK" as "(_ & H2 & _)".
      iApply (scan_dash_exit_arg entry_scan_keys n av ar p os lo li lonly b r ps j G T fp dom M se sereg
                f138 f139 f140 f141 lmid mid3 mid4 pdd sdd los F Φ with "Ht Hdd Hos HF HM Hli H2");
        try call_keys; try assumption.
    + iApply (scan_long_only_exit entry_scan_keys entry_scan_keys n av ar p os lo li lonly b r ps j G T fp dom M
                se sereg f138 f139 f140 f141 lmid mid3 mid4 pfx7 pxs7 los F Φ with "Ht Hp7 Hos HF HM Hli [HK]");
        try call_keys; try assumption.
      iSplit; [iDestruct "HK" as "(_ & _ & H3 & _)"; iExact "H3" |].
      iApply (long_only_fallback_char entry_scan_keys entry_scan_keys call_char_keys call_req_keys n av ar p os lo li
                lonly b r ps j G T fp dom se sereg mid mid' F M Φ with "Hos [HK]"); try call_keys; try assumption.
      unfold long_only_short_exits. iSplit; [|iDestruct "HK" as "(_ & _ & _ & H4 & _)"; iExact "H4"].
      iDestruct "HK" as "(_ & _ & _ & _ & H5 & _)".
      iApply (long_only_w_ret call_char_keys call_req_keys n av ar p os lo li lonly b r ps j G T fp dom M se sereg mid
                f138 f139 f140 f141 lmid mid3 mid4 los F pfx0 pxs0 Φ with "Ht Hp0 Hos H5"); try call_keys; try assumption.
  - unfold scan_char_exits. iSplit.
    + iDestruct "HK" as "(_ & _ & _ & _ & _ & _ & H7 & _)".
      iApply (scan_w_ret_arg call_char_keys call_req_keys n av ar p os lo li lonly b r ps j G T fp dom M se sereg mid
                f138 f139 f140 f141 lmid mid3 mid4 los F pfx0 pxs0 Φ with "Ht Hp0 Hos HF HM Hli H7");
        try call_keys; try assumption.
    + iDestruct "HK" as "(_ & _ & _ & _ & _ & H6 & _)".
      iIntros (s s' w ps' i' f' l' x i'' oo' a' c' Hc) "Hws Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl Hs' HG Hca".
      iApply ("H6" with "[%] Hws Hl Hi Ho Hab Hcur Hw Hsl Hsc Ha Hcl Hs' HG Hca HF HM Hli"). exact Hc.
  - iSplit.
    + iDestruct "HK" as "(_ & _ & _ & _ & _ & _ & _ & H8 & _)".
      iApply (entry_w_ret_arg call_char_keys call_req_keys n av ar p os lo li lonly b r ps j G T fp dom M se sereg mid
                f138 f139 f140 f141 lmid mid3 mid4 los F pfx0 pxs0 Φ with "Ht Hp0 Hos Hsl Hsc Hs HF HM Hli H8");
        try call_keys; try assumption.
    + iDestruct "HK" as "(_ & _ & _ & _ & _ & _ & _ & _ & H9)".
      iIntros (s q sq k0 x i' oo' a' c' Hc) "Hwq Hl Hi Ho Hab Hcur Hw Ha Hcl HG Hca".
      iApply ("H9" with "[%] Hwq Hl Hi Ho Hab Hcur Hw Ha Hcl HG Hca HF HM Hli"). exact Hc.
Qed.

(** Callers that need neither the entry nor the string use this rule. *)
Lemma wp_getopt_call_parse cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) T fp dom se sereg mid mid'
    pdd sdd (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 los F pfx7 pxs7 pfx0 pxs0 Φ :
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
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx7 ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx0 ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
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
  getopt_entry_pre b r av ar ps j -∗ word_string DfracDiscarded p os -∗ G -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  opt_table lo los -∗ word_string DfracDiscarded pfx7 pxs7 -∗ word_string DfracDiscarded pfx0 pxs0 -∗
  flags_own F -∗ M -∗ longind_own li -∗
  call_parse_rets n av ar p os li lonly b r ps j G se sereg fp los F M Φ -∗
  WP (ERun cf : gexpr) {{ Φ }}.
Proof.
  intros. iIntros "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd Ht Hp7 Hp0 HF HM Hli HK".
  iApply (wp_getopt_call_parse_arg cf n av ar p os lo li lonly pc penv b r ps j G T fp dom se sereg mid mid' pdd sdd M f138 f139 f140 f141 lmid mid3 mid4 los F pfx7 pxs7 pfx0 pxs0 Φ with "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd Ht Hp7 Hp0 HF HM Hli");
    try eassumption.
  iApply call_parse_rets_weaken. iExact "HK".
Qed.

End call_parse.
