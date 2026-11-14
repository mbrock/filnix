From Glibc Require Import GlibcProgram.
(** A word that starts with two dashes, such as "--name=x", goes to
    glibc's long-option parser with the cursor past the dashes. The
    getopt wrapper then copies the private index, the bad-option field
    and the argument into the public variables, so the return must hand
    over those fields with the evidence that the argument is usable. The
    next call needs the session back. This file runs that call through
    the existing rule for it, adds the evidence for the argument, and
    gives the caller a wand that restores the session. It then proves
    the exit for such a word after the scan. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec GetoptLongMissOnly
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint GetoptLongAmbItem GetoptLongAmbList
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch GetoptLongSession GetoptLongDash GetoptLongCap
  GetoptShortCap GetoptColon GetoptEntry GetoptEntryScan GetoptScanChoice GetoptCharRet GetoptEntryChar GetoptScanChar.
From Glibc Require GetoptLongDash GetoptLongCap GetoptShortCap GetoptEntryScan GetoptScanChar FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongCall GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongPfxAlloc GetoptLongSession GetoptLongStore GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The ways the long-option parser returns

    The parser moves the index by at most two words, and by two only when
    a word was left. It leaves the cursor cleared, where it was, or at
    the end of the current string s at cur. It keeps the argument a, or
    points it after the equals sign of s, or at the next word. A return
    of -1 either leaves the cursor and index alone or comes from a table
    entry that stores a flag. This is the fact part of the parser's
    return state, without its resources. *)
Definition plo_ret_case (ps : list ptr) (i n : Z) (cur : ptr) (s : list Z) (a : ptr) (os : list lopt)
    (x i' : Z) (a' c' : ptr) : Prop :=
  ((i <= i' <= i + 1 \/ (i' = i + 2 /\ i + 1 < n)) /\
   (c' = null \/ (c' = cur /\ i' = i) \/ c' = ptr_add cur (Z.of_nat (List.length s))) /\
   (a' = a \/ a' = ptr_add cur (Z.of_nat (eq_len s) + 1) \/ a' = nth (Z.to_nat (i + 1)) ps null) /\
   0 <= x < 2 ^ 32 /\ (x = 4294967295 -> (c' = cur /\ i' = i) \/
     exists y, y ∈ os /\ lo_flag y = null /\ lo_val y mod 2 ^ 32 = 4294967295))%Z.

(** The word "--" alone leaves the empty string after the dashes, so the
    cursor there already points at the terminator. *)
Lemma dash_ret_ctl_empty : drop 2 [45; 45] = [] /\ Z.of_nat (List.length (take 2 [45; 45])) = 2.
Proof. split; reflexivity. Qed.

Import GetoptLongCall GetoptLongSession GetoptLongBody GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongStore
  GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongCap GetoptShortCap GetoptExchange GetoptInitialize
  GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section dash_ret.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance dashret_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The call for a word with two dashes

    The wrapper must read the fields that the parser wrote, so their
    values cannot stay hidden inside a session. The rule below runs the
    call through the existing rule and keeps those fields in the open.
    The caller lends what that rule needs: the strings, the option table,
    the flags, the longind cell and the allocator resource M. The entry
    blocks cleared the argument, so it starts out null. *)

(** A call for a word with two dashes is safe, and it hands back what
    the wrapper and the next call need. The word sq sits at index i, and
    the call returns the parser's answer x. The caller gets the fields
    that the parser wrote and the proof that the new argument can be
    read. It also gets a way to turn those fields back into a session,
    and every resource it lent. *)
Lemma wp_getopt_dash_ret e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq n lonly pe i oo b r li er ord fst lst Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
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
  ps !! Z.to_nat i = Some q -> sbyte sq 0 = 45 -> sbyte sq 1 = 45 ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 null -∗ int_cell b 24 1 -∗
  pcell b 32 (ptr_add q 2) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ x i' oo' a' c', ⌜plo_ret_case ps i n (ptr_add q 2) (drop 2 sq) null os x i' a' c'⌝ -∗
     live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
        getopt_session b r av ar ps i') -∗
     live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
     Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L342") long_call long_jump)) : gexpr) {{ Φ }}.
Proof.
  intros Hgp H0 H2 H1 H6 H8 H10 H12 H3 Hstr Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3
    Hmid4 Hfl Hos Hpe Hlo Hq Hq0 Hq1 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser Hord Hfst Hlst.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli HK".
  assert (H2l : (1 < List.length sq)%nat) by (apply sbyte_in_len; lia).
  assert (Hl2 : Z.of_nat (List.length (take 2 sq)) = 2) by (rewrite length_take_le; lia).
  iAssert (word_string DfracDiscarded (ptr_add q 2) (drop 2 sq)) as "#Hws".
  { rewrite -Hl2. iApply word_string_suffix. by rewrite take_drop. }
  iApply (GetoptLongDash.wp_getopt_long_dash e G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo
    os F pfx pxs po so q sq (ptr_add q 2) (drop 2 sq) n lonly pe i oo null b r li
    with "Ht Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli"); try (assumption || lia).
  iIntros (x) "Hres".
  iDestruct (plo_res_capped_null with "Hws Hs Hres") as "Hres".
  iDestruct "Hres" as (i' oo' a' c') "(Hl & Hib & Hoob & Hab & Hcur & Ha & Hcl & HG & HF & HM & Hli & Hcap & %Hra' & %Hp)".
  pose proof Hp as (Hi' & Hc' & _ & _ & _).
  iApply ("HK" $! x i' oo' a' c' with "[%] Hl Hib Hoob Hab Hcur [Her Hini Hor Hfi Hla] Ha Hcl HG HF HM Hli [Hcap]");
    [exact Hp | | by iSplitL "Hcap"].
  iIntros "Hl Hib Hoob Hab Hcur".
  set (s0 := mkGetoptState i er oo null 1 (ptr_add q 2) ord fst lst).
  iApply (GetoptLongSession.long_session b r av ar ps s0 i' oo' a' c' (drop 2 sq)
    with "[] Hws Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla");
    try (unfold getopt_bounds; cbn; lia); try (cbn; lia); try reflexivity; try exact Hc'.
  unfold GetoptState.getopt_cursor. unfold s0. cbn [gs_next gs_last gs_ind]. destruct (drop 2 sq) as [|t0 t] eqn:Ht0.
  - iRight. iLeft. iExact "Hws".
  - iRight. iRight. iExists q, (take 2 sq), (drop 2 sq). iSplit; [iPureIntro|].
    + rewrite Ht0. split; [lia|]. split; [by apply dash_nth_error|]. split; [discriminate|].
      split; [by rewrite Hl2|lia].
    + by rewrite take_drop.
Qed.

(** ## The exit after the scan

    When the scan finds a word with two dashes, the choice sends it to
    the call above. The lemma below proves that exit of the scan file for
    such a word. The caller lends the parser's own resources openly, and
    it gets them back with every return. *)

(** A shared view of the stream's liveness can be copied. *)
Local Instance dashret_liveq_persistent b0 reg : Persistent (liveq DfracDiscarded b0 reg).
Proof. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance dashret_pcellq_persistent b0 o x : Persistent (pcellq DfracDiscarded b0 o x).
Proof. unfold pcellq. apply _. Qed.

(** After the scan, a word with two dashes goes to the parser, and the
    caller must then deal with whatever the parser returns. The word is
    at index i' of the reordered vector. The string after its dashes is
    drop 2 w, and it may be empty. The caller lends the table los, the
    flags F, the longind cell, the resource M and the parser's rules. *)
Lemma scan_dash_exit ks4 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 pfx pxs los F Φ :
  incl entry_scan_keys ks4 ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z ->
  0 <= lonly < 2 ^ 32 -> n < 2 ^ 31 - 1 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ s s' w ps' i' f' l' x i'' oo' a' c',
     ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ sbyte w 1 = 45 /\
       plo_ret_case ps' i' n (ptr_add (nth (Z.to_nat i') ps' null) 2) (drop 2 w) null los x i'' a' c'⌝ -∗
     live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     (live b r -∗ int_cell b 0 i'' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
        getopt_session b r av ar ps' i'') -∗
     liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
     arg_cap a' -∗ Φ (Ret (WInt x))) -∗
  ∀ e' e1 s s' w ps' i' f' l',
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
        {{ Φ }}.
Proof.
  intros Hin4 Hgp Hstr Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3 Hmid4 Hfl Hos
    Hlo Hn Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hos HF HM Hli HK".
  iIntros (e' e1 s s' w ps' i' f' l' (Hfacts & Henv & H100 & Hk1 & H45))
    "#Hws Hl Hi He Hoo Hab Hini Hcur Ho Hf Hla #Hsl #Hsc Ha Hcl #Hs HG".
  pose proof (GetoptEntryScan.entry_env_keeps ks4 e' e1 _ _ _ _ _ _ _ _ Hk1 Hin4 Henv)
    as (H0 & H2 & H6 & H8 & H10 & H12 & Hpr1 & Hpr3 & _).
  pose proof Hfacts as (Hst & Hj & Hini1 & Hord & Harg & Hp & Hlen & Hfl' & Hli' & Hii & Hw0 & Hw1 & Hb & Hal & Hend &
    Hr & Hav & Hala & Hda & Hra).
  destruct (lookup_lt_is_Some_2 ps' (Z.to_nat i')) as [q Hq]; [lia|].
  assert (Hnq : ps' !! Z.to_nat i' = Some (nth (Z.to_nat i') ps' null)) by (by rewrite (nth_lookup_Some _ _ _ _ Hq)).
  iDestruct "He" as "[%Herr0 He]". rewrite (GetoptScanChar.entry_state_err _ _ Hst) in Herr0.
  iDestruct (ws_suffix p os (opt_skip os) (GetoptColon.opt_skip_le os) with "Hos") as "#Hpo".
  iApply (wp_getopt_dash_ret e1 G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps' lo los F pfx pxs
            (ptr_add p (Z.of_nat (opt_skip os))) (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w n lonly
            (print_errors os (gs_err s)) i' (gs_opt s') b r li (gs_err s') (gs_order s') f' l' Φ
            with "Ht Hws Hpo Hpfx Hsl Hsc Hl Hi [He] Hoo Hab Hini Hcur Ho Hf Hla Ha Hcl Hs HG HF HM Hli [HK]");
    try (assumption || lia || exact (print_errors_range os (gs_err s) Herr0)).
  { rewrite (GetoptScanChar.entry_state_err _ _ Hst). by iSplit. }
  iIntros (x i'' oo' a' c' Hc) "Hl Hi Hoo Hab Hcur Hw Ha Hcl HG HF HM Hli Hca".
  iApply ("HK" $! s s' w ps' i' f' l' x i'' oo' a' c'
            with "[%] Hl Hi Hoo Hab Hcur Hw Hsl Hsc Ha Hcl Hs HG HF HM Hli Hca").
  exact (conj Hfacts (conj H45 Hc)).
Qed.

End dash_ret.
