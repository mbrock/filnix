From Glibc Require Import Unit_string_strchr_os Unit_string_strchrnul_os Unit_string_strcmp_os Unit_string_strncmp_os.
From Glibc Require Import GlibcProgram.
(** A program that calls getopt_long reads optarg after each option. For
    an option that requires an argument, it treats optarg as a string.
    The safety rule for the call only says that optarg is live, which is
    not enough to read it. This file proves that the parser leaves a
    readable string there whenever it returns the code of an option that
    requires an argument. The code must name such an option both in the
    option string and in the table of long options. *)

From Glibc Require Import GlibcTactics OsTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrnulLogic StrlenLogic StrlenWord
  StrcmpBits StrncmpLogic
  GetoptModule GetoptState ByteRead GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore
  GetoptLongPfxCmp GetoptLongPfxAlloc GetoptLongAmbTail
  GetoptLongJoinMiss GetoptLongSite GetoptWExit GetoptCallParse GetoptLongWrapper GetoptWrapParse
  GetoptShortCap GetoptCharRet.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptLongSite GetoptLongJoinMiss GetoptShortCap GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic ByteRead GetoptArgv.

(** ## Codes that carry a string

    Some return values always come with an argument. A value c is such
    a code when three facts hold. No error, fallback or nonoption return
    uses c. Every letter of the option string with code c is followed by
    exactly one colon. Every table entry with value c and no flag has
    the argument kind 1. The definition below states these facts about
    the option string so and the table los. *)

(** The code c of a getopt return always comes with a readable argument. *)
Definition str_code (so : list Z) (los : list lopt) (c : Z) : Prop :=
  c <> 4294967295 /\ c <> 63 /\ c <> 58 /\ c <> 0 /\ c <> 1 /\
  (forall k, (k < List.length so)%nat -> sbyte so k <> 58 -> sbyte so k <> 59 -> chr_w (sbyte so k) = c ->
     sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58) /\
  (forall y, y ∈ los -> lo_flag y = null -> lo_val y mod 2 ^ 32 = c -> lo_has y = 1).

(** A short option with that code takes its argument from the rest of
    the word, which is not empty, or from the next word, which exists. *)
Lemma char_code_arg ps n i oo cur a t so los x i' oo' a' c' c :
  str_code so los c -> char_ret_case ps n i oo cur a t so x i' oo' a' c' -> x = c ->
  (a' = ptr_add cur 1 /\ sbyte t 1 <> 0) \/ (a' = nth (Z.to_nat (i + 1)) ps null /\ i + 1 < n).
Proof.
  intros (Hn1 & H63 & H58 & _ & _ & Hso & _) Hc Hxc. subst c.
  destruct Hc as [(Hx & _) | (k & Hk & Hsk & Ht58 & Ht59 & H)]; [congruence|].
  assert (Hcode : forall y, x = chr_w y -> y = sbyte t 0 -> sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58).
  { intros y Hy ->. apply Hso; [exact Hk | congruence | congruence | congruence]. }
  destruct H as [(Hs1 & Hx & _) | [(Hs1 & Hs2 & Hx & _) | [(_ & _ & Ht1 & Hx & _ & _ & Ha & _) |
    [(_ & _ & _ & Hlt & Hx & _ & _ & Ha & _) | (_ & _ & _ & _ & Hx & _)]]]].
  - destruct (Hcode _ Hx eq_refl). congruence.
  - destruct (Hcode _ Hx eq_refl). congruence.
  - left. split; assumption.
  - right. split; assumption.
  - destruct (_ =? _); congruence.
Qed.

(** A long option with that code takes its argument after an equals
    sign in the word, or from the next word, which exists. *)
Lemma plo_code_arg ps i n cur s a so los x i' a' c :
  str_code so los c -> plo_arg_case ps i n cur s a los x i' a' -> x = c ->
  (a' = ptr_add cur (Z.of_nat (eq_len s) + 1) /\ sbyte s (eq_len s) = 61) \/
  (a' = nth (Z.to_nat (i + 1)) ps null /\ i + 1 < n).
Proof.
  intros (Hn1 & H63 & H58 & H0 & _ & _ & Hlo) Hc ->.
  destruct Hc as [? | [? | [? | [? | (y & Hy & Hf & Hv & Hl)]]]]; try congruence.
  pose proof (Hlo y Hy Hf (eq_sym Hv)) as Hh.
  destruct Hl as [(Heq & _ & _ & Ha) | [(_ & Hh1 & _) | (_ & _ & Hlt & _ & Ha)]].
  - left. split; assumption.
  - congruence.
  - right. split; assumption.
Qed.

(** The option string "g:t" and the table of hello's options make 103,
    the code of 'g', such a code. The table has four entries, and only
    the first one, with value 103, takes an argument. *)
Lemma str_code_g los :
  List.map (fun y => (lo_has y, lo_flag y, lo_val y)) los =
    [(1, null, 103); (0, null, 116); (0, null, 128); (0, null, 129)] ->
  str_code (drop (opt_skip [103; 58; 116]) [103; 58; 116]) los 103.
Proof.
  intros Hm. cbn. split_and!; try discriminate.
  - intros k Hk H58 H59 Hc. destruct k as [|[|[|k]]]; cbn in *; try lia; try (split; congruence).
    vm_compute in Hc. discriminate.
  - intros y Hy Hf Hv. apply list_elem_of_In in Hy.
    apply (in_map (fun y => (lo_has y, lo_flag y, lo_val y))) in Hy. rewrite Hm in Hy. cbn in Hy.
    destruct Hy as [Hy | [Hy | [Hy | [Hy | []]]]]; injection Hy as Hh _ Hval; try (symmetry; exact Hh);
      rewrite <- Hval in Hv; vm_compute in Hv; discriminate.
Qed.

Import ProgramAbbreviations.
Section long_str.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance longstr_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A shared view of the stream's liveness can be copied. *)
Local Instance longstr_liveq_persistent b0 reg : Persistent (liveq DfracDiscarded b0 reg).
Proof using Type. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance longstr_pcellq_persistent b0 o x : Persistent (pcellq DfracDiscarded b0 o x).
Proof using Type. unfold pcellq. apply _. Qed.
(** A shared view of the argument's object life can be copied. *)
Local Instance longstr_capq_persistent c reg : Persistent (live_capq DfracDiscarded c reg).
Proof using Type. destruct c; cbn; apply _. Qed.

(** ## Strings at the argument

    The argument is a suffix of a word or the next word of the vector.
    The lemmas below read a string at each of those places from the
    string of the word or from the strings of the vector. *)

(** The argument holds a string when the return has code c. *)
Definition arg_str (c x : Z) (a : ptr) : iProp Σ :=
  (if x =? c then ∃ s, word_string DfracDiscarded a s else True)%I.

(** The fact can be copied, so every return can keep it. *)
Local Instance arg_str_persistent c x a : Persistent (arg_str c x a).
Proof using Type. unfold arg_str. destruct (x =? c); apply _. Qed.

(** A return with another code needs no string. *)
Lemma arg_str_other c x a : x <> c -> ⊢ arg_str c x a.
Proof using Type. intros H. unfold arg_str. rewrite (proj2 (Z.eqb_neq x c) H). done. Qed.

(** A word of the vector below its length holds a string. *)
Lemma arg_str_next c x ps k : (k < List.length ps)%nat -> argv_strs ps ⊢ arg_str c x (nth k ps null).
Proof using Type.
  intros Hk. iIntros "Hs". unfold arg_str. destruct (x =? c); [|done].
  destruct (lookup_lt_is_Some_2 ps k Hk) as [q Hq]. rewrite (nth_lookup_Some _ _ _ _ Hq).
  iDestruct (big_sepL_lookup with "Hs") as (s) "Hw"; [exact Hq|]. by iExists s.
Qed.

(** The rest of a word after a byte that is not its end holds a string. *)
Lemma arg_str_one c x cur t : sbyte t 1 <> 0 ->
  word_string DfracDiscarded cur t ⊢ arg_str c x (ptr_add cur 1).
Proof using Type.
  intros Ht. iIntros "Hw". unfold arg_str. destruct (x =? c); [|done].
  pose proof (sbyte_in_len t 1 Ht). iExists (drop 1 t). iApply (ws_suffix cur t 1 with "Hw"). lia.
Qed.

(** The rest of a word after its equals sign holds a string, which may be
    empty. *)
Lemma arg_str_eq c x cur s : sbyte s (eq_len s) = 61 ->
  word_string DfracDiscarded cur s ⊢ arg_str c x (ptr_add cur (Z.of_nat (eq_len s) + 1)).
Proof using Type.
  intros He. iIntros "Hw". unfold arg_str. destruct (x =? c); [|done].
  assert (Hl : (eq_len s < List.length s)%nat) by (apply sbyte_in_len; lia).
  iExists (drop (S (eq_len s)) s). replace (Z.of_nat (eq_len s) + 1) with (Z.of_nat (S (eq_len s))) by lia.
  iApply (ws_suffix cur s (S (eq_len s)) with "Hw"). lia.
Qed.

(** A long return with code c leaves a string, given the word at the
    cursor and the strings of the vector. *)
Lemma plo_arg_str ps i n cur s a so los x i' a' c :
  str_code so los c -> plo_arg_case ps i n cur s a los x i' a' -> Z.of_nat (List.length ps) = n -> 0 <= i ->
  word_string DfracDiscarded cur s -∗ argv_strs ps -∗ arg_str c x a'.
Proof using Type.
  intros Hc Ha Hn Hi. iIntros "#Hw #Hs". destruct (decide (x = c)) as [Hx | Hx]; [|by iApply arg_str_other].
  destruct (plo_code_arg ps i n cur s a so los x i' a' c Hc Ha Hx) as [[-> He] | [-> Hlt]].
  - by iApply arg_str_eq.
  - iApply (arg_str_next with "Hs"). lia.
Qed.

(** A short return with code c leaves a string, given the word at the
    cursor and the strings of the vector. *)
Lemma char_arg_str ps n i oo cur a t so los x i' oo' a' c' c :
  str_code so los c -> char_ret_case ps n i oo cur a t so x i' oo' a' c' -> Z.of_nat (List.length ps) = n ->
  0 <= i -> word_string DfracDiscarded cur t -∗ argv_strs ps -∗ arg_str c x a'.
Proof using Type.
  intros Hc Ha Hn Hi. iIntros "#Hw #Hs". destruct (decide (x = c)) as [Hx | Hx]; [|by iApply arg_str_other].
  destruct (char_code_arg ps n i oo cur a t so los x i' oo' a' c' c Hc Ha Hx) as [[-> Ht] | [-> Hlt]].
  - by iApply arg_str_one.
  - iApply (arg_str_next with "Hs"). lia.
Qed.

(** ## Returns that keep the string

    The wrapper's return gives back the rest of the parser's state. The
    definition below adds the string fact to that rest, and the lemmas
    after it show that every kind of return supplies it. *)

(** This is what the wrapper gives back, together with the string fact
    for the code c. *)
Definition str_rest (b : Z) (r : region) (av : Z) (ar : region) (ps : list ptr) (G : iProp Σ) (F : list ptr)
    (M : iProp Σ) (li : ptr) (c x i' c' : Z) (a' : ptr) : iProp Σ :=
  wrap_rest b r av ar ps G F M li x i' c' a' ∗ arg_str c x a'.

(** Every path returns the same pieces and the string fact. *)
Lemma str_ret b r av ar ps ps' (G : iProp Σ) F (M : iProp Σ) li c x i' oo' a' c' :
  0 <= x < 2 ^ 32 -> Permutation ps ps' ->
  live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
  (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     getopt_session b r av ar ps' i') -∗
  live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
  arg_str c x a' -∗ wrap_post b r (str_rest b r av ar ps G F M li c) (Ret (WInt x)).
Proof using Type.
  intros Hx Hp. iIntros "Hl Hi Ho Hab Hcur Hw Ha Hcl #Hs HG HF HM Hli [[%ra #Hcap] %Hra] #Hstr".
  iExists x, i', oo', a', ra. iSplit; [iPureIntro; split_and!; [reflexivity | lia | lia | lia | lia] |].
  iSplitL "Hl"; [done|]. iSplitL "Hi"; [done|]. iSplitL "Ho"; [done|]. iSplitL "Hab"; [done|].
  iSplitR; [iExact "Hcap"|]. iSplitL; [|iExact "Hstr"]. iExists ps', c'.
  iSplit; [iPureIntro; split; [exact Hp | lia]|].
  iSplitL "Hcur"; [done|]. iSplitL "Hw"; [done|]. iSplitL "Ha"; [done|]. iSplitL "Hcl"; [done|].
  iSplitR; [done|]. iSplitL "HG"; [done|]. iSplitL "HF"; [done|]. iSplitL "HM"; [done|].
  iSplitL "Hli"; [done|]. iSplit; [by iExists ra | iPureIntro; lia].
Qed.

(** The three ends of the W option keep the string. The W sits at byte
    k0 of the word q, whose string the caller lends. *)
Lemma w_ret_exits_str b r av ar ps ps' los li F (G M : iProp Σ) i n cw a so q sq k0 c :
  Permutation ps ps' -> Z.of_nat (List.length ps') = n -> str_code so los c -> 0 <= i ->
  word_string DfracDiscarded q sq -∗ argv_strs ps' -∗
  w_ret_exits_arg b r av ar ps' los li F G M i n cw a so q sq k0
    (wrap_post b r (str_rest b r av ar ps G F M li c)).
Proof using Type.
  intros Hp Hn Hc Hi. iIntros "#Hq #Hs". unfold w_ret_exits_arg. iSplit; [|iSplit].
  - iIntros (x i' oo' a' c' (Hs1 & Hr & Ha)) "Hl Hi Ho Hab Hcur Hw Ha Hcl HG HF HM Hli Hca".
    pose proof (sbyte_in_len sq (S k0) Hs1).
    iDestruct (ws_suffix q sq (S k0) with "Hq") as "#Hw1"; [lia|].
    iApply (str_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca [ ]");
      [exact (plo_ret_x _ _ _ _ _ _ _ _ _ _ _ Hr) | exact Hp |].
    iApply (plo_arg_str _ _ _ _ _ _ _ _ _ _ _ _ Hc Ha Hn Hi with "Hw1 Hs").
  - iIntros (s2 x i' oo' a' c' (_ & _ & Hr & Ha)) "#Hw2 Hl Hi Ho Hab Hcur Hw Ha Hcl HG HF HM Hli Hca".
    iApply (str_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca [ ]");
      [exact (plo_ret_x _ _ _ _ _ _ _ _ _ _ _ Hr) | exact Hp |].
    iApply (plo_arg_str _ _ _ _ _ _ _ _ _ _ _ _ Hc Ha Hn ltac:(lia) with "Hw2 Hs").
  - iIntros "_ Hl Hi Ho Hab Hcur Hw Ha Hcl HG HF HM Hli Hca".
    destruct Hc as (_ & H63 & H58 & _).
    iApply (str_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca [ ]");
      [destruct (_ =? _); lia | exact Hp |].
    iApply arg_str_other. destruct (_ =? _); congruence.
Qed.

(** Each kind of return keeps the string fact. Only six kinds can
    happen when long-only mode is off, and each of them holds the string
    of the word that the argument comes from. *)
Lemma call_parse_rets_str n av ar p os li b r ps j (G : iProp Σ) se sereg fp los F (M : iProp Σ) c :
  Z.of_nat (List.length ps) = n -> str_code (drop (opt_skip os) os) los c -> argv_strs ps -∗
  call_parse_rets_arg n av ar p os li 0 b r ps j G se sereg fp los F M
    (wrap_post b r (str_rest b r av ar ps G F M li c)).
Proof using Type.
  intros Hn Hc. iIntros "#Hs0". unfold call_parse_rets_arg.
  iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
  - iIntros (s s' ps' x i' a' (_ & _ & Hp & Hr)) "Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl #Hs HG Hca HF HM Hli".
    iApply (str_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca [ ]");
      [exact (scan_ret_x _ _ _ _ _ _ _ Hr) | exact Hp |].
    iApply arg_str_other. destruct Hc as (? & _ & _ & _ & ? & _).
    destruct Hr as [(-> & _) | [(-> & _) | (-> & _)]]; congruence.
  - iIntros (s s' w ps' i' f' l' x i'' oo' a' c' (Hf & _ & Hr & Ha)) "#Hww Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl #Hs HG HF HM Hli Hca".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & Hlen & Hfl & Hli & _ & _ & Hw1 & _).
    pose proof (sbyte_in_len w 1 Hw1).
    iDestruct (ws_suffix _ w 2 with "Hww") as "#Hw2"; [lia|].
    iApply (str_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca [ ]");
      [exact (plo_ret_x _ _ _ _ _ _ _ _ _ _ _ Hr) | exact Hp |].
    iApply (plo_arg_str _ _ _ _ _ _ _ _ _ _ _ _ Hc Ha Hlen ltac:(lia) with "Hw2 Hs").
  - iIntros (s s' w ps' i' f' l' x i'' oo' a' c' (_ & Hlo & _)). exfalso. apply Hlo. reflexivity.
  - iIntros (s s' w ps' i' f' l' oo' a' x i'' oo'' a'' c'' (_ & Hlo & _)). exfalso. apply Hlo. reflexivity.
  - iIntros (s s' w ps' i' f' l' a' (_ & Hlo & _)). exfalso. apply Hlo. reflexivity.
  - iIntros (s s' w ps' i' f' l' x i'' oo' a' c' (Hf & Hr)) "#Hww Hl Hi Ho Hab Hcur Hw _ _ Ha Hcl #Hs HG Hca HF HM Hli".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & Hlen & Hfl & Hli & _ & Hw0 & _).
    pose proof (sbyte_in_len w 0 ltac:(lia)).
    iDestruct (ws_suffix _ w 1 with "Hww") as "#Hw1"; [lia|].
    iApply (str_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs HG HF HM Hli Hca [ ]");
      [exact (char_ret_x _ _ _ _ _ _ _ _ _ _ _ _ _ Hr) | exact Hp |].
    iApply (char_arg_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc Hr Hlen ltac:(lia) with "Hw1 Hs").
  - iIntros (s s' w ps' i' f' l' Hf) "#Hww #Hs".
    pose proof Hf as (_ & _ & _ & _ & _ & Hp & Hlen & Hfl & Hli & _).
    iApply (w_ret_exits_str with "Hww Hs"); (assumption || lia).
  - iIntros (s q sq k0 Hf) "#Hq". pose proof Hf as (_ & _ & _ & _ & _ & Hj & _).
    iApply (w_ret_exits_str with "Hq Hs0"); [reflexivity | exact Hn | exact Hc | lia].
  - iIntros (s q sq k0 x i' oo' a' c' (Hf & Hr)) "#Hq Hl Hi Ho Hab Hcur Hw Ha Hcl HG Hca HF HM Hli".
    pose proof Hf as (_ & _ & _ & _ & _ & Hj & _ & Hk0 & _ & Hnx & _).
    iDestruct (ws_suffix q sq k0 with "Hq") as "#Hwk"; [lia|]. rewrite -Hnx.
    iApply (str_ret with "Hl Hi Ho Hab Hcur Hw Ha Hcl Hs0 HG HF HM Hli Hca [ ]");
      [exact (char_ret_x _ _ _ _ _ _ _ _ _ _ _ _ _ Hr) | reflexivity |].
    iApply (char_arg_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc Hr Hn ltac:(lia) with "Hwk Hs0").
Qed.

(** ## The whole call of getopt_long

    A program calls getopt_long to read its options, and it needs both
    safety and the string. getopt_long runs the wrapper with long-only
    mode off. The rule below combines the rule for the wrapper with the
    proved call of the parser. The program gets the string fact as well
    as everything that the general rule gives. *)

(** A program can call getopt_long safely. If the call returns the code
    c, the argument in optarg is a readable string. The program also
    gets back the session, the public cells and everything it lent. *)
Lemma wp_getopt_long_str_with_at e n av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0
    (G : iProp Σ) T fp dom se sereg mid mid' pdd sdd (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 penv c Φ :
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
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
  GetenvCall.getenv_at_rule w0 registry ge G penv -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx7 ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx0 ->
  getopt_cutoff_rule_with w0 registry ge G -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
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
  Z.of_nat (List.length ps) = n -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  str_code (drop (opt_skip os) os) los c ->
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
     arg_str c x a' -∗ Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_long e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type.
  intros H0 H2 H4 H6 H8 Hfi Hfr Hgd Hgi Hge Hga Hgo Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer
    Hoa Hoaa Hoae Hoar Hoo Hooe Hoor Hgc Hdd Hget Hpenv Hg Hgn Hdiag Hse Hmid' Hmid Hgp Hp7 Hp0 Hcut Hmal Hset
    Hlrule Hfree Hgsn Hgl H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hneg Hlen Hn Hse0 Hsea Hsee Hser Hcode.
  iIntros "(%i0 & %e0 & Hl & Hb0 & Hb4 & Hpre) Hoi Hi Hoe He Hoa Hpa Hoo Hc #Hos HG #Hsl #Hsc Ha Hcl #Hs #Hdd
    #Ht #Hp7 #Hp0 HF HM Hli HK".
  iApply (GetoptLongWrapper.wp_getopt_long e n (mkPtr av (Obj av)) p lo li b r oi roi oe roe oa roa oo roo i err
            a0 c0 i0 e0 (str_rest b r av ar ps G F M li c) Φ
            with "Hoi Hi Hoe He Hoa Hpa Hoo Hc Hl Hb0 Hb4 [Hpre HG Ha Hcl HF HM Hli] [HK]"); try (assumption || lia).
  - iIntros (cf Hcf) "Hl Hb0 Hb4". iSpecialize ("Hpre" with "Hl Hb0 Hb4").
    iApply (wp_getopt_call_parse_arg_with_at cf n av ar p os lo li 0 0 penv b r ps i G T fp dom se sereg mid mid' pdd sdd M
              f138 f139 f140 f141 lmid mid3 mid4 los F pfx7 pxs7 pfx0 pxs0
              (wrap_post b r (str_rest b r av ar ps G F M li c))
              with "Hpre Hos HG Hsl Hsc Ha Hcl Hs Hdd Ht Hp7 Hp0 HF HM Hli [ ]"); try (assumption || lia).
    iApply (call_parse_rets_str with "Hs"); assumption.
  - iIntros (x i' c' a' Hx) "[Hrest #Hstr] Hl Hb0 Hb8 Hb16 Hoi Hi Hoe He Hoa Hpa Hoo Hc".
    iDestruct "Hrest" as (ps' cur) "(%Hp & Hcur & Hw & Ha & Hcl & #Hs' & HG & HF & HM & Hli & Hca)".
    iSpecialize ("Hw" with "Hl Hb0 Hb8 Hb16 Hcur").
    iApply ("HK" with "[%] Hw Hoi Hi Hoe He Hoa Hpa Hoo Hc Ha Hcl Hs' HG HF HM Hli Hca Hstr"). exact Hp.
Qed.

(** Legacy callers retain the resource-aware cutoff and all index bounds. *)
Definition wp_getopt_long_str_with e n av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0
    G T fp dom se sereg mid mid' pdd sdd M f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 penv c Φ
    H0 H2 H4 H6 H8 Hfi Hfr Hgd Hgi Hge Hga Hgo Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer
    Hoa Hoaa Hoae Hoar Hoo Hooe Hoor Hgc Hdd
    (Hget : GetoptInitialize.getenv_rule w0 registry ge G) :=
  wp_getopt_long_str_with_at e n av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0
    G T fp dom se sereg mid mid' pdd sdd M f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 penv c Φ
    H0 H2 H4 H6 H8 Hfi Hfr Hgd Hgi Hge Hga Hgo Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer
    Hoa Hoaa Hoae Hoar Hoo Hooe Hoor Hgc Hdd
    (GetoptInitialize.getenv_rule_at w0 registry ge G penv Hget).

(** Callers that need no resource for the cutoff keep this form. *)
Lemma wp_getopt_long_str e n av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0
    (G : iProp Σ) T fp dom se sereg mid mid' pdd sdd (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 penv c Φ :
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
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
  Z.of_nat (List.length ps) = n -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  str_code (drop (opt_skip os) os) los c ->
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
     arg_str c x a' -∗ Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_long e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 Hcut.
  exact (wp_getopt_long_str_with e n av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0 G T fp dom se sereg mid mid' pdd sdd M f138 f139 f140 f141 lmid mid3 mid4 los F pfx7 pxs7 pfx0 pxs0 penv c Φ H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

(** ## The call as the program makes it

    A program calls getopt_long by name with five arguments. Its vector
    ends with a null cell that getopt never reads, and each word holds a
    read-only string. The lemmas below build the frame of that call,
    split the null cell off the vector and restore it afterwards, and
    restate the rule for that frame. *)

(** The call puts the count, the vector, the option string, the table
    and the longind pointer into these names. *)
Definition getopt_long_env (n av : Z) (p lo li : ptr) : env :=
  put (TAtom "v8") (WPtr li) (put (TAtom "v6") (WPtr lo) (put (TAtom "v4") (WPtr p)
    (put (TAtom "v2") (WPtr (mkPtr av (Obj av))) (put (TAtom "v0") (WInt n) [])))).

(** The call frame enters the block named start with that environment. *)
Lemma getopt_long_call_frame n av p lo li :
  call_frame glibc_getopt_long [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li] =
  Some (mkFrame glibc_getopt_long (getopt_long_env n av p lo li) [] None (Enter (TAtom "start") None)).
Proof using Type*. reflexivity. Qed.

(** A vector with its null cell holds the cells of the words and one more
    cell after them. The rules of getopt own only the first part, so the
    caller keeps the null cell aside and gets it back unchanged. *)
Lemma argv_cells_null av ps :
  ([∗ list] k ↦ q ∈ ps ++ [null], pcell av (8 * Z.of_nat k) q) ⊣⊢
  argv_cells av ps ∗ pcell av (8 * Z.of_nat (List.length ps)) null.
Proof using Type. unfold argv_cells. rewrite big_sepL_app big_sepL_singleton Nat.add_0_r. reflexivity. Qed.

(** A session keeps its index between zero and the count of words. *)
Lemma getopt_session_index b r av ar ps i :
  getopt_session b r av ar ps i -∗ ⌜0 <= i <= Z.of_nat (List.length ps)⌝ ∗ getopt_session b r av ar ps i.
Proof using Type.
  iIntros "[%Ha (%s & Hs & %Hb & Hc)]". unfold getopt_bounds in Hb.
  iSplit; [iPureIntro; lia|]. iSplit; [done|]. iExists s. iSplitL "Hs"; [done|]. iSplit; [done | iExact "Hc"].
Qed.

(** A program can call getopt_long by name safely. The frame cf is the
    one that the five arguments build. The program lends its vector with
    the null cell and the strings of the words, and it gets them back in
    the same form over the reordered words. Everything else is as in the
    rule above. *)
Lemma wp_getopt_long_str_call_with_at cf av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0
    (G : iProp Σ) T fp dom se sereg mid mid' pdd sdd (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 penv c Φ :
  call_frame glibc_getopt_long
    [WInt (Z.of_nat (List.length ps)); WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li] = Some cf ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
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
  GetenvCall.getenv_at_rule w0 registry ge G penv -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx7 ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx0 ->
  getopt_cutoff_rule_with w0 registry ge G -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
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
  Z.of_nat (List.length ps) < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  str_code (drop (opt_skip os) os) los c ->
  copy_in_view b r av ar ps i err -∗
  live oi roi -∗ int_cell oi 0 i -∗ live oe roe -∗ int_cell oe 0 err -∗
  live oa roa -∗ pcell oa 0 a0 -∗ live oo roo -∗ int_cell oo 0 c0 -∗
  word_string DfracDiscarded p os -∗ G -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ ([∗ list] k ↦ q ∈ ps ++ [null], pcell av (8 * Z.of_nat k) q) -∗
  ([∗ list] q ∈ ps, ∃ s, word_string DfracDiscarded q s) -∗ word_string DfracDiscarded pdd sdd -∗
  opt_table lo los -∗ word_string DfracDiscarded pfx7 pxs7 -∗ word_string DfracDiscarded pfx0 pxs0 -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ x i' c' a' ps', ⌜Permutation ps ps' /\ 0 <= x < 2 ^ 32⌝ -∗ getopt_session b r av ar ps' i' -∗
     live oi roi -∗ int_cell oi 0 i' -∗ live oe roe -∗ int_cell oe 0 err -∗
     live oa roa -∗ pcell oa 0 a' -∗ live oo roo -∗ int_cell oo 0 c' -∗
     live av ar -∗ ([∗ list] k ↦ q ∈ ps' ++ [null], pcell av (8 * Z.of_nat k) q) -∗
     ([∗ list] q ∈ ps', ∃ s, word_string DfracDiscarded q s) -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
     arg_cap a' -∗
     arg_str c x a' -∗ Φ (Ret (WInt x))) -∗
  WP (ERun cf : gexpr) {{ Φ }}.
Proof using Type.
  intros Hcf. rewrite getopt_long_call_frame in Hcf. injection Hcf as <-. intros.
  iIntros "Hci Hoi Hi Hoe He Hoa Hpa Hoo Hc Hos HG Hsl Hsc Ha Hcl Hs Hdd Ht Hp7 Hp0 HF HM Hli HK".
  iDestruct (argv_cells_null with "Hcl") as "[Hcl Hnull]".
  iApply (wp_getopt_long_str_with_at (getopt_long_env (Z.of_nat (List.length ps)) av p lo li) (Z.of_nat (List.length ps))
            av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0 G T fp dom se sereg mid mid' pdd sdd M
            f138 f139 f140 f141 lmid mid3 mid4 los F pfx7 pxs7 pfx0 pxs0 penv c Φ
            with "Hci Hoi Hi Hoe He Hoa Hpa Hoo Hc Hos HG Hsl Hsc Ha Hcl Hs Hdd Ht Hp7 Hp0 HF HM Hli [Hnull HK]");
    try (reflexivity || assumption || lia).
  iIntros (x i' c' a' ps' [Hp Hx]) "Hw Hoi Hi Hoe He Hoa Hpa Hoo Hc Ha Hcl Hs' HG HF HM Hli Hca Hstr".
  iEval (rewrite (Permutation_length Hp)) in "Hnull".
  iApply ("HK" with "[%] Hw Hoi Hi Hoe He Hoa Hpa Hoo Hc Ha [Hcl Hnull] Hs' HG HF HM Hli Hca Hstr");
    [split; assumption|].
  iApply argv_cells_null. iSplitL "Hcl"; [iExact "Hcl" | iExact "Hnull"].
Qed.

(** Legacy real calls keep their original statement through the same proof. *)
Definition wp_getopt_long_str_call_with cf av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0
    G T fp dom se sereg mid mid' pdd sdd M f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 penv c Φ Hcf Hfi Hfr Hgd Hgi Hge Hga Hgo
    Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer Hoa Hoaa Hoae Hoar Hoo Hooe Hoor Hgc Hdd
    (Hget : GetoptInitialize.getenv_rule w0 registry ge G) :=
  wp_getopt_long_str_call_with_at cf av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0
    G T fp dom se sereg mid mid' pdd sdd M f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 penv c Φ Hcf Hfi Hfr Hgd Hgi Hge Hga Hgo
    Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer Hoa Hoaa Hoae Hoar Hoo Hooe Hoor Hgc Hdd
    (GetoptInitialize.getenv_rule_at w0 registry ge G penv Hget).

(** Callers that need no resource for the cutoff keep this form. *)
Lemma wp_getopt_long_str_call cf av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0
    (G : iProp Σ) T fp dom se sereg mid mid' pdd sdd (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 los F
    pfx7 pxs7 pfx0 pxs0 penv c Φ :
  call_frame glibc_getopt_long
    [WInt (Z.of_nat (List.length ps)); WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li] = Some cf ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
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
  Z.of_nat (List.length ps) < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  str_code (drop (opt_skip os) os) los c ->
  copy_in_view b r av ar ps i err -∗
  live oi roi -∗ int_cell oi 0 i -∗ live oe roe -∗ int_cell oe 0 err -∗
  live oa roa -∗ pcell oa 0 a0 -∗ live oo roo -∗ int_cell oo 0 c0 -∗
  word_string DfracDiscarded p os -∗ G -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ ([∗ list] k ↦ q ∈ ps ++ [null], pcell av (8 * Z.of_nat k) q) -∗
  ([∗ list] q ∈ ps, ∃ s, word_string DfracDiscarded q s) -∗ word_string DfracDiscarded pdd sdd -∗
  opt_table lo los -∗ word_string DfracDiscarded pfx7 pxs7 -∗ word_string DfracDiscarded pfx0 pxs0 -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ x i' c' a' ps', ⌜Permutation ps ps' /\ 0 <= x < 2 ^ 32⌝ -∗ getopt_session b r av ar ps' i' -∗
     live oi roi -∗ int_cell oi 0 i' -∗ live oe roe -∗ int_cell oe 0 err -∗
     live oa roa -∗ pcell oa 0 a' -∗ live oo roo -∗ int_cell oo 0 c' -∗
     live av ar -∗ ([∗ list] k ↦ q ∈ ps' ++ [null], pcell av (8 * Z.of_nat k) q) -∗
     ([∗ list] q ∈ ps', ∃ s, word_string DfracDiscarded q s) -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
     arg_cap a' -∗
     arg_str c x a' -∗ Φ (Ret (WInt x))) -∗
  WP (ERun cf : gexpr) {{ Φ }}.
Proof using Type.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 Hcut.
  exact (wp_getopt_long_str_call_with cf av ar p os lo li b r ps i err oi roi oe roe oa roa oo roo a0 c0 G T fp dom se sereg mid mid' pdd sdd M f138 f139 f140 f141 lmid mid3 mid4 los F pfx7 pxs7 pfx0 pxs0 penv c Φ H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

End long_str.
