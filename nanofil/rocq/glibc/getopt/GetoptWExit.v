From Glibc Require Import GlibcProgram.
(** The option string "W;" tells getopt to read "-W foo" as "--foo".
    getopt can meet that W in three places. It can be in a group that a
    call resumes, at the start of a new group, or in a single-dash word
    that the long-option parser turned down. Earlier files stop at the W
    in each place. This file carries each of them on to a return. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch GetoptLongSession GetoptLongDash GetoptLongSite GetoptLongCap GetoptDashRet GetoptLongOnlyRet GetoptLongOnlyShort GetoptWTail GetoptWOpt GetoptLongW GetoptWOptSession GetoptWRet GetoptKnownCap GetoptDiag GetoptReqTail GetoptShort GetoptOptArg GetoptShortRet
  GetoptShortCap GetoptColon GetoptEntry GetoptEntryScan GetoptScanChoice GetoptCharRet GetoptEntryChar GetoptScanChar.
From Glibc Require GetoptLongOnlyShort GetoptWRet GetoptWOptSession GetoptLongOnlyRet GetoptCharRet GetoptLongSite GetoptDashRet GetoptLongDash GetoptLongCap GetoptShortCap GetoptEntryScan GetoptScanChar FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongCall GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongPfxAlloc GetoptLongSession GetoptLongStore GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptLongCall GetoptLongSite GetoptLongSession GetoptLongJoinMiss GetoptLongCap GetoptShortCap GetoptKnownCap
  GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic
  GetoptBytes GetoptArgv.

(** The W block reads the option table and the longind pointer from two
    names. The character step may forget those names, so a caller must
    keep them, and no block ever assigns them. This lemma shows that a
    caller can keep them and still meet the step's other rules. *)
Lemma w_exit_keys : avoids (char_ret_keys ++ [TAtom "v8"]) char_names = true /\
  avoids (known_req_keys ++ [TAtom "v6"; TAtom "v8"]) opt_names = true /\
  avoids (known_req_keys ++ [TAtom "v6"; TAtom "v8"]) req_names = true /\
  avoids (known_req_keys ++ [TAtom "v6"; TAtom "v8"]) diag_names = true /\
  avoids (known_req_keys ++ [TAtom "v6"; TAtom "v8"]) ret_names = true.
Proof. split_and!; vm_compute; reflexivity. Qed.

(** The byte W reads as 87 after the character step widens it. *)
Lemma w_exit_chr : chr_w 87 = 87.
Proof. reflexivity. Qed.

(** This tactic proves that a name is in a key list. *)
Ltac wx_in Hin L :=
  first [assumption | solve [apply Hin; unfold L; cbn [In]; repeat first [left; reflexivity | right]]].

Import ProgramAbbreviations.
Section w_exit.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance wexit_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A shared view of the stream's liveness can be copied. *)
Local Instance wexit_liveq_persistent b0 reg : Persistent (liveq DfracDiscarded b0 reg).
Proof. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance wexit_pcellq_persistent b0 o x : Persistent (pcellq DfracDiscarded b0 o x).
Proof. unfold pcellq. apply _. Qed.

(** ## What the W option returns

    A caller that reaches a W must say what happens next in each case.
    The word after the W may come from the same word or from the next
    one, or there may be no word left. The definition below lists these
    three cases as the W rule states them. *)

(** The W option takes the rest of its word, takes the next word, or
    finds no word at all. Each case hands over its own fields. *)
Definition w_ret_exits (b : Z) (r : region) (av : Z) (ar : region) (ps : list ptr) (los : list lopt) (li : ptr)
    (F : list ptr) (G M : iProp Σ) (i n c : Z) (a : ptr) (so : list Z) (q : ptr) (sq : list Z) (k0 : nat)
    (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  (∀ x i' oo' a' c',
      ⌜sbyte sq (S k0) <> 0 /\
        plo_ret_case ps i n (ptr_add q (Z.of_nat (S k0))) (drop (S k0) sq) null los x i' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (∀ s2 x i' oo' a' c',
      ⌜sbyte sq (S k0) = 0 /\ i + 1 < n /\
        plo_ret_case ps (i + 1) n (nth (Z.to_nat (i + 1)) ps null) s2 null los x i' a' c'⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat (i + 1)) ps null) s2 -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (⌜sbyte sq (S k0) = 0 /\ (i + 1)%Z = n⌝ -∗
      live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
      (live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
         getopt_session b r av ar ps n) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a -∗
      Φ (Ret (WInt (if sbyte so 0 =? 58 then 58 else 63)))).

(** The same three cases can also hand the caller the relation that
    names the entry behind the argument, in both cases where the parser
    runs. *)
Definition w_ret_exits_arg (b : Z) (r : region) (av : Z) (ar : region) (ps : list ptr) (los : list lopt) (li : ptr)
    (F : list ptr) (G M : iProp Σ) (i n c : Z) (a : ptr) (so : list Z) (q : ptr) (sq : list Z) (k0 : nat)
    (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  (∀ x i' oo' a' c',
      ⌜sbyte sq (S k0) <> 0 /\
        plo_ret_case ps i n (ptr_add q (Z.of_nat (S k0))) (drop (S k0) sq) null los x i' a' c' /\
        plo_arg_case ps i n (ptr_add q (Z.of_nat (S k0))) (drop (S k0) sq) null los x i' a'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (∀ s2 x i' oo' a' c',
      ⌜sbyte sq (S k0) = 0 /\ i + 1 < n /\
        plo_ret_case ps (i + 1) n (nth (Z.to_nat (i + 1)) ps null) s2 null los x i' a' c' /\
        plo_arg_case ps (i + 1) n (nth (Z.to_nat (i + 1)) ps null) s2 null los x i' a'⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat (i + 1)) ps null) s2 -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (⌜sbyte sq (S k0) = 0 /\ (i + 1)%Z = n⌝ -∗
      live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
      (live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
         getopt_session b r av ar ps n) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a -∗
      Φ (Ret (WInt (if sbyte so 0 =? 58 then 58 else 63)))).

(** A caller that handles the three cases without the relation also
    handles them with it. *)
Lemma w_ret_exits_weaken b r av ar ps los li F (G M : iProp Σ) i n c a so q sq k0 Φ :
  w_ret_exits b r av ar ps los li F G M i n c a so q sq k0 Φ ⊢
  w_ret_exits_arg b r av ar ps los li F G M i n c a so q sq k0 Φ.
Proof.
  iIntros "H". unfold w_ret_exits, w_ret_exits_arg. iSplit; [|iSplit].
  - iIntros (x i' oo' a' c' (Hs & Hp & _)). iDestruct "H" as "[H _]".
    iApply ("H" $! x i' oo' a' c' with "[%]"). exact (conj Hs Hp).
  - iIntros (s2 x i' oo' a' c' (Hs & Hin & Hp & _)). iDestruct "H" as "[_ [H _]]".
    iApply ("H" $! s2 x i' oo' a' c' with "[%]"). exact (conj Hs (conj Hin Hp)).
  - iDestruct "H" as "[_ [_ H]]". iExact "H".
Qed.

(** ## One bridge for every W exit

    A proof for each place on its own would repeat the same steps three
    times. Each place reaches the option with the cursor just past the
    letter, so one proof can serve all three. *)

(** This lemma finishes "-W" after getopt has read the letter at byte
    k0 of the word q. The caller says what happens in each of the three
    cases, and it learns which entry chose the argument. The step before
    kept the names in kc and kr and set v455 and chk137. *)
Lemma w_exit_bridge_arg kc kr e1 e2 e3 n av ar p os lo li lonly pe b r ps i q sq k0 oo a er ord fst lst
    (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys kc -> In (TAtom "v8") kc -> incl known_req_keys kr -> In (TAtom "v6") kr ->
  In (TAtom "v8") kr ->
  entry_env e1 n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b pe ->
  keeps kc e1 e2 -> keeps kr e2 e3 -> lookup (TAtom "v455") e2 = Some (WInt (chr_w (sbyte (drop k0 sq) 0))) ->
  lookup (TAtom "chk137") e2 = Some (WPtr (mkPtr (b + 32) (Obj b))) -> sbyte (drop k0 sq) 0 = 87 ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z ->
  ps !! Z.to_nat i = Some q -> (k0 < List.length sq)%nat ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo los -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded p os -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte (drop k0 sq) 1 =? 0 then i + 1 else i) -∗ int_cell b 4 er -∗
  int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗ pcell b 32 (ptr_add (ptr_add q (Z.of_nat k0)) 1) -∗
  int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a -∗
  w_ret_exits_arg b r av ar ps los li F G M i n 87 a (drop (opt_skip os) os) q sq k0 Φ -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e3 [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hinc Hc8 Hinr Hr6 Hr8 Henv Hk2 Hk3 H455 H137 H87 Hrule Hse Hmid Hgp Hstr Hcut Hmal Hset Hlrule Hfree
    Hgn Hgl Hg Hgc H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hq Hk0 Hi Hn Hlen Hpe
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser Hord Hfst Hlst.
  iIntros "#Ht #Hwq #Hos #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli Hca HK".
  pose proof Henv as (H0 & H2 & H6 & H8 & _ & H12 & Hp1 & Hp3 & Hc0 & Hc1 & Hc2 & Hc19 & Hc20 & _).
  assert (L : forall k v, In k kc -> In k kr -> lookup k e1 = v -> lookup k e3 = v).
  { intros k v Hkc Hkr H. exact (keeps_in kr e2 e3 k v Hk3 Hkr (keeps_in kc e1 e2 k v Hk2 Hkc H)). }
  assert (L2 : forall k v, In k kr -> lookup k e2 = v -> lookup k e3 = v).
  { intros k v Hkr H. exact (keeps_in kr e2 e3 k v Hk3 Hkr H). }
  rewrite H87 w_exit_chr in H455.
  assert (E0 : lookup (TAtom "v0") e3 = Some (WInt n))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact H0]).
  assert (E2 : lookup (TAtom "v2") e3 = Some (WPtr (mkPtr av (Obj av))))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact H2]).
  assert (E6 : lookup (TAtom "v6") e3 = Some (WPtr lo))
    by (apply L; [wx_in Hinc char_ret_keys | exact Hr6 | exact H6]).
  assert (E8 : lookup (TAtom "v8") e3 = Some (WPtr li)) by (apply L; [exact Hc8 | exact Hr8 | exact H8]).
  assert (E12 : lookup (TAtom "v12") e3 = Some (WPtr (mkPtr b (Obj b))))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact H12]).
  assert (P1 : lookup (TAtom "pr.1") e3 = Some (WPtr (ptr_add p (Z.of_nat (opt_skip os)))))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact Hp1]).
  assert (P3 : lookup (TAtom "pr.3") e3 = Some (WInt pe))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact Hp3]).
  assert (C0 : lookup (TAtom "chk0") e3 = Some (WPtr (mkPtr (b + 4) (Obj b))))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact Hc0]).
  assert (C1 : lookup (TAtom "chk1") e3 = Some (WPtr (mkPtr (b + 16) (Obj b))))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact Hc1]).
  assert (C2 : lookup (TAtom "chk2") e3 = Some (WPtr (mkPtr b (Obj b))))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact Hc2]).
  assert (C19 : lookup (TAtom "chk19") e3 = Some (WPtr (ptr_add p (Z.of_nat (opt_skip os)))))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact Hc19]).
  assert (C20 : lookup (TAtom "chk20") e3 = Some (WPtr (mkPtr (b + 32) (Obj b))))
    by (apply L; [wx_in Hinc char_ret_keys | wx_in Hinr known_req_keys | exact Hc20]).
  assert (E455 : lookup (TAtom "v455") e3 = Some (WInt 87)) by (apply L2; [wx_in Hinr known_req_keys | exact H455]).
  assert (C137 : lookup (TAtom "chk137") e3 = Some (WPtr (mkPtr (b + 32) (Obj b))))
    by (apply L2; [wx_in Hinr known_req_keys | exact H137]).
  assert (Hsk : sbyte sq k0 <> 0) by (rewrite sbyte_drop in H87; [rewrite Nat.add_0_r in H87; lia | lia]).
  assert (Ht1 : sbyte (drop k0 sq) 1 = sbyte sq (S k0)) by (rewrite sbyte_drop; [f_equal; lia | lia]).
  assert (Hc1' : ptr_add (ptr_add q (Z.of_nat k0)) 1 = ptr_add q (Z.of_nat (S k0))) by (rewrite wos_ptr_add; f_equal; lia).
  iEval (rewrite Ht1) in "Hib". iEval (rewrite Hc1') in "Hcur".
  iDestruct (ws_suffix p os (opt_skip os) (GetoptColon.opt_skip_le os) with "Hos") as "#Hpo".
  iApply (wp_getopt_w_ret_arg e3 (TAtom "L524") i n 87 pe (ptr_add p (Z.of_nat (opt_skip os))) (drop (opt_skip os) os)
    oo a b r av ar ps G T fp dom se sereg mid M f138 f139 f140 f141 lmid mid3 mid4 lo los F pfx pxs q sq k0 li
    er ord fst lst Φ
    with "Ht Hwq Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli Hca HK");
    try (assumption || lia).
Qed.

(** The same bridge serves a caller that handles the cases without the relation. *)
Lemma w_exit_bridge kc kr e1 e2 e3 n av ar p os lo li lonly pe b r ps i q sq k0 oo a er ord fst lst
    (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys kc -> In (TAtom "v8") kc -> incl known_req_keys kr -> In (TAtom "v6") kr ->
  In (TAtom "v8") kr ->
  entry_env e1 n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b pe ->
  keeps kc e1 e2 -> keeps kr e2 e3 -> lookup (TAtom "v455") e2 = Some (WInt (chr_w (sbyte (drop k0 sq) 0))) ->
  lookup (TAtom "chk137") e2 = Some (WPtr (mkPtr (b + 32) (Obj b))) -> sbyte (drop k0 sq) 0 = 87 ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z ->
  ps !! Z.to_nat i = Some q -> (k0 < List.length sq)%nat ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo los -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded p os -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte (drop k0 sq) 1 =? 0 then i + 1 else i) -∗ int_cell b 4 er -∗
  int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗ pcell b 32 (ptr_add (ptr_add q (Z.of_nat k0)) 1) -∗
  int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a -∗
  w_ret_exits b r av ar ps los li F G M i n 87 a (drop (opt_skip os) os) q sq k0 Φ -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e3 [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
    {{ Φ }}.
Proof.
  intros. iIntros "Ht Hwq Hos Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli Hca HK".
  iApply (w_exit_bridge_arg kc kr e1 e2 e3 n av ar p os lo li lonly pe b r ps i q sq k0 oo a er ord fst lst G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ with "Ht Hwq Hos Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli Hca");
    try eassumption.
  iApply w_ret_exits_weaken. iExact "HK".
Qed.

(** ## The three W exits

    In "-ab -Wfoo", the W starts a new group. In "-aWfoo", a later call
    resumes the group at the W. A word that the long-option parser turns
    down is read like a new group. The first two cases have no argument
    yet, but in the third case the parser may have set one. *)

(** This is the W exit of a resumed cluster in [wp_getopt_entry_char],
    word for word. *)
Definition entry_w_exit (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr) (lonly b : Z) (r : region)
    (ps : list ptr) (j : Z) (G : iProp Σ) (ks ks2 : list name)
    (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ e' e2 e3 s q sq k0 k,
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
        {{ Φ }}.

(** This is the W exit of a new cluster in [scan_char_exits], word for
    word. *)
Definition scan_w_exit (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr) (lonly b : Z) (r : region)
    (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr) (ks ks2 : list name)
    (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ e1 e2 e3 s s' w ps' i' f' l' k,
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
        {{ Φ }}.

(** This is the W exit of a long-only fallback in [long_only_short_exits],
    word for word. *)
Definition long_only_w_exit (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr) (lonly b : Z)
    (r : region) (ps : list ptr) (j : Z) (G : iProp Σ) (se : Z) (sereg : region) (fp : ptr) (kc kr : list name)
    (F : list ptr) (M : iProp Σ) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ e3 e4 e5 s s' w ps' i' f' l' oo' a' k,
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
        {{ Φ }}.

End w_exit.
