(** A call of glibc's scanner that resumes inside a cluster such as
    "-ab" runs the entry blocks and then reads the next character of the
    cluster. The entry rule leaves that path at the block L75, with the
    private object, the current word and the option string in hand. The
    character step needs the rest of the word, the option string after
    its ordering prefix, an argument it may keep, and a bound on the
    print-errors flag. This file shows that the entry exit supplies all
    of them, and it joins the real call of the parser with the short
    returns. The path that scans for a new word and the form W; keep
    their own exits. *)

From Glibc Require Import OsMemLogic GetenvSpec LongOption Unit_string_strchr_os
  Unit_string_strchrnul_os GlibcProgram GlibcTactics OsTactics GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld WordString StrchrnulLogic GetoptModule
  GetoptState ByteRead GetoptInitialize GetoptColon GetoptEntry GetoptEntryPre GetoptEntryCall GetoptArgv
  GetoptExchange GetoptDiag GetoptReqTail GetoptShort GetoptOptArg GetoptShortRet GetoptShortCap GetoptKnownCap
  GetoptCharRet.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** An element at an index is the element that [nth_error] finds there. *)
Lemma entry_char_nth_error (l : list ptr) k x : l !! k = Some x -> nth_error l k = Some x.
Proof. revert k. induction l as [|y l IH]; intros [|k] H; cbn in *; try discriminate; auto. Qed.

(** The print-errors flag is 0 or the error field, so it fits in a word
    whenever the error field does. *)
Lemma print_errors_range os err : 0 <= err < 2 ^ 32 -> 0 <= print_errors os err < 2 ^ 32.
Proof. unfold print_errors. destruct (_ =? _); lia. Qed.

(** The option string "+a" sets the flag to the error field, and ":a"
    sets it to 0. *)
Lemma print_errors_ctl : print_errors [43; 97] 5 = 5 /\ print_errors [58; 97] 5 = 0.
Proof. split; reflexivity. Qed.

(** ## What the entry exit says

    A return must tell the caller where the step started, so that the
    caller can restore the session later. When the entry blocks resume a
    cluster, they know the state s, the word q at the index, its bytes sq
    and how far into it the cursor is. The definition below collects what
    they know into one fact that the returns pass on. *)

(** A resumed call starts from an initialized state whose cursor lies
    inside the word at the index, before its terminator. *)
Definition entry_resume_facts (n av : Z) (ar : region) (b : Z) (r : region) (ps : list ptr) (j : Z)
    (s : getopt_state) (q : ptr) (sq : list Z) (k0 : nat) : Prop :=
  ~ needs_init s /\ gs_ind s = j /\ gs_initialized s = 1 /\ 0 <= gs_order s <= 2 /\ getopt_bounds n j s /\
  0 <= j < n /\ ps !! Z.to_nat j = Some q /\ (k0 < List.length sq)%nat /\ sbyte sq k0 <> 0 /\
  gs_next s = ptr_add q (Z.of_nat k0) /\ gs_last s <= j /\
  0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
  0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48.

(** The resumed exit points the cursor into the word at the index, with a
    nonempty rest, so the cursor of the session holds. *)
Section cursor.
Context `{!gen_heapGS piece pval Σ}.

(** The cursor at offset k0 of the word q at the index is a session
    cursor, because the bytes after it are not empty. *)
Lemma entry_resume_cursor n av ar b r ps j s q sq k0 :
  entry_resume_facts n av ar b r ps j s q sq k0 -> Z.of_nat (List.length ps) = n ->
  word_string DfracDiscarded q sq -∗ getopt_cursor ps j s.
Proof using Type.
  intros (_ & _ & _ & _ & _ & Hj & Hq & Hk0 & _ & Hnx & Hla & _) Hlen. iIntros "#Hq".
  iRight. iRight. iExists q, (take k0 sq), (drop k0 sq). rewrite take_drop. iFrame "Hq". iPureIntro.
  split_and!; [lia | lia | by apply entry_char_nth_error | | | exact Hla].
  - intros E. apply (f_equal List.length) in E. rewrite length_drop in E. cbn in E. lia.
  - rewrite length_take_le; [exact Hnx | lia].
Qed.
End cursor.

Import GetoptShortCap GetoptKnownCap GetoptDiag GetoptExchange GetoptInitialize GetoptState Fix.ML0 Fix.LG0
  Fix.LG0.L ByteRead GetoptArgv. Import ProgramAbbreviations. Section entry_char.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance entrychar_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The scanning exit

    Sometimes no cluster is left to resume, and the scanner must look for
    a new word instead. This file leaves that work to the caller. The
    caller states it as the same promise that the entry rule asks for, so
    one proof of it serves both rules. *)

(** This is the scanning exit of [getopt_entry_exits], word for word. *)
Definition entry_scan_exit (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr)
    (lonly b : Z) (r : region) (ps : list ptr) (j : Z) (G : iProp Σ)
    (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ e' s s', ⌜entry_state s s' /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b (print_errors os (gs_err s)) /\
        gs_ind s = j /\ gs_initialized s' = 1 /\ 0 <= gs_order s' <= 2 /\ getopt_bounds n (gs_ind s') s' /\
        gs_arg s' = null /\ gs_ind s' = (if j =? 0 then 1 else j) /\
        0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
        0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ -∗
      live b r -∗ int_cell b 0 (gs_ind s') -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗
      pcell b 16 (gs_arg s') -∗ int_cell b 24 (gs_initialized s') -∗ pcell b 32 (gs_next s') -∗
      int_cell b 40 (gs_order s') -∗ int_cell b 44 (gs_first s') -∗ int_cell b 48 (gs_last s') -∗
      (⌜gs_next s' = null⌝ ∨ word_string DfracDiscarded (gs_next s') []) -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L73") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }}.

(** ## From the call to a short return

    The rule below starts at the real call of the parser. The caller
    lends the argument vector, the stream that reports go to, and the
    resource G, which serves both the environment lookup and the reports.
    A resumed cluster then runs the character step to its return. The
    caller gets the four fields that the wrapper copies, the evidence for
    the argument, and a wand that turns those fields back into a session
    at the new index. *)

(** A call either looks for a new word or resumes the cluster. Looking
    for a new word goes to the caller's exit at L73. Resuming reads one
    character and then stops at W; through its own exit, or returns in a
    way that [char_ret_case] lists. The entry blocks clear the argument
    before the step, so the caller needs no evidence for it. The count of
    words must stay below 2^31. A step by two happens only when the
    second word lies below the count, so the index still fits in an int. A return after a resumed character also gives the string
    of the word. *)
Lemma wp_getopt_entry_char_ws_at ks ks2 cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) T fp dom
    se sereg mid mid' Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  call_frame glibc_getopt_internal_r
    [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] = Some cf ->
  GetenvSpec.getenv_at_rule w0 registry ge G penv -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
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
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗ live av ar -∗ argv_cells av ps -∗
      entry_scan_exit n av ar p os lo li lonly b r ps j G Φ) ∧
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
  intros Hks Hkin Hop Hrq Hdg Hrt Hinc Hcf Hget Hpenv Hg Hgn Hdiag Hse Hmid' Hmid Hlen Hn Hse0 Hsea Hsee Hser.
  iIntros "Hpre #Hos HG Hsl Hsc Ha Hcl #Hs HK".
  iApply (wp_getopt_entry_call_at cf n av ar p os lo li lonly pc penv b r ps j G Φ with "Hpre Hos HG [-]");
    try assumption.
  iSplit; [iDestruct "HK" as "[HK _]"; iApply ("HK" with "Hsl Hsc Ha Hcl") |].
  iIntros (e' s q sq k0 Hf) "#Hq #Hws Hl Hib Her Hoob Hab Hini Hcur Hord Hfi Hla HG".
  destruct Hf as (Henv & Hfacts).
  pose proof Hfacts as (Hni & Hj & Hin & Hor & Hbd & Hjn & Hqj & Hk0 & Hsk & Hnx & Hla' & Hb & Hal & Hend & Hr &
    Hav & Hala & Hda & Hra).
  iDestruct "Her" as "[%Herr Her]".
  iDestruct (ws_suffix p os (opt_skip os) (opt_skip_le os) with "Hos") as "#Hpo".
  iPoseProof arg_cap_null as "Hnull".
  assert (Ht0 : sbyte (drop k0 sq) 0 <> 0) by (rewrite sbyte_drop; [rewrite Nat.add_0_r; exact Hsk | lia]).
  iApply (wp_getopt_char_ret ks ks2 e' (TAtom "L83") j n (print_errors os (gs_err s)) (gs_next s) (drop k0 sq)
            (ptr_add p (Z.of_nat (opt_skip os))) (drop (opt_skip os) os) (gs_opt s) null lo li lonly b r av ar ps
            G T fp dom se sereg mid mid' Φ
            with "Hws Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG Hnull [-]");
    try (assumption || lia || exact (print_errors_range os (gs_err s) Herr)).
  iSplit.
  - iDestruct "HK" as "[_ [HK _]]". iIntros (e2 e3 k Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG _".
    iApply ("HK" $! e' e2 e3 s q sq k0 k with "[%] Hq Hws Hl Hib [Her] Hoob Hab Hini Hcur Hord Hfi Hla Ha Hcl HG");
      [exact (conj Hfacts (conj Henv Hp)) | by iSplit].
  - iDestruct "HK" as "[_ [_ HK]]". iIntros (x i' oo' a' c' Hc) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
    iApply ("HK" $! s q sq k0 x i' oo' a' c' with "[%] Hq Hl Hib Hoob Hab Hcur [Her Hini Hord Hfi Hla] Ha Hcl HG Hca");
      [exact (conj Hfacts Hc) |].
    iIntros "Hl Hib Hoob Hab Hcur". subst j.
    iPoseProof (entry_resume_cursor n av ar b r ps (gs_ind s) s q sq k0 Hfacts Hlen with "Hq") as "Hcu".
    iAssert (int_cell b 4 (gs_err s)) with "[Her]" as "Her"; [by iSplit|].
    iAssert (int_cell b 24 (gs_initialized s)) with "[Hini]" as "Hini"; [by rewrite Hin|].
    subst n.
    iApply (char_ret_session b r av ar ps s (gs_opt s) (drop k0 sq) (drop (opt_skip os) os) x i' oo' null a' c'
              with "Hcu Hws Hl Hib Her Hoob Hab Hini Hcur Hord Hfi Hla"); try (assumption || lia).
Qed.

(** Legacy callers keep the same character-scanning contract. *)
Definition wp_getopt_entry_char_ws ks ks2 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom
    se sereg mid mid' Φ Hks Hkin Hop Hrq Hdg Hrt Hinc Hcf
    (Hget : GetoptInitialize.getenv_rule w0 registry ge G) :=
  wp_getopt_entry_char_ws_at ks ks2 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom
    se sereg mid mid' Φ Hks Hkin Hop Hrq Hdg Hrt Hinc Hcf
    (GetoptInitialize.getenv_rule_at w0 registry ge G penv Hget).

(** The same call serves a caller that needs no string of the word. *)
Lemma wp_getopt_entry_char ks ks2 cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) T fp dom
    se sereg mid mid' Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
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
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗ live av ar -∗ argv_cells av ps -∗
      entry_scan_exit n av ar p os lo li lonly b r ps j G Φ) ∧
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
  intros. iIntros "Hpre Hos HG Hsl Hsc Ha Hcl Hs HK".
  iApply (wp_getopt_entry_char_ws ks ks2 cf n av ar p os lo li lonly pc penv b r ps j G T fp dom se sereg mid mid' Φ with "Hpre Hos HG Hsl Hsc Ha Hcl Hs");
    try eassumption.
  iSplit; [iDestruct "HK" as "[H _]"; iExact "H"|].
  iSplit; [iDestruct "HK" as "[_ [H _]]"; iExact "H"|].
  iDestruct "HK" as "[_ [_ H]]". iIntros (s q sq k0 x i' oo' a' c' Hc) "_".
  iApply ("H" $! s q sq k0 x i' oo' a' c' with "[%]"). exact Hc.
Qed.

End entry_char.
