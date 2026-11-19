From Glibc Require Import Unit_string_strchr_os Unit_string_strchrnul_os Unit_string_strncmp_os.
From Glibc Require Import GlibcProgram.
(** A program can write "-W foo" or "-Wfoo" to mean "--foo" when its
    option string holds "W;". In that case getopt passes the word after
    the W to the long-option parser. Afterwards, the getopt wrapper
    copies the index, the bad option and the argument into the public
    variables, so it needs those fields in hand and needs to know that
    the argument is live. The next call needs the session back. This
    file proves the three ways the W option can end: the rest of the
    word, the next word, or no word at all. *)

From Glibc Require Import GlibcTactics OsTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require OsWorld FileInv LibioLogic WordString StrchrnulLogic StrlenLogic StrlenWord StrcmpBits StrncmpLogic GetoptModule GetoptState ByteRead GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongPfxCmp GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongJoinMiss GetoptLongSession GetoptLongCap GetoptShortCap GetoptWTail GetoptWOpt GetoptLongW GetoptWOptSession GetoptDashRet.
Import OsWorld FileInv LibioLogic WordString StrchrnulLogic StrlenLogic StrlenWord StrcmpBits StrncmpLogic GetoptModule GetoptState ByteRead GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongPfxCmp GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongJoinMiss GetoptLongSession GetoptLongCap GetoptShortCap GetoptEntry GetoptWTail GetoptWOpt GetoptLongW GetoptWOptSession GetoptDashRet.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptLongSession GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongCap GetoptShortCap GetoptExchange GetoptInitialize GetoptState FileInv Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic ByteRead GetoptArgv.

(** A name that the W option keeps has the same value after it. *)
Local Ltac wr_lk Hk :=
  lazymatch goal with |- lookup ?k ?e' = _ =>
    rewrite (keeps_in wos_keys k _ e' Hk);
    [|unfold wos_keys; cbn [In]; repeat first [left; reflexivity | right]] end.

(** This tactic proves a pure premise and leaves the proof-mode goal alone. *)
Local Ltac wr_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- avoids _ _ = true => vm_compute; reflexivity
  | _ => first [assumption | lia | (hnf; apply Forall_forall; intros; reflexivity)]
  end.

Import ProgramAbbreviations.
Section w_ret.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance wret_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The call for the W option

    When getopt has found the word after the W, it calls the long-option
    parser on that word. The lemma below runs that call. It returns the
    fields the parser wrote, proof that the argument is live, and a wand
    that rebuilds the session from those fields. *)

(** The call returns the parser's answer x. The caller gets the fields
    that the parser wrote, the proof for the new argument, a way back to
    the session, and every resource that it lent the parser. It also gets
    the relation that names the entry behind the argument. *)
Lemma wp_getopt_w_call_ret_arg_with e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq k n pe j oo b r li er ord fst lst Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
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
  0 <= pe < 2 ^ 32 -> ps !! Z.to_nat j = Some q -> (k <= List.length sq)%nat ->
  0 <= j < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= j ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 j -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 null -∗ int_cell b 24 1 -∗
  pcell b 32 (ptr_add q (Z.of_nat k)) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ x i' oo' a' c', ⌜plo_ret_case ps j n (ptr_add q (Z.of_nat k)) (drop k sq) null os x i' a' c' /\
       plo_arg_case ps j n (ptr_add q (Z.of_nat k)) (drop k sq) null os x i' a'⌝ -∗
     live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
        getopt_session b r av ar ps i') -∗
     live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
     Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L533") w_call w_jump)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hgp H0 H2 H1 H6 H8 H12 H3 Hstr Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3
    Hmid4 Hfl Hos Hpe Hq Hk Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser Hord Hfst Hlst.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli HK".
  assert (Hlk : Z.of_nat (List.length (take k sq)) = Z.of_nat k) by (rewrite length_take_le; lia).
  iAssert (word_string DfracDiscarded (ptr_add q (Z.of_nat k)) (drop k sq)) as "#Hws".
  { rewrite -Hlk. iApply word_string_suffix. by rewrite take_drop. }
  iApply (wp_getopt_long_w_arg_with e G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo
    os F pfx pxs po so q sq (ptr_add q (Z.of_nat k)) (drop k sq) n pe j oo null b r li
    with "Ht Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli"); try (assumption || lia).
  iIntros (x) "Hres".
  iDestruct "Hres" as (i' oo' a' c') "(Hl & Hib & Hoob & Hab & Hcur & Ha & Hcl & HG & HF & HM & Hli & %Hp & %Harg)".
  pose proof Hp as (Hi' & Hc' & Ha' & _ & _).
  iDestruct (plo_arg_capped_null _ _ _ _ _ ar Ha' with "Hws Hs") as "[Hcap %Hra']".
  iApply ("HK" $! x i' oo' a' c' with "[%] Hl Hib Hoob Hab Hcur [Her Hini Hor Hfi Hla] Ha Hcl HG HF HM Hli [Hcap]");
    [exact (conj Hp Harg) | | by iSplitL "Hcap"].
  iIntros "Hl Hib Hoob Hab Hcur".
  set (s0 := mkGetoptState j er oo null 1 (ptr_add q (Z.of_nat k)) ord fst lst).
  iApply (GetoptLongSession.long_session b r av ar ps s0 i' oo' a' c' (drop k sq)
    with "[] Hws Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla");
    try (unfold getopt_bounds; cbn; lia); try (cbn; lia); try reflexivity; try exact Hc'.
  unfold GetoptState.getopt_cursor. unfold s0. cbn [gs_next gs_last gs_ind]. destruct (drop k sq) as [|t0 t] eqn:Ht0.
  - iRight. iLeft. iExact "Hws".
  - iRight. iRight. iExists q, (take k sq), (drop k sq). iSplit; [iPureIntro|].
    + rewrite Ht0. split; [lia|]. split; [by apply w_nth_error|]. split; [discriminate|].
      split; [by rewrite Hlk|lia].
    + by rewrite take_drop.
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma wp_getopt_w_call_ret_arg e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq k n pe j oo b r li er ord fst lst Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
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
  0 <= pe < 2 ^ 32 -> ps !! Z.to_nat j = Some q -> (k <= List.length sq)%nat ->
  0 <= j < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= j ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 j -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 null -∗ int_cell b 24 1 -∗
  pcell b 32 (ptr_add q (Z.of_nat k)) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ x i' oo' a' c', ⌜plo_ret_case ps j n (ptr_add q (Z.of_nat k)) (drop k sq) null os x i' a' c' /\
       plo_arg_case ps j n (ptr_add q (Z.of_nat k)) (drop k sq) null os x i' a'⌝ -∗
     live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
        getopt_session b r av ar ps i') -∗
     live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
     Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L533") w_call w_jump)) : gexpr) {{ Φ }}.
Proof using Type.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 Hcut.
  exact (wp_getopt_w_call_ret_arg_with e G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq k n pe j oo b r li er ord fst lst Φ H0 H1 H2 H3 H4 H5 H6 H7 H8 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

(** The same call ends in a return without the relation. *)
Lemma wp_getopt_w_call_ret e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq k n pe j oo b r li er ord fst lst Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
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
  0 <= pe < 2 ^ 32 -> ps !! Z.to_nat j = Some q -> (k <= List.length sq)%nat ->
  0 <= j < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= j ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 j -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 null -∗ int_cell b 24 1 -∗
  pcell b 32 (ptr_add q (Z.of_nat k)) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ x i' oo' a' c', ⌜plo_ret_case ps j n (ptr_add q (Z.of_nat k)) (drop k sq) null os x i' a' c'⌝ -∗
     live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
     (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
        getopt_session b r av ar ps i') -∗
     live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
     Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L533") w_call w_jump)) : gexpr) {{ Φ }}.
Proof using Type.
  intros. iIntros "Ht Hwq Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli HK".
  iApply (wp_getopt_w_call_ret_arg e G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq k n pe j oo b r li er ord fst lst Φ with "Ht Hwq Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli");
    try eassumption.
  iIntros (x i' oo' a' c' [Hc _]). iApply ("HK" $! x i' oo' a' c' with "[%]"). exact Hc.
Qed.

(** ## The three ways out of the W option

    The W sits k0 bytes into the word q at index i. If more of the word
    follows, that rest is the long option. If the word ends there, the
    next word is the long option, and it may be empty. If no word is left
    below the count n, the W becomes the bad option and getopt answers
    ':' or '?'. Each of these ways hands its fields to the caller. *)

(** This tactic restates cells between the two copies of their modules. *)
Local Ltac wr_conv b r j av ar ps c :=
  iAssert (pcell b 32 c) with "[Hcur]" as "Hcur"; [iExact "Hcur"|];
  iAssert (live b r) with "[Hl]" as "Hl"; [iExact "Hl"|];
  iAssert (int_cell b 0 j) with "[Hib]" as "Hib"; [iExact "Hib"|];
  iAssert (live av ar) with "[Ha]" as "Ha"; [iExact "Ha"|];
  iAssert (argv_cells av ps) with "[Hcl]" as "Hcl"; [iExact "Hcl"|].

(** The W may sit anywhere in a group of short options. When a word
    follows it, getopt returns the parser's answer and says which entry
    chose the argument. When no word follows, getopt returns ':' or '?',
    records the W as the bad option and keeps the old argument. *)
Lemma wp_getopt_w_ret_arg_with e fr i n c pe po so oo a b r av ar ps (G : iProp Σ) T fp dom se sereg mid
    (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 lo os F pfx pxs q sq k0 li er ord fst lst Φ :
  GetoptDiag.getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "v6") e = Some (WPtr lo) -> lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule_with w0 registry ge G -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  ps !! Z.to_nat i = Some q -> (k0 < List.length sq)%nat -> sbyte sq k0 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte sq (S k0) =? 0 then i + 1 else i) -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗
  pcell b 16 a -∗ int_cell b 24 1 -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
  int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a -∗
  ((∀ x i' oo' a' c',
      ⌜sbyte sq (S k0) <> 0 /\
        plo_ret_case ps i n (ptr_add q (Z.of_nat (S k0))) (drop (S k0) sq) null os x i' a' c' /\
        plo_arg_case ps i n (ptr_add q (Z.of_nat (S k0))) (drop (S k0) sq) null os x i' a'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (∀ s2 x i' oo' a' c',
      ⌜sbyte sq (S k0) = 0 /\ i + 1 < n /\
        plo_ret_case ps (i + 1) n (nth (Z.to_nat (i + 1)) ps null) s2 null os x i' a' c' /\
        plo_arg_case ps (i + 1) n (nth (Z.to_nat (i + 1)) ps null) s2 null os x i' a'⌝ -∗
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
      Φ (Ret (WInt (if sbyte so 0 =? 58 then 58 else 63))))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L508") (Some fr))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hrule Hse Hmid H0 H2 H12 H455 Hpo Hpe H6 H8 Hc0 Hc1 Hc2 Hc19 Hc20 H137 Hgp Hstr Hcut Hmal Hset Hlrule
    Hfree Hgn Hgl Hg Hgc H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hq Hk0 Hsk Hi Hn Hlen Hc Hper
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser Hord Hfst Hlst.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli Hca HK".
  iDestruct (ws_shape with "Hwq") as %(Hch & _ & _).
  assert (Hlk : Z.of_nat (List.length (take k0 sq)) = Z.of_nat k0) by (rewrite length_take_le; lia).
  iAssert (word_string DfracDiscarded (ptr_add q (Z.of_nat k0)) (drop k0 sq)) as "#Hwc".
  { rewrite -Hlk. iApply word_string_suffix. by rewrite take_drop. }
  assert (Ht0 : sbyte (drop k0 sq) 0 <> 0) by (rewrite sbyte_drop; [rewrite Nat.add_0_r; exact Hsk | lia]).
  assert (Ht1 : sbyte (drop k0 sq) 1 = sbyte sq (S k0)) by (rewrite sbyte_drop; [f_equal; lia | lia]).
  assert (Hc1' : ptr_add (ptr_add q (Z.of_nat k0)) 1 = ptr_add q (Z.of_nat (S k0))) by (rewrite wos_ptr_add; f_equal; lia).
  iEval (rewrite -Ht1) in "Hib". iEval (rewrite -Hc1') in "Hcur".
  iApply (GetoptWOpt.wp_getopt_wopt wos_keys e e fr i n c pe (ptr_add q (Z.of_nat k0)) (drop k0 sq) po so a oo b r
    av ar ps G T fp dom se sereg mid with "Hwc Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG [-]"); try wr_side.
  iSplit; [|iSplit].
  - iIntros (e' [Hk Hs1]) "Hl Hib Hoob Hab Hcur Ha Hcl HG". rewrite Hc1'. rewrite Ht1 in Hs1.
    wr_conv b r i av ar ps (ptr_add q (Z.of_nat (S k0))). iDestruct "HK" as "[HK _]".
    assert (Hk1 : (S k0 <= List.length sq)%nat) by (pose proof (sbyte_in_len sq (S k0) Hs1); lia).
    iApply (wp_getopt_w_call_ret_arg_with e' G T fp dom M se sereg f138 f139 f140 f141 lmid mid3 mid4 av ar ps
      lo os F pfx pxs po so q sq (S k0) n pe i oo b r li er ord fst lst
      with "Ht Hwq Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli");
      try (wr_lk Hk; assumption); try wr_side.
    iIntros (x i' oo' a' c' Hp). iApply ("HK" $! x i' oo' a' c'). iPureIntro. split; [exact Hs1 | exact Hp].
  - iIntros (e' (Hk & Hs1 & Hin)) "Hl Hib Hoob Hab Hcur Ha Hcl HG". rewrite Ht1 in Hs1.
    destruct (lookup_lt_is_Some_2 ps (Z.to_nat (i + 1))) as [q2 Hq2]; [lia|].
    assert (Hn2 : nth (Z.to_nat (i + 1)) ps null = q2) by (by rewrite (nth_lookup_Some _ _ _ _ Hq2)).
    iDestruct (big_sepL_lookup with "Hs") as (s2) "#Hw2"; [exact Hq2|].
    rewrite Hn2. iAssert (pcell b 32 (ptr_add q2 (Z.of_nat 0))) with "[Hcur]" as "Hcur".
    { cbn [Z.of_nat]. rewrite wos_ptr_add_0. iExact "Hcur". }
    wr_conv b r (i + 1) av ar ps (ptr_add q2 (Z.of_nat 0)). iDestruct "HK" as "[_ [HK _]]".
    iApply (wp_getopt_w_call_ret_arg_with e' G T fp dom M se sereg f138 f139 f140 f141 lmid mid3 mid4 av ar ps
      lo os F pfx pxs po so q2 s2 0 n pe (i + 1) oo b r li er ord fst lst
      with "Ht Hw2 Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli");
      try (wr_lk Hk; assumption); try wr_side.
    iIntros (x i' oo' a' c' Hp). cbn [Z.of_nat drop] in Hp. rewrite wos_ptr_add_0 in Hp.
    iApply ("HK" $! s2 x i' oo' a' c' with "[%] Hw2"). split; [exact Hs1|]. split; [exact Hin | exact Hp].
  - iIntros (e' (Hk & Hs1 & Hin & H575)) "Hl Hib Hoob Hab Hcur Ha Hcl HG". rewrite Hc1'. rewrite Ht1 in Hs1.
    wr_conv b r n av ar ps (ptr_add q (Z.of_nat (S k0))). iDestruct "HK" as "[_ [_ HK]]".
    assert (HSk : S k0 = List.length sq).
    { apply (proj1 (sbyte_zero sq (S k0) Hch ltac:(lia))). exact Hs1. }
    iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt (if sbyte so 0 =? 58 then 58 else 63)));
      [reflexivity | unfold value_x; cbn -[lookup]; rewrite H575; cbn [word_at_class];
       destruct (sbyte so 0 =? 58); reflexivity |]. iNext.
    iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur [Her Hini Hor Hfi Hla] Ha Hcl HG HF HM Hli Hca");
      [split; [exact Hs1 | exact Hin] |].
    iIntros "Hl Hib Hoob Hab Hcur".
    set (s0 := mkGetoptState i er oo a 1 (ptr_add q (Z.of_nat k0)) ord fst lst).
    iApply (GetoptLongSession.long_session b r av ar ps s0 n c a (ptr_add q (Z.of_nat (S k0))) (drop k0 sq)
      with "[] Hwc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla");
      try (unfold getopt_bounds; cbn; lia); try (cbn; lia); try reflexivity.
    + right. right. cbn [gs_next]. rewrite wos_ptr_add length_drop. f_equal. lia.
    + unfold GetoptState.getopt_cursor. unfold s0. cbn [gs_next gs_last gs_ind].
      iRight. iRight. iExists q, (take k0 sq), (drop k0 sq). iSplit; [iPureIntro|].
      * split; [lia|]. split; [by apply w_nth_error|]. split.
        { intros Hd. apply (f_equal (@List.length Z)) in Hd. rewrite length_drop in Hd. cbn in Hd. lia. }
        split; [by rewrite Hlk | lia].
      * by rewrite take_drop.
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma wp_getopt_w_ret_arg e fr i n c pe po so oo a b r av ar ps (G : iProp Σ) T fp dom se sereg mid
    (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 lo os F pfx pxs q sq k0 li er ord fst lst Φ :
  GetoptDiag.getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "v6") e = Some (WPtr lo) -> lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  ps !! Z.to_nat i = Some q -> (k0 < List.length sq)%nat -> sbyte sq k0 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte sq (S k0) =? 0 then i + 1 else i) -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗
  pcell b 16 a -∗ int_cell b 24 1 -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
  int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a -∗
  ((∀ x i' oo' a' c',
      ⌜sbyte sq (S k0) <> 0 /\
        plo_ret_case ps i n (ptr_add q (Z.of_nat (S k0))) (drop (S k0) sq) null os x i' a' c' /\
        plo_arg_case ps i n (ptr_add q (Z.of_nat (S k0))) (drop (S k0) sq) null os x i' a'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (∀ s2 x i' oo' a' c',
      ⌜sbyte sq (S k0) = 0 /\ i + 1 < n /\
        plo_ret_case ps (i + 1) n (nth (Z.to_nat (i + 1)) ps null) s2 null os x i' a' c' /\
        plo_arg_case ps (i + 1) n (nth (Z.to_nat (i + 1)) ps null) s2 null os x i' a'⌝ -∗
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
      Φ (Ret (WInt (if sbyte so 0 =? 58 then 58 else 63))))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L508") (Some fr))) : gexpr) {{ Φ }}.
Proof using Type.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hcut.
  exact (wp_getopt_w_ret_arg_with e fr i n c pe po so oo a b r av ar ps G T fp dom se sereg mid M f138 f139 f140 f141 lmid mid3 mid4 lo os F pfx pxs q sq k0 li er ord fst lst Φ H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

(** The same exits end in returns without the relation. *)
Lemma wp_getopt_w_ret e fr i n c pe po so oo a b r av ar ps (G : iProp Σ) T fp dom se sereg mid
    (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 lo os F pfx pxs q sq k0 li er ord fst lst Φ :
  GetoptDiag.getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "v6") e = Some (WPtr lo) -> lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  ps !! Z.to_nat i = Some q -> (k0 < List.length sq)%nat -> sbyte sq k0 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte sq (S k0) =? 0 then i + 1 else i) -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗
  pcell b 16 a -∗ int_cell b 24 1 -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
  int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a -∗
  ((∀ x i' oo' a' c',
      ⌜sbyte sq (S k0) <> 0 /\
        plo_ret_case ps i n (ptr_add q (Z.of_nat (S k0))) (drop (S k0) sq) null os x i' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
         getopt_session b r av ar ps i') -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ arg_cap a' -∗
      Φ (Ret (WInt x))) ∧
   (∀ s2 x i' oo' a' c',
      ⌜sbyte sq (S k0) = 0 /\ i + 1 < n /\
        plo_ret_case ps (i + 1) n (nth (Z.to_nat (i + 1)) ps null) s2 null os x i' a' c'⌝ -∗
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
      Φ (Ret (WInt (if sbyte so 0 =? 58 then 58 else 63))))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L508") (Some fr))) : gexpr) {{ Φ }}.
Proof using Type.
  intros. iIntros "Ht Hwq Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli Hca HK".
  iApply (wp_getopt_w_ret_arg e fr i n c pe po so oo a b r av ar ps G T fp dom se sereg mid M f138 f139 f140 f141 lmid mid3 mid4 lo os F pfx pxs q sq k0 li er ord fst lst Φ with "Ht Hwq Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli Hca");
    try eassumption.
  iSplit; [|iSplit].
  - iIntros (x i' oo' a' c' (Hs1 & Hp & _)). iDestruct "HK" as "[HK _]".
    iApply ("HK" $! x i' oo' a' c' with "[%]"). exact (conj Hs1 Hp).
  - iIntros (s2 x i' oo' a' c' (Hs1 & Hin & Hp & _)). iDestruct "HK" as "[_ [HK _]]".
    iApply ("HK" $! s2 x i' oo' a' c' with "[%]"). exact (conj Hs1 (conj Hin Hp)).
  - iDestruct "HK" as "[_ [_ HK]]". iExact "HK".
Qed.

End w_ret.
