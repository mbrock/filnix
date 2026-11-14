From Glibc Require Import GlibcProgram.
(** The getopt wrapper copies the parser's argument pointer into the
    public optarg, and its proof needs that pointer's capability at the
    copy. A short option sets the argument in three ways: to the rest of
    its cluster, to the next word of the vector, or to null when an
    optional argument is absent. When a required argument is missing,
    the argument keeps its old value. This file shows that each choice
    carries a live capability, using the strings that the caller already
    shares with the parser, and it restates the two short-option rules
    so that their exits hand that evidence on. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail GetoptReqNext
  GetoptShort GetoptOptArg GetoptReqArg.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptOptArg
  GetoptReqArg GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## Where a short option's argument points

    A pointer into the middle of a word keeps the word's capability, and
    a missing optional argument is null. The controls below check both
    facts on small examples. *)

(** One byte into a read-only word, the pointer keeps the word's capability. *)
Lemma short_cap_ctl_add : ptr_cap (ptr_add (mkPtr 4096 (Ro 4096)) 1) = Ro 4096 /\
  ptr_addr (ptr_add (mkPtr 4096 (Ro 4096)) 1) = 4097.
Proof. split; reflexivity. Qed.

(** The cluster "a" has nothing after its option, so the optional
    argument is null. The cluster "ab" has "b" after it, so the argument
    points one byte past the option. *)
Lemma short_cap_ctl_opt : (if sbyte [97] 1 =? 0 then null else mkPtr 4097 (Ro 4096)) = null /\
  (if sbyte [97; 98] 1 =? 0 then null else mkPtr 4097 (Ro 4096)) = mkPtr 4097 (Ro 4096).
Proof. split; reflexivity. Qed.

Import GetoptReqNext GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState
  FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section cap.
Context `{!gen_heapGS piece pval Σ}.

(** ## Usable argument pointers

    The wrapper reads nothing through optarg, but a later reader may.
    The predicate below is what the wrapper's proof asks of the argument
    when it copies it out. The lemmas after it supply that predicate for
    every pointer that a short option can choose. *)

(** The argument's capability names a live object, or no object at all,
    and its address lies below 2^64. *)
Definition arg_cap (a : ptr) : iProp Σ :=
  (∃ ra, live_capq DfracDiscarded (ptr_cap a) ra) ∗ ⌜0 <= ptr_addr a < 2 ^ 64⌝.

(** A null argument names no object. *)
Lemma arg_cap_null : ⊢ arg_cap null.
Proof. iSplit; [by iExists (mkRegion 0 0 Heap Freed) | iPureIntro; cbn; lia]. Qed.

(** The rest of a cluster lies inside the shared word, so it keeps the
    word's capability, and its address stays below 2^48. *)
Lemma arg_cap_rest cur t : word_string DfracDiscarded cur t ⊢ arg_cap (ptr_add cur 1).
Proof.
  iIntros "#Hws". iDestruct (ws_shape with "Hws") as %(_ & Hc0 & Hce).
  iDestruct (argv_str_cap with "Hws") as (rc) "[Hc _]".
  iSplitL "Hc"; [by iExists rc | iPureIntro; unfold ptr_add; cbn; lia].
Qed.

(** An optional argument is the rest of the cluster, or null when the
    cluster ends after the option. *)
Lemma arg_cap_opt cur t : word_string DfracDiscarded cur t ⊢
  arg_cap (if sbyte t 1 =? 0 then null else ptr_add cur 1).
Proof.
  iIntros "#Hws". destruct (sbyte t 1 =? 0); [iApply arg_cap_null | by iApply arg_cap_rest].
Qed.

(** A word of the vector has its own string, and an index past the end
    gives null. *)
Lemma arg_cap_nth ps k : argv_strs ps ⊢ arg_cap (nth k ps null).
Proof.
  iIntros "Hs". destruct (Nat.lt_ge_cases k (List.length ps)) as [Hlt | Hge].
  - iDestruct (argv_strs_cap ps k Hlt with "Hs") as (rn) "[Hc %Hn]".
    iSplitL "Hc"; [by iExists rn | done].
  - rewrite (nth_overflow ps null Hge). iApply arg_cap_null.
Qed.

End cap.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance shortcap_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The short-option rules with argument evidence

    The two rules below run the same blocks as the rules they restate,
    with the same premises and the same exits. Each exit also receives
    the evidence that its argument is usable. Where the argument keeps
    its old value, the caller supplies that evidence, because nothing
    about the private object says that an old argument is live. *)

(** An option with an optional argument sets the argument to the rest
    of its cluster or to null, and the exit learns that it is usable. *)
Lemma wp_getopt_optarg_cap ks e0 e fr i cur t a b r Φ :
  avoids ks opt_names = true -> keeps ks e0 e ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= i < 2 ^ 31 - 1 -> sbyte t 0 <> 0 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗
  live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 16 a -∗ pcell b 32 (ptr_add cur 1) -∗
  (∀ e', ⌜keeps ks e0 e'⌝ -∗
     live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 16 (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗
     pcell b 32 null -∗ arg_cap (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L619")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L610") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hk0 H12 Hc1 Hc2 Hc20 H137 Hi Ht0 Hb Hal Hend Hr.
  iIntros "#Hws Hl Hib Hab Hcur HK".
  iApply (GetoptOptArg.wp_getopt_optarg ks e0 e fr i cur t a b r Φ with "Hws Hl Hib Hab Hcur [HK]");
    try assumption.
  iIntros (e' Hk) "Hl Hib Hab Hcur". iApply ("HK" with "[%] Hl Hib Hab Hcur []"); [exact Hk |].
  iApply (arg_cap_opt with "Hws").
Qed.

(** An option with a required argument sets it to the rest of its
    cluster or to the next word, and those exits learn that it is
    usable. When no word is left, the argument keeps its old value, and
    the evidence the caller supplied for it reaches that exit. *)
Lemma wp_getopt_reqarg_cap ks e0 e fr i n c pe cur t po so a oo b r av ar ps (G : iProp Σ) T fp dom se sereg mid Φ :
  avoids ks req_names = true -> avoids ks diag_names = true -> keeps ks e0 e ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n -> sbyte t 0 <> 0 ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗ word_string DfracDiscarded po so -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
  pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ arg_cap a -∗
  ((∀ e', ⌜keeps ks e0 e' /\ sbyte t 1 <> 0 /\ lookup (TAtom "pr.7") e' = Some (WInt c)⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 oo -∗ pcell b 16 (ptr_add cur 1) -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e0 e' /\ sbyte t 1 = 0 /\ i + 1 < n /\ lookup (TAtom "pr.7") e' = Some (WInt c)⌝ -∗
      live b r -∗ int_cell b 0 (i + 2) -∗ int_cell b 8 oo -∗ pcell b 16 (nth (Z.to_nat (i + 1)) ps null) -∗
      pcell b 32 null -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (nth (Z.to_nat (i + 1)) ps null) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e0 e' /\ sbyte t 1 = 0 /\ (i + 1)%Z = n /\
        lookup (TAtom "pr.7") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
      live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L611") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hrq Hdg Hk0 Hdiag Hse Hmid H0 H2 H12 H455 Hpr1 Hpr3 Hc0 Hc1 Hc2 Hc19 Hc20 H137 Hi Hn Hlen Ht0 Hc Hpe
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Hws #Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG Hca HK".
  iApply (GetoptReqArg.wp_getopt_reqarg ks e0 e fr i n c pe cur t po so a oo b r av ar ps G T fp dom se sereg mid Φ
            with "Hws Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG [Hca HK]"); try assumption.
  iSplit; [|iSplit].
  - iClear "Hca". iDestruct "HK" as "[HK _]". iIntros (e' Hp) "Hl Hi Ho Hab Hc Ha Hcl HG".
    iApply ("HK" with "[%] Hl Hi Ho Hab Hc Ha Hcl HG []"); [exact Hp |]. iApply (arg_cap_rest with "Hws").
  - iClear "Hca". iDestruct "HK" as "[_ [HK _]]". iIntros (e' Hp) "Hl Hi Ho Hab Hc Ha Hcl HG".
    iApply ("HK" with "[%] Hl Hi Ho Hab Hc Ha Hcl HG []"); [exact Hp |]. iApply (arg_cap_nth with "Hs").
  - iDestruct "HK" as "[_ [_ HK]]". iIntros (e' Hp) "Hl Hi Ho Hab Hc Ha Hcl HG".
    iApply ("HK" with "[%] Hl Hi Ho Hab Hc Ha Hcl HG Hca"). exact Hp.
Qed.

End rules.
