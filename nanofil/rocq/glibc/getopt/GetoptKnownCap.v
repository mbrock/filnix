From Glibc Require Import GlibcProgram.
(** When glibc's scanner finds a known short option, it looks at the
    colons after that option in the option string. No colon means no
    argument, one colon means a required argument, two colons mean an
    optional one, and "W;" leads to the long-option form of the W option.
    The getopt wrapper later copies the chosen argument into optarg, so
    every way out of this choice must say that the argument is usable.
    This file joins the choice with the required-argument blocks and
    hands each exit the evidence for its argument. *)

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
  GetoptShort GetoptOptArg GetoptReqArg GetoptShortOpt GetoptShortCap.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptShortCap
  GetoptShortOpt GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## Names that survive the choice

    The required-argument blocks read the argument count, the vector,
    the option character and several checked pointers. The choice must
    not change them on the way, so the caller keeps them in its list of
    preserved names. *)

(** These are the names that the required-argument blocks read. *)
Definition known_req_keys : list name := Eval vm_compute in
  List.map TAtom ["v0"; "v2"; "v12"; "v455"; "pr.1"; "pr.3"; "chk0"; "chk1"; "chk2"; "chk19"; "chk20"; "chk137"]%string.

(** A preserved name answers in the later environment as it did before. *)
Lemma keeps_in ks e e' k v : keeps ks e e' -> In k ks -> lookup k e = v -> lookup k e' = v.
Proof. unfold keeps. rewrite List.Forall_forall. intros H Hk <-. exact (H k Hk). Qed.

(** The option character comes fourth in the list, and the checked
    pointer to the error field comes seventh. *)
Lemma known_req_keys_ctl : nth 3 known_req_keys (TAtom "") = TAtom "v455" /\
  nth 6 known_req_keys (TAtom "") = TAtom "chk0".
Proof. split; reflexivity. Qed.

Import GetoptShortCap GetoptReqNext GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState
  FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section known.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance knowncap_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The known option with argument evidence

    The rule below runs the choice for a known option and, when the
    option needs an argument, the blocks that find it. It ends at the W
    form or at the common return block. The caller lends the resources
    that the required-argument blocks use, and every exit hands them
    back with the evidence for its argument. *)

(** The caller holds a known option x at index k of the option string,
    and evidence that the current argument a is usable. The W form and
    an option without an argument keep a, so their exits get the
    caller's evidence back. An optional argument comes from the rest of
    the cluster. A required argument comes from the rest of the cluster
    or the next word. If no word is left, the option is reported as
    missing its argument through the caller's report rule, and a stays. *)
Lemma wp_getopt_known_cap ks e i n c pe cur t po so k a lo oo b r av ar ps (G : iProp Σ) T fp dom se sereg mid Φ :
  avoids ks opt_names = true -> avoids ks req_names = true -> avoids ks diag_names = true ->
  incl known_req_keys ks ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v80") e = Some (WInt 0) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "v459") e = Some (WPtr (ptr_add po (Z.of_nat k))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  (k < List.length so)%nat -> 0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n -> sbyte t 0 <> 0 ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗ word_string DfracDiscarded po so -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
  pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ arg_cap a -∗
  ((∀ e', ⌜keeps ks e e' /\ sbyte so k = 87 /\ sbyte so (S k) = 59 /\ ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte so (S k) <> 58⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L510")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte so (S k) = 58 /\ sbyte so (S (S k)) = 58⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 oo -∗
      pcell b 16 (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L619")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\
        keeps ks e e' /\ sbyte t 1 <> 0 /\ lookup (TAtom "pr.7") e' = Some (WInt c)⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 oo -∗ pcell b 16 (ptr_add cur 1) -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\
        keeps ks e e' /\ sbyte t 1 = 0 /\ i + 1 < n /\ lookup (TAtom "pr.7") e' = Some (WInt c)⌝ -∗
      live b r -∗ int_cell b 0 (i + 2) -∗ int_cell b 8 oo -∗ pcell b 16 (nth (Z.to_nat (i + 1)) ps null) -∗
      pcell b 32 null -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (nth (Z.to_nat (i + 1)) ps null) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\
        keeps ks e e' /\ sbyte t 1 = 0 /\ (i + 1)%Z = n /\
        lookup (TAtom "pr.7") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
      live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L473") (Some (TAtom "L485")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hop Hrq Hdg Hinc Hdiag Hse Hmid H0 H2 H6 H12 H80 H455 H459 Hpr1 Hpr3 Hc0 Hc1 Hc2 Hc19 Hc20 H137
    Hk Hi Hn Hlen Ht0 Hc Hpe Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Hws #Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG Hca HK".
  iApply (GetoptShortOpt.wp_getopt_known ks e i cur t po so k a lo b r Φ
            with "Hws Hpo Hl Hib Hab Hcur [-]"); try (assumption || lia).
  iSplit; [|iSplit; [|iSplit]].
  - iClear "Hsl Hsc". iDestruct "HK" as "[HK _]". iIntros (e' Hp) "Hl Hib Hab Hcur".
    iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca"). exact Hp.
  - iClear "Hsl Hsc". iDestruct "HK" as "[_ [HK _]]". iIntros (e' Hp) "Hl Hib Hab Hcur".
    iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca"). exact Hp.
  - iClear "Hsl Hsc Hca". iDestruct "HK" as "[_ [_ [HK _]]]". iIntros (e' Hp) "Hl Hib Hab Hcur".
    iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG []"); [exact Hp |].
    iApply (arg_cap_opt with "Hws").
  - iDestruct "HK" as "[_ [_ [_ HK]]]". iIntros (e' (Hk' & H58 & H58')) "Hl Hib Hab Hcur".
    assert (Hkin : forall k0 v, In k0 known_req_keys -> lookup k0 e = v -> lookup k0 e' = v).
    { intros k0 v Hm. apply keeps_in with ks; [exact Hk' | exact (Hinc k0 Hm)]. }
    iApply (wp_getopt_reqarg_cap ks e e' (TAtom "L603") i n c pe cur t po so a oo b r av ar ps G T fp dom se sereg mid Φ
              with "Hws Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG Hca [HK]");
      try (assumption || lia); try (apply Hkin; [cbn; repeat (first [left; reflexivity | right]) | assumption]).
    iSplit; [|iSplit].
    + iDestruct "HK" as "[HK _]". iIntros (e'' Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hcap".
      iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hcap"). auto.
    + iDestruct "HK" as "[_ [HK _]]". iIntros (e'' Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hcap".
      iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hcap"). auto.
    + iDestruct "HK" as "[_ [_ HK]]". iIntros (e'' Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hcap".
      iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hcap"). auto.
Qed.

End known.
