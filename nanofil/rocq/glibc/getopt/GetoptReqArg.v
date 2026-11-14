(** A short option with a required argument takes the rest of its
    cluster as that argument, or else the next argument of the vector.
    When the cluster ends at the last argument, nothing is left to take:
    glibc's scanner records the option character as the bad option,
    reports it on stderr if the caller lets it print errors, and answers
    ':' or '?' as the option string asks. This file proves those steps
    safe: the scanner reads the cluster only through its cursor, reads
    the vector only below the argument count, and writes only the fields
    of its own state. *)

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
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail GetoptReqNext.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptReqNext GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The next-argument module supplies the argument vector and its tactics. *)
Import GetoptReqNext GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section req.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance req_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance req_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The scanner has just stepped over the option character c in the
    cluster t, which stood at index i below the argument count n. If the
    cluster goes on, its rest is the argument, and the index steps past
    the cluster. If the cluster ends, the index already stands at i + 1.
    When that is below n, the argument there is the option argument, and
    the index steps past it. When it equals n, no argument is left: c
    becomes the bad option, the caller's report rule keeps G, and the
    answer is ':' or '?' as the option string so asks. Every case leaves
    the cursor null. The names ks keep their values from the caller's
    environment e0. *)
Lemma wp_getopt_reqarg ks e0 e fr i n c pe cur t po so a oo b r av ar ps (G : iProp Σ) T fp dom se sereg mid Φ :
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
  pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  ((∀ e', ⌜keeps ks e0 e' /\ sbyte t 1 <> 0 /\ lookup (TAtom "pr.7") e' = Some (WInt c)⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 oo -∗ pcell b 16 (ptr_add cur 1) -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e0 e' /\ sbyte t 1 = 0 /\ i + 1 < n /\ lookup (TAtom "pr.7") e' = Some (WInt c)⌝ -∗
      live b r -∗ int_cell b 0 (i + 2) -∗ int_cell b 8 oo -∗ pcell b 16 (nth (Z.to_nat (i + 1)) ps null) -∗
      pcell b 32 null -∗ live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e0 e' /\ sbyte t 1 = 0 /\ (i + 1)%Z = n /\
        lookup (TAtom "pr.7") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
      live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L605") (Some (TAtom "L639")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L611") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksd Hk0 Hrule Hse Hmid H0 H2 H12 H455 Hpo Hpe Hc0 Hc1 Hc2 Hc19 Hc20 H137 Hi Hn Hlen Ht0 Hc Hper
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Hws #Hpo #Hsl #Hsc Hl Hib Hoo Hab Hcur Ha Hcl #Hs HG HK".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iDestruct (ws_shape with "Hpo") as %(Hcho & Hpop & Hpoe).
  pose proof (sbyte_in_len t 0 Ht0) as Hlt. pose proof (sbyte_range t 1 Hch) as Ht1r.
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  step. step.
  iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapq");
    [reflexivity | vx | left; reflexivity | arith | arith | unfold ptr_add; cbn [ptr_addr]; lia |].
  iNext. iIntros "Hl Hcur _".
  iDestruct (ws_byte cur t 1 with "Hws") as (bb1 breg1) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap' & ? & ? & ? & ?).
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap' | rawa | rawa | apply Z.mod_1_r |]; iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap' | rawa |].
  iNext; iIntros "_ _". iClear "Hbl Hbt". step.
  rewrite (Z.mod_small (chr_w (sbyte t 1)) (2 ^ 32)); [|apply chr_w_range].
  change (0 mod 2 ^ 32) with 0. rewrite chr_w_eqb; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte t 1) 0) as [E1 | E1]; close_br.
  2: {
    iDestruct "HK" as "[HK _]".
    iApply (wp_getopt_reqrest w0 registry ge ks e0 _ _ i c cur t with "Hws Hl Hib Hab Hcur [Hoo Ha Hcl HG HK]");
      [ exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lia | exact Hc
      | exact Hb | exact Hal | exact Hend | exact Hr |].
    iIntros (e') "[%Hk' %H7] Hl Hib Hab Hcur".
    iApply ("HK" with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG"). split; [exact Hk'|]. split; [exact E1 | exact H7]. }
  iDestruct "Hib" as "[%Hi0 Hib]".
  step. check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. rewrite (Z.mod_small (i + 1) (2 ^ 32)); [|lia].
  rewrite (Z.mod_small n (2 ^ 32)); [|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (i + 1) n) as [En | En]; close_br.
  - iDestruct "HK" as "[_ [_ HK]]".
    iApply (wp_getopt_reqmiss w0 registry ge ks e0 with "Hpo Hsl Hsc Hl Hoo Hcur Ha Hcl Hs HG [Hib Hab HK]");
      [ exact Hks | exact Hksd | xkeep | exact Hrule | exact Hse | exact Hmid | lk_prove | lk_prove | lk_prove
      | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | exact Hc | exact Hper | exact Hb | exact Hal | exact Hend
      | exact Hr | exact Hav | exact Hala | lia | exact Hra | intros ->; cbn in Hlen; lia | exact Hse0 | exact Hsea
      | exact Hsee | exact Hser |].
    iIntros (e') "[%Hk' %H7] Hl Hoo Hcur Ha Hcl HG".
    iApply ("HK" with "[%] Hl [Hib] Hoo Hab Hcur Ha Hcl HG"); [split; [exact Hk'|]; split; [exact E1|]; split; [lia | exact H7]|].
    iSplit; [iPureIntro; lia|]. by rewrite <- En.
  - iDestruct "HK" as "[_ [HK _]]".
    iApply (wp_getopt_reqnext w0 registry ge ks e0 _ _ i n c with "Hl [Hib] Hab Hcur Ha Hcl Hs [Hoo HG HK]");
      [ exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lia | lia
      | exact Hn | exact Hlen | exact Hc | exact Hb | exact Hal | exact Hend | exact Hr | exact Hav | exact Hala
      | exact Hda | exact Hra | (iSplit; [iPureIntro; lia | done]) |].
    iIntros (e') "[%Hk' %H7] Hl Hib Hab Hcur Ha Hcl".
    iApply ("HK" with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG"). split; [exact Hk'|]. split; [exact E1|]. split; [lia | exact H7].
Qed.

End req.
