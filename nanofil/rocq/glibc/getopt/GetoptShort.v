From Glibc Require Import GlibcProgram.
(** A cluster of short options such as "-ab" names one option per
    character. Each call of glibc's scanner takes the character at the
    private cursor, steps the cursor past it, and looks the character up
    in the short option string with glibc's own strchr. When the cluster
    ends, the scanner also steps the public index past the argument.
    This file proves that step safe: the scanner reads the cursor's
    string only up to its terminator and writes only the fields of its
    own state. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic GetoptModule
  GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptState LibioLogic OsWorld StrchrnulLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The character step assigns these names. *)
Definition char_names : list name := Eval vm_compute in
  List.map TAtom ["v452"; "chk134"; "v453"; "v454"; "chk135"; "chk136"; "v455"; "v459"; "chk137"; "v465";
    "chk138"; "v466"; "v467"; "chk139"; "v469"; "v470"; "chk140"; "v475"; "v477"; "v481"; "v483"; "v487";
    "v489"]%string.

(** The byte value of a loaded character is the character. *)
Lemma chr_w_byte x : 0 <= x < 256 -> chr_w x mod 256 = x.
Proof.
  intros Hx. unfold chr_w, sign_extension. rewrite (Z.mod_small x 256); [|lia].
  destruct (128 <=? x) eqn:E.
  - replace (x - 256) with (x + (-1) * 256) by lia. rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia |].
    + rewrite Z.mod_add; [|lia]. apply Z.mod_small. lia.
    + exists (2 ^ 24). reflexivity.
  - rewrite (Z.mod_small x (2 ^ 32)); [|lia]. apply Z.mod_small. lia.
Qed.


(** The exchange module supplies the argument vector and its tactics. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.
(** The strchr module proves glibc's own strchr. *)

(** This tactic enters a block and evaluates its phi assignments. *)


(** This tactic loads an owned private integer field as a signed 32-bit value. *)


Import ProgramAbbreviations.
Section short.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance short_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The step must read only the cursor's string and the short option
    string, and write only its own fields. The cursor points at a shared
    string t whose first character is not the terminator, and the short
    option string po follows its ordering prefix. The step stores the
    cursor one byte further on. When that byte ends the string, it also
    steps the public index i. A character that the option string does
    not name, or a colon or a semicolon, leads to the unknown-option
    blocks. Any other character leads on with the strchr result, which
    points at that character inside the option string. *)
Lemma wp_getopt_char ks e fr i cur t po so b r Φ :
  avoids ks char_names = true ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "v80") e = Some (WInt 0) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= i < 2 ^ 31 - 1 -> sbyte t 0 <> 0 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗ word_string DfracDiscarded po so -∗
  live b r -∗ int_cell b 0 i -∗ pcell b 32 cur -∗
  ((∀ e', ⌜keeps ks e e' /\ lookup (TAtom "v455") e' = Some (WInt (chr_w (sbyte t 0)))⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 32 (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L471") (Some (TAtom "L485")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' k, ⌜keeps ks e e' /\ lookup (TAtom "v455") e' = Some (WInt (chr_w (sbyte t 0))) /\
        (k < List.length so)%nat /\ sbyte so k = sbyte t 0 /\ sbyte t 0 <> 58 /\ sbyte t 0 <> 59 /\
        lookup (TAtom "v459") e' = Some (WPtr (ptr_add po (Z.of_nat k))) /\
        lookup (TAtom "chk137") e' = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ pcell b 32 (ptr_add cur 1) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L473") (Some (TAtom "L485")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L75") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hg Hgn Hv12 Hpo Hv80 Hc2 Hc20 Hi Ht0 Hb Hal Hend Hr.
  iIntros "#Hws #Hpo Hl [%Hi0 Hib] Hcur HK".
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iDestruct (ws_shape with "Hpo") as %(Hcho & Hpop & Hpoe).
  step. step. check "Hl".
  load_pointer_dq "Hl Hcur Hcapq" by arith.
  iNext. iIntros "Hl Hcur _". step. check "Hl".
  store_pointer "Hl Hcur" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hcur".
  assert (Ha1 : (ptr_addr cur mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 = ptr_addr cur + 1)
    by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
  rewrite Ha1.
  pose proof (sbyte_in_len t 0 Ht0) as Hlt.
  iDestruct (ws_byte cur t 0 with "Hws") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap & ? & ? & ? & ?).
  check_read_dq "Hbl" by arith; iNext; iIntros "_".
  load_bytes_dq "Hbl Hbt" decode (apply extended_chr) by arith.
  iNext; iIntros "_ _". iClear "Hbl Hbt".
  pose proof (sbyte_range t 0 Hch) as Ht0r.
  iApply (StrchrnulLogic.wp_call_glibc_strchr registry (os_wi w0) ge with "Hpo");
    [vx | apply Z.mod_pos_bound; lia | exact Hg | exact Hgn | reflexivity |].
  iNext. iIntros "_". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. norm. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | cbn [ptr_addr]; lia |].
  iNext. iIntros "Hl Hcur _". norm.
  iDestruct (ws_byte cur t 1 with "Hws") as (bb1 breg1) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap' & ? & ? & ? & ?).
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap' | arith | cbn [ptr_addr]; unfold raw_address; rewrite Z.mod_small; lia | arith |].
  iNext; iIntros "_".
  load_bytes_dq "Hbl Hbt" decode (apply extended_chr) by arith.
  iNext; iIntros "_ _". iClear "Hbl Hbt". step.
  pose proof (sbyte_range t 1 Hch) as Ht1r. rewrite chr_cmp; [|lia|lia].
  rewrite (Z.mod_small (chr_w (sbyte t 0)) (2 ^ 32)); [|apply chr_w_range].
  rewrite (chr_w_byte (sbyte t 0)); [|lia].
  set (x := sbyte t 0) in *. set (k := chr_idx x so).
  pose proof (strchr_hit x so ltac:(lia) Hcho) as Hhit. fold k in Hhit.
  rewrite (proj2 (Z.eqb_neq x 0)) in Hhit; [|exact Ht0]. rewrite orb_false_r in Hhit.
  iAssert (∀ (e2 : env) (fr : name) (i' : Z), ⌜keeps ks e e2 /\ i' = (if sbyte t 1 =? 0 then i + 1 else i)%Z /\
      lookup (TAtom "v455") e2 = Some (WInt (chr_w x)) /\
      lookup (TAtom "v459") e2 = Some (WPtr (strchr_ptr po x so)) /\
      lookup (TAtom "v80") e2 = Some (WInt 0) /\
      lookup (TAtom "chk137") e2 = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗
    live b r -∗ int_cell b 0 i' -∗ pcell b 32 (ptr_add cur 1) -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L462") (Some fr))) : gexpr) {{ Φ }})%I
    with "[HK]" as "HL462".
  { iIntros (e2 fr2 i' (Hk & -> & H455 & H459 & H80 & H137)) "Hl Hi Hcur".
    unfold strchr_ptr in H459. fold k in H459. rewrite (proj2 (Z.eqb_neq x 0)) in H459; [|exact Ht0].
    rewrite orb_false_r in H459.
    destruct (k <? List.length so)%nat eqn:Ek.
    - apply Nat.ltb_lt in Ek. pose proof (eq_sym Hhit) as Hx. apply Z.eqb_eq in Hx.
      step. step. step. iApply wp_branch; [vx | iNext].
      rewrite (Z.mod_small (ptr_addr po + Z.of_nat k) (2 ^ 64)); [|lia].
      rewrite (proj2 (Z.eqb_neq (ptr_addr po + Z.of_nat k) (0 mod 2 ^ 64))); [|rewrite Zmod_0_l; lia]. cbn [edge_label].
      step. step. step. step. rewrite chr_cmp; [|lia|lia].
      iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec x 58) as [E58 | E58]; close_br.
      { step. iApply wp_branch; [vx | iNext]. close_br. iDestruct "HK" as "[HK _]".
        iApply ("HK" with "[%] Hl Hi Hcur"). split; [xkeep | lk_prove]. }
      step. step. step. step. rewrite chr_cmp; [|lia|lia].
      iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec x 59) as [E59 | E59]; close_br.
      { iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl Hi Hcur"). split; [xkeep | lk_prove]. }
      iDestruct "HK" as "[_ HK]". iApply ("HK" $! _ k with "[%] Hl Hi Hcur").
      split; [xkeep|]. split; [lk_prove|]. split; [exact Ek|].
      split; [unfold sbyte; exact Hx|]. split; [exact E58|]. split; [exact E59|]. split; lk_prove.
    - step. step. step. iApply wp_branch; [vx | iNext]. close_br.
      step. iApply wp_branch; [vx | iNext]. close_br. step. iApply wp_branch; [vx | iNext]. close_br.
      iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl Hi Hcur"). split; [xkeep | lk_prove]. }
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte t 1) 0) as [E1 | E1]; close_br.
  - step. check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. norm. check "Hl".
    store_word "Hl Hib" by (arith) preserving wi_store.
    iNext. iIntros "Hl Hib". step.
    iApply ("HL462" $! _ _ (i + 1) with "[%] Hl [Hib] Hcur").
    { split; [xkeep|]. split; [reflexivity|]. repeat split; lk_prove. }
    iSplit; [iPureIntro; lia|]. rewrite (Z.mod_small (i + 1) (2 ^ 32)); [iAssumption | lia].
  - iApply ("HL462" $! _ _ i with "[%] Hl [Hib] Hcur"); [| by iSplit].
    split; [xkeep|]. split; [reflexivity|]. repeat split; lk_prove.
Qed.

End short.
