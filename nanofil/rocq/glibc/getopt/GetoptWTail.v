From Glibc Require Import GlibcProgram.
(** "W;" in the option string lets "-W foo" stand for the long option
    "--foo". glibc's scanner takes the word after the W as a required
    argument and hands it to the long-option parser. This file proves the
    two ends of that path safe. The scanner stores the word as its private
    cursor and clears the option argument just before it calls the parser.
    With no word left, it records the bad option, reports it through the
    caller's rule, and answers ':' or '?'. *)

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
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The W blocks assign these names. *)
Definition w_names : list name := Eval vm_compute in
  List.map TAtom ["v535"; "v536"; "chk147"; "v537"; "v538"; "v540"; "v542"; "v543"; "chk149"; "chk150"; "v548";
    "v550"; "v578"; "v581"; "v582"; "v583"; "v584"; "chk156"; "v585"; "chk157"; "v587"; "v589"; "chk158";
    "v590"; "chk159"; "chk160"; "v566"; "chk153"; "chk154"; "v573"; "v574"; "pr.4"; "v575"]%string.

(** The W option calls the long-option parser here. *)
Definition w_call : list inst := Eval vm_compute in skipn 8 (b_insts (x_blk "L533")).
(** The block returns the parser's result. *)
Definition w_jump : jump := Eval vm_compute in b_jump (x_blk "L533").
(** The missing-argument answer of the W option returns from this block. *)
Definition getopt_blk570 : block := Eval vm_compute in x_blk "L570".


(** The tail module supplies the report rule, the argument vector and its tactics. *)
Import GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section wtail.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance wtail_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The option argument q, whose object the caller keeps alive, becomes
    the cursor, and the option argument becomes null. The scanner then stands just before
    its call of the long-option parser. The names ks keep their values
    from the caller's environment e0. *)
Lemma wp_getopt_wstore ks e0 e fr q rq x b r Φ :
  avoids ks w_names = true -> keeps ks e0 e ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= ptr_addr q < 2 ^ 64 -> 0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  live_capq DfracDiscarded (ptr_cap q) rq -∗ live b r -∗ pcell b 16 q -∗ pcell b 32 x -∗
  (∀ e', ⌜keeps ks e0 e'⌝ -∗ live b r -∗ pcell b 16 null -∗ pcell b 32 q -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L533") w_call w_jump)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L533") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hk0 H12 Hc1 Hc20 Hq0 Hb Hal Hend Hr.
  iIntros "Hcapq Hl Hab Hcur HK".
  step. step. step. check "Hl".
  load_pointer_dq "Hl Hab Hcapq" by arith.
  iNext. iIntros "Hl Hab _". check "Hl".
  store_pointer "Hl Hcur" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hcur". check "Hl".
  store_pointer "Hl Hab" by (arith) preserving wi_store.
  iNext. iIntros "Hl Hab". iApply ("HK" with "[%] Hl Hab Hcur"). xkeep.
Qed.

(** With no word left after the W, the caller's report rule keeps G when
    the scanner prints errors. Then the option character c becomes the
    bad option, and the answer is ':' when the option string so starts
    with a colon and '?' otherwise. *)
Lemma wp_getopt_wmiss ks e0 e fr c pe po so oo b r av ar ps (G : iProp Σ) T fp dom se sereg mid Φ :
  avoids ks w_names = true -> avoids ks diag_names = true -> keeps ks e0 e ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded po so -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 8 oo -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e0 e' /\ lookup (TAtom "v575") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
     live b r -∗ int_cell b 8 c -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L570") [] (b_jump getopt_blk570))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L544") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksd Hk0 Hrule Hse Hmid H2 H12 H455 Hpo Hpe Hc0 Hc19 Hc Hper Hb Hal Hend Hr Hav Hala Hda Hra Hps
    Hse0 Hsea Hsee Hser.
  iIntros "#Hpo #Hsl #Hsc Hl [%Hoo Hoob] Ha Hcl #Hs HG HK".
  iDestruct (ws_shape with "Hpo") as %(Hcho & Hpop & Hpoe).
  pose proof (sbyte_range so 0 Hcho) as Hs0r.
  iAssert (∀ e1 fr1, ⌜keeps ks e0 e1 /\ lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "v455") e1 = Some (WInt c) /\ lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
      lookup (TAtom "chk19") e1 = Some (WPtr po) /\ lookup (TAtom "pr.1") e1 = Some (WPtr po)⌝ -∗
    live av ar -∗ argv_cells av ps -∗ G -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e1 [] None (Enter (TAtom "L553") (Some fr1))) : gexpr) {{ Φ }})%I
    with "[Hl Hoob HK]" as "HL553".
  { iIntros (e1 fr1 (Hk1 & H12' & H455' & Hc0' & Hc19' & Hpo')) "Ha Hcl HG".
    step. step. check "Hl".
    store_word "Hl Hoob" by (arith) preserving wi_store.
    iNext. iIntros "Hl Hoob".
    iDestruct (ws_byte po so 0 with "Hpo") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
    destruct Hbb as (Hcap & ? & ? & ? & ?).
    iApply (wp_renew_read_dq with "Hbl"); [reflexivity | vx | reflexivity | exact Hcap | rawa | rawa | apply Z.mod_1_r |].
    iNext. iIntros "_".
    load_bytes_dq "Hbl Hbt" decode (apply extended_chr) by rawa.
    iNext; iIntros "_ _". iClear "Hbl Hbt". step. rewrite chr_cmp; [|lia|lia].
    rewrite (Z.mod_small c (2 ^ 32)); [|lia].
    iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte so 0) 58) as [E58 | E58]; close_br.
    - step. step. iApply ("HK" with "[%] Hl [Hoob] Ha Hcl HG"); [split; [xkeep | lk_prove] | by iSplit].
    - step. step. step. step. iApply ("HK" with "[%] Hl [Hoob] Ha Hcl HG"); [split; [xkeep | lk_prove] | by iSplit]. }
  step. iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small pe (2 ^ 32)); [|lia].
  destruct (Z.eqb_spec pe 0) as [Ep | Ep]; cbn [edge_label].
  - iApply ("HL553" with "[%] Ha Hcl HG"). split; [xkeep|]. repeat split; lk_prove.
  - iApply (wp_getopt_diag_wmissing (tail_keys ++ ks) with "Hsl Hsc Ha Hcl Hs HG [HL553]");
      [rewrite avoids_app_l; rewrite Hksd; vm_compute; reflexivity | exact Hrule | exact Hse | exact Hmid | lk_prove
      | lk_prove | exact Hc | exact Hse0 | exact Hsea | exact Hsee | exact Hser | exact Hav | exact Hala | exact Hda
      | exact Hra | exact Hps |].
    iIntros (e1) "%Hk1 Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
    iApply ("HL553" with "[%] Ha Hcl HG"). split; [(eapply keeps_trans; [|exact Hk1]; xkeep)|].
    repeat split; viakeep Hkt.
Qed.

End wtail.
