(** A short option ends glibc's scanner in one of two returns. A
    character that the option string does not name, or a colon or a
    semicolon, is an unknown option: the scanner records it as the bad
    option, reports it on stderr if the caller lets it print errors, and
    answers '?'. Every other short option answers with a byte that the
    option blocks chose. This file proves both returns safe: they write
    only the bad-option field of the scanner's own state, and the report
    goes through the caller's rule. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The two returns assign these names. *)
Definition ret_names : list name := Eval vm_compute in
  List.map TAtom ["v505"; "chk143"; "pr.5"; "v696"]%string.

(** The unknown-option return starts in this block. *)
Definition getopt_blk492 : block := Eval vm_compute in x_blk "L492".
(** The other short options return from this block. *)
Definition getopt_blk605 : block := Eval vm_compute in x_blk "L605".

(** A byte read back from a 32-bit word is the byte of the original value. *)
Lemma chr_w_mod32 v : sign_extension 256 128 ((v mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32 = chr_w v.
Proof.
  unfold chr_w, sign_extension. rewrite Z.mod_mod; [|lia].
  rewrite <- (Znumtheory.Zmod_div_mod 256 (2 ^ 32)); [reflexivity | lia | lia | exists (2 ^ 24); reflexivity].
Qed.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptShortRetOn (R : Runtime) (LG0 : LogicSig R).
(** The tail module supplies the report rule, the argument vector and its tactics. *)
Module RT := GetoptReqTailOn R LG0.
Import RT RT.D RT.D.X RT.D.X.I RT.D.X.I.S RT.D.X.I.S.FI RT.D.X.I.S.FI.ML RT.D.X.I.S.FI.LG RT.D.X.I.S.FI.L RT.D.X.I.ST
  RT.D.X.I.GB RT.D.X.A.

Section ret.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance ret_stable : SafepointStable (os_wi w0) := RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance ret_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** An unknown option c is reported through the caller's rule when the
    caller lets the scanner print errors, and the rule keeps G. Then c
    becomes the bad option, and the scanner stands at its return of '?'.
    The names ks keep their values from the caller's environment e. *)
Lemma wp_getopt_unknown ks e fr c pe oo b r av ar ps (G : iProp Σ) T fp dom se sereg mid Φ :
  avoids ks ret_names = true -> avoids ks diag_names = true ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 8 oo -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ live b r -∗ int_cell b 8 c -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L492") [] (b_jump getopt_blk492))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L471") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksd Hrule Hse Hmid H2 H12 H455 Hpe Hc0 Hc Hper Hb Hal Hend Hr Hav Hala Hda Hra Hps
    Hse0 Hsea Hsee Hser.
  iIntros "#Hsl #Hsc Hl [%Hoo Hoob] Ha Hcl #Hs HG HK".
  iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "v455") e1 = Some (WInt c) /\
      lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr (b + 4) (Obj b)))⌝ -∗
    live av ar -∗ argv_cells av ps -∗ G -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e1 [] None (Enter (TAtom "L492") (Some fr1))) : gexpr) {{ Φ }})%I
    with "[Hl Hoob HK]" as "HL492".
  { iIntros (e1 fr1 (Hk1 & H12' & H455' & Hc0')) "Ha Hcl HG".
    en. st. chk "Hl".
    iApply (wp_raw_store_w with "Hl Hoob"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hoob". rewrite (Z.mod_small c (2 ^ 32)); [|lia].
    iApply ("HK" with "[%] Hl [Hoob] Ha Hcl HG"); [xkeep | by iSplit]. }
  en. iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small pe (2 ^ 32)); [|lia].
  destruct (Z.eqb_spec pe 0) as [Ep | Ep]; cbn [edge_label].
  - iApply ("HL492" with "[%] Ha Hcl HG"). split; [apply keeps_refl|]. split; [exact H12|]. split; assumption.
  - iApply (wp_getopt_diag_unknown w0 registry ge (tail_keys ++ ks) with "Hsl Hsc Ha Hcl Hs HG [HL492]");
      [rewrite avoids_app_l; rewrite Hksd; vm_compute; reflexivity | exact Hrule | exact Hse | exact Hmid | lk_prove
      | lk_prove | exact Hc | exact Hse0 | exact Hsea | exact Hsee | exact Hser | exact Hav | exact Hala | exact Hda
      | exact Hra | exact Hps |].
    iIntros (e1) "%Hk1 Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
    iApply ("HL492" with "[%] Ha Hcl HG"). split; [exact Hk1|]. split; [viakeep Hkt|]. split; viakeep Hkt.
Qed.

(** Every other short option returns from one block. Its value v comes
    from the option character when the blocks before it chose that, and
    from the answer pr.7 after a required argument. The block reads v
    back as a signed byte. *)
Lemma wp_getopt_short_ret ks e fr v Φ :
  avoids ks ret_names = true ->
  ((fr = TAtom "L510" \/ fr = TAtom "L619") /\ lookup (TAtom "v455") e = Some (WInt v) \/
   fr = TAtom "L639" /\ lookup (TAtom "pr.7") e = Some (WInt v)) ->
  (∀ e', ⌜keeps ks e e' /\ lookup (TAtom "v696") e' = Some (WInt (chr_w v))⌝ -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L605") [] (b_jump getopt_blk605))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L605") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hv. iIntros "HK".
  destruct Hv as [[[-> | ->] Hv] | [-> Hv]];
    enter; st; iApply ("HK" with "[%]"); (split; [xkeep | rewrite chr_w_mod32; lk_prove]).
Qed.

End ret.
End GetoptShortRetOn.
