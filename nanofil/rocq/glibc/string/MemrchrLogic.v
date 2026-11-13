(** This module proves that glibc's `__memrchr` finds the last byte
    matching `c mod 256` within `n` bytes starting at `p`, discharging
    the `memrchr_spec` premise that [StrrchrLogic] previously left
    abstract.

    When n is zero, `c: memrchr` returns null immediately. Otherwise it
    loads the word containing the final byte, marks lanes matching c,
    and clears any marks at or past the end offset when the end is not
    8-aligned. From there, [MemrchrMask] and [MemrchrLoop] finish the
    scan. The theorems below cover a word window, a [word_string], and
    the contract needed by `c: strrchr`. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrcmpBits StrcmpLoop StrrchrLogic
  MemchrLast MemchrLogic MemrchrCode MemrchrBits MemrchrLoop MemrchrMask.
Open Scope Z_scope.
Open Scope list_scope.

(** This functor packages the whole-function `memrchr` specifications
    over a [[runtime]] R and a program logic instance LG0. *)
Module MemrchrLogicOn (R : Runtime) (LG0 : LogicSig R).
(** Module [RL] provides the backward word-loop invariant. *)
Module RL := MemrchrLoopOn R LG0.
(** Module [SL] supplies the step rules for symbolic execution. *)
Module SL := RL.SL.
(** Module [WS] provides word-window and fractional read helpers. *)
Module WS := SL.WS.
(** Module [MM] handles the final-word mask and join block. *)
Module MM := MemrchrMaskOn R LG0.
(** Module [SR] defines the [memrchr_spec] interface used by `strrchr`. *)
Module SR := StrrchrLogicOn R LG0.
(** Module [LG] re-exports the program logic instance. *)
Module LG := LG0.
(** Module [L] re-exports the core logic definitions. *)
Module L := LG.L.
Import L LG WS SL.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** This instance equips the nanofil language with a program-logic
    state interpretation built from the contract registry and world
    invariant. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** This shorthand names the expression type of the instantiated
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Tactic [sl] advances one pure `let` instruction while keeping its
    result expression symbolic. *)
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** Tactic [sn] advances one `let` instruction and names its integer
    result in the context. *)
Ltac sn := eapply (s_letn registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.
(** Tactic [sf] advances one [[flight]] instruction in the proof mode. *)
Ltac sf := eapply (s_flight registry wi ge); [reflexivity | reflexivity | reflexivity |].
(** Tactic [en] steps into the target block and exposes its instructions
    and terminator. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** Tactic [sg] follows an unconditional `goto` and immediately enters the
    destination block. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** Tactic [sb] advances one conditional `branch` while keeping its
    condition expression symbolic. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** To resolve IR temporary arguments during symbolic execution, [vx]
    looks up each temporary in the environment hypotheses and evaluates
    the remaining argument expressions. *)
Ltac vx :=
  cbn [map2_option map_option flight_arg_x flight_cap arg_x];
  repeat match goal with |- context [value_x ?g ?E ?k (Tmp ?n)] =>
    match goal with H : lookup n _ = Some ?x |- _ =>
      rewrite (value_x_tmp g E k n x); [|look H] end end;
  reflexivity.
(** Tactic [sl'] advances one `let` instruction whose arguments are
    resolved via [vx]. *)
Ltac sl' := eapply (s_let registry wi ge); [reflexivity | reflexivity | vx | intros ?; reflexivity |].
(** Tactic [sf'] advances one [[flight]] instruction whose arguments are
    resolved via [vx]. *)
Ltac sf' := eapply (s_flight registry wi ge); [vx | reflexivity | vx |].
(** Tactic [sb'] advances one `branch` instruction whose arguments are
    resolved via [vx]. *)
Ltac sb' := eapply (s_branch registry wi ge); [vx|].
(** To resolve a temporary lookup in the environment during a proof,
    [lk] skips newer `put` bindings until it finds a matching
    hypothesis. *)
Ltac lk := repeat (rewrite lookup_after_put_other; [|reflexivity]);
  first [rewrite lookup_after_put_same; reflexivity | eassumption].
(** To keep intermediate integers readable, [normt] rewrites the
    integer in the newest temporary to `v` using tactic `tac`. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Tactic [normp] rewrites the address of the pointer stored in
    temporary `name` to `v` by arithmetic. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** Executing [glibc_memrchr] on n bytes starting at offset k in a
    shared word window `ws` returns [hit_ptr] for [last_hit] and
    restores the window [wwin]. *)
Lemma memrchr_win dq b reg ws a cp c (k n : nat) e r Φ :
  0 < b -> (cp = Obj b \/ cp = Ro b) -> b mod 8 = 0 -> b <= a - Z.of_nat k -> a mod 8 = Z.of_nat k ->
  a - Z.of_nat k + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws -> 0 <= c < 2 ^ 32 ->
  Z.of_nat (List.length ws) = (Z.of_nat k + Z.of_nat n + 7) / 8 ->
  last_hit (take n (drop k (wbytes ws))) (c mod 256) r ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr a cp)) -> lookup (TAtom "v2") e = Some (WInt c) ->
  lookup (TAtom "v4") e = Some (WInt (Z.of_nat n)) ->
  wwin dq b reg (a - Z.of_nat k - b) ws -∗
  (wwin dq b reg (a - Z.of_nat k - b) ws -∗ Φ (Ret (WPtr (hit_ptr (mkPtr a cp) r)))) -∗
  WP (ERun (mkFrame glibc_memrchr e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hb0 Hc Hb8 Hba Hk Hend Hreg Hr Hcr Hlen Hhit H0 H2 H4. iIntros "Hw HK".
  assert (Han : Z.of_nat k + Z.of_nat n <= 8 * Z.of_nat (List.length ws)) by (Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Hk8.
  en. sl'. sb. rewrite (Z.mod_small (Z.of_nat n)); [|arith]. change (0 mod 2 ^ 64) with 0.
  destruct n as [|n].
  { (* No bytes: null. *)
    close_if. en. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    destruct r as [t|]; [destruct Hhit as [Ht _]; rewrite take_0 lookup_nil in Ht; discriminate|].
    iApply ("HK" with "Hw"). }
  rewrite (proj2 (Z.eqb_neq _ _)); [|lia]. close_if. en.
  set (W := a - Z.of_nat k) in *. set (Lz := (Z.of_nat k + Z.of_nat (S n) - 1) / 8).
  assert (HW8 : W mod 8 = 0) by (unfold W; Z.div_mod_to_equations; lia).
  assert (HL : 0 <= Lz /\ 8 * Lz < Z.of_nat k + Z.of_nat (S n) <= 8 * Lz + 8) by (unfold Lz; Z.div_mod_to_equations; lia).
  assert (HLw : Lz + 1 = Z.of_nat (List.length ws)) by (rewrite Hlen; unfold Lz; Z.div_mod_to_equations; lia).
  sf'. normp "v17" (a + Z.of_nat (S n)). sl. sl. sl. sl.
  match goal with |- context [put (TAtom "v22") (WInt ?X) _] => replace X with (W + 8 * Lz + 8) end.
  2:{ cbn [ptr_addr]. unwrap. rewrite land_align; [|arith]. arith. }
  sl. sf. normp "v23" (W + 8 * Lz + 8). sl'. normt a ltac:(arith). sl'. normt (a + Z.of_nat (S n)) ltac:(arith).
  sf. normp "v31" (W + 8 * Lz). cbn [ptr_cap].
  iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ (mkPtr (W + 8 * Lz) cp) dq b reg (W - b) ws Lz with "Hw");
    [reflexivity | exact Hc | cbn; lia | lia | exact Hb0 | lia | lia | exact Hreg | exact Hr |].
  iIntros "Hw". pose proof (wrd_range ws Lz Hr) as Hw0. set (w := wrd ws Lz) in *.
  sl'. sl. sl. normt (rep c) ltac:(symmetry; apply rep_ext; exact Hcr).
  sl. normt W ltac:(cbn [ptr_addr]; unwrap; rewrite land_align; [|arith]; arith). sl. sf'. normp "v42" W.
  sl. rewrite (Z.mod_small w (2 ^ 64) Hw0) rep_mod. sl. sl. sl. sl. sl.
  normt (first_mask (Z.lxor w (rep c))) ltac:(reflexivity).
  sl. normt ((a + Z.of_nat (S n)) mod 8) ltac:(symmetry; apply land7; arith). sl. sb.
  pose proof (Z.mod_pos_bound (a + Z.of_nat (S n)) 8 ltac:(lia)) as He8.
  rewrite (Z.mod_small ((a + Z.of_nat (S n)) mod 8)); [|lia]. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec ((a + Z.of_nat (S n)) mod 8) 0) as [He0|He0].
  - (* The end is 8-aligned: all of the last word's bytes count. *)
    close_if. en. rewrite (Z.mod_small _ _ (marks_range w c)).
    iApply (MM.memrchr_mask registry wi ge dq b reg ws a cp c k (S n) Lz 8 (first_mask (Z.lxor w (rep c)))
              with "Hw HK"); [exact Hb0 | exact Hc | exact Hba | exact HW8 | lia | exact Hend | exact Hreg | exact Hr
      | lia | exact HLw | Z.div_mod_to_equations; lia | lia | apply marks_range | | exact Hhit | lk | lk | lk | lk | lk].
    intros i Hi. rewrite marks_byte; [|exact Hi]. rewrite (proj2 (Z.ltb_lt i 8)); [reflexivity | lia].
  - (* The last word's bytes below the end. *)
    close_if. en. sl. sl. sl. sl.
    normt (keep_low (first_mask (Z.lxor w (rep c))) ((a + Z.of_nat (S n)) mod 8)) ltac:(reflexivity). sg. rewrite (Z.mod_small _ _ (keep_low_range _ _)).
    iApply (MM.memrchr_mask registry wi ge dq b reg ws a cp c k (S n) Lz ((a + Z.of_nat (S n)) mod 8)
              (keep_low (first_mask (Z.lxor w (rep c))) ((a + Z.of_nat (S n)) mod 8))
              with "Hw HK"); [exact Hb0 | exact Hc | exact Hba | exact HW8 | lia | exact Hend | exact Hreg | exact Hr
      | lia | exact HLw | unfold W in HW8; Z.div_mod_to_equations; lia | lia | apply keep_low_range | | exact Hhit
      | lk | lk | lk | lk | lk].
    intros i Hi. rewrite keep_low_byte; [|lia | exact Hi]. rewrite marks_byte; [|exact Hi].
    destruct (_ <? _); reflexivity.
Qed.

(** Executing a call [[frame]] of [glibc_memrchr] over a [word_string]
    and its NUL terminator at any share returns a pointer to the last
    byte matching `c mod 256`, or null, and restores the string. *)
Lemma wp_glibc_memrchr_ws fr dq p s c Φ : 0 <= c < 2 ^ 32 ->
  call_frame glibc_memrchr [WPtr p; WInt c; WInt (Z.of_nat (List.length s) + 1)] = Some fr ->
  word_string dq p s -∗
  (word_string dq p s -∗ Φ (Ret (WPtr (hit_ptr p (last_byte (c mod 256) (s ++ [0])))))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof.
  intros Hcr Hfr. iIntros "(%b & %reg & %ws & %Hs & Hw) HK". cbn in Hfr. injection Hfr as <-.
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hwr Hby Hch].
  destruct p as [a cp]. unfold wstart in *. cbn [ptr_addr ptr_cap] in *.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Hk8.
  set (k := Z.to_nat (a mod 8)) in Hby. assert (Hk : a mod 8 = Z.of_nat k) by (unfold k; rewrite Z2Nat.id; lia).
  rewrite Hk in Hf Hlen. iEval (rewrite Hk) in "Hw".
  iApply (memrchr_win dq b reg ws a cp c k (S (List.length s)) _ _ with "[Hw] [HK]");
    [exact Hb0 | exact Hc | exact Hb8 | pose proof (Z.div_mod a 8 ltac:(lia)); pose proof (Z.div_mod b 8 ltac:(lia)); nia
    | exact Hk | exact Hf | exact Hsp | exact Hwr | exact Hcr | rewrite Hlen; f_equal; lia | | reflexivity
    | reflexivity | cbn; do 2 f_equal; lia | | ].
  - rewrite Hby. apply last_byte_hit.
  - iExact "Hw".
  - iIntros "Hw". iApply "HK". iExists b, reg, ws. iSplit; [done|]. unfold wstart. cbn [ptr_addr]. rewrite Hk. iExact "Hw".
Qed.

(** Because `c: strrchr` delegates its backward scan to `c: memrchr`,
    [glibc_memrchr_spec] packages the frame specification above into the
    [SR.memrchr_spec] contract. *)
Lemma glibc_memrchr_spec :
  find_fn ge (TAtom "__GI___memrchr") = Some (Defined glibc_memrchr) -> SR.memrchr_spec registry wi ge.
Proof.
  intros Hf. exists glibc_memrchr. split; [exact Hf|]. split; [intros; eexists; reflexivity|].
  intros fr dq p s c Φ Hc Hfr. iIntros "Hs HK". iApply (wp_glibc_memrchr_ws with "Hs HK"); [exact Hc | exact Hfr].
Qed.

End rules.
End MemrchrLogicOn.
