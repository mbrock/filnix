(** When `c: strncmp` exits one of its word loops—either on a differing
    or zero byte, or when at most eight bytes remain—it jumps to one of
    three inlined copies of the final comparison epilogue. Each epilogue
    computes the comparison mask, locates the first stopping byte from
    its trailing bit count, and returns zero if the remaining byte limit
    expires first or the byte difference otherwise.

    Because basic blocks bind many local variables in sequence, resolving
    environment lookups by rewriting grows quadratically with block
    length. This module applies [lk_put] directly to keep each lookup
    step constant-time, and proves the three epilogue lemmas for
    `c: strncmp`. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrncmpCode
  StrcmpBits StrcmpLoop StrncmpBits.
Open Scope Z_scope.
Open Scope list_scope.

(** Lemma [lk_put] resolves a variable lookup past an unrelated binding
    by backward application so environment terms do not expand. *)
Lemma lk_put {A} k k' (v : A) ps x : name_eqb k k' = false -> lookup k ps = x -> lookup k (put k' v ps) = x.
Proof. intros H E. rewrite lookup_after_put_other; [exact E | exact H]. Qed.

(** Tactic [lkf] walks through a chain of variable updates to find the
    value given by hypothesis H. *)
Ltac lkf H := repeat (apply lk_put; [reflexivity|]); exact H.

(** Tactic [vxf] resolves every operand lookup in the current instruction
    from the environment hypotheses. *)
Ltac vxf :=
  cbn [map2_option map_option flight_arg_x flight_cap arg_x];
  repeat match goal with |- context [value_x ?g ?E ?k (Tmp ?n)] =>
    match goal with H : lookup n _ = Some ?x |- _ =>
      rewrite (value_x_tmp g E k n x); [|lkf H] end end;
  reflexivity.

(** Module [StrncmpLoopOn] proves the final comparison epilogues over a
    given [[runtime]] R and logic instance LG0. *)
Module StrncmpLoopOn (R : Runtime) (LG0 : LogicSig R).
(** Module [SL] provides the shared stepping and window-read lemmas. *)
Module SL := StrcmpLoopOn R LG0.
(** Module [WS] provides the word-window string representation. *)
Module WS := SL.WS.
(** Module [LG] re-exports the program logic instance LG0. *)
Module LG := LG0.
(** Module [L] provides the nanofil language definition for LG. *)
Module L := LG.L.
Import L LG WS SL.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** Instance [rules_irisGS] builds the [[iris]] machine semantics from
    the external registry and world invariant. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** Notation [gexpr] abbreviates expressions in the instantiated language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** Notation [ent] abbreviates proof-mode entailment in the Iris context. *)
Local Notation ent Δ P := (environments.envs_entails Δ P).

(** Tactic [sl] steps past a `let` instruction while keeping its bound
    value symbolic. *)
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** Tactic [sv] steps past a `let` instruction after resolving its
    operand variables from the environment. *)
Ltac sv := eapply (s_let registry wi ge); [reflexivity | reflexivity | vxf | intros ?; reflexivity |].
(** Tactic [sn] steps past an integer `let` and names the resulting
    integer in the context. *)
Ltac sn := eapply (s_letn registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.
(** Tactic [en] enters the target basic block of a pending frame jump. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** Tactic [sg] steps through a `goto` terminator and immediately enters
    its destination block. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** Tactic [sb] steps past a conditional `branch` instruction without
    evaluating its condition. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** Tactic [normt] normalizes the integer in the newest local variable
    to v using tactic tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.

(** Tactic [fin_tac] steps through glibc's final word comparison on x
    and y with remaining count r, returning [strncmp_res]. *)
Ltac fin_tac x y r Hl HK Hc A1 A2 :=
  assert (Hr0 : 0 < r) by (destruct Hl as (_ & _ & _ & ? & _); lia);
  do 10 sv; normt (cmp_mask x y) ltac:(reflexivity); sl; sb;
  pose proof (cmp_mask_range x y);
  rewrite (Z.mod_small (cmp_mask x y)); [|lia]; change (0 mod 2 ^ 64) with 0;
  let j := fresh "j" in let Hj := fresh "Hj" in let Hst := fresh "Hst" in let Hs := fresh "Hs" in
  destruct (word_first_stop x y) as [(j & Hj & Hst & Hs) | Hs];
  [ let Ht := fresh "Ht" in let Hn := fresh "Hn" in
    destruct (cmp_mask_first x y j Hj Hst Hs) as [Ht Hn];
    rewrite (proj2 (Z.eqb_neq _ _) Hn); close_if;
    en; do 15 sn;
    match goal with |- context [mkFrame _ (put _ (WInt ?t) _) _ _ _] =>
      let H := fresh in assert (H : t = tail (cmp_mask x y)) by (eapply tail_chain; eassumption);
      rewrite H Ht; clear H end;
    repeat match goal with H : ?v = _ |- _ => is_var v; clear H end;
    sg; sl; normt j ltac:(arith); sl; normt j ltac:(arith); sv; sb;
    rewrite (Z.mod_small r); [|lia]; rewrite (Z.mod_small j); [|lia];
    rewrite (fin_stop _ _ _ _ _ _ _ _ _ j Hc A1 A2 Hl Hj Hst Hs) in HK;
    let Erj := fresh "Erj" in destruct (r <=? j) eqn:Erj; close_if;
    [ en; eapply (s_ret registry wi ge); [reflexivity | reflexivity | reflexivity | exact HK]
    | pose proof (byte_of_range x j); pose proof (byte_of_range y j);
      en; sl; normt (8 * j) ltac:(arith); sv; sl; normt (byte_of x j) ltac:(symmetry; apply ub_shift; lia);
      sv; sl; normt (byte_of y j) ltac:(symmetry; apply ub_shift; lia);
      sl; normt ((byte_of x j - byte_of y j) mod 2 ^ 32) ltac:(arith);
      sg; eapply (s_ret registry wi ge); [reflexivity | reflexivity | rewrite !Zmod_mod; reflexivity | exact HK] ]
  | let Hr8 := fresh "Hr8" in let Hres := fresh "Hres" in
    destruct (fin_none _ _ _ _ _ _ _ _ _ Hc A1 A2 Hl Hs) as [Hr8 Hres];
    rewrite (cmp_mask_none x y Hs); close_if;
    en; sl; normt 8 ltac:(arith); sl; normt 8 ltac:(arith); sv; sb;
    rewrite (Z.mod_small r); [|lia]; change (8 mod 2 ^ 64) with 8; replace (r <=? 8) with true by (symmetry; apply Z.leb_le; lia); close_if;
    en; eapply (s_ret registry wi ge); [reflexivity | reflexivity | symmetry; exact Hres | exact HK] ].

(** Lemma [fin_a] verifies the final comparison epilogue for the aligned
    word loop, where pr.3 and pr.5 hold x and y and pr.4 holds r. *)
Lemma fin_a Δ e fl s1 s2 f1 f2 c x y L r Φ :
  lookup (TAtom "iw_1.pr.3") e = Some (WInt x) -> lookup (TAtom "iw_1.pr.5") e = Some (WInt y) ->
  lookup (TAtom "iw_1.pr.4") e = Some (WInt r) -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> r < 2 ^ 64 ->
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> last_cmp f1 f2 c x y L r ->
  ent Δ (Φ (Ret (WInt (strncmp_res (c + r) s1 s2)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strncmp e [] None (Enter (TAtom "iw_1.iw_2.start") (Some fl))) : gexpr) {{ Φ }}).
Proof. intros H3 H5 H4 X Y Rr Hc A1 A2 Hl HK. en. fin_tac x y r Hl HK Hc A1 A2. Qed.

(** Lemma [fin_b] verifies the final comparison epilogue for the
    unaligned word loop against merged word y in v58. *)
Lemma fin_b Δ e fl s1 s2 f1 f2 c x y L r Φ :
  lookup (TAtom "iw_2.pr.4") e = Some (WInt x) -> lookup (TAtom "iw_2.v58") e = Some (WInt y) ->
  lookup (TAtom "iw_2.pr.6") e = Some (WInt r) -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> r < 2 ^ 64 ->
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> last_cmp f1 f2 c x y L r ->
  ent Δ (Φ (Ret (WInt (strncmp_res (c + r) s1 s2)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strncmp e [] None (Enter (TAtom "iw_2.iw_2.start") (Some fl))) : gexpr) {{ Φ }}).
Proof. intros H3 H5 H4 X Y Rr Hc A1 A2 Hl HK. en. fin_tac x y r Hl HK Hc A1 A2. Qed.

(** Function [nblk] looks up basic block l in `__GI_strncmp`. *)
Definition nblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks glibc_strncmp) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** Constant [blk32] holds the basic block for the trailing-bytes exit
    of an unaligned second string. *)
Definition blk32 : block := Eval vm_compute in nblk "iw_2.L32".

(** Lemma [fin_c] verifies the final comparison epilogue after block
    `iw_2.L32` resolves its phi bindings when an unaligned second string
    ends early. *)
Lemma fin_c Δ e s1 s2 f1 f2 c x y L r Φ :
  lookup (TAtom "iw_2.pr.3") e = Some (WInt x) -> lookup (TAtom "iw_2.pr.9") e = Some (WInt y) ->
  lookup (TAtom "iw_2.pr.5") e = Some (WInt r) -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> r < 2 ^ 64 ->
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> last_cmp f1 f2 c x y L r ->
  ent Δ (Φ (Ret (WInt (strncmp_res (c + r) s1 s2)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strncmp e [] None (Exec (TAtom "iw_2.L32") (b_insts blk32) (b_jump blk32))) : gexpr)
           {{ Φ }}).
Proof. intros H3 H5 H4 X Y Rr Hc A1 A2 Hl HK. cbn [blk32 b_insts b_jump]. fin_tac x y r Hl HK Hc A1 A2. Qed.

End rules.
End StrncmpLoopOn.
