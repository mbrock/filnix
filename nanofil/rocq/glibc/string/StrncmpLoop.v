(** The last comparisons of glibc's own `strncmp` (`__GI_strncmp`,
    StrncmpCode.v), for StrncmpWords.v's loops and StrncmpLogic.v's
    triple over [word_string]s (WordString.v).

    glibc's word loops end, for a word pair with a difference or a zero
    or with at most 8 bytes left, in one of three copies of the same
    last comparison its inlining makes ([fin_a], [fin_b], [fin_c]): it
    finds the words' first stop by the comparison mask and its
    population count, and returns 0 when the count of bytes left ends
    at or before it, else the difference of the bytes there
    (StrncmpBits.v's [fin_stop], [fin_none]). Lookups through a block's
    puts are applied ([lk_put]), not rewritten, which keeps each step's
    cost fixed. *)

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

(** Looking k up after a [put] of another name: what it answered
    before. Applied, not rewritten, so its cost does not grow with the
    values the environment holds. *)
Lemma lk_put {A} k k' (v : A) ps x : name_eqb k k' = false -> lookup k ps = x -> lookup k (put k' v ps) = x.
Proof. intros H E. rewrite lookup_after_put_other; [exact E | exact H]. Qed.

(** The lookup of a temporary through the puts of a block, by H below them. *)
Ltac lkf H := repeat (apply lk_put; [reflexivity|]); exact H.

(** MemchrLast.v's [vx], each lookup by [lkf]. *)
Ltac vxf :=
  cbn [map2_option map_option flight_arg_x flight_cap arg_x];
  repeat match goal with |- context [value_x ?g ?E ?k (Tmp ?n)] =>
    match goal with H : lookup n _ = Some ?x |- _ =>
      rewrite (value_x_tmp g E k n x); [|lkf H] end end;
  reflexivity.

(** The last comparisons over the [[runtime]] R and the Logic instance LG0. *)
Module StrncmpLoopOn (R : Runtime) (LG0 : LogicSig R).
(** StrcmpLoop.v's steps and reads over R and LG0. *)
Module SL := StrcmpLoopOn R LG0.
(** Strings' windows. *)
Module WS := SL.WS.
(** The Logic instance. *)
Module LG := LG0.
(** Its language. *)
Module L := LG.L.
Import L LG WS SL.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** The proof mode's entailment. *)
Local Notation ent Δ P := (environments.envs_entails Δ P).

(** StrcmpLoop.v's steps: a let, its value whole. *)
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** A let that reads the abstract environment ([vxf]). *)
Ltac sv := eapply (s_let registry wi ge); [reflexivity | reflexivity | vxf | intros ?; reflexivity |].
(** A let of an integer, named x with its equation E ([s_letn]). *)
Ltac sn := eapply (s_letn registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.
(** Entering the block a frame is entering. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** A goto and the block it enters. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** A branch, its condition left whole. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** Replace the integer the newest temporary holds by v, proved by tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.

(** glibc's last comparison of the words x and y, r bytes left
    ([last_cmp]), from its first block on: the comparison mask, its
    population count, and 0 or the difference of the bytes at the first
    stop, returned as [strncmp_res]. *)
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

(** The last comparison of the aligned loop: x and y are pr.3 and
    pr.5, r is pr.4. *)
Lemma fin_a Δ e fl s1 s2 f1 f2 c x y L r Φ :
  lookup (TAtom "iw_1.pr.3") e = Some (WInt x) -> lookup (TAtom "iw_1.pr.5") e = Some (WInt y) ->
  lookup (TAtom "iw_1.pr.4") e = Some (WInt r) -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> r < 2 ^ 64 ->
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> last_cmp f1 f2 c x y L r ->
  ent Δ (Φ (Ret (WInt (strncmp_res (c + r) s1 s2)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strncmp e [] None (Enter (TAtom "iw_1.iw_2.start") (Some fl))) : gexpr) {{ Φ }}).
Proof. intros H3 H5 H4 X Y Rr Hc A1 A2 Hl HK. en. fin_tac x y r Hl HK Hc A1 A2. Qed.

(** The last comparison of the unaligned loop: x is pr.4, y is v58,
    the merged word, and r is pr.6. *)
Lemma fin_b Δ e fl s1 s2 f1 f2 c x y L r Φ :
  lookup (TAtom "iw_2.pr.4") e = Some (WInt x) -> lookup (TAtom "iw_2.v58") e = Some (WInt y) ->
  lookup (TAtom "iw_2.pr.6") e = Some (WInt r) -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> r < 2 ^ 64 ->
  Forall (fun ch => 0 < ch < 256) s1 -> agree_str f1 s1 -> agree_str f2 s2 -> last_cmp f1 f2 c x y L r ->
  ent Δ (Φ (Ret (WInt (strncmp_res (c + r) s1 s2)))) ->
  ent Δ (WP (ERun (mkFrame glibc_strncmp e [] None (Enter (TAtom "iw_2.iw_2.start") (Some fl))) : gexpr) {{ Φ }}).
Proof. intros H3 H5 H4 X Y Rr Hc A1 A2 Hl HK. en. fin_tac x y r Hl HK Hc A1 A2. Qed.

(** The block of glibc's strncmp labelled l. *)
Definition nblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks glibc_strncmp) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** The last comparison's block of an unaligned second string. *)
Definition blk32 : block := Eval vm_compute in nblk "iw_2.L32".

(** The last comparison of an unaligned second string, after L32's
    phis: x is pr.3, y is pr.9, r is pr.5. *)
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
