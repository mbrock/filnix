(** After checking the first aligned word, glibc's `__strlen` scans
    subsequent 8-byte [[word|words]] one at a time until it finds one
    containing a zero byte. This module proves the loop invariant
    [loop_spec_dq] by induction over the remaining words, at any
    ownership share of the memory it reads, so that [StrlenWord] can
    verify whole calls to `c: strlen`.

    To locate the NUL byte inside the final word, `__strlen` runs a
    sixteen-step population count. The proof names each intermediate
    bit-twiddling value so the calculation stays readable and fast to
    check, and [StrlenWord] reuses the same helper tactics. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString.
Open Scope Z_scope.
Open Scope list_scope.

(** When `__strlen` finds a zero byte in a word, it isolates the lowest
    matching bit and counts the trailing bits to locate the byte index.
    This lemma equates the sixteen-step wrapped IR chain with [tail] r. *)
Lemma tail_chain r x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 :
  x = - (r mod 2 ^ 64) mod 2 ^ 64 ->
  x0 = Z.land (r mod 2 ^ 64) (x mod 2 ^ 64) ->
  x1 = (x0 mod 2 ^ 64 - 1 mod 2 ^ 64) mod 2 ^ 64 ->
  x2 = x1 mod 2 ^ 64 / 2 ^ ((1 mod 2 ^ 32) mod 64) ->
  x3 = Z.land (x2 mod 2 ^ 64) (6148914691236517205 mod 2 ^ 64) ->
  x4 = (x1 mod 2 ^ 64 - x3 mod 2 ^ 64) mod 2 ^ 64 ->
  x5 = Z.land (x4 mod 2 ^ 64) (3689348814741910323 mod 2 ^ 64) ->
  x6 = x4 mod 2 ^ 64 / 2 ^ ((2 mod 2 ^ 32) mod 64) ->
  x7 = Z.land (x6 mod 2 ^ 64) (3689348814741910323 mod 2 ^ 64) ->
  x8 = (x5 mod 2 ^ 64 + x7 mod 2 ^ 64) mod 2 ^ 64 ->
  x9 = x8 mod 2 ^ 64 / 2 ^ ((4 mod 2 ^ 32) mod 64) ->
  x10 = (x8 mod 2 ^ 64 + x9 mod 2 ^ 64) mod 2 ^ 64 ->
  x11 = Z.land (x10 mod 2 ^ 64) (1085102592571150095 mod 2 ^ 64) ->
  x12 = (x11 mod 2 ^ 64 * (72340172838076673 mod 2 ^ 64)) mod 2 ^ 64 ->
  x13 = x12 mod 2 ^ 64 / 2 ^ ((56 mod 2 ^ 32) mod 64) ->
  x13 = tail r.
Proof.
  intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->. unfold tail.
  change (1 mod 2 ^ 64) with 1. change (6148914691236517205 mod 2 ^ 64) with 6148914691236517205.
  change (3689348814741910323 mod 2 ^ 64) with 3689348814741910323.
  change (1085102592571150095 mod 2 ^ 64) with 1085102592571150095.
  change (72340172838076673 mod 2 ^ 64) with 72340172838076673.
  change (1 mod 2 ^ 32) with 1. change (2 mod 2 ^ 32) with 2. change (4 mod 2 ^ 32) with 4. change (56 mod 2 ^ 32) with 56.
  reflexivity.
Qed.

(** To keep proof terms small after a sixteen-step population count,
    [set_tail] collapses the final temporary to `[tail] r` and discards
    the intermediate variable chain. *)
Ltac set_tail name r :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] =>
    let H := fresh in assert (H : X = tail r) by (eapply tail_chain; eassumption); rewrite H; clear H;
    repeat match goal with H : ?x = _ |- _ => is_var x; clear H end end.

(** Tactic [unwrap] removes 64-bit and 32-bit modulo wraps when linear
    arithmetic shows the value already fits in range. *)
Ltac unwrap :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)); [|lia]
    | |- context [?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)); [|lia]
    end.

(** Tactic [clear_junk] discards non-arithmetic hypotheses from the
    context so that `lia` does not waste time scanning them. *)
Ltac clear_junk :=
  repeat match goal with
    H : ?T |- _ =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | and (Z.le _ _) _ => fail
      | lt _ _ => fail | le _ _ => fail
      | _ => clear H
      end
    end.
(** Tactic [pow_closed] evaluates closed power-of-two shift factors by
    computation before handing the goal to `lia`. *)
Ltac pow_closed :=
  repeat match goal with |- context [2 ^ (?n mod ?m)] =>
    let v := fresh "v" in let Ev := fresh "Ev" in
    remember (2 ^ (n mod m)) as v eqn:Ev; vm_compute in Ev; subst v end.
(** Tactic [arith] normalizes pointer and address projections, strips
    non-arithmetic hypotheses, and solves linear or division goals. *)
Ltac arith := cbn [ptr_addr ptr_cap extension]; unfold raw_address; clear_junk; pow_closed; unwrap;
  first [lia | Z.div_mod_to_equations; lia].

(** Tactic [close_if] simplifies a conditional branch edge once its
    boolean condition reduces to `true` or `false`. *)
Ltac close_if :=
  match goal with |- context [edge_label (if ?c then _ else _)] =>
    first [change c with true | change c with false]
  end; cbn [edge_label].

(** Tactic [look] resolves a lookup in the environment by skipping over
    newer `put` bindings until it reaches hypothesis H. *)
Ltac look H := repeat (rewrite lookup_after_put_other; [|reflexivity]); exact H.

(** Tactic [set_int] normalizes the integer stored in temporary `name`
    to `v` by computation or [arith]. *)
Ltac set_int name v :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by first [reflexivity | arith] end.
(** Tactic [set_ptr] normalizes the address stored in pointer temporary
    `name` to `v` by computation or [arith]. *)
Ltac set_ptr name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by first [reflexivity | arith] end.

(** Tactic [gen_top] binds the newest temporary's integer expression to
    a fresh variable unless it is already a constant or variable, keeping
    the population-count terms small. *)
Ltac gen_top :=
  try match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] =>
    lazymatch X with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
    tryif is_var X then fail else (let x := fresh "x" in let E := fresh "E" in remember X as x eqn:E) end.

(** This functor packages the `c: strlen` word-loop proof over a
    [[runtime]] R and a program logic instance LG0. *)
Module StrlenLoopOn (R : Runtime) (LG0 : LogicSig R).
Module WS := WordStringOn R LG0.
Module LG := LG0.
Module L := LG.L.
Import L LG WS.

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

(** Tactic [st] advances the symbolic execution by one pure `let`,
    `flight`, block entry, or `goto` step whose premises reduce by
    computation. *)
Ltac st :=
  first
    [ iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | iNext]
    | iApply wp_flight; [reflexivity | reflexivity | reflexivity | iNext]
    | iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]
    | iApply wp_goto; iNext ].

(** Block `L28` is the main word loop of [glibc_strlen]: it advances to
    the next 8-byte word, checks read access, loads the word, and tests
    whether it contains a zero byte. *)
Definition strlen_blk28 : block := Eval vm_compute in
  match find_block (TAtom "L28") (fn_blocks glibc_strlen) with
  | Some b => b | None => mkBlock (TAtom "L28") [] [] JUnreachable end.

(** This lemma proves the word-loop invariant for `__strlen`: starting
    from an 8-aligned offset o with the previous word pointer in `pr.1`
    and the string start address a in `v4`, the loop scans the remaining
    words ws until it finds the first zero byte t bytes in, returns the
    distance from a to that NUL byte, and restores the live [[region]]
    and word pieces. *)
Lemma loop_spec_dq dq b reg c a ws o e from t q Φ :
  (c = Obj b \/ c = Ro b) -> 0 <= o -> 8 <= b + o -> (b + o) mod 8 = 0 -> 0 <= a <= b + o ->
  b + o + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws -> first_zero (wbytes ws) t ->
  ptr_addr q = b + o - 8 -> ptr_cap q = c ->
  phis_env ge (b_phis strlen_blk28) from e = Some (put (TAtom "pr.1") (WPtr q) e) ->
  lookup (TAtom "v4") e = Some (WInt a) ->
  liveq dq b reg -∗ ptsq dq (words_ps b o ws) -∗
  (liveq dq b reg -∗ ptsq dq (words_ps b o ws) -∗ Φ (Ret (WInt (b + o + Z.of_nat t - a)))) -∗
  WP (ERun (mkFrame glibc_strlen e [] None (Enter (TAtom "L28") from)) : gexpr) {{ Φ }}.
Proof.
  revert o e from t q. induction ws as [|w ws IH]; intros o e from t q Hc Ho Hb8 Hal Ha Hend Hreg Hr Hz Hqa Hqc Hphi Hv4.
  { destruct Hz as [Hz _]. cbn in Hz. discriminate. }
  cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  iIntros "Hl Hps HK". cbn [words_ps]. rewrite ptsq_app. iDestruct "Hps" as "[Hw Hps]".
  iApply wp_enter; [reflexivity | exact Hphi |]. iNext. cbn [b_insts b_jump strlen_blk28].
  st. set_ptr "v32" (b + o).
  iApply (wp_check_read_dq with "Hl").
  { reflexivity. } { reflexivity. } { cbn [ptr_cap]. rewrite Hqc. exact Hc. } { arith. } { arith. } { apply Z.mod_1_r. }
  iNext. iIntros "Hl".
  iApply (wp_raw_load_read_dq with "Hl Hw"); [reflexivity | reflexivity | cbn [ptr_cap]; rewrite Hqc; exact Hc | arith |].
  iNext. iIntros "Hl Hw".
  apply Forall_cons_1 in Hr as [Hw0 Hr]. rewrite (Z.mod_small w (2 ^ 64) Hw0).
  do 4 st. set_int "iw_4.iw_1.v13" (loop_mask w).
  st. iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (loop_mask w) (2 ^ 64) (loop_mask_range w)) Zmod_0_l.
  destruct (Nat.lt_ge_cases t 8) as [Ht|Ht].
  - (* w holds the NUL, at byte t. *)
    destruct (first_zero_in w ws 0 t ltac:(lia) Hz ltac:(lia)) as [Hzt Hnz]. cbn [Nat.add] in Hzt.
    assert (Hlow : forall i, 0 <= i < Z.of_nat t -> byte_of w i <> 0).
    { intros i Hi. specialize (Hnz (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hnz; [exact Hnz | lia]. }
    assert (Hb : byte_of (loop_mask w) (Z.of_nat t) = 128) by (apply loop_mask_at; [lia | exact Hlow | exact Hzt]).
    assert (Hm : (loop_mask w =? 0) = false).
    { apply Z.eqb_neq. intros E. rewrite E in Hb. unfold byte_of in Hb. rewrite Z.div_0_l in Hb; [discriminate|].
      apply Z.pow_nonzero; lia. }
    rewrite Hm. close_if.
    st. iApply wp_branch; [reflexivity|]. iNext. close_if.
    do 16 (st; gen_top).
    set_tail "iw_5.iw_3.iw_1.iw_1.v22" (loop_mask w).
    rewrite (tail_first (loop_mask w) (Z.of_nat t) (loop_mask_range w) (loop_mask_01 w) ltac:(lia) Hb
      (fun i Hi => loop_mask_below w (Z.of_nat t) i ltac:(lia) Hlow Hi)).
    st. st. set_int "iw_5.iw_3.iw_1.iw_1.v23" (8 * Z.of_nat t + 7).
    st. set_int "iw_5.iw_3.iw_1.v27" (Z.of_nat t).
    st. set_int "v41" (Z.of_nat t).
    st. set_ptr "v42" (b + o + Z.of_nat t).
    st.
    iApply wp_let;
      [reflexivity | reflexivity
      | cbn [map2_option]; rewrite (value_x_tmp _ _ _ (TAtom "v4") (WInt a)); [reflexivity | look Hv4]
      | intros ?; reflexivity | iNext].
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) => replace X with (b + o + Z.of_nat t - a) by arith end.
    iApply ("HK" with "Hl [$Hw $Hps]").
  - (* w has no zero byte: the next word. *)
    destruct (first_zero_past w ws 0 t ltac:(lia) Hz ltac:(lia)) as [Hnz Hz']. cbn [Nat.add] in Hz'.
    assert (Hm : loop_mask w = 0).
    { apply zero_word; [apply loop_mask_range|]. intros i Hi. apply (loop_mask_below w 8 i); [lia | | lia].
      intros k Hk. specialize (Hnz (Z.to_nat k) ltac:(lia)). rewrite Z2Nat.id in Hnz; [exact Hnz | lia]. }
    rewrite Hm. close_if.
    iApply (IH (o + 8) _ (Some (TAtom "L28")) (t - 8)%nat (mkPtr (b + o) (ptr_cap q)) with "Hl Hps [Hw HK]").
    + exact Hc.
    + lia.
    + lia.
    + replace (b + (o + 8)) with (b + o + 1 * 8) by ring. rewrite Z_mod_plus_full. exact Hal.
    + lia.
    + lia.
    + exact Hreg.
    + exact Hr.
    + exact Hz'.
    + cbn. lia.
    + exact Hqc.
    + reflexivity.
    + look Hv4.
    + iIntros "Hl Hps". replace (b + (o + 8) + Z.of_nat (t - 8) - a) with (b + o + Z.of_nat t - a) by lia.
      iApply ("HK" with "Hl [$Hw $Hps]").
Qed.

End rules.
End StrlenLoopOn.
