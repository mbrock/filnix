(** Several small functions in userland glibc's `c: stdlib` only read
    thread-local or locale state without allocating memory or making
    system calls. This module proves [[hoare-triple|Hoare triples]] for
    four such leaf functions over any [[runtime]] registry, world, and
    [[genv|global environment]] that binds their global symbols.

    Two of those functions simply return pointers to thread-local
    globals: [wp_glibc_errno_location] returns the address of
    `__libc_errno`, and [wp_glibc_ctype_b_loc] returns the address of
    `__libc_tsd_CTYPE_B`. The third, [wp_glibc_mb_cur_max], follows the
    thread's locale pointer `__libc_tsd_LOCALE` to its `LC_CTYPE` table
    and reads the 32-bit `MB_CUR_MAX` value at offset 160 under shared
    fractional ownership.

    The fourth leaf, `c: mbsinit`, tests whether a multibyte conversion
    state is in its initial state. Lemma [wp_glibc_mbsinit_null] shows
    that a null pointer returns 1, while [wp_glibc_mbsinit] reads the
    4-byte `__count` field at a fractional share and returns 1 when it
    is zero. Both this file and its siblings also rely on
    [wp_check_read_dq] to verify read checks against fractional
    liveness tokens. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic MemLogic.
From Glibc Require Import StdlibCode GlibcLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The module

    The compiled fixture [stdlib_term] bundles the `c: stdlib` units
    into one decoded IR module. Here we decode that module and extract
    the four leaf function bodies that the proofs below step through. *)

(** [stdlib_module] holds the decoded IR module for the linked
    `c: stdlib` units in [stdlib_term]. *)
Definition stdlib_module : module :=
  match decode_module stdlib_term with Some md => md | None => [] end.

(** [stdlib_fn] looks up a defined function named n in [stdlib_module],
    falling back to an empty stub when missing. *)
Definition stdlib_fn (n : string) : func :=
  match find_direct (TAtom n) stdlib_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** [errno_location_fn] is the decoded IR body of glibc's
    `__GI___errno_location`. *)
Definition errno_location_fn : func := Eval vm_compute in stdlib_fn "__GI___errno_location".
(** [ctype_b_loc_fn] is the decoded IR body of glibc's
    `__ctype_b_loc`. *)
Definition ctype_b_loc_fn : func := Eval vm_compute in stdlib_fn "__ctype_b_loc".
(** [mb_cur_max_fn] is the decoded IR body of glibc's
    `__ctype_get_mb_cur_max`. *)
Definition mb_cur_max_fn : func := Eval vm_compute in stdlib_fn "__ctype_get_mb_cur_max".
(** [mbsinit_fn] is the decoded IR body of glibc's `__mbsinit`. *)
Definition mbsinit_fn : func := Eval vm_compute in stdlib_fn "__mbsinit".

(** ## Arithmetic tactics

    Stepping through compiled C functions leaves modulo wraps, pointer
    arithmetic, and integer comparisons at every instruction. These
    shared tactics simplify those expressions by computation and `lia`
    so the proofs in this file and in [AllocLogic](AllocLogic.v) and
    [AtexitLogic](AtexitLogic.v) stay short. *)

(** Modulo wraps around 64-bit and 32-bit operations block `lia` from
    seeing linear inequalities. The tactic [unwrap] removes any innermost
    wrap whenever `lia` proves its argument is already in range. *)
Ltac unwrap :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] =>
        lazymatch x with context [_ mod _] => fail | _ => rewrite (Z.mod_small x (2 ^ 64)); [|lia] end
    | |- context [?x mod 2 ^ 32] =>
        lazymatch x with context [_ mod _] => fail | _ => rewrite (Z.mod_small x (2 ^ 32)); [|lia] end
    end.

(** The tactic [decide_cmp] rewrites every integer equality or ordering
    comparison that `lia` can settle directly. *)
Ltac decide_cmp :=
  repeat match goal with
    | |- context [?x =? ?y] =>
        first [rewrite (proj2 (Z.eqb_neq x y)); [|lia] | rewrite (proj2 (Z.eqb_eq x y)); [|lia]]
    | |- context [?x <? ?y] =>
        first [rewrite (proj2 (Z.ltb_lt x y)); [|lia] | rewrite (proj2 (Z.ltb_ge x y)); [|lia]]
    end.

(** The tactic [pow_closed] evaluates closed shift multipliers of the
    form `2 ^ (n mod m)` by computation. *)
Ltac pow_closed :=
  repeat match goal with |- context [2 ^ (?n mod ?m)] =>
    let v := fresh "v" in let Ev := fresh "Ev" in
    remember (2 ^ (n mod m)) as v eqn:Ev; vm_compute in Ev; subst v end.

(** The tactic [simp] normalizes pointer fields, evaluates closed shift
    factors, removes redundant wraps, and resolves comparisons across
    the goal. *)
Ltac simp :=
  cbn [ptr_addr ptr_cap null]; rewrite ?Zmod_0_l; pow_closed;
  repeat progress (unwrap; decide_cmp; cbn [negb]; cbv beta iota; rewrite ?Zmod_0_l); cbn [edge_label].

(** Sign-extending a 32-bit value preserves its low 32 bits modulo 2^32,
    as [ext_sw_mod] verifies. *)
Lemma ext_sw_mod x : extension Sw x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  unfold extension, sign_extension. destruct (_ <=? _); [|apply Zmod_mod].
  rewrite Zminus_mod Z_mod_same_full Z.sub_0_r !Zmod_mod. reflexivity.
Qed.

(** The tactic [decide_branch] settles the condition of a conditional
    branch whenever arithmetic simplification determines whether it is
    true or false. *)
Ltac decide_branch :=
  try match goal with |- context [edge_label (if ?c then _ else _)] =>
    let E := fresh "E" in
    first [ assert (E : c = false) by (simp; reflexivity) | assert (E : c = true) by (simp; reflexivity) ];
    rewrite E; clear E; cbn [edge_label]
  end.

(** Stepping through a long function can slow down if every instruction
    searches all proof hypotheses for time-stepped facts. When no
    hypothesis needs advancing, [nx] advances the goal by one step
    directly. *)
Ltac nx := iApply bi.later_intro.

(** Address checks and alignment constraints reduce to linear arithmetic
    once pointer records are unfolded. The tactic [arith] discharges
    those side conditions by removing wraps and calling `lia`. *)
Ltac arith := cbn [ptr_addr ptr_cap null]; unfold raw_address; rewrite ?Z.add_0_r; unwrap;
  first [lia | apply Z.mod_1_r | reflexivity | assumption | Z.div_mod_to_equations; lia].

(** ## Rule application

    Using Iris's `iApply` at every instruction performs a full proof-mode
    context search and builds a large kernel term. Instead, these helper
    lemmas apply a step rule as a direct entailment on the proof-mode
    environment, keeping both proof checking and interactive stepping
    fast. *)

(** [step_wand] applies a zero-resource step rule directly to the
    current proof-mode context. *)
Lemma step_wand {PROP : bi} (Δ : environments.envs PROP) (P Q : PROP) :
  (⊢ ▷ P -∗ Q) -> environments.envs_entails Δ P -> environments.envs_entails Δ Q.
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H". iApply HW. iNext. iExact "H".
Qed.

(** [step_res1] applies a step rule that consumes and returns one
    named separation-logic resource. *)
Lemma step_res1 {PROP : bi} (Δ : environments.envs PROP) (R R' P Q : PROP) :
  (⊢ R -∗ ▷ (R' -∗ P) -∗ Q) -> environments.envs_entails Δ (R' -∗ P) -> environments.envs_entails Δ (R -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR". iApply (HW with "HR"). iNext. iExact "H".
Qed.

(** [step_res2] extends [step_res1] to step rules that thread two
    named resources across an instruction. *)
Lemma step_res2 {PROP : bi} (Δ : environments.envs PROP) (R1 R2 R1' R2' P Q : PROP) :
  (⊢ R1 -∗ R2 -∗ ▷ (R1' -∗ R2' -∗ P) -∗ Q) ->
  environments.envs_entails Δ (R1' -∗ R2' -∗ P) -> environments.envs_entails Δ (R1 -∗ R2 -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR1 HR2". iApply (HW with "HR1 HR2"). iNext. iExact "H".
Qed.

(** Stepping through a memory read or check requires handing a named
    hypothesis to a step rule and getting it back without triggering an
    `iApply` search. The tactic [rule1] automates that pattern for one
    resource H using [step_res1]. *)
Ltac rule1 H t := iRevert H; eapply step_res1; [t |]; iIntros H.

(** Memory loads often thread both a liveness token and a cell resource
    across the same instruction. The tactic [rule2] automates that
    pattern for two hypotheses H1 and H2 using [step_res2]. *)
Ltac rule2 H1 H2 t := iRevert H2; iRevert H1; eapply step_res2; [t |]; iIntros H1; iIntros H2.

(** The module [LeavesOn] proves the leaf specifications over an
    arbitrary [[runtime]] R and logic instance LG0. *)
Module LeavesOn (R : Runtime) (LG0 : LogicSig R).
Module GL := GlibcLogicOn R LG0.
Module ML := MemLogicOn R LG0.
Module LG := LG0.
Module L := LG.L.
Import L LG GL ML.

Local Opaque errno_location_fn ctype_b_loc_fn mb_cur_max_fn mbsinit_fn.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** Every Iris proof needs a state interpretation linking memory and
    world state to the operational semantics. [leaves_irisGS] builds
    that instance from [registry], [wi], and [ge]. *)
Local Instance leaves_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** [gexpr] abbreviates the expression type of the parameterized
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Reading through a pointer only requires shared ownership of the
    target object's liveness token. Lemma [wp_check_read_dq] verifies a
    read [[check]] using a fractional share dq of [liveq] and binds the
    checked pointer to d. *)
Lemma wp_check_read_dq f e ls l d lo hi al args rest j classes p b reg dq Φ :
  op_arg_classes (Check lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi Read al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp H1 H2 H3. apply (wp_read_dq _ _ _ _ _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_check. exact (access_read _ _ _ _ _ _ _ Hp E H1 H2 H3).
Qed.

(** Applying a step rule creates a side condition showing that the world
    stays valid across garbage-collection safepoints. The tactic [inst]
    closes that [SafepointStable] obligation by typeclass search. *)
Ltac inst := lazymatch goal with |- SafepointStable _ => exact _ | _ => idtac end.

(** The tactic [st] advances the proof by one symbolic IR step,
    dispatching on whether the frame sits at a let binding, a
    [[flight]], a block entry, or a jump. *)
Ltac st :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (ERun (mkFrame _ _ _ _ ?pos)) _) =>
      lazymatch pos with
      | Exec _ (Let _ _ _ _ :: _) _ =>
          eapply step_wand;
            [eapply wp_let; inst; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity] |]
      | Exec _ (Flight _ _ _ _ :: _) _ =>
          eapply step_wand; [eapply wp_flight; inst; [reflexivity | reflexivity | reflexivity] |]
      | Enter _ _ =>
          eapply step_wand; [eapply wp_enter; inst; [reflexivity | reflexivity] |]; cbn [b_insts b_jump]
      | Exec _ [] (JGoto _) => eapply step_wand; [eapply wp_goto; inst |]
      end
  end.

(** Functions in this file read global variables such as `__libc_errno`
    and `__libc_tsd_LOCALE` directly. The tactic [st_global] steps past
    a global pointer load using its binding hypothesis Hs. *)
Ltac st_global Hs :=
  eapply step_wand;
    [eapply wp_let; inst;
       [reflexivity | reflexivity | cbn [map2_option value_x]; rewrite Hs; reflexivity | intros ?; reflexivity] |].

(** Calling `__errno_location` returns the pointer `errno_p` that the
    global environment binds to `__libc_errno` without requiring any
    heap ownership, as [wp_glibc_errno_location] proves. *)
Lemma wp_glibc_errno_location errno_p Φ :
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some errno_p ->
  Φ (Ret (WPtr errno_p)) -∗
  WP (ERun (mkFrame errno_location_fn [] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hs. iIntros "HΦ". st. st_global Hs.
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iExact "HΦ".
Qed.

(** Calling `__ctype_b_loc` returns the pointer `tsd_p` that the global
    environment binds to `__libc_tsd_CTYPE_B` without requiring any heap
    ownership, as [wp_glibc_ctype_b_loc] proves. *)
Lemma wp_glibc_ctype_b_loc tsd_p Φ :
  lookup (TAtom "__libc_tsd_CTYPE_B") (ge_globals ge) = Some tsd_p ->
  Φ (Ret (WPtr tsd_p)) -∗
  WP (ERun (mkFrame ctype_b_loc_fn [] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hs. iIntros "HΦ". st. st_global Hs.
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iExact "HΦ".
Qed.

(** Calling `__ctype_get_mb_cur_max` reads `MB_CUR_MAX` by following
    `__libc_tsd_LOCALE` to the locale object, loading its `LC_CTYPE`
    pointer, and reading the 32-bit word at offset 160. Theorem
    [wp_glibc_mb_cur_max] proves that the call returns the low 32 bits
    of v and restores all fractional shares. *)
Lemma wp_glibc_mb_cur_max tb treg lc lb lreg cc cb creg v dq1 dq2 dq3 dq4 dq5 dq6 Φ :
  lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (mkPtr tb (Obj tb)) ->
  (lc = Obj lb \/ lc = Ro lb) -> (cc = Obj cb \/ cc = Ro cb) ->
  0 <= tb -> tb mod 8 = 0 -> tb + 8 <= r_end treg <= 2 ^ 64 ->
  0 <= lb -> lb mod 8 = 0 -> lb + 8 <= r_end lreg <= 2 ^ 64 ->
  0 <= cb -> cb + 168 <= r_end creg <= 2 ^ 64 ->
  liveq dq1 tb treg ∗ pcellq dq2 tb 0 (mkPtr lb lc) ∗ liveq dq3 lb lreg ∗ pcellq dq4 lb 0 (mkPtr cb cc) ∗
    liveq dq5 cb creg ∗ icellq dq6 cb 160 v -∗
  (liveq dq1 tb treg ∗ pcellq dq2 tb 0 (mkPtr lb lc) ∗ liveq dq3 lb lreg ∗ pcellq dq4 lb 0 (mkPtr cb cc) ∗
     liveq dq5 cb creg ∗ icellq dq6 cb 160 v -∗ Φ (Ret (WInt (v mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame mb_cur_max_fn [] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hs Hlc Hcc Ht0 Ht8 Htb Hl0 Hl8 Hlb Hc0 Hcb.
  iIntros "(Ht & Htc & Hl & Hlc & Hc & Hv) HΦ". st. st_global Hs.
  iApply (wp_check_read_dq with "Ht"); [reflexivity | reflexivity | left; reflexivity | arith | arith | arith |].
  nx. iIntros "Ht".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Ht Htc [Hl]");
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith | |].
  { destruct Hlc as [-> | ->]; iExact "Hl". }
  nx. iIntros "Ht Htc Hl".
  iAssert (liveq dq3 lb lreg) with "[Hl]" as "Hl"; [destruct Hlc as [-> | ->]; iExact "Hl"|].
  iApply (wp_check_read_dq with "Hl"); [reflexivity | reflexivity | exact Hlc | arith | arith | arith |].
  nx. iIntros "Hl".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 with "Hl Hlc [Hc]");
    [reflexivity | reflexivity | exact Hlc | arith | arith | arith | |].
  { destruct Hcc as [-> | ->]; iExact "Hc". }
  nx. iIntros "Hl Hlc Hc".
  iAssert (liveq dq5 cb creg) with "[Hc]" as "Hc"; [destruct Hcc as [-> | ->]; iExact "Hc"|].
  st. st.
  iApply (wp_check_read_dq with "Hc"); [reflexivity | reflexivity | exact Hcc | arith | arith | arith |].
  nx. iIntros "Hc".
  iApply (wp_raw_load_sub_read_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 160 with "Hc Hv");
    [reflexivity | reflexivity | reflexivity | exact Hcc | arith |].
  nx. iIntros "Hc Hv".
  iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | nx].
  iApply wp_ret; [reflexivity | reflexivity |]. nx.
  change (2 ^ (8 * (narrow_type Uw).1)) with (2 ^ 32). rewrite !Zmod_mod. unfold extension. rewrite Zmod_mod.
  rewrite (Z.mod_small (v mod 2 ^ 32) (2 ^ 64)); [|pose proof (Z.mod_pos_bound v (2 ^ 32)); lia].
  iApply "HΦ". iFrame.
Qed.

(** Passing a null pointer to `c: mbsinit` indicates an initial shift
    state without reading memory. Lemma [wp_glibc_mbsinit_null] proves
    that the call returns 1 with no ownership preconditions. *)
Lemma wp_glibc_mbsinit_null p Φ :
  ptr_addr p = 0 -> Φ (Ret (WInt 1)) -∗
  WP (ERun (mkFrame mbsinit_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct p as [a c]. cbn [ptr_addr]. intros ->. iIntros "HΦ".
  st. st. st. st. iApply wp_branch; [reflexivity|]. nx. simp. st.
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iExact "HΦ".
Qed.

(** Calling `c: mbsinit` on a non-null pointer p checks the 4-byte
    `__count` field at offset o of object b. Under fractional ownership
    of b's liveness token and those four bytes bs, [wp_glibc_mbsinit]
    returns 1 when bs encodes zero and 0 otherwise, restoring both
    shares. *)
Lemma wp_glibc_mbsinit p b reg o bs dq1 dq2 Φ :
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> ptr_addr p = b + o -> 0 < b + o < 2 ^ 64 -> 0 <= o ->
  b + o + 4 <= r_end reg -> List.length bs = 4%nat ->
  liveq dq1 b reg -∗ bytesq dq2 b o bs -∗
  (liveq dq1 b reg -∗ bytesq dq2 b o bs -∗ Φ (Ret (WInt (if of_bytes bs mod 2 ^ 32 =? 0 then 1 else 0)))) -∗
  WP (ERun (mkFrame mbsinit_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct p as [a c]. cbn [ptr_addr ptr_cap]. intros Hc -> Ha Ho Hend Hlen.
  iIntros "Hl Hb HΦ". st. st. st. st.
  iApply wp_branch; [reflexivity|]. nx. simp. st.
  iApply (wp_check_read_dq with "Hl"); [reflexivity | reflexivity | exact Hc | arith | arith | arith |].
  nx. iIntros "Hl".
  iApply (wp_raw_load_sub_bytes_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ o with "Hl Hb");
    [reflexivity | reflexivity | rewrite Hlen; reflexivity | reflexivity | exact Hc | arith |].
  nx. iIntros "Hl Hb". st. st. st.
  iApply wp_ret; [reflexivity | reflexivity |]. nx.
  rewrite !Zmod_mod ext_sw_mod Zmod_0_l.
  destruct (of_bytes bs mod 2 ^ 32 =? 0); unwrap; iApply ("HΦ" with "Hl Hb").
Qed.

End rules.
End LeavesOn.
