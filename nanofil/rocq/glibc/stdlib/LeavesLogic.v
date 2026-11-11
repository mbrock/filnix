(** Triples for the leaves of user glibc's stdlib that read only
    thread-local or locale state (docs/glibc-ir.md), over any registry,
    world and genv in which their symbols are bound, so a program
    linked with them uses each as a rule at its call:

    - [wp_glibc_errno_location]: `__errno_location` returns the
      address of the thread's `errno`, the global `__libc_errno`;
    - [wp_glibc_ctype_b_loc]: `__ctype_b_loc` returns the address of
      the thread's ctype class table pointer, `__libc_tsd_CTYPE_B`;
    - [wp_glibc_mb_cur_max]: `__ctype_get_mb_cur_max` reads the
      current locale's LC_CTYPE data, `MB_CUR_MAX` its word at 160
      (`values[_NL_ITEM_INDEX (_NL_CTYPE_MB_CUR_MAX)]`, 56 + 13 * 8),
      through two pointers, all at shares;
    - [wp_glibc_mbsinit_null] and [wp_glibc_mbsinit]: `mbsinit` of a
      null state is 1, else whether the state's 4-byte `__count` is 0,
      read at a share.

    The decoded functions come from StdlibCode.v's linked module, and
    [wp_check_read_dq] is the read check at a share of an object's
    life that the triples here and in AllocLogic.v and AtexitLogic.v
    use. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic MemLogic.
From Glibc Require Import StdlibCode GlibcLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The module *)

(** The linked module of the stdlib units ([stdlib_term]). *)
Definition stdlib_module : module :=
  match decode_module stdlib_term with Some md => md | None => [] end.

(** The function named n of [stdlib_module], or an empty one. *)
Definition stdlib_fn (n : string) : func :=
  match find_direct (TAtom n) stdlib_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** glibc's `__GI___errno_location`. *)
Definition errno_location_fn : func := Eval vm_compute in stdlib_fn "__GI___errno_location".
(** glibc's `__ctype_b_loc`. *)
Definition ctype_b_loc_fn : func := Eval vm_compute in stdlib_fn "__ctype_b_loc".
(** glibc's `__ctype_get_mb_cur_max`. *)
Definition mb_cur_max_fn : func := Eval vm_compute in stdlib_fn "__ctype_get_mb_cur_max".
(** glibc's `__mbsinit`. *)
Definition mbsinit_fn : func := Eval vm_compute in stdlib_fn "__mbsinit".

(** ## Arithmetic tactics *)

(** Drop each wrap to 2^64 or 2^32 of a term with no wrap inside that
    arithmetic shows the identity, innermost first. *)
Ltac unwrap :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] =>
        lazymatch x with context [_ mod _] => fail | _ => rewrite (Z.mod_small x (2 ^ 64)); [|lia] end
    | |- context [?x mod 2 ^ 32] =>
        lazymatch x with context [_ mod _] => fail | _ => rewrite (Z.mod_small x (2 ^ 32)); [|lia] end
    end.

(** Decide each comparison arithmetic decides. *)
Ltac decide_cmp :=
  repeat match goal with
    | |- context [?x =? ?y] =>
        first [rewrite (proj2 (Z.eqb_neq x y)); [|lia] | rewrite (proj2 (Z.eqb_eq x y)); [|lia]]
    | |- context [?x <? ?y] =>
        first [rewrite (proj2 (Z.ltb_lt x y)); [|lia] | rewrite (proj2 (Z.ltb_ge x y)); [|lia]]
    end.

(** Compute each closed shift factor 2 ^ (n mod m). *)
Ltac pow_closed :=
  repeat match goal with |- context [2 ^ (?n mod ?m)] =>
    let v := fresh "v" in let Ev := fresh "Ev" in
    remember (2 ^ (n mod m)) as v eqn:Ev; vm_compute in Ev; subst v end.

(** Simplify the goal's addresses, wraps, shift factors, comparisons
    and the branches they decide. *)
Ltac simp :=
  cbn [ptr_addr ptr_cap null]; rewrite ?Zmod_0_l; pow_closed;
  repeat progress (unwrap; decide_cmp; cbn [negb]; cbv beta iota; rewrite ?Zmod_0_l); cbn [edge_label].

(** A 32-bit sign extension keeps the low 32 bits. *)
Lemma ext_sw_mod x : extension Sw x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  unfold extension, sign_extension. destruct (_ <=? _); [|apply Zmod_mod].
  rewrite Zminus_mod Z_mod_same_full Z.sub_0_r !Zmod_mod. reflexivity.
Qed.

(** Decide the condition of the branch the goal enters, if arithmetic
    decides it, simplifying only the condition. *)
Ltac decide_branch :=
  try match goal with |- context [edge_label (if ?c then _ else _)] =>
    let E := fresh "E" in
    first [ assert (E : c = false) by (simp; reflexivity) | assert (E : c = true) by (simp; reflexivity) ];
    rewrite E; clear E; cbn [edge_label]
  end.

(** Strip the later of a step from the goal alone, where no hypothesis
    holds a later. *)
Ltac nx := iApply bi.later_intro.

(** An address or alignment fact, by arithmetic below 2^64. *)
Ltac arith := cbn [ptr_addr ptr_cap null]; unfold raw_address; rewrite ?Z.add_0_r; unwrap;
  first [lia | apply Z.mod_1_r | reflexivity | assumption | Z.div_mod_to_equations; lia].

(** ## Rule application

    [iApply] of a rule costs a proof-mode search at each step, and its
    term a kernel check; these lemmas apply a step rule as a plain
    entailment instead. *)

(** Apply a step rule ⊢ ▷ P -∗ Q to the goal Q, leaving P. *)
Lemma step_wand {PROP : bi} (Δ : environments.envs PROP) (P Q : PROP) :
  (⊢ ▷ P -∗ Q) -> environments.envs_entails Δ P -> environments.envs_entails Δ Q.
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H". iApply HW. iNext. iExact "H".
Qed.

(** Apply a step rule R -∗ ▷ (R' -∗ P) -∗ Q, over one resource, to
    the goal R -∗ Q, leaving R' -∗ P. *)
Lemma step_res1 {PROP : bi} (Δ : environments.envs PROP) (R R' P Q : PROP) :
  (⊢ R -∗ ▷ (R' -∗ P) -∗ Q) -> environments.envs_entails Δ (R' -∗ P) -> environments.envs_entails Δ (R -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR". iApply (HW with "HR"). iNext. iExact "H".
Qed.

(** [step_res1] over two resources. *)
Lemma step_res2 {PROP : bi} (Δ : environments.envs PROP) (R1 R2 R1' R2' P Q : PROP) :
  (⊢ R1 -∗ R2 -∗ ▷ (R1' -∗ R2' -∗ P) -∗ Q) ->
  environments.envs_entails Δ (R1' -∗ R2' -∗ P) -> environments.envs_entails Δ (R1 -∗ R2 -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR1 HR2". iApply (HW with "HR1 HR2"). iNext. iExact "H".
Qed.

(** Apply a rule over the resource H by the tactic t. *)
Ltac rule1 H t := iRevert H; eapply step_res1; [t |]; iIntros H.

(** Apply a rule over the resources H1 and H2 by the tactic t. *)
Ltac rule2 H1 H2 t := iRevert H2; iRevert H1; eapply step_res2; [t |]; iIntros H1; iIntros H2.

(** The leaves over the [[runtime]] R and the Logic instance LG0. *)
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
(** The Iris instance of the registry and wi. *)
Local Instance leaves_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** [wp_check_read] at a share dq of the life of b: a [[check]] for
    reading of the pointer p, through a read-write or read-only
    capability for b, whose checked bytes lie in its bounds and are
    aligned, binds d to p. *)
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

(** Close the instance premise a rule's eapply leaves. *)
Ltac inst := lazymatch goal with |- SafepointStable _ => exact _ | _ => idtac end.

(** One step whose premises reduce, by the instruction it runs: a pure
    let, a flight, entering a block, or a goto. *)
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

(** A let copying the global s, bound to p in the genv by Hs. *)
Ltac st_global Hs :=
  eapply step_wand;
    [eapply wp_let; inst;
       [reflexivity | reflexivity | cbn [map2_option value_x]; rewrite Hs; reflexivity | intros ?; reflexivity] |].

(** `__errno_location` returns the pointer errno_p the genv binds to
    `__libc_errno`, owning nothing. *)
Lemma wp_glibc_errno_location errno_p Φ :
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some errno_p ->
  Φ (Ret (WPtr errno_p)) -∗
  WP (ERun (mkFrame errno_location_fn [] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hs. iIntros "HΦ". st. st_global Hs.
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iExact "HΦ".
Qed.

(** `__ctype_b_loc` returns the pointer tsd_p the genv binds to
    `__libc_tsd_CTYPE_B`, owning nothing. *)
Lemma wp_glibc_ctype_b_loc tsd_p Φ :
  lookup (TAtom "__libc_tsd_CTYPE_B") (ge_globals ge) = Some tsd_p ->
  Φ (Ret (WPtr tsd_p)) -∗
  WP (ERun (mkFrame ctype_b_loc_fn [] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hs. iIntros "HΦ". st. st_global Hs.
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iExact "HΦ".
Qed.

(** `__ctype_get_mb_cur_max`, where `__libc_tsd_LOCALE` is the
    8-aligned object tb, holding the pointer to the locale object lb,
    whose first pointer, `__locales[LC_CTYPE]`, is to the LC_CTYPE data
    object cb, whose cell at 160 holds v: it returns v's low 32 bits,
    `MB_CUR_MAX`. Every piece is owned at a share and handed back. *)
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

(** `mbsinit` of a pointer whose address is 0: 1, owning nothing. *)
Lemma wp_glibc_mbsinit_null p Φ :
  ptr_addr p = 0 -> Φ (Ret (WInt 1)) -∗
  WP (ERun (mkFrame mbsinit_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct p as [a c]. cbn [ptr_addr]. intros ->. iIntros "HΦ".
  st. st. st. st. iApply wp_branch; [reflexivity|]. nx. simp. st.
  iApply wp_ret; [reflexivity | reflexivity |]. nx. iExact "HΦ".
Qed.

(** `mbsinit` of the pointer p to offset o of the object b, at a
    nonzero address, read-write or read-only, where the four bytes bs
    of the state's `__count` are owned at a share: 1 if they are 0,
    else 0, the pieces handed back. *)
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
