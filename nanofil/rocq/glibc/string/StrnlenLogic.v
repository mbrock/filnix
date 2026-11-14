(** In C, `c: strnlen(p, n)` returns the length of string `s` at `p`,
    capped at `n`. Glibc's `__GI___strnlen` implements it by calling
    `__GI_memchr(p, 0, n)` to search the first `n` bytes for the NUL
    terminator, returning `n` when `memchr` returns null or `hit - p`
    otherwise.

    Because `c: strnlen` searches for a NUL byte within a bounded
    prefix, this module specializes `c: memchr` to scanning a
    [word_string] for zero. It then composes that NUL search with the
    pointer subtraction in `c: strnlen` to prove frame and call
    specifications at any ownership share. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrchrCode MemchrLast MemchrLoop
  MemchrFirst MemchrLogic.
From Glibc Require MemchrLast MemchrLogic WordString.
From Glibc Require Import Fix.
From Glibc Require Import GlibcProgram GlibcSpec.
Open Scope Z_scope.
Open Scope list_scope.

(** Function [nul_hit] models what `c: memchr(p, 0, n)` finds on string
    s: the NUL offset when `length s < n`, or `None` when the NUL lies
    at or past n. *)
Definition nul_hit (s : list Z) (n : Z) : option nat :=
  if Z.of_nat (List.length s) <? n then Some (List.length s) else None.

(** Searching the first n bytes of a valid [str_shape] for zero always
    satisfies [loop_hit] with `[nul_hit] s n`. *)
Lemma memchr_nul_hit p b reg ws s n : str_shape p b reg ws s -> 0 <= n < 2 ^ 64 ->
  loop_hit (drop (Z.to_nat (ptr_addr p mod 8)) (wbytes ws)) (0 mod 256) (ptr_addr p)
    (memchr_end (ptr_addr p) n) (nul_hit s n).
Proof.
  intros Hs Hn. pose proof (str_shape_first_zero _ _ _ _ _ Hs) as [Hz Hnz].
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hr Hby Hch].
  set (bs := drop _ (wbytes ws)) in *.
  assert (Hbl : (S (List.length s) <= List.length bs)%nat).
  { pose proof (f_equal (@List.length Z) Hby) as HL. rewrite length_take length_app in HL. cbn [List.length] in HL. pose proof (Nat.le_min_l (S (List.length s)) (List.length bs)). pose proof (Nat.le_min_r (S (List.length s)) (List.length bs)). lia. }
  assert (Hend : ptr_addr p + Z.of_nat (List.length s) + 1 <= r_end reg).
  { unfold wstart in Hf. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (List.length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (List.length s) + 8) 8 ltac:(lia)). lia. }
  unfold memchr_end, nul_hit. change (0 mod 256) with 0.
  destruct (Z.ltb_spec (Z.of_nat (List.length s)) n) as [H|H]; unfold loop_hit.
  - split; [lia|]. split; [exact Hz | exact Hnz].
  - split; [lia|]. intros u Hu. apply Hnz. lia.
Qed.


Module LG := LG0.
Module L := LG.L.
Import L LG WordString MemchrLast.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** To step through IR instructions in [[separation-logic|separation logic]],
    [rules_irisGS] connects the contract registry and world invariant `wi`
    to the Iris program logic. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** This shorthand names the expression type of the instantiated
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** To step past pure instructions without manual boilerplate, [st]
    advances one pure `let`, [[flight]], block entry, or `goto` step
    whose premises reduce. *)


(** To search a [word_string] for its terminating NUL within n bytes,
    [wp_glibc_memchr_nul] executes a call [[frame]] of [glibc_memchr]
    with target byte zero and returns the pointer for [nul_hit]. *)
Lemma wp_glibc_memchr_nul dq p s n e Φ :
  0 <= n < 2 ^ 64 ->
  lookup (TAtom "v0") e = Some (WPtr p) -> lookup (TAtom "v2") e = Some (WInt 0) ->
  lookup (TAtom "v4") e = Some (WInt n) ->
  word_string dq p s -∗ (word_string dq p s -∗ Φ (Ret (WPtr (hit_ptr p (nul_hit s n))))) -∗
  WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hn H0 H2 H4. iIntros "(%b & %reg & %ws & %Hs & Hl & Hw) HK".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp _ Hr _ _].
  iApply (MemchrLogic.wp_glibc_memchr_dq registry wi ge dq p 0 n b reg ws _ e with "Hl Hw");
    [exact Hc | exact Hb0 | exact Hb8 | exact Hst | exact Hf | exact Hsp | exact Hr | lia | exact Hn
    | exact (memchr_nul_hit _ _ _ _ _ _ Hs Hn) | exact H0 | exact H2 | exact H4 |].
  iIntros "Hl Hw". iApply "HK". iExists b, reg, ws. by iFrame.
Qed.

(** The bounded NUL search preserves the string and reports its first terminator. *)
Definition memchr_nul_spec : fspec Σ :=
  FSpec (dfrac * ptr * list Z * Z)
    (fun '(_, p, _, n) => [WPtr p; WInt 0; WInt n])
    (fun '(dq, p, s, n) => ⌜0 <= n < 2 ^ 64⌝ ∗ word_string dq p s)%I
    (fun '(dq, p, s, n) v => ⌜v = Ret (WPtr (hit_ptr p (nul_hit s n)))⌝ ∗ word_string dq p s)%I.

(** Memchr searches for the terminator without consuming the caller's string ownership. *)
Lemma memchr_nul_spec_valid g : find_fn ge g = Some (Defined glibc_memchr) ->
  HasSpec registry wi ge g memchr_nul_spec.
Proof.
  intros Hg [[[dq p] s] n]. exists glibc_memchr. split; [exact Hg|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn in Hfr. injection Hfr as <-. cbn [fs_pre fs_post memchr_nul_spec].
  iIntros "[%Hn Hs] HK". iApply (wp_glibc_memchr_nul with "Hs");
    [exact Hn | reflexivity | reflexivity | reflexivity |].
  iIntros "Hs". iApply "HK". by iFrame.
Qed.

(** The linked program identifies the memchr implementation used by callers. *)
#[global] Instance memchr_nul_has_spec n `{!Defines ge n glibc_memchr} :
  HasSpec registry wi ge (TAtom n) memchr_nul_spec.
Proof. apply memchr_nul_spec_valid. apply defines. Qed.

(** When a caller invokes `c: memchr(p, 0, n)` on a [word_string],
    [wp_call_glibc_memchr_nul] resumes the caller with the pointer for
    [nul_hit] and restores the string. *)
Lemma wp_call_glibc_memchr_nul f e ls l r g args rest j dq p s n cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p; WInt 0; WInt n] -> 0 <= n < 2 ^ 64 ->
  find_fn ge g = Some (Defined glibc_memchr) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WPtr (hit_ptr p (nul_hit s n)))) = Some cf' ->
  word_string dq p s -∗ ▷ (word_string dq p s -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hn Hg Hr. iIntros "Hs HK".
  pose proof (memchr_nul_spec_valid g Hg) as Hspec.
  iApply (wp_call_spec registry wi ge g memchr_nul_spec (dq, p, s, n) with "[Hs]");
    [exact Hx | by iFrame |].
  iIntros (v) "[-> Hs]". iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hs").
Qed.

(** Executing a call [[frame]] of [glibc_strnlen] on a [word_string] at
    any share returns the minimum of the string's length and n, and
    restores the string. *)
Lemma wp_glibc_strnlen_ws dq p s n Φ :
  find_fn ge (TAtom "__GI_memchr") = Some (Defined glibc_memchr) -> 0 <= n < 2 ^ 64 ->
  word_string dq p s -∗ (word_string dq p s -∗ Φ (Ret (WInt (Z.min (Z.of_nat (List.length s)) n)))) -∗
  WP (ERun (mkFrame glibc_strnlen [(TAtom "v2", WInt n); (TAtom "v0", WPtr p)] [] None
              (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hg Hn. iIntros "Hs HK".
  iDestruct "Hs" as "(%b & %reg & %ws & %Hs & Hw)".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hr Hby Hch].
  assert (Hend : ptr_addr p + Z.of_nat (List.length s) + 1 <= r_end reg).
  { unfold wstart in Hf. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (List.length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (List.length s) + 8) 8 ltac:(lia)). lia. }
  iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hs|].
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (wp_call_glibc_memchr_nul with "Hs"); [ | exact Hn | exact Hg | reflexivity |].
  { cbn. rewrite (Z.mod_small n); [reflexivity | lia]. }
  iNext. iIntros "Hs". destruct p as [a c0]. cbn [ptr_addr ptr_cap] in *. unfold nul_hit.
  destruct (Z.ltb_spec (Z.of_nat (List.length s)) n) as [Hls|Hls]; cbn [hit_ptr ptr_addr ptr_cap].
  - step. step. cbn [fr_fn ptr_addr]. iApply wp_branch; [reflexivity|]. iNext.
    rewrite Zmod_0_l (Z.mod_small (a + Z.of_nat (List.length s))); [|lia].
    replace (a + Z.of_nat (List.length s) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). close_if.
    do 3 step. si "v18" (Z.of_nat (List.length s)). step. step.
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    rewrite Z.min_l; [|lia].
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) =>
      replace X with (Z.of_nat (List.length s)) by ar end.
    iApply ("HK" with "Hs").
  - step. step. cbn [fr_fn ptr_addr]. iApply wp_branch; [reflexivity|]. iNext. close_if.
    step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    rewrite Z.min_r; [|lia].
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) => replace X with n by ar end.
    iApply ("HK" with "Hs").
Qed.

(** The bounded length contract returns the smaller of the length and limit. *)
Definition strnlen_spec : fspec Σ :=
  FSpec (dfrac * ptr * list Z * Z)
    (fun '(_, p, _, n) => [WPtr p; WInt n])
    (fun '(dq, p, s, n) => ⌜0 <= n < 2 ^ 64⌝ ∗ word_string dq p s)%I
    (fun '(dq, p, s, n) v =>
      ⌜v = Ret (WInt (Z.min (Z.of_nat (List.length s)) n))⌝ ∗ word_string dq p s)%I.

(** Strnlen uses the linked memchr definition to establish its length contract. *)
Lemma strnlen_spec_valid g : find_fn ge g = Some (Defined glibc_strnlen) ->
  find_fn ge (TAtom "__GI_memchr") = Some (Defined glibc_memchr) ->
  HasSpec registry wi ge g strnlen_spec.
Proof.
  intros Hg Hm [[[dq p] s] n]. exists glibc_strnlen. split; [exact Hg|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn in Hfr. injection Hfr as <-. cbn [fs_pre fs_post strnlen_spec].
  iIntros "[%Hn Hs] HK". iApply (wp_glibc_strnlen_ws with "Hs"); [exact Hm | exact Hn |].
  iIntros "Hs". iApply "HK". by iFrame.
Qed.

(** Linked callers provide definitions of both strnlen and its memchr dependency. *)
#[global] Instance strnlen_has_spec n `{!Defines ge n glibc_strnlen,
    !Defines ge "__GI_memchr" glibc_memchr} :
  HasSpec registry wi ge (TAtom n) strnlen_spec.
Proof. apply strnlen_spec_valid; apply defines. Qed.

(** When a caller invokes `c: strnlen(p, n)` through a module whose
    `__GI_memchr` resolves to [glibc_memchr], [wp_call_glibc_strnlen]
    resumes the caller with the capped length and restores the string. *)
Lemma wp_call_glibc_strnlen f e ls l r g args rest j dq p s n cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p; WInt n] -> 0 <= n < 2 ^ 64 ->
  find_fn ge g = Some (Defined glibc_strnlen) ->
  find_fn ge (TAtom "__GI_memchr") = Some (Defined glibc_memchr) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None)
    (Ret (WInt (Z.min (Z.of_nat (List.length s)) n))) = Some cf' ->
  word_string dq p s -∗ ▷ (word_string dq p s -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hn Hg Hm Hr. iIntros "Hs HK".
  pose proof (strnlen_spec_valid g Hg Hm) as Hspec.
  iApply (wp_call_spec registry wi ge g strnlen_spec (dq, p, s, n) with "[Hs]");
    [exact Hx | by iFrame |].
  iIntros (v) "[-> Hs]". iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hs").
Qed.

End rules.
