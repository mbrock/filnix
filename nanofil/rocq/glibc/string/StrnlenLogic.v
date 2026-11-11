(** glibc's own `__memchr` for the NUL of a string, and its
    `__GI___strnlen` (StrchrCode.v's [glibc_strnlen]), which calls it,
    over a [word_string] (WordString.v) at any share.

    memchr(p, 0, n) on the string s at p finds its NUL when that is one
    of the n bytes ([memchr_nul_hit]): [wp_glibc_memchr_nul] for a frame
    of it, [wp_call_glibc_memchr_nul] for a call. strnlen(p, n) returns
    the least of s's length and n: [wp_glibc_strnlen_ws] for a frame of
    it, and [wp_call_glibc_strnlen] for a call of any module whose
    function at the called name is it and at `__GI_memchr` glibc's
    memchr. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrchrCode MemchrLast MemchrLoop
  MemchrFirst MemchrLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** What memchr(p, 0, n) finds on the string s at p: its NUL, when that
    is one of the n bytes. *)
Definition nul_hit (s : list Z) (n : Z) : option nat :=
  if Z.of_nat (List.length s) <? n then Some (List.length s) else None.

(** The string s at p: memchr's search for 0 in its first n bytes finds
    [nul_hit] s n. *)
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

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
Module StrnlenLogicOn (R : Runtime) (LG0 : LogicSig R).
Module MC := MemchrLogicOn R LG0.
Module ML := MC.ML.
Module WS := ML.WS.
Module LG := LG0.
Module L := LG.L.
Import L LG WS ML.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** One step whose premises reduce, as MemchrLast.v's. *)
Ltac st :=
  first
    [ iApply wp_let; [reflexivity | reflexivity | vx | intros ?; reflexivity | iNext]
    | iApply wp_flight; [vx | reflexivity | vx | iNext]
    | iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]
    | iApply wp_goto; iNext ].

(** glibc's memchr of the n bytes from the string s at p for its NUL: it
    returns the pointer to the NUL when that is one of the n bytes, and
    null otherwise, and hands the string back. *)
Lemma wp_glibc_memchr_nul dq p s n e Φ :
  0 <= n < 2 ^ 64 ->
  lookup (TAtom "v0") e = Some (WPtr p) -> lookup (TAtom "v2") e = Some (WInt 0) ->
  lookup (TAtom "v4") e = Some (WInt n) ->
  word_string dq p s -∗ (word_string dq p s -∗ Φ (Ret (WPtr (hit_ptr p (nul_hit s n))))) -∗
  WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hn H0 H2 H4. iIntros "(%b & %reg & %ws & %Hs & Hl & Hw) HK".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp _ Hr _ _].
  iApply (MC.wp_glibc_memchr_dq registry wi ge dq p 0 n b reg ws _ e with "Hl Hw");
    [exact Hc | exact Hb0 | exact Hb8 | exact Hst | exact Hf | exact Hsp | exact Hr | lia | exact Hn
    | exact (memchr_nul_hit _ _ _ _ _ _ Hs Hn) | exact H0 | exact H2 | exact H4 |].
  iIntros "Hl Hw". iApply "HK". iExists b, reg, ws. by iFrame.
Qed.

(** A call of glibc's memchr, in any module whose function at the called
    name g is glibc's `__memchr`, for the NUL of a string at any share:
    the caller resumes with [hit_ptr] of [nul_hit] and the string. *)
Lemma wp_call_glibc_memchr_nul f e ls l r g args rest j dq p s n cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p; WInt 0; WInt n] -> 0 <= n < 2 ^ 64 ->
  find_fn ge g = Some (Defined glibc_memchr) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WPtr (hit_ptr p (nul_hit s n)))) = Some cf' ->
  word_string dq p s -∗ ▷ (word_string dq p s -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hn Hg Hr. iIntros "Hs HK".
  iApply (wp_call_bind with "[Hs HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_memchr_nul with "Hs"); [exact Hn | reflexivity | reflexivity | reflexivity |].
  iIntros "Hs". iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hs").
Qed.

(** glibc's strnlen of the string s at p and n: it returns the least of
    s's length and n, and hands the string back. *)
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
  - st. st. cbn [fr_fn ptr_addr]. iApply wp_branch; [reflexivity|]. iNext.
    rewrite Zmod_0_l (Z.mod_small (a + Z.of_nat (List.length s))); [|lia].
    replace (a + Z.of_nat (List.length s) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). close_if.
    do 3 st. si "v18" (Z.of_nat (List.length s)). st. st.
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    rewrite Z.min_l; [|lia].
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) =>
      replace X with (Z.of_nat (List.length s)) by ar end.
    iApply ("HK" with "Hs").
  - st. st. cbn [fr_fn ptr_addr]. iApply wp_branch; [reflexivity|]. iNext. close_if.
    st. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    rewrite Z.min_r; [|lia].
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) => replace X with n by ar end.
    iApply ("HK" with "Hs").
Qed.

(** A call of glibc's strnlen, in any module whose function at the
    called name g is glibc's `__GI___strnlen` and at `__GI_memchr`
    glibc's `__memchr`, on a string at any share: the caller resumes
    with the least of its length and n, and the string. *)
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
  iApply (wp_call_bind with "[Hs HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_strnlen_ws with "Hs"); [exact Hm | exact Hn |].
  iIntros "Hs". iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hs").
Qed.

End rules.
End StrnlenLogicOn.
