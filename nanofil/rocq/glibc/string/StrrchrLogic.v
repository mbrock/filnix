(** In C, `c: strrchr(p, c)` returns a pointer to the last occurrence
    of `c mod 256` in the string at `p`, including its terminating NUL
    byte, or null if `c mod 256` does not appear. Glibc's `__GI_strrchr`
    computes the string's length with `__GI_strlen` and then searches
    `length s + 1` bytes backwards with `__GI___memrchr`.

    Because `c: memrchr` is compiled in a separate file, this module
    assumes its backward-search contract as a hypothesis. That lets us
    verify `c: strrchr` on any shared string independently of how
    `c: memrchr` is implemented. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrlenWord StrchrCode MemchrLast.
From Glibc Require StrlenWord WordString.
From Glibc Require Import Fix.
From Glibc Require Import GlibcProgram GlibcSpec.
Open Scope Z_scope.
Open Scope list_scope.

(** Helper [last_from] scans byte list bs from index i, updating acc
    whenever an element equals target byte c. *)
Fixpoint last_from (c : Z) (i : nat) (bs : list Z) (acc : option nat) : option nat :=
  match bs with
  | [] => acc
  | b :: bs' => last_from c (S i) bs' (if Z.eqb b c then Some i else acc)
  end.

(** Function [last_byte] returns the index of the last occurrence of
    byte c in bs, or `None` if c is absent. *)
Definition last_byte (c : Z) (bs : list Z) : option nat := last_from c 0 bs None.


Module LG := LG0.
Module L := LG.L.
Import L LG WordString.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** Each instruction must preserve the caller's interpretation of memory.
    This instance supplies that interpretation to [[separation-logic|separation logic]]. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** This shorthand names the expression type of the instantiated
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Because `__GI___memrchr` is linked by name from another translation
    unit, [memrchr_spec] abstracts its call contract: on a [word_string]
    at any share, searching `length s + 1` bytes returns the last
    `c mod 256` or null and restores the string. *)
Definition memrchr_spec : Prop :=
  exists F, find_fn ge (TAtom "__GI___memrchr") = Some (Defined F) /\
  (forall p c n, is_Some (call_frame F [WPtr p; WInt c; WInt n])) /\
  forall fr dq p s c Φ, 0 <= c < 2 ^ 32 ->
    call_frame F [WPtr p; WInt c; WInt (Z.of_nat (List.length s) + 1)] = Some fr ->
    ⊢ word_string dq p s -∗
      (word_string dq p s -∗ Φ (Ret (WPtr (hit_ptr p (last_byte (c mod 256) (s ++ [0])))))) -∗
      WP (ERun fr : gexpr) {{ Φ }}.

(** Executing a call [[frame]] of [glibc_strrchr] on a [word_string] at
    any share returns a pointer to the last matching byte from
    [last_byte], or null, and restores the string. *)
Lemma wp_glibc_strrchr_ws (Hm : memrchr_spec) dq p s c Φ :
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) -> 0 <= c < 2 ^ 32 ->
  word_string dq p s -∗
  (word_string dq p s -∗ Φ (Ret (WPtr (hit_ptr p (last_byte (c mod 256) (s ++ [0])))))) -∗
  WP (ERun (mkFrame glibc_strrchr [(TAtom "v2", WInt c); (TAtom "v0", WPtr p)] [] None
              (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  destruct Hm as (F & HF & Hfr & Hspec). intros Hsl Hc. iIntros "Hs HK".
  iDestruct "Hs" as "(%b & %reg & %ws & %Hs & Hw)".
  pose proof Hs as [Hcap Hb0 Hb8 Hst Hf Hsp Hlen Hr Hby Hch].
  assert (Hn : Z.of_nat (List.length s) + 1 < 2 ^ 64).
  { unfold wstart in Hf. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (List.length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (List.length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). lia. }
  iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hs|].
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (StrlenWord.wp_call_glibc_strlen registry wi ge with "Hs"); [reflexivity | exact Hsl | reflexivity |].
  iNext. iIntros "Hs".
  iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | iNext].
  destruct (Hfr p c (Z.of_nat (List.length s) + 1)) as [fr Hfr'].
  iApply (wp_call_bind with "[-]"); [ | exact HF | |].
  { cbn. rewrite (Z.mod_small c); [|lia]. rewrite !(Z.mod_small (Z.of_nat (List.length s))); try lia.
    rewrite (Z.mod_small 1); [|lia]. rewrite (Z.mod_small (Z.of_nat (List.length s) + 1)); [reflexivity | lia]. }
  { rewrite (Z.mod_small (Z.of_nat (List.length s) + 1)); [exact Hfr' | lia]. }
  iNext. iApply (Hspec with "Hs"); [exact Hc | exact Hfr' |]. iIntros "Hs".
  iExists _. iSplit; [done|]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "Hs").
Qed.

(** Backward search preserves the string and returns its last matching byte. *)
Definition strrchr_spec : fspec Σ :=
  FSpec (dfrac * ptr * list Z * Z)
    (fun '(_, p, _, c) => [WPtr p; WInt c])
    (fun '(dq, p, s, c) => ⌜0 <= c < 2 ^ 32⌝ ∗ word_string dq p s)%I
    (fun '(dq, p, s, c) v =>
      ⌜v = Ret (WPtr (hit_ptr p (last_byte (c mod 256) (s ++ [0]))))⌝ ∗ word_string dq p s)%I.

(** Strrchr first measures the string and then searches backwards, preserving the caller's ownership. *)
Lemma strrchr_spec_valid (Hm : memrchr_spec) g :
  find_fn ge g = Some (Defined glibc_strrchr) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  HasSpec registry wi ge g strrchr_spec.
Proof.
  intros Hg Hsl [[[dq p] s] c]. exists glibc_strrchr. split; [exact Hg|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn in Hfr. injection Hfr as <-. cbn [fs_pre fs_post strrchr_spec].
  iIntros "[%Hc Hs] HK". iApply (wp_glibc_strrchr_ws Hm with "Hs"); [exact Hsl | exact Hc|].
  iIntros "Hs". iApply "HK". by iFrame.
Qed.

(** A linked program must provide both helper functions before a caller can search backwards. *)
#[global] Instance strrchr_has_spec n `{!Defines ge n glibc_strrchr,
    !Defines ge "__GI_strlen" glibc_strlen} (Hm : memrchr_spec) :
  HasSpec registry wi ge (TAtom n) strrchr_spec.
Proof. apply (strrchr_spec_valid Hm); apply defines. Qed.

(** When a caller invokes `c: strrchr(p, c)` in a module providing
    `__GI_strlen` and [memrchr_spec], [wp_call_glibc_strrchr] resumes
    the caller with the last matching byte or null and restores the
    string. *)
Lemma wp_call_glibc_strrchr (Hm : memrchr_spec) f e ls l r g args rest j dq p s c cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p; WInt c] -> 0 <= c < 2 ^ 32 ->
  find_fn ge g = Some (Defined glibc_strrchr) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None)
    (Ret (WPtr (hit_ptr p (last_byte (c mod 256) (s ++ [0]))))) = Some cf' ->
  word_string dq p s -∗ ▷ (word_string dq p s -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hc Hg Hsl Hr. iIntros "Hs HK".
  pose proof (strrchr_spec_valid Hm g Hg Hsl) as Hspec.
  iApply (wp_call_spec registry wi ge g strrchr_spec (dq, p, s, c) with "[Hs]");
    [exact Hx | by iFrame |].
  iIntros (v) "[-> Hs]". iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hs").
Qed.

End rules.
