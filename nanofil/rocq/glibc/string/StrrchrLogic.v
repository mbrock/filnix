(** glibc's own `__GI_strrchr` (StrchrCode.v's [glibc_strrchr]) over a
    [word_string] (WordString.v) at any share.

    strrchr(p, c) calls glibc's strlen and then `__GI___memrchr` on the
    string and its NUL. memrchr is not among the captured units
    (StrchrCode.v links it by name only), so the triple takes any
    function at that name with a call triple ([memrchr_spec]) that finds
    the last byte c mod 256 of the bytes ([last_byte]).
    [wp_glibc_strrchr_ws] is the triple for a frame of strrchr, and
    [wp_call_glibc_strrchr] for a call of it. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrlenWord StrchrCode MemchrLast.
Open Scope Z_scope.
Open Scope list_scope.

(** The index of the last byte c of bs, counting from i, after acc. *)
Fixpoint last_from (c : Z) (i : nat) (bs : list Z) (acc : option nat) : option nat :=
  match bs with
  | [] => acc
  | b :: bs' => last_from c (S i) bs' (if Z.eqb b c then Some i else acc)
  end.

(** The index of the last byte c of bs, if any. *)
Definition last_byte (c : Z) (bs : list Z) : option nat := last_from c 0 bs None.

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
Module StrrchrLogicOn (R : Runtime) (LG0 : LogicSig R).
Module SW := StrlenWordOn R LG0.
Module WS := SW.WS.
Module LG := LG0.
Module L := LG.L.
Import L LG WS.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A call triple for the function at `__GI___memrchr` on a string: for
    the string s at p at any share, memrchr(p, c, length s + 1) returns
    the pointer to the last byte c mod 256 of s and its NUL, or null,
    and hands the string back. *)
Definition memrchr_spec : Prop :=
  exists F, find_fn ge (TAtom "__GI___memrchr") = Some (Defined F) /\
  (forall p c n, is_Some (call_frame F [WPtr p; WInt c; WInt n])) /\
  forall fr dq p s c Φ, 0 <= c < 2 ^ 32 ->
    call_frame F [WPtr p; WInt c; WInt (Z.of_nat (List.length s) + 1)] = Some fr ->
    ⊢ word_string dq p s -∗
      (word_string dq p s -∗ Φ (Ret (WPtr (hit_ptr p (last_byte (c mod 256) (s ++ [0])))))) -∗
      WP (ERun fr : gexpr) {{ Φ }}.

(** glibc's strrchr of the string s at p for c: it returns the pointer
    to the last byte c mod 256 of s and its NUL, or null, and hands the
    string back. *)
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
  iApply (SW.wp_call_glibc_strlen registry wi ge with "Hs"); [reflexivity | exact Hsl | reflexivity |].
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

(** A call of glibc's strrchr, in any module whose function at the
    called name g is glibc's `__GI_strrchr`, at `__GI_strlen` glibc's
    strlen and at `__GI___memrchr` one with [memrchr_spec], on a string
    at any share: the caller resumes with the last c's pointer, or null,
    and the string. *)
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
  iApply (wp_call_bind with "[Hs HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_strrchr_ws Hm with "Hs"); [exact Hsl | exact Hc |].
  iIntros "Hs". iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hs").
Qed.

End rules.
End StrrchrLogicOn.
