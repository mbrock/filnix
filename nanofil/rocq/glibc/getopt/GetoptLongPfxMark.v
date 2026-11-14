(** When glibc's long-option parser meets a word that names more than
    one option by a prefix, it may remember which entries matched. It
    keeps one byte per table entry in a set, and it marks the bytes of
    the matching entries. This file states what the parser owns of that
    set, and it proves the marking of one entry safe: the parser writes
    only a byte of the set, and only below the count of entries. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec GetoptLongMissOnly
  GetoptLongMiss GetoptLongPfxCmp.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongDiag GetoptLongExact GetoptLongPfxCmp GetoptLongScan GetoptLongStore GetoptReqTail GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The marking of an entry assigns these names. *)
Definition pmark_names : list name := Eval vm_compute in
  List.map TAtom ["v218"; "v219"; "v222"; "v223"; "chk18"]%string.

(** The parser decides here whether it marks the current entry. *)
Definition plo_blk172 : block := Eval vm_compute in plo_blk "L172".


(** The comparison module supplies the option table, the targets and the tactics. *)
Import GetoptLongPfxCmp GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section set.
Context `{!gen_heapGS piece pval Σ}.

(** The set s of the parser has a byte for each of n entries. It is
    null before the parser allocates it, and it stays null when the
    allocation fails. Otherwise the parser owns the lifetime and the
    first n bytes of a heap object whose base s points at. *)
Definition amb_set (n : Z) (s : ptr) : iProp Σ :=
  ⌜s = null⌝ ∨ ∃ sb sreg xs, ⌜s = mkPtr sb (Obj sb) /\ r_kind sreg = Heap /\ 0 < sb /\ sb + n <= r_end sreg /\
     r_end sreg <= 2 ^ 48 /\ Z.of_nat (List.length xs) = n⌝ ∗ live sb sreg ∗ bytes sb 0 xs.

(** The bytes xs give up their byte at index t as a single byte. *)
Lemma bytes_at b xs t x :
  xs !! t = Some x ->
  bytes b 0 xs ⊣⊢ bytes b 0 (take t xs) ∗ ibyte b (Z.of_nat t) x ∗ bytes b (Z.of_nat t + 1) (drop (S t) xs).
Proof.
  intros Hx. pose proof (lookup_lt_Some _ _ _ Hx) as Ht.
  rewrite (bytes_take_drop b 0 xs t); [|lia]. rewrite (drop_S _ _ _ Hx).
  rewrite /bytes /ibyte /pts byte_ps_cons big_sepL_cons big_sepL_singleton !Z.add_0_l. done.
Qed.

End set.

Section mark.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance mark_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance mark_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser marks the byte at index t of its set, whose base is sb.
    It checks the byte's address and stores 1 there. *)
Lemma wp_amb_mark f e ls l d a rest j sb sreg xs t Φ :
  lookup a e = Some (WPtr (mkPtr (sb + Z.of_nat t) (Obj sb))) ->
  (t < List.length xs)%nat -> 0 < sb -> sb + Z.of_nat (List.length xs) <= r_end sreg -> r_end sreg <= 2 ^ 48 ->
  live sb sreg -∗ bytes sb 0 xs -∗
  ▷ (live sb sreg -∗ bytes sb 0 (<[t := 1]> xs) -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (sb + Z.of_nat t) (Obj sb))) e) ls None (Exec l rest j)) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Let d A (Check 0 1 Write 1) [Tmp a] :: RawStore Wb 0 (Const 1) (Tmp d) :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Ha Ht Hsb Hend Hr. iIntros "Hl Hx HK".
  destruct (lookup_lt_is_Some_2 xs t Ht) as [x Hx].
  iApply (wp_check with "Hl"); [reflexivity | vx | reflexivity | StrlenLoop.arith | StrlenLoop.arith | apply Z.mod_1_r |].
  iNext. iIntros "Hl". rewrite (bytes_at sb xs t x Hx). iDestruct "Hx" as "(Hx0 & Hb & Hx1)".
  iApply (wp_raw_store_byte with "Hl Hb"); [vx | vx | reflexivity | StrlenLoop.arith | wi_store |].
  iNext. iIntros "Hl Hb". iApply ("HK" with "Hl"). change (1 mod 256) with 1.
  rewrite (bytes_at sb (<[t := 1]> xs) t 1); [|apply list_lookup_insert_eq; exact Ht].
  rewrite take_insert_ge; [|lia]. rewrite drop_insert_lt; [|lia]. iFrame.
Qed.

(** The parser decides whether it marks the current entry k, the n
    entries' set being s. When s is not null, it marks the entry's
    byte. Then it goes on to the next entry. *)
Lemma wp_pfx_mark ks e n s k Φ :
  avoids ks pmark_names = true ->
  lookup (TAtom "pr.18") e = Some (WPtr s) -> lookup (TAtom "pr.13") e = Some (WInt (Z.of_nat k)) ->
  Z.of_nat k < n -> n < 2 ^ 31 ->
  amb_set n s -∗
  (∀ e' P, ⌜keeps ks e e' /\ (P = TAtom "L214" \/ P = TAtom "L172")⌝ -∗ amb_set n s -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L108") (Some P))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L172") (b_insts plo_blk172) (b_jump plo_blk172))) : gexpr) {{ Φ }}.
Proof.
  intros Hks H18 H13 Hk Hn. iIntros "Hs HK". cbn [b_insts b_jump plo_blk172].
  iDestruct "Hs" as "[-> | (%sb & %sreg & %xs & %Hs & Hl & Hx)]".
  - step. step. unfold null; cbn [ptr_addr]. change (0 mod 2 ^ 64) with 0.
    iApply wp_branch; [vx | iNext]. close_br.
    iApply ("HK" with "[%] []"); [split; [xkeep | right; reflexivity] | by iLeft].
  - destruct Hs as (-> & Hk' & Hsb & Hend & Hr & Hlen). step. step.
    rewrite (Z.mod_small sb (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
    rewrite (proj2 (Z.eqb_neq sb 0)); [|lia].
    iApply wp_branch; [vx | iNext]. close_br. step. step. step. norm.
    rewrite (sx_nonneg (Z.of_nat k)); [|lia].
    match goal with |- context [put (TAtom "v223") (WPtr {| ptr_addr := ?X; ptr_cap := Obj sb |})] =>
      replace X with (sb + Z.of_nat k) by (rewrite !Z.mod_small; lia) end.
    iApply (wp_amb_mark with "Hl Hx"); [lk_prove | lia | lia | lia | lia |].
    iNext. iIntros "Hl Hx". step.
    iApply ("HK" with "[%] [Hl Hx]"); [split; [xkeep | left; reflexivity]|].
    iRight. iExists sb, sreg, (<[k := 1]> xs). iFrame. iPureIntro.
    repeat split; try assumption. rewrite length_insert. exact Hlen.
Qed.

End mark.
