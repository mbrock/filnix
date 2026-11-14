From Glibc Require Import GlibcProgram.
(** When glibc's long-option parser has found the option that a word
    names in the caller's table, it first tests the found entry, steps
    the index past the word and clears its cursor. Then it reads the
    byte that ended the name, which is an equals sign or the end of the
    word. This file proves those first blocks safe: they write only the
    parser's own index and cursor, and they read the word only inside
    its string. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongDiag GetoptLongEq GetoptLongExact GetoptLongReq GetoptLongScan GetoptLongStore GetoptLongTail GetoptReqTail GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The found path's first blocks assign these names. *)
Definition larg_names : list name := Eval vm_compute in
  List.map TAtom ["v329"; "v331"; "chk47"; "v392"; "v393"; "chk48"; "v395"; "chk49"; "chk50"; "v400"]%string.

(** The test of the found entry starts in this block. *)
Definition plo_blk87 : block := Eval vm_compute in plo_blk "L87".


(** The equals-sign module supplies the option table and the tactics. *)
Import GetoptLongEq GetoptLongReq GetoptLongTail GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section pre.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance pre_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser has found the entry at index j of the table lo for the
    word at index i, whose name starts at the cursor cur in the string s.
    It steps the index to i + 1 and clears the cursor. Then it goes on
    at the equals-sign path or at the end-of-word path, as the byte
    after the name says. *)
Lemma wp_long_pre ks e lo j cur s c0 i b r Φ :
  avoids ks larg_names = true ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v90") e = Some (WInt 0) ->
  lookup (TAtom "pr.7") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  lookup (TAtom "pr.1") e = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) ->
  0 < ptr_addr lo -> ptr_addr lo + 32 * Z.of_nat j < 2 ^ 48 -> 0 <= i < 2 ^ 31 - 1 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur s -∗ live b r -∗ int_cell b 0 i -∗ pcell b 32 c0 -∗
  ((∀ e', ⌜keeps ks e e' /\ sbyte s (eq_len s) = 0 /\ lookup (TAtom "chk47") e' = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 32 null -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L397") (Some (TAtom "L327")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte s (eq_len s) = 61⌝ -∗ live b r -∗ int_cell b 0 (i + 1) -∗ pcell b 32 null -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L396") (Some (TAtom "L327")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}.
Proof.
  intros Hks H12 H90 H7 Hp1 Hc0 Hc1 Hlo Hlj Hi Hb Hal Hend Hr.
  iIntros "#Hws Hl [%Hi0 Hib] Hcur HK".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe). pose proof (eq_len_le s) as Hle.
  cbn [b_insts b_jump plo_blk87]. step. step.
  rewrite (Z.mod_small (ptr_addr lo + 32 * Z.of_nat j) (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
  rewrite (proj2 (Z.eqb_neq (ptr_addr lo + 32 * Z.of_nat j) 0)); [|lia].
  iApply wp_branch; [vx | iNext]. close_br.
  step. check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. norm. check "Hl".
  store_word "Hl Hib" by (StrlenLoop.arith) preserving wi_store.
  iNext. iIntros "Hl Hib". step. check "Hl".
  store_pointer "Hl Hcur" by (StrlenLoop.arith) preserving wi_store.
  iNext. iIntros "Hl Hcur".
  iDestruct (ws_byte cur s (eq_len s) with "Hws") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap & ? & ? & ? & ?).
  iApply (wp_renew_read_dq with "Hbl"); [reflexivity | vx | reflexivity | exact Hcap | rawa | rawa | apply Z.mod_1_r |].
  iNext. iIntros "_".
  load_bytes_dq "Hbl Hbt" decode (apply extended_chr) by rawa.
  iNext; iIntros "_ _". iClear "Hbl Hbt".
  rewrite (Z.mod_small (i + 1) (2 ^ 32)); [|lia]. change (0 mod 2 ^ 64) with 0. fold null.
  iAssert (int_cell b 0 (i + 1)) with "[Hib]" as "Hib"; [iSplit; [iPureIntro; lia | iExact "Hib"]|].
  pose proof (sbyte_range s (eq_len s) Hch) as Hsr.
  iApply wp_branch; [vx | iNext].
  rewrite (Z.mod_small (chr_w _) (2 ^ 32)); [|apply chr_w_range]. rewrite chr_w_eqb; [|lia|lia].
  destruct (eq_len_stop s) as [E0 | E61]; rewrite ?E0 ?E61; close_br.
  - iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl Hib Hcur"). split; [xkeep|]. split; [first [reflexivity | exact E0] | lk_prove].
  - iDestruct "HK" as "[_ HK]". iApply ("HK" with "[%] Hl Hib Hcur"). split; [xkeep | first [reflexivity | exact E61]].
Qed.

End pre.
