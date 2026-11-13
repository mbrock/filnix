(** When glibc's long-option parser has found the option that a word
    names in the caller's table, it first tests the found entry, steps
    the index past the word and clears its cursor. Then it reads the
    byte that ended the name, which is an equals sign or the end of the
    word. This file proves those first blocks safe: they write only the
    parser's own index and cursor, and they read the word only inside
    its string. *)

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

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongPreOn (R : Runtime) (LG0 : LogicSig R).
(** The equals-sign module supplies the option table and the tactics. *)
Module LQE := GetoptLongEqOn R LG0.
Import LQE LQE.LQ LQE.LQ.LL LQE.LQ.LL.LT LQE.LQ.LL.LT.LD LQE.LQ.LL.LT.LD.LE LQE.LQ.LL.LT.LD.LE.LS
  LQE.LQ.LL.LT.LD.LE.LS.RT LQE.LQ.LL.LT.LD.LE.LS.RT.D LQE.LQ.LL.LT.LD.LE.LS.RT.D.X LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.

Section pre.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance pre_stable : SafepointStable (os_wi w0) := LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance pre_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
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
  cbn [b_insts b_jump plo_blk87]. st. st.
  rewrite (Z.mod_small (ptr_addr lo + 32 * Z.of_nat j) (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
  rewrite (proj2 (Z.eqb_neq (ptr_addr lo + 32 * Z.of_nat j) 0)); [|lia].
  iApply wp_branch; [vx | iNext]. close_br.
  en. chk "Hl". load_int "Hl Hib". st. norm. chk "Hl".
  iApply (wp_raw_store_w with "Hl Hib"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
  iNext. iIntros "Hl Hib". st. chk "Hl".
  iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
  iNext. iIntros "Hl Hcur".
  iDestruct (ws_byte cur s (eq_len s) with "Hws") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap & ? & ? & ? & ?).
  iApply (wp_renew_read_dq with "Hbl"); [reflexivity | vx | reflexivity | exact Hcap | rawa | rawa | apply Z.mod_1_r |].
  iNext. iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | rawa |].
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
End GetoptLongPreOn.
