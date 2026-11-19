(** Each round of the formatter's loop handles one conversion, and
    the round starts at the block `L79`. The variable `c: f` points to
    a percent sign there. The code steps over the sign and reads the
    letter of the conversion. It looks the letter up in two tables,
    and it compares the result with the number of each conversion
    until it finds the code of this one. This module follows the code
    from the block `L79` to the first block of the conversion, for
    each letter that the proof covers. It proves the rows of the block
    `L79` in the table of [PrintfLoopState](PrintfLoopState.v). *)

From Glibc Require Import PrintfTables.
From Glibc Require FixVariadic.
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os GlibcProgram GlibcSpec GlibcTactics
  OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic LibioDefaultXsputnBuf WordString StrchrnulLogic
  StrlenWord NarrowFormat
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec FormatterNames PrintfLoopState.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic FixVariadic.VL0.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The tactic [letter_dispatch] follows the code from the letter to
    the first block of its conversion. The letter stands at the index
    j of the first table, and the table holds the number v there. The
    second table holds the same number at the offset t. The code
    compares the number with n constants on its way. *)
Local Tactic Notation "letter_dispatch" constr(j) constr(t) integer(n) :=
  step; step; branch; step; step; step; step; branch;
  iPoseProof "Hro" as "(Hjt & Hst & _)";
  iDestruct "Hjt" as (jb jr) "((%Hjg & %Hjb & %Hje & %Hjr) & Hjl & Hjbs)";
  iDestruct "Hst" as (tb tr) "((%Htg & %Htb & %Hte & %Htr) & Htl & Htbs)";
  repeat match goal with
    | H : context [Z.of_nat (length (table_bytes jump_table))] |- _ =>
        change (Z.of_nat (length (table_bytes jump_table))) with 91 in H
    | H : context [Z.of_nat (length (table_bytes step0_jumps))] |- _ =>
        change (Z.of_nat (length (table_bytes step0_jumps))) with 128 in H
    end;
  iDestruct (bytesq_sub _ _ _ _ j 1 with "Hjbs") as "[Hj _]"; [vm_compute; lia|];
  iDestruct (bytesq_sub _ _ _ _ t 4 with "Htbs") as "[Ht _]"; [vm_compute; lia|];
  let bj := eval vm_compute in (take 1 (drop j (table_bytes jump_table))) in
  change (take 1 (drop j (table_bytes jump_table))) with bj;
  let bt := eval vm_compute in (take 4 (drop t (table_bytes step0_jumps))) in
  change (take 4 (drop t (table_bytes step0_jumps))) with bt;
  let zj := eval vm_compute in (0 + Z.of_nat j) in change (0 + Z.of_nat j) with zj;
  let zt := eval vm_compute in (0 + Z.of_nat t) in change (0 + Z.of_nat t) with zt;
  step;
  lazymatch goal with
  | Hj : lookup (TAtom jump_table) _ = _, Ht : lookup (TAtom step0_jumps) _ = _ |- _ =>
      unfold jump_table in Hj; unfold step0_jumps in Ht; step_global Ht; step_global Hj
  end;
  do 3 step; closed_ints;
  check_read_dq "Hjl" by ar; iNext; iIntros "_";
  load_bytes_dq "Hjl Hj" decode (reflexivity) by ar;
  iNext; iIntros "_ _"; do 3 step; closed_ints;
  check_read_dq "Htl" by ar; iNext; iIntros "_";
  load_bytes_dq "Htl Ht" decode (reflexivity) by ar;
  iNext; iIntros "_ _"; step; closed_ints; step;
  step; do 4 step; closed_ints; step;
  step; step; closed_ints; branch;
  do n (step; step; closed_ints; branch).

(** The tactic [conv_enter] finishes a round at the jump to the code
    of a conversion. It shows that the loop is in the same state as at
    the start of the round, except that the variable `c: f` now points
    to the letter of the conversion. *)
Local Ltac conv_enter :=
  row_simpl; rewrite length_app Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat];
  iFrame "Hout Hs Hfl Hva Hargs Hwork Hro"; iSplit;
  [iPureIntro; split_and!;
     first [assumption | lia | discriminate | (rewrite -app_assoc; assumption) | (eexists; split; [reflexivity | assumption])]
  | unfold ptr_add; cbn [ptr_addr ptr_cap];
    lazymatch goal with |- context [?a + (?p + Z.of_nat 1)] => replace (a + (p + Z.of_nat 1)) with (a + p + 1) by lia end;
    iFrame "Hfc"].

Section head.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!Callees (loop_callees k R)}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation blocks := (loop_blocks k R).

(** The block needs the state of the loop with `c: f` at a percent
    sign. It leaves `c: f` at the letter and goes to the first block
    of the conversion that the letter names. *)
Lemma head_body_holds :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢
  body_triple Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer "L79" head_body pl_in pl_vals (head_pre k R) (pl_post k R).
Proof using Type*.
  iIntros "#IH". iModIntro. iIntros ([[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] e Φ) "%He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(((%Hbytes & %Hfit & %Hfb & %Hf8 & %Hfe & %Hn) & %Hhd & %Hp) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Hwork & #Hro)".
  destruct tl as [|c tl]; [discriminate|]. injection Hhd as ->.
  destruct (conv_start tl ds Hp) as (x & tail & d & ds1 & -> & Hd & -> & Hptail).
  iDestruct (word_string_range with "Hs") as %Hfr. cbn [ptr_addr] in Hfr.
  iDestruct (work_own_range with "Hwork") as %Hwr.
  assert (Hlen : length bytes = (length pre + S (S (length tail)))%nat) by (rewrite Hbytes length_app; reflexivity).
  assert (Hx : (bytes ++ [0]) !! S (length pre) = Some x).
  { rewrite Hbytes -app_assoc lookup_app_r; [|lia]. replace (S (length pre) - length pre)%nat with 1%nat by lia. reflexivity. }
  body_start Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer "L79". step. check "Hfl". load_fmt "Hfl" "Hfc" "Hs". step. check "Hfl". store "Hfl" "Hfc".
  cbn [ptr_add ptr_addr ptr_cap]. unwrap2.
  destruct (conv_letter x d Hd) as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]].
  - read_byte "Hs" (S (length pre)) 115 Hx. letter_dispatch 83%nat 84%nat 4.
    goto_block "IH" "HK" 3%nat
      with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb (pre ++ [37]) (115 :: tail)
              (FmtStr :: ds1) i n).
    conv_enter.
  - read_byte "Hs" (S (length pre)) 99 Hx. letter_dispatch 67%nat 80%nat 3.
    goto_block "IH" "HK" 6%nat
      with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb (pre ++ [37]) (99 :: tail)
              (FmtChar :: ds1) i n).
    conv_enter.
  - read_byte "Hs" (S (length pre)) 100 Hx. letter_dispatch 68%nat 60%nat 6.
    goto_block "IH" "HK" 13%nat
      with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb (pre ++ [37]) (100 :: tail)
              (FmtInt :: ds1) i n).
    conv_enter.
  - read_byte "Hs" (S (length pre)) 37 Hx. letter_dispatch 5%nat 56%nat 5.
    goto_block "IH" "HK" 7%nat
      with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb (pre ++ [37]) (37 :: tail)
              (FmtPercent :: ds1) i n).
    conv_enter.
Qed.

(** Each row for the block `L79` takes the step into the block and
    uses the body. The step sets the count of conversions, which is
    zero before the first round. *)
Lemma head_rows_hold :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (head_rows k R).
Proof using Type*.
  iIntros "#IH". iPoseProof (head_body_holds with "IH") as "#Hhead". repeat iSplit; [| | done]; iModIntro.
  - iIntros (y e from Φ) "%Hfrom %He H HK". row_simpl. iDestruct "H" as "[%Hn0 H]". c_env_open He.
    block_enter_from Hfrom.
    iApply ("Hhead" $! y with "[] [H] HK"); [iPureIntro; row_simpl; rewrite Hn0; c_env_close | row_simpl; iExact "H"].
  - iIntros (y e from Φ) "%Hfrom %He H HK". row_simpl. iDestruct "H" as "[%Hok H]". c_env_open He.
    block_enter_from Hfrom.
    iApply ("Hhead" $! y with "[] [H] HK");
      [iPureIntro; row_simpl; rewrite (Z.mod_small (pl_n y)); [c_env_close | lia] | row_simpl; iFrame "H"; done].
Qed.

End head.
