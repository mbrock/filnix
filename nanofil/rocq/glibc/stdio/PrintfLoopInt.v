(** The conversion `%d` of the formatter's loop prints a signed
    decimal number. Its code starts at the block `L1155`, which reads
    the argument and takes its sign away. The function
    `c: _itoa_word` then writes the digits at the end of the work
    buffer, and the code appends a minus sign and the digits to the
    output. This module proves the rows of that code in the table of
    [PrintfLoopState](PrintfLoopState.v). The format of a `%d` has no
    flag, no width and no precision here, so the code pads with
    nothing, and the proof follows the padding code without counting
    what it writes. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic LibioDefaultXsputnBuf WordString StrchrnulLogic
  StrlenWord FxprintfStream NarrowFormat NarrowArgs DcigettextExit DcigettextPreRules
  FormatterCode FormatterSrc FormatterStringTable FormatterStringArg FormatterStringDispatch FormatterStringRead
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec ItoaWordSpec PrintfCopy FormatterNames VaArgRound PrintfLoopState.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic StringVL.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The tactic [run] follows the code as far as it goes without a
    choice: it runs the instructions that own nothing, and it takes
    each jump whose condition is a constant. *)
Local Ltac const_cond c := tryif has_var c then fail "branch_det: the condition is not a constant" else idtac.
Local Ltac branch_det :=
  iStartProof; eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    const_cond c; let d := eval vm_compute in c in change c with d end;
  cbn [edge_label].
Local Ltac run := repeat first [step | branch_det].

(** The tactic [run_to] does the same, and it stops at the entry of
    the block l. *)
Local Ltac at_block l :=
  lazymatch goal with |- context [mkFrame _ _ _ None (Enter (TAtom l) _)] => idtac end.
Local Ltac at_edge l :=
  lazymatch goal with |- context [mkFrame _ _ _ None (Enter (edge_label (To (TAtom l))) _)] => idtac end.
Local Ltac at_enter l := first [at_block l | at_edge l].
Local Tactic Notation "run_to" constr(l) := repeat (tryif at_enter l then fail else first [step | branch_det]).

(** ## The sign of the argument *)

(** A `%d` takes a 32-bit integer, and the compiled code extends it to
    64 bits with its sign. It then tests the sign, and it negates a
    negative number, so that the digits are those of the magnitude.
    The lemmas below say what these steps compute. *)

(** Sign extension keeps a number below the half h of the modulus m,
    and it subtracts the modulus from a number from the half on. *)
Lemma sext_low m h u : 0 <= u < h -> h <= m -> sign_extension m h u = u.
Proof. intros Hu Hm. unfold sign_extension. rewrite Z.mod_small; [|lia]. destruct (Z.leb_spec h u); lia. Qed.
Lemma sext_high m h u : 0 <= h -> h <= u < m -> sign_extension m h u = u - m.
Proof. intros Hh Hu. unfold sign_extension. rewrite Z.mod_small; [|lia]. destruct (Z.leb_spec h u); lia. Qed.

(** An argument below 2^31 is not negative, and its 64-bit form is the
    argument itself. *)
Lemma int_arg_pos x : 0 <= x < 2 ^ 31 -> sign_extension (2 ^ 32) (2 ^ 31) ((x mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 64 = x.
Proof. intros Hx. rewrite !(Z.mod_small x (2 ^ 32)); [|lia..]. rewrite sext_low; [|lia..]. apply Z.mod_small. lia. Qed.

(** An argument from 2^31 on is negative, and its 64-bit form has the
    upper 32 bits set. *)
Lemma int_arg_neg x :
  2 ^ 31 <= x < 2 ^ 32 -> sign_extension (2 ^ 32) (2 ^ 31) ((x mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 64 = 2 ^ 64 - 2 ^ 32 + x.
Proof.
  intros Hx. rewrite !(Z.mod_small x (2 ^ 32)); [|lia..]. rewrite sext_high; [|lia..]. symmetry.
  apply (Z.mod_unique _ _ (-1)); lia.
Qed.

(** The test for a negative 64-bit number asks whether the number is
    in the upper half of the 64-bit range. *)
Lemma neg_test a :
  0 <= a < 2 ^ 64 ->
  (sign_extension (2 ^ 64) (2 ^ 63) ((a mod 2 ^ 64) mod 2 ^ 64) <? sign_extension (2 ^ 64) (2 ^ 63) (0 mod 2 ^ 64)) =
  (2 ^ 63 <=? a).
Proof.
  intros Ha. rewrite !(Z.mod_small a (2 ^ 64)); [|lia..]. change (sign_extension (2 ^ 64) (2 ^ 63) (0 mod 2 ^ 64)) with 0.
  destruct (Z.leb_spec (2 ^ 63) a).
  - rewrite sext_high; [|lia..]. apply Z.ltb_lt. lia.
  - rewrite sext_low; [|lia..]. apply Z.ltb_ge. lia.
Qed.

(** Negating a 64-bit number that is not zero gives its distance from
    2^64. *)
Lemma neg_mod a : 0 < a < 2 ^ 64 -> - a mod 2 ^ 64 = 2 ^ 64 - a.
Proof. intros Ha. symmetry. apply (Z.mod_unique _ _ (-1)); lia. Qed.

Section int.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z * region * Z * Z -> iProp Σ).
Context `{!Callees (loop_callees k R)}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation blocks := (loop_blocks k R).

(** ## The digits in the work buffer *)

(** The code appends the digits with `c: __printf_buffer_write`, which
    takes a run of bytes. The work buffer lends its digits as a run,
    and the function owns the end of its work buffer again when the
    run comes back. *)
Lemma work_digits_run wb u :
  work_digits wb u ⊢
  byte_run (DfracOwn 1) (mkPtr (wb + 1000 - Z.of_nat (length (dec_digits u))) (Obj wb)) wb
    (mkRegion wb (wb + 1008) Heap Live) (dec_digits u) ∗
  (byte_run (DfracOwn 1) (mkPtr (wb + 1000 - Z.of_nat (length (dec_digits u))) (Obj wb)) wb
     (mkRegion wb (wb + 1008) Heap Live) (dec_digits u) -∗ work_own wb).
Proof using Type.
  iIntros "(%old & (%Hwb & %Hw8 & %Hwe & %Hold) & Hwl & Hwx)".
  pose proof (dec_digits_length u) as Hlen. pose proof (dec_digits_range u) as Hrange.
  remember (dec_digits u) as dg eqn:Hdg.
  assert (Htake : length (take (20 - length dg) old) = (20 - length dg)%nat) by (rewrite length_take; lia).
  iDestruct (bytes_app with "Hwx") as "[Hwa Hwd]". rewrite Htake.
  replace (980 + Z.of_nat (20 - length dg)) with (wb + 1000 - Z.of_nat (length dg) - wb) by lia.
  unfold byte_run. cbn [ptr_cap ptr_addr r_end]. rewrite /live /liveq /bytes /bytesq !pts_ptsq.
  iFrame "Hwl Hwd". iSplit.
  - iPureIntro. split_and!; first [left; reflexivity | assumption | lia | idtac].
    revert Hrange. apply Forall_impl. intros y Hy. lia.
  - iIntros "(_ & Hwl & Hwd)". iExists (take (20 - length dg) old ++ dg). iFrame "Hwl". iSplit.
    + iPureIntro. split_and!; try assumption. rewrite length_app Htake. lia.
    + iApply bytes_app. rewrite Htake.
      replace (980 + Z.of_nat (20 - length dg)) with (wb + 1000 - Z.of_nat (length dg) - wb) by lia. iFrame.
Qed.

(** ## The rows of a `%d` *)

(** The block `L1155` reads the argument of a `%d`. *)
Lemma int_start_holds :
  ▷ blocks_hold glibc_printf_buffer blocks ⊢
  block_triple glibc_printf_buffer
    (BSpec "L1155" None int_sig pl_in (conv_vals 100) (conv_pre k R FmtInt) (pl_post k R)).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] e from Φ) "_ %He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(((%Hbytes & %Hfit & %Hfb & %Hf8 & %Hfe & %Hn) & %Hne & %ds1 & -> & %Hptail) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Hwork & Herrno & #Hro)".
  destruct (int_fits _ _ _ Hfit) as (x & args & Hargs_eq & Hx & Hfit1).
  destruct (skipn_cons _ _ _ _ Hargs_eq) as (Hxi & Hskip1 & Hilt).
  iEval (rewrite Hargs_eq big_sepL_cons) in "Hargs". iDestruct "Hargs" as "[_ Hargs1]". subst args.
  iDestruct (va_cur_int _ i xs x Hxi with "Hva")
    as (cb sb cur) "((-> & %Hc8 & %Hsb & %Hse & %Hsr & %Hcur0 & %Hround) & Hcur & Hsl & Hxc & Hvback)".
  block_enter. run.
  iApply (wp_va_arg_w _ _ _ _ _ _ _ _ cb _ cur sb _ (8 * Z.of_nat i) x with "Hcur Hsl Hxc");
    [vx | assumption | assumption | lia | cbn [r_end]; lia | cbn [r_end]; lia | assumption | exact Hround |].
  iNext. iIntros "Hcur Hsl Hxc". iDestruct ("Hvback" with "Hcur Hsl Hxc") as "Hva". run.
  iDestruct (work_own_range with "Hwork") as %Hwr.
  destruct (Z.lt_ge_cases x (2 ^ 31)) as [Hpos | Hneg].
  - (* The number is not negative. *)
    assert (Hp : 0 <= x < 2 ^ 31) by lia. rewrite !(int_arg_pos x Hp). rewrite (neg_test x); [|lia].
    rewrite (proj2 (Z.leb_gt (2 ^ 63) x)); [|lia]. unwrap2. run_to "L1290". unwrap2.
    goto_block "IH" "HK" 14%nat
      with (PiIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 (mkPtr cb (Obj cb)) skip xs rest eb) fb wb pre tl ds1 (S i) n)
              x 0 0 0 0).
    row_simpl. iFrame "Hout Hs Hfl Hfc Hva Hargs1 Hwork Herrno Hro". iPureIntro.
    split_and!; first [reflexivity | assumption | lia].
  - (* The number is negative, and the code negates it. *)
    assert (Hq : 2 ^ 31 <= x < 2 ^ 32) by lia. rewrite !(int_arg_neg x Hq). rewrite (neg_test (2 ^ 64 - 2 ^ 32 + x)); [|lia].
    rewrite (proj2 (Z.leb_le (2 ^ 63) (2 ^ 64 - 2 ^ 32 + x))); [|lia]. unwrap2. run_to "L1290". unwrap2.
    rewrite (neg_mod (2 ^ 64 - 2 ^ 32 + x)); [|lia]. unwrap2.
    goto_block "IH" "HK" 14%nat
      with (PiIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 (mkPtr cb (Obj cb)) skip xs rest eb) fb wb pre tl ds1 (S i) n)
              (2 ^ 64 - (2 ^ 64 - 2 ^ 32 + x)) 1 0 0 0).
    row_simpl. iFrame "Hout Hs Hfl Hfc Hva Hargs1 Hwork Herrno Hro". iPureIntro.
    split_and!; first [reflexivity | assumption | lia].
Qed.

(** The tactic [explore_to] follows the code on every path to the
    entry of the block l. It takes both edges of a jump whose
    condition the proof does not know. *)
Local Ltac branch_any := let E := fresh "E" in branch_eqn E; clear E.
Local Tactic Notation "explore_to" constr(l) :=
  repeat (tryif at_enter l then fail else first [step | branch_det | branch_any]).

(** The block `L1290` turns the number into digits with
    `c: _itoa_word`, which writes them at the end of the work buffer.
    The code then measures the digits. *)
Lemma number_holds :
  ▷ blocks_hold glibc_printf_buffer blocks ⊢
  block_triple glibc_printf_buffer
    (BSpec "L1290" None number_sig pi_in pi_vals (number_pre k R) (fun z => pl_post k R (pi_y z))).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] u neg nz w cnt] e from Φ)
    "_ %He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(%Hu & (%Hok & %Hne & %Hp) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Hwork & Herrno & #Hro)".
  iDestruct "Hwork" as (old) "((%Hwb & %Hw8 & %Hwe & %Hold) & Hwl & Hwx)".
  iPoseProof "Hro" as "(_ & _ & Hdig & _)". pose proof (dec_digits_length u) as Hlen.
  block_enter. step. step. closed_ints.
  call_spec itoa_word_spec with (u, wb, mkRegion wb (wb + 1008) Heap Live, 1000, old) giving "Hwl Hwx";
    [iFrame "Hwl Hwx Hdig"; iPureIntro; cbn [r_end]; lia|].
  iDestruct "Hpost" as "(-> & Hwl & Hwx)". block_resume. remember (dec_digits u) as dg eqn:Hdg.
  (* The precision is one, and the number has at least one digit. *)
  run_to "L1442". unwrap2.
  replace (wb + 1000 - (wb + 1000 - Z.of_nat (length dg))) with (Z.of_nat (length dg)) by lia. unwrap2.
  rewrite !sext_low; [|lia..]. rewrite (proj2 (Z.leb_le 1 (Z.of_nat (length dg)))); [|lia].
  (* The code asks whether the number is zero, and both answers lead to the same block. *)
  run_to "L1442". unwrap2. destruct (Z.eqb_spec u 0) as [Hz | Hnz]; cbn [negb]; run_to "L1442".
  (* The precision adds no zeros, whether the number has one digit or more. *)
  all: change (sign_extension (2 ^ 32) (2 ^ 31) (1 mod 2 ^ 32)) with 1;
    change (sign_extension (2 ^ 64) (2 ^ 63) (0 mod 2 ^ 64)) with 0; unwrap2.
  all: replace (wb + 1000 - (wb + 1000 - Z.of_nat (length dg))) with (Z.of_nat (length dg)) by lia.
  all: destruct (Z.leb_spec 2 (Z.of_nat (length dg))) as [Hl2 | Hl1];
    [replace (1 - Z.of_nat (length dg)) with (- (Z.of_nat (length dg) - 1)) by lia; rewrite neg_mod; [|lia]; unwrap2;
     rewrite sext_high; [|lia..]; rewrite (proj2 (Z.ltb_lt _ 0)); [|lia]
    |replace (1 - Z.of_nat (length dg)) with 0 by lia; change (0 mod 2 ^ 64) with 0;
     change (sign_extension (2 ^ 64) (2 ^ 63) 0 <? 0) with false].
  all: run_to "L1442"; unwrap2.
  all: goto_block "IH" "HK" 15%nat
         with (PiIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n)
                 u neg 0 w (Z.of_nat (length dg))).
  all: row_simpl.
  all: subst dg; iFrame "Hout Hs Hfl Hfc Hva Hargs Herrno Hro"; iSplit;
    [iPureIntro; split; [exact Hok | split_and!; first [reflexivity | assumption]]|].
  all: unfold work_digits; iExists old; iFrame "Hwl Hwx"; iPureIntro; split_and!; assumption.
Qed.

(** The block `L1442` takes the count of the digits from the width.
    The code then takes one more from the width for a sign. *)
Lemma digits_holds :
  ▷ blocks_hold glibc_printf_buffer blocks ⊢
  block_triple glibc_printf_buffer
    (BSpec "L1442" None digits_sig pi_in pi_vals (digits_pre k R) (fun z => pl_post k R (pi_y z))).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] u neg nz w cnt] e from Φ)
    "_ %He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(%Hok & Hown)".
  block_enter. explore_to "L1498".
  all: goto_block "IH" "HK" 16%nat
         with (PiIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n) u neg _ _ cnt).
  all: row_simpl; iFrame "Hown"; done.
Qed.

(** The block `L1498` pads on the left with spaces. The code then
    writes a minus sign for a negative number. *)
Lemma pad_holds :
  ▷ blocks_hold glibc_printf_buffer blocks ⊢
  block_triple glibc_printf_buffer
    (BSpec "L1498" None pad_sig pi_in pi_vals (digits_pre k R) (fun z => pl_post k R (pi_y z))).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] u neg nz w cnt] e from Φ)
    "_ %He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(%Hok & Hout & Hown)".
  block_enter. step.
  call_callee with (bb, 32, _) giving "Hout"; [iFrame "Hout"; iPureIntro; split; [lia | apply Z.mod_pos_bound; lia]|].
  iDestruct "Hpost" as "(-> & Hout)". block_resume. step. step. branch_any; run_to "L1508".
  2: { (* The number is negative. *)
       call_callee with (bb, 45) giving "Hout"; [iFrame "Hout"; iPureIntro; lia|].
       iDestruct "Hpost" as "(-> & Hout)". block_resume. step.
       goto_block "IH" "HK" 17%nat
         with (PiIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n) u neg nz _ cnt).
       row_simpl. iFrame "Hout Hown". done. }
  goto_block "IH" "HK" 17%nat
    with (PiIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n) u neg nz _ cnt).
  row_simpl. iFrame "Hout Hown". done.
Qed.

(** The block `L1508` writes the digits. The code first pads with
    zeros, which a `%d` without a precision does not need. It then
    appends the digits from the work buffer and goes to the end of the
    conversion. *)
Lemma sign_holds :
  ▷ blocks_hold glibc_printf_buffer blocks ⊢
  block_triple glibc_printf_buffer
    (BSpec "L1508" None sign_sig pi_in pi_vals (digits_pre k R) (fun z => pl_post k R (pi_y z))).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] u neg nz w cnt] e from Φ)
    "_ %He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "((%Hok & %Hne & %Hp & %Hcnt) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Hwork & Herrno & #Hro)".
  iDestruct (work_digits_run with "Hwork") as "[Hrun Hback]". rewrite -Hcnt.
  pose proof (dec_digits_length u) as Hlen. remember (dec_digits u) as dg eqn:Hdg.
  block_enter. explore_to "L1523".
  all: block_enter; run.
  all: call_callee with (bb, 48, _) giving "Hout"; [iFrame "Hout"; iPureIntro; split; [lia | apply Z.mod_pos_bound; lia]|].
  all: iDestruct "Hpost" as "(-> & Hout)"; block_resume; run_to "L1558"; block_enter.
  all: call_spec (write_bytes_spec k R)
         with (bb, DfracOwn 1, mkPtr (wb + 1000 - cnt) (Obj wb), wb, mkRegion wb (wb + 1008) Heap Live, dg, _)
         giving "Hout Hrun"; [iFrame "Hout Hrun"; iPureIntro; unwrap2; lia|].
  all: iDestruct "Hpost" as "(-> & Hout & Hrun)"; block_resume; step.
  all: iDestruct ("Hback" with "Hrun") as "Hwork".
  all: goto_block "IH" "HK" 12%nat
         with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n).
  all: row_simpl; iFrame "Hout Hs Hfl Hfc Hva Hargs Hwork Herrno Hro"; done.
Qed.

(** ## The group of rows *)

(** The five rows of a `%d` hold when the whole table holds one step
    later. *)
Lemma int_rows_hold :
  ▷ blocks_hold glibc_printf_buffer blocks ⊢ blocks_hold glibc_printf_buffer (int_rows k R).
Proof using Type*.
  iIntros "#IH". iSplit; [iApply (int_start_holds with "IH")|]. iSplit; [iApply (number_holds with "IH")|].
  iSplit; [iApply (digits_holds with "IH")|]. iSplit; [iApply (pad_holds with "IH")|].
  iSplit; [iApply (sign_holds with "IH") | done].
Qed.

End int.
