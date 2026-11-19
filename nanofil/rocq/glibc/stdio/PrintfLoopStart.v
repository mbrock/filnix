(** The formatter's loop starts in the entry block of the function
    `c: __printf_buffer`. The block allocates the function's local
    variables and saves errno. It writes the plain text before the
    first percent sign. It returns when the format has no conversion,
    and otherwise it goes to the first round of the loop. This module
    proves the row of the entry block in the table of
    [PrintfLoopState](PrintfLoopState.v). *)

From Glibc Require FixVariadic.
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic LibioDefaultXsputnBuf WordString StrchrnulLogic
  StrlenWord DcigettextExit DcigettextPreRules
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec PrintfCopy FormatterNames PrintfLoopState.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic FixVariadic.VL0.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The function allocates its local variables on the heap when it
    starts. The tactic [alloc_keep] runs one allocation and names the
    new object, and the tactic [alloc_drop] runs one whose object the
    proof never uses. *)
Local Ltac alloc_keep b H :=
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  iNext; iIntros (b H) "Hobj".
Local Ltac alloc_drop :=
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  iNext; iIntros (? _) "_".

Section start.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!Callees (loop_callees k R)}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation blocks := (loop_blocks k R).

(** The entry block needs what the function's contract asks for. *)
Lemma start_rows_hold :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (start_rows k R).
Proof using Type*.
  iIntros "#IH". iSplit; [|done]. iModIntro.
  iIntros ([bb [fa fc] dq bytes ds ap skip xs rest eb] e from Φ) "_ %He H HK". row_simpl. c_env_open He.
  iDestruct "H" as "((%Hp & %Hfit & %Hs0 & %Hs8 & %Herr & %Hge) & Hout & Hs & Hva & #Hargs & #Hlend & #Hro)".
  block_enter.
  alloc_keep fb Hfb. change (0 < fb /\ fb mod 16 = 0 /\ fb + 16 <= 2 ^ 48) in Hfb. destruct Hfb as (Hfb & Hf16 & Hfe).
  iDestruct (obj_zero_block with "Hobj") as "(Hfl & Hfx & Hfc)"; [compute; discriminate|].
  iAssert (live fb (mkRegion fb (fb + 16) Heap Live)) with "Hfl" as "Hfl".
  iDestruct (zero_cell_prefix fb 0 8 with "Hfx Hfc") as "(Hfc & _ & _)".
  alloc_keep wb Hwb. change (0 < wb /\ wb mod 16 = 0 /\ wb + 1008 <= 2 ^ 48) in Hwb. destruct Hwb as (Hwb & Hw16 & Hwe).
  iDestruct (obj_zero_block with "Hobj") as "(Hwl & Hwx & _)"; [compute; discriminate|].
  iAssert (work_own wb) with "[Hwl Hwx]" as "Hwork".
  { change (Z.to_nat (req_extent (heap_req 4 1000))) with (980 + (20 + 8))%nat. rewrite !replicate_add !bytes_app.
    iDestruct "Hwx" as "(_ & Hwx & _)". iExists (replicate 20 0). iFrame "Hwl". rewrite length_replicate. iFrame "Hwx".
    iPureIntro. split_and!; [lia | Z.div_mod_to_equations; lia | lia | reflexivity]. }
  alloc_keep vb Hvb. change (0 < vb /\ vb mod 16 = 0 /\ vb + 32 <= 2 ^ 48) in Hvb. destruct Hvb as (Hvb & Hv16 & Hve).
  iDestruct (obj_zero_block with "Hobj") as "(Hvl & Hvx & Hvc)"; [compute; discriminate|].
  iAssert (live vb (mkRegion vb (vb + 32) Heap Live)) with "Hvl" as "Hvl".
  iDestruct (zero_cell_prefix vb 0 24 with "Hvx Hvc") as "(Hvc & _ & _)". do 8 alloc_drop.
  step_global Hge. iApply (wp_dci_errno_check eb Herr); [vx|]. iNext.
  (* The buffer's invariant lends errno for the one load. *)
  iDestruct "Hout" as (breg w written mode) "(%Hmd & Hbuf & HR)". iDestruct ("Hlend" with "HR") as "[Herrno Hback]".
  iDestruct "Herrno" as (bs cs [Hbs Hcs]) "Hp". iEval (rewrite pts_app) in "Hp". iDestruct "Hp" as "[Heb Hea]".
  iApply (wp_dci_errno_load eb Herr with "Heb"); [vx | exact Hbs|]. iNext. iIntros "Heb".
  iAssert (errno_any eb) with "[Heb Hea]" as "Herrno". { iExists bs, cs. iSplit; [done|]. rewrite pts_app. iFrame. }
  iDestruct ("Hback" with "Herrno") as "HR".
  iAssert (printf_out k R bb) with "[Hbuf HR]" as "Hout". { iExists breg, w, written, mode. iFrame "Hbuf HR". done. }
  clear breg w written mode Hmd.
  step.
  iDestruct (va_at_cursor with "Hva") as (cb sb) "((-> & %Hcb & %Hc8 & %Hce & %Hsb & %Hsk & _) & Hcl & Hcc & Hsl & Hvback)".
  check "Hcl". iApply (wp_raw_load_pointer_dq with "Hcl Hcc Hsl"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hcl Hcc Hsl". iDestruct ("Hvback" with "Hcl Hcc Hsl") as "Hva".
  check "Hvl". store "Hvl" "Hvc". iClear "Hvl Hvc".
  iDestruct (word_string_short with "Hs") as %Hshort.
  call_callee with (dq, mkPtr fa fc, bytes) giving "Hs"; [iExact "Hs"|]. iDestruct "Hpost" as "[-> Hs]". block_resume.
  check "Hfl". store "Hfl" "Hfc". step. step. step.
  iDestruct (word_string_range with "Hs") as %Hfr. cbn [ptr_addr] in Hfr. pose proof (chr_idx_le 37 bytes) as Hidx.
  call_callee with (bb, dq, mkPtr fa fc, bytes, _) giving "Hout Hs"; [iFrame "Hout Hs"; iPureIntro; unwrap2; lia|].
  iDestruct "Hpost" as "(-> & Hout & Hs)". block_resume.
  call_callee with bb giving "Hout"; [iExact "Hout"|]. iDestruct "Hpost" as (b) "((-> & %Hb) & Hout)". block_resume.
  step. branch_eqn E.
  2: { step. iApply wp_ret_void. iNext. iApply "HK". iFrame "Hout Hs". done. }
  clear E. step. check "Hfl". load_fmt "Hfl" "Hfc" "Hs".
  destruct (lit_run bytes ds Hp) as (lit & tl & ds' & Hbytes & Hlit & Htl & Hptl & Hfit').
  destruct Htl as [-> | [tl' ->]].
  { (* The format has no conversion, and the function returns. *)
    assert (Hx : (bytes ++ [0]) !! chr_idx 37 bytes = Some 0) by (rewrite -Hlit Hbytes; apply byte_after; reflexivity).
    read_byte "Hs" (chr_idx 37 bytes) 0 Hx. step. branch. step. iApply wp_ret_void. iNext. iApply "HK".
    iFrame "Hout Hs". done. }
  assert (Hx : (bytes ++ [0]) !! chr_idx 37 bytes = Some 37) by (rewrite -Hlit Hbytes; apply byte_after; reflexivity).
  read_byte "Hs" (chr_idx 37 bytes) 37 Hx. step. branch.
  (* No conversion is registered, so the function takes the loop without positional arguments. *)
  iPoseProof "Hro" as "(_ & _ & _ & _ & Hn1 & Hn2 & Hn3)".
  iDestruct "Hn1" as (n1 r1) "((%Hg1 & %Hb1 & %Ha1 & %He1 & %Hr1) & Hl1 & Hc1)".
  iDestruct "Hn2" as (n2 r2) "((%Hg2 & %Hb2 & %Ha2 & %He2 & %Hr2) & Hl2 & Hc2)".
  iDestruct "Hn3" as (n3 r3) "((%Hg3 & %Hb3 & %Ha3 & %He3 & %Hr3) & Hl3 & Hc3)".
  step. step_global Hg1. check_read_dq "Hl1" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hl1 Hc1 []"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia | done |].
  iNext. iIntros "_ _ _". step. step. step. branch.
  step. step_global Hg2. check_read_dq "Hl2" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hl2 Hc2 []"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia | done |].
  iNext. iIntros "_ _ _". step. step. step. step. branch.
  step. step_global Hg3. check_read_dq "Hl3" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hl3 Hc3 []"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia | done |].
  iNext. iIntros "_ _ _". step. step. step. step. branch.
  assert (Hi0 : 8 * Z.of_nat (Z.to_nat (skip / 8)) = skip) by (Z.div_mod_to_equations; lia).
  iDestruct (va_at_cur _ (Z.to_nat (skip / 8)) with "[Hva]") as "Hva"; [rewrite Hi0; iExact "Hva"|].
  goto_block "IH" "HK" 1%nat
    with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds (mkPtr cb (Obj cb)) skip xs rest eb) fb wb lit (37 :: tl') ds'
            (Z.to_nat (skip / 8)) 0).
  row_simpl. rewrite Hlit. iFrame "Hout Hs Hfl Hfc Hva Hargs Hwork Hro". iPureIntro.
  split_and!; [reflexivity | exact Hbytes | exact (Hfit' _ _ Hfit) | lia | Z.div_mod_to_equations; lia |
               lia | lia | lia | reflexivity | exact Hptl].
  (* The block loads three cells that hold null pointers, and a null pointer names no object. *)
  Unshelve. all: first [exact DfracDiscarded | exact (mkRegion 0 0 Heap Live)].
Qed.

End start.
