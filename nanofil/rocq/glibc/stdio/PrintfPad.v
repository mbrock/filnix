(** The narrow formatter pads a field by filling one window at a time.
    Each round writes the smaller of the remaining count and the free
    space. A full window needs a flush first. If that flush fails, the
    function returns without writing to the window. *)
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_pad_1_os Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic CFrame CStruct CBlocks
  PrintfLayout PrintfOut PrintfSpec PrintfFill PrintfPadOneSrc.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope string_scope. Open Scope list_scope. Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Module S := PrintfPadOneSrc.fn___printf_buffer_pad_1.
Local Notation fn := Unit_stdioZ2dcommon_printf_buffer_pad_1_os.fn___printf_buffer_pad_1.
Local Definition cuts := Eval vm_compute in cut_table S.temp_keys S.live_in.
Local Definition head_start := Eval vm_compute in cut_edge S.temp_keys S.live_in fn "L15" "start".
Local Definition head_again := Eval vm_compute in cut_edge S.temp_keys S.live_in fn "L15" "L66".
Local Definition head_body := Eval vm_compute in cut_body S.temp_keys S.live_in fn "L15" "start".
Local Definition fill_body := Eval vm_compute in cut_body S.temp_keys S.live_in fn "L66" "L65".

Section pad.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush") (flush_spec k R)}.
Context `{!HasSpec registry (os_wi w0) ge (TAtom "__GI_memset") win_fill_spec}.

Record round := Round { pb : Z; pc : Z; pn : Z }.
Local Definition vals x := [("buf", WPtr (mkPtr (pb x) (Obj (pb x)))); ("ch", WInt (pc x)); ("count", WInt (pn x))].
Local Definition valid x := 0 <= pc x < 2^32 /\ 0 <= pn x < 2^64.
Local Definition pre x : iProp Σ := (⌜valid x⌝ ∗ printf_out k R (pb x))%I.
Local Definition post x (v : outcome) : iProp Σ := (⌜v = RetVoid⌝ ∗ printf_out k R (pb x))%I.

(** After a successful flush, the window may have changed. The fill
    must use the new pointer, end and allocation lifetime together. *)
Record room := Room { pr : round; br : region; pw : pwin; wr : Z; md : Z; nf : Z }.
Local Definition room_pre y : iProp Σ :=
  (⌜valid (pr y) /\ pw_ptr (pw y) < pw_end (pw y) /\ (md y = mode_failed \/ md y = k)⌝ ∗
   printf_buf (pb (pr y)) (br y) (pw y) (wr y) (md y) ∗ R (pb (pr y)) (br y) (pw_place (pw y)))%I.
Local Definition fits y := 0 <= nf y <= pn (pr y) /\ nf y <= pw_end (pw y) - pw_ptr (pw y).
Local Definition fill_vals y := vals (pr y) ++ [("to_fill", WInt (nf y))].
Local Definition rows : list bspec :=
  [BSpec "start" None (cut_in cuts "start") round vals pre post;
   BSpec "L15" (Some "start") head_start round vals pre post;
   BSpec "L15" (Some "L66") head_again round vals pre post;
   BSpec "L20" None (cut_in cuts "L20") room (fun y => vals (pr y)) room_pre (fun y => post (pr y))].

Local Ltac simp := cbn [bs_sig bs_vals bs_pre bs_post bs_label] in *;
  unfold pre, post, fits, room_pre, valid, fill_vals, vals in *;
  cbn [pb pc pn pr br pw wr md nf app] in *.

Local Lemma pad_table : ⊢ blocks_hold fn rows.
Proof using Type*.
  apply blocks_close. iIntros "#IH".
  iAssert (body_triple fn "L66" fill_body room fill_vals
    (fun y => ⌜fits y⌝ ∗ room_pre y)%I (fun y => post (pr y))) as "#Hfill".
  { iModIntro. iIntros ([[bb c n] breg w written mode m] e Φ) "%He HP HK". simp. c_env_open He.
    iDestruct "HP" as "((%Hm & %Hlim) & (%Hv & %Hroom & %Hmd) & Hbuf & HR)".
    buf_open "Hbuf". unfold pwin_ok in Hw. body_start fn "L66". step. load_window "Hl" "Hptr" "Hwl". step.
    iDestruct (win_live_acc with "Hl Hwl") as "[Hwo Hback]".
    call_callee with (pw_obj w, pw_reg w, pw_lo w, pw_end w, pw_ptr w, _, m) giving "Hwo Hwin".
    { iFrame. iPureIntro. unfold pw_lo. repeat split; try apply Z.mod_pos_bound; Z.div_mod_to_equations; lia. }
    iDestruct "Hpost" as "(-> & Hwo & Hwin)". iDestruct ("Hback" with "Hwo") as "[Hl Hwl]". block_resume.
    check "Hl". load_window "Hl" "Hptr" "Hwl". step. check "Hl". store "Hl" "Hptr". step. step.
    cbn [ptr_addr ptr_cap]. unwrap2. branch_eqn E.
    - step. iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|].
      out_close "HR" with (PWin (pw_obj w) (pw_reg w) (pw_base w) (pw_ptr w + m) (pw_end w)).
      unfold pwin_ok. cbn [pw_obj pw_reg pw_base pw_ptr pw_end]. lia.
    - goto_block "IH" "HK" 2%nat with (Round bb c (n-m)). simp. iSplit; [iPureIntro; lia|].
      out_close "HR" with (PWin (pw_obj w) (pw_reg w) (pw_base w) (pw_ptr w + m) (pw_end w)).
      unfold pwin_ok. cbn [pw_obj pw_reg pw_base pw_ptr pw_end]. lia. }
  iAssert (body_triple fn "L15" head_body round vals pre post) as "#Hhead".
  { iModIntro. iIntros ([bb c n] e Φ) "%He [%Hv Hout] HK". simp. c_env_open He.
    iDestruct "Hout" as (breg w written mode) "(%Hmd & Hbuf & HR)". buf_open "Hbuf".
    body_start fn "L15". step. check "Hl". load_window "Hl" "Hptr" "Hwl".
    step. check "Hl". load_window "Hl" "Hend" "Hwl". step. step. step. branch_eqn E.
    - step. branch. goto_block "IH" "HK" 3%nat with (Room (Round bb c n) breg w written mode 0).
      simp. iFrame "HR". iSplit; [iPureIntro|buf_close; exact Hw]. unfold pwin_ok in Hw. branch_fact E. lia.
    - step. call_callee with bb giving "Hl Hbase Hptr Hend Hwr Hmode Hwl Hwin HR".
      { out_close "HR" with w. exact Hw. }
      clear Hmd. iDestruct "Hpost" as (r breg' w' written' mode') "((-> & %Hr & %Hmd & %Hroom) & Hbuf & HR)".
      block_resume. destruct Hr as [-> | ->]; step; step; step; step; branch.
      + step. iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|]. iExists breg',w',written',mode'. by iFrame.
      + goto_block "IH" "HK" 3%nat with (Room (Round bb c n) breg' w' written' mode' 0).
        simp. iFrame. iPureIntro. auto. }
  repeat iSplit; [| | | | done]; iModIntro.
  2,3: (iIntros ([bb c n] e from Φ) "%Hfrom %He [%Hv Hout] HK"; simp; c_env_open He; block_enter_from Hfrom;
        rewrite (Z.mod_small n (2^64)); [|lia]; iApply ("Hhead" $! (Round bb c n) with "[] [Hout] HK");
        [iPureIntro; c_env_close | simp; iFrame; done]).
  - iIntros ([bb c n] e from Φ) "_ %He [%Hv Hout] HK". simp. c_env_open He.
    iDestruct "Hout" as (breg w written mode) "(%Hmd & Hbuf & HR)". buf_open "Hbuf".
    block_enter. step. check "Hl". load_mode "Hl" "Hmode". step. branch_eqn E.
    + goto_block "IH" "HK" 1%nat with (Round bb c n). simp. iSplit; [done|]. out_close "HR" with w. exact Hw.
    + step. iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|]. out_close "HR" with w. exact Hw.
  - iIntros ([[bb c n] breg w written mode m] e from Φ) "_ %He ((%Hv & %Hroom & %Hmd) & Hbuf & HR) HK". simp. c_env_open He.
    buf_open "Hbuf". unfold pwin_ok in Hw. block_enter.
    step. check "Hl". load_window "Hl" "Hptr" "Hwl". step. check "Hl". load_window "Hl" "Hend" "Hwl".
    step. step. step. branch_as false. step.
    step. check "Hl". load_window "Hl" "Hend" "Hwl". step. check "Hl". load_window "Hl" "Hptr" "Hwl".
    step. step. step. step. unwrap2. branch_eqn E.
    + step. step. step. rewrite (Z.mod_small (pw_end w - pw_ptr w) (2^64)); [|lia].
      iApply ("Hfill" $! (Room (Round bb c n) breg w written mode (pw_end w - pw_ptr w)) with "[] [-HK] HK").
      { iPureIntro. c_env_close. } simp. iFrame "HR". iSplit; [iPureIntro; branch_fact E; lia|].
      iSplit; [done|]. buf_close. exact Hw.
    + step. rewrite (Z.mod_small n (2^64)); [|lia].
      iApply ("Hfill" $! (Room (Round bb c n) breg w written mode n) with "[] [-HK] HK").
      { iPureIntro. c_env_close. } simp. iFrame "HR". iSplit; [iPureIntro; branch_fact E; lia|].
      iSplit; [done|]. buf_close. exact Hw.
Qed.

(** The out-of-line function fills windows until the count is exhausted
    or the flush fails. Even a zero count fits its first fill. *)
Lemma pad_one_has_spec `{!Defines ge "__printf_buffer_pad_1" fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_pad_1") (pad_spec k R).
Proof using Type*.
  eapply (blocks_has_spec _ _ _ rows); [exact defines | reflexivity | reflexivity | | exact pad_table].
  intros [[bb c] n]. eexists _, (Round bb c n). split; [reflexivity|]. split; [c_env_close|].
  cbn [fs_pre fs_post bs_pre bs_post pad_spec]. iIntros "$" (r) "$".
Qed.

(** The inline wrapper skips nonpositive signed widths. For a positive
    width it passes the sign-extended character to the out-of-line writer. *)
Lemma pad_has_spec `{!Defines ge "glibc_vfprintf_internal#__printf_buffer_pad" Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_pad}
    `{!Defines ge "__printf_buffer_pad_1" fn} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_vfprintf_internal#__printf_buffer_pad") (pad_spec k R).
Proof using Type*.
  pose proof pad_one_has_spec as Hslow. intros [[bb c] n]. exists Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_pad.
  split; [exact defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post pad_spec]. iIntros "[(%Hc & %Hn) Hout] HK". step. step. branch_eqn E.
  - step. iApply wp_ret_void. iNext. iApply "HK". by iFrame.
  - step. step. call_callee with (bb, _, n) giving "Hout".
    { iFrame. iPureIntro. split; [apply Z.mod_pos_bound; lia | exact Hn]. }
    iDestruct "Hpost" as "(-> & Hout)". block_resume. step. step. iApply wp_ret_void. iNext. iApply "HK". by iFrame.
Qed.
End pad.
