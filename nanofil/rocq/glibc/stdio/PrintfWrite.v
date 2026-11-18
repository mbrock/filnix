(** The formatter appends a run of bytes with
    `c: __printf_buffer_write`. The function copies as many bytes as
    the buffer's window has room for, and it calls
    `c: __printf_buffer_flush` to make room whenever the window is
    full. This module proves that the compiled function meets two
    contracts of [PrintfSpec](PrintfSpec.v). The contract
    [write_bytes_spec] is for a run of bytes, and the contract
    [write_spec] is for the first bytes of a string.

    The function is a loop, and each round of the loop copies some
    bytes. A proof about a loop states what is true whenever a round
    starts. Three things are true here. The buffer is usable. The
    pointer `c: s` points to the first byte that is not yet copied.
    The number `c: count` of bytes that are not yet copied is no more
    than the number of bytes from `c: s` to the end of the run.

    The compiler turns the function into blocks of instructions that
    jump to one another. The proof has one part for each block where it
    needs to state what is true, and the module
    [CBlocks](../CBlocks.v) joins the parts into a proof about the
    whole function. The loop starts at the block named `L15`. The
    function jumps to that block from its entry and again from the end
    of every round, and `c: s` and `c: count` have different values on
    the two jumps. The proof therefore has two parts for this block,
    one for each jump.

    The block named `L68` copies the bytes, and two jumps lead to it
    as well. The function takes the first jump when the window has
    room for all the bytes that are left, and the round then copies
    all of them. It takes the second jump when the window has less
    room, and the round then fills the window. The proof assumes
    contracts for the two functions that the loop calls,
    `c: __printf_buffer_flush` and `c: memcpy`. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic WordString MemFwdCode MemFwdLogic
  PrintfBufferIoCode PrintfBufferIoSrc CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec
  PrintfCopy PrintfBufferIoNames.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Module S := PrintfBufferIoSrc.fn___printf_buffer_write.

(** The table [write_cuts] gives, for each label, the temporaries that
    are live there and the C variable that each one holds. *)
Definition write_cuts : list (string * cut_sig) :=
  Eval vm_compute in cut_table S.temp_keys S.live_in.

(** The compiled code can reach the start of the loop from two blocks,
    and a variable such as `c: count` is held in a different temporary
    on each way in. The block starts with phi nodes, which pick the
    temporary for the way that was taken. The table above cannot say
    which temporary holds `c: count` there, so the proof computes one
    list of temporaries for each way in. The function reaches the
    start of the loop from its entry and from the block that copies. *)
Definition loop_from_start : cut_sig :=
  Eval vm_compute in cut_edge S.temp_keys S.live_in glibc___printf_buffer_write "L15" "start".
Definition loop_from_copy : cut_sig :=
  Eval vm_compute in cut_edge S.temp_keys S.live_in glibc___printf_buffer_write "L15" "L68".

(** Each round of the loop starts with phi nodes, which copy `c: s`
    and `c: count` into two fixed temporaries. So the rest of the block
    reads the same temporaries whichever way the function came in. The
    definition [loop_body] lists the temporaries that the rest of the
    block reads. The proof below treats that rest once and uses it for
    both rows of the block. *)
Definition loop_body : cut_sig :=
  Eval vm_compute in cut_body S.temp_keys S.live_in glibc___printf_buffer_write "L15" "start".

(** The function also reaches the block that copies the bytes from
    two blocks. It comes from the block `L43` when the window has room
    for all the bytes that are left, and from the block `L67` when the
    window has less room. The next two definitions list the
    temporaries for these two cases. *)
Definition copy_from_count : cut_sig :=
  Eval vm_compute in cut_edge S.temp_keys S.live_in glibc___printf_buffer_write "L68" "L43".
Definition copy_from_room : cut_sig :=
  Eval vm_compute in cut_edge S.temp_keys S.live_in glibc___printf_buffer_write "L68" "L67".

(** The block that copies starts with a phi node as well. The node
    copies the number of bytes to copy into one fixed temporary, so
    the rest of the block reads that temporary on both ways in. The
    definition [copy_body] lists the temporaries that the rest of the
    block reads. *)
Definition copy_body : cut_sig :=
  Eval vm_compute in cut_body S.temp_keys S.live_in glibc___printf_buffer_write "L68" "L67".

Section write.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!Callees [(TAtom "__printf_buffer_flush", flush_spec k R); (TAtom "__GI_memcpy", win_copy_spec)] }.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The block table *)

(** The record [wr_in] is the logical input of a round of the loop.
    It names the buffer and the run of bytes with its object, the
    number of bytes already copied and the number still to copy. *)
Record wr_in : Type := WrIn {
  wr_buf : Z; wr_dq : dfrac; wr_p : ptr; wr_sb : Z; wr_sreg : region; wr_str : list Z;
  wr_done : Z; wr_count : Z
}.

(** The pointer `c: s` points past the bytes that are already copied. *)
Definition wr_vals (x : wr_in) : list (string * word) :=
  [("buf", WPtr (mkPtr (wr_buf x) (Obj (wr_buf x))));
   ("s", WPtr (mkPtr (ptr_addr (wr_p x) + wr_done x) (ptr_cap (wr_p x))));
   ("count", WInt (wr_count x))].

(** The bytes still to copy lie in the run, and their number is a C
    integer. *)
Definition wr_ok (x : wr_in) : Prop :=
  0 <= wr_done x /\ 0 <= wr_count x < 2 ^ 64 /\ wr_done x + wr_count x <= Z.of_nat (length (wr_str x)).

(** The function returns nothing and gives back the usable buffer and
    the run of bytes. *)
Definition wr_post (x : wr_in) (o : outcome) : iProp Σ :=
  (⌜o = RetVoid⌝ ∗ printf_out k R (wr_buf x) ∗ byte_run (wr_dq x) (wr_p x) (wr_sb x) (wr_sreg x) (wr_str x))%I.

(** A round starts with a usable buffer and the caller's run of
    bytes. *)
Definition wr_pre (x : wr_in) : iProp Σ :=
  (⌜wr_ok x⌝ ∗ printf_out k R (wr_buf x) ∗ byte_run (wr_dq x) (wr_p x) (wr_sb x) (wr_sreg x) (wr_str x))%I.

(** The record [wr_room] adds the buffer's parts to the input of a
    round, for the blocks that run when the window has a free byte.
    Its last field is the number of bytes that the round copies. *)
Record wr_room : Type := WrRoom {
  wm_in : wr_in; wm_breg : region; wm_win : pwin; wm_written : Z; wm_mode : Z;
  wm_copy : Z
}.

(** The window has a free byte, and there is a byte to copy. *)
Definition room_pre (y : wr_room) : iProp Σ :=
  (⌜wr_ok (wm_in y) /\ 0 < wr_count (wm_in y) /\ pw_ptr (wm_win y) < pw_end (wm_win y) /\
    (wm_mode y = mode_failed \/ wm_mode y = k)⌝ ∗
   printf_buf (wr_buf (wm_in y)) (wm_breg y) (wm_win y) (wm_written y) (wm_mode y) ∗ R (wr_buf (wm_in y)) (wm_breg y) (pw_place (wm_win y)) ∗
   byte_run (wr_dq (wm_in y)) (wr_p (wm_in y)) (wr_sb (wm_in y)) (wr_sreg (wm_in y)) (wr_str (wm_in y)))%I.

(** The round copies at least one byte, no more than the count and no
    more than the window has room for. *)
Definition copy_ok (y : wr_room) : Prop :=
  0 < wm_copy y /\ wm_copy y <= wr_count (wm_in y) /\ wm_copy y <= pw_end (wm_win y) - pw_ptr (wm_win y).

(** The block that copies also has the variable `c: to_copy`. *)
Definition copy_vals (y : wr_room) : list (string * word) :=
  wr_vals (wm_in y) ++ [("to_copy", WInt (wm_copy y))].

(** The table has a row for the entry, two rows for the start of the
    loop, a row for the block that runs when the window has room, and
    two rows for the block that copies. The first of those two is for
    a round that copies every byte that is left. *)
Definition write_blocks : list bspec :=
  [BSpec "start" None (cut_in write_cuts "start") wr_in wr_vals wr_pre wr_post;
   BSpec "L15" (Some "start") loop_from_start wr_in wr_vals wr_pre wr_post;
   BSpec "L15" (Some "L68") loop_from_copy wr_in wr_vals wr_pre wr_post;
   BSpec "L22" None (cut_in write_cuts "L22") wr_room (fun y => wr_vals (wm_in y)) room_pre
     (fun y => wr_post (wm_in y));
   BSpec "L68" (Some "L43") copy_from_count wr_room copy_vals
     (fun y => ⌜copy_ok y /\ wm_copy y = wr_count (wm_in y)⌝ ∗ room_pre y)%I (fun y => wr_post (wm_in y));
   BSpec "L68" (Some "L67") copy_from_room wr_room copy_vals
     (fun y => ⌜copy_ok y⌝ ∗ room_pre y)%I (fun y => wr_post (wm_in y))].

(** ## The blocks *)

(** The tactic [row_simpl] unfolds a row's statement into the facts
    and the ownership that it stands for. *)
Local Ltac row_simpl :=
  cbn [bs_sig bs_vals bs_pre bs_post bs_label] in *;
  unfold wr_pre, wr_post, room_pre, wr_ok, copy_ok, wr_vals, copy_vals in *;
  cbn [app wr_buf wr_dq wr_p wr_sb wr_sreg wr_str wr_done wr_count wm_in wm_breg wm_win wm_written wm_mode wm_copy
       ptr_addr ptr_cap] in *.

(** Every block of the function meets its row. *)
Lemma write_table : ⊢ blocks_hold glibc___printf_buffer_write write_blocks.
Proof using Type*.
  apply blocks_close. iIntros "#IH".
  (* L15: a round of the loop returns when no byte is left. Otherwise it looks for a free byte in the
     window, and it calls the flushing function when the window is full. The two rows for this block
     share this proof of the block's body. *)
  iAssert (body_triple glibc___printf_buffer_write "L15" loop_body wr_in wr_vals wr_pre wr_post) as "#Hloop".
  { iModIntro;
  iIntros ([bb dq [pa pc] sb sreg str d cnt] e Φ) "%He H HK"; row_simpl; c_env_open He;
  iDestruct "H" as "[%Hok [Hout Hstr]]"; body_start glibc___printf_buffer_write "L15"; step; branch_eqn E;
  [step; iApply wp_ret_void; iNext; iApply "HK"; iFrame "Hstr Hout"; done|];
  step; iDestruct "Hout" as (breg w written mode) "(%Hmd & Hbuf & HR)"; buf_open "Hbuf";
  step; check "Hl"; load_window "Hl" "Hptr" "Hwl"; step; check "Hl"; load_window "Hl" "Hend" "Hwl";
  step; step; step; branch_eqn E2;
  [step; branch;
   goto_block "IH" "HK" 3%nat with (WrRoom (WrIn bb dq (mkPtr pa pc) sb sreg str d cnt) breg w written mode 0);
   row_simpl; iFrame "Hstr HR"; iSplit; [iPureIntro|buf_close; exact Hw];
   unfold pwin_ok in Hw; branch_fact E; branch_fact E2; lia|];
  step; call_callee with bb giving "Hl Hbase Hptr Hend Hwr Hmode Hwl Hwin HR"; [out_close "HR" with w; exact Hw|];
  clear Hmd E2;
  iDestruct "Hpost" as (b breg2 w2 written2 mode2) "((-> & %Hb & %Hmd & %Hroom) & Hbuf & HR)";
  block_resume; destruct Hb as [-> | ->]; step; step; step; step; branch;
  [step; iApply wp_ret_void; iNext; iApply "HK"; iFrame "Hstr"; iSplit; [done|];
   iExists breg2, w2, written2, mode2; iFrame "Hbuf HR"; done|];
  goto_block "IH" "HK" 3%nat with (WrRoom (WrIn bb dq (mkPtr pa pc) sb sreg str d cnt) breg2 w2 written2 mode2 0);
  row_simpl; iFrame "Hstr HR Hbuf"; iPureIntro; branch_fact E; lia. }
  (* L68: the round copies the bytes, advances the buffer's write pointer and the pointer into the
     run, and goes back to the start of the loop. The run lends the bytes to memcpy, and the
     buffer lends its window. The two rows for this block share this proof of the block's body. *)
  iAssert (body_triple glibc___printf_buffer_write "L68" copy_body wr_room copy_vals
    (fun y => ⌜copy_ok y⌝ ∗ room_pre y)%I (fun y => wr_post (wm_in y))) as "#Hcopy".
  { iModIntro;
  iIntros ([[bb dq [pa pc] sb sreg str d cnt] breg w written mode m] e Φ) "%He H HK"; row_simpl; c_env_open He;
  iDestruct "H" as "(%Hcp & (%Hok & %Hcnt & %Hroom & %Hmd) & Hbuf & HR & Hstr)"; destruct Hcp as [Hcp Hm0]; destruct Hm0;
  buf_open "Hbuf"; unfold pwin_ok in Hw; body_start glibc___printf_buffer_write "L68"; step; load_window "Hl" "Hptr" "Hwl";
  iDestruct (byte_run_lend dq (mkPtr pa pc) sb sreg str d m with "Hstr")
    as (ys) "((%Hlen & %Hc & %Hsb8 & %Hsa & %Hsend & %Hsp & %Hy) & Hsl & Hys & Hback)"; [lia..|];
  cbn [ptr_addr ptr_cap] in *; destruct Hlen;
  iDestruct (win_live_acc with "Hl Hwl") as "[Hwo Hwback]";
  call_callee with (pw_obj w, pw_reg w, pw_lo w, pw_end w, pw_ptr w, dq, sb, sreg, mkPtr (pa + d) pc, ys)
    giving "Hwo Hwin Hsl Hys";
  [iFrame "Hwo Hwin Hsl Hys"; iPureIntro; unfold pw_lo; cbn [ptr_addr ptr_cap];
   repeat split; try assumption; try (Z.div_mod_to_equations; lia)|];
  iDestruct "Hpost" as "(-> & Hwo & Hwin & Hsl & Hys)"; iDestruct ("Hback" with "Hsl Hys") as "Hstr";
  iDestruct ("Hwback" with "Hwo") as "[Hl Hwl]"; block_resume;
  check "Hl"; load_window "Hl" "Hptr" "Hwl"; step; check "Hl"; store "Hl" "Hptr"; step; step; step;
  cbn [ptr_addr ptr_cap edge_label]; unwrap2;
  goto_block "IH" "HK" 2%nat with (WrIn bb dq (mkPtr pa pc) sb sreg str (d + Z.of_nat (length ys)) _);
  row_simpl; iFrame "Hstr"; iSplit; [iPureIntro; lia|];
  out_close "HR" with (PWin (pw_obj w) (pw_reg w) (pw_base w) (pw_ptr w + Z.of_nat (length ys)) (pw_end w));
  unfold pwin_ok; cbn [pw_obj pw_reg pw_base pw_ptr pw_end]; lia. }
  repeat iSplit; [| | | | | | done]; iModIntro.
  (* The two rows for L15 take the step into the block and use its body. *)
  2,3: (iIntros ([bb dq [pa pc] sb sreg str d cnt] e from Φ) "%Hfrom %He H HK"; row_simpl; c_env_open He;
        iDestruct "H" as "[%Hok H]"; block_enter_from Hfrom; rewrite (Z.mod_small cnt (2 ^ 64)); [|lia];
        iApply ("Hloop" $! (WrIn bb dq (mkPtr pa pc) sb sreg str d cnt) with "[] [H] HK");
        [iPureIntro; c_env_close | row_simpl; iFrame "H"; done]).
  (* The two rows for L68 do the same. The first row copies every byte that is left. *)
  3: (iIntros (y e from Φ) "%Hfrom %He [[%Hcp %Hm] H] HK"; row_simpl; c_env_open He;
      iDestruct "H" as "[%Hroom H]"; block_enter_from Hfrom;
      rewrite (Z.mod_small (wr_count (wm_in y)) (2 ^ 64)); [|lia];
      iApply ("Hcopy" $! y with "[] [H] HK");
      [iPureIntro; row_simpl; rewrite Hm; c_env_close
      | cbn beta; row_simpl; iFrame "H"; iPureIntro; split; assumption]).
  3: (iIntros (y e from Φ) "%Hfrom %He [%Hcp H] HK"; row_simpl; c_env_open He;
      iDestruct "H" as "[%Hroom H]"; block_enter_from Hfrom;
      rewrite (Z.mod_small (wm_copy y) (2 ^ 64)); [|lia];
      iApply ("Hcopy" $! y with "[] [H] HK");
      [iPureIntro; row_simpl; c_env_close
      | cbn beta; row_simpl; iFrame "H"; iPureIntro; split; assumption]).
  - (* start: a buffer that has failed takes no bytes. *)
    iIntros ([bb dq [pa pc] sb sreg str d cnt] e from Φ) "_ %He H HK".
    row_simpl. c_env_open He. iDestruct "H" as "[%Hok [Hout Hstr]]".
    iDestruct "Hout" as (breg w written mode) "(%Hmd & Hbuf & HR)". buf_open "Hbuf".
    block_enter. step. check "Hl". load_mode "Hl" "Hmode". step. branch_eqn E.
    + goto_block "IH" "HK" 1%nat with (WrIn bb dq (mkPtr pa pc) sb sreg str d cnt).
      row_simpl. iFrame "Hstr". iSplit; [done|]. out_close "HR" with w. exact Hw.
    + step. iApply wp_ret_void. iNext. iApply "HK". iFrame "Hstr". iSplit; [done|].
      out_close "HR" with w. exact Hw.
  - (* L22: the window has room, so the round copies what fits. *)
    iIntros ([[bb dq [pa pc] sb sreg str d cnt] breg w written mode m] e from Φ) "_ %He H HK". row_simpl. c_env_open He.
    iDestruct "H" as "((%Hok & %Hcnt & %Hroom & %Hmd) & Hbuf & HR & Hstr)". buf_open "Hbuf". unfold pwin_ok in Hw.
    block_enter. step. check "Hl". load_window "Hl" "Hptr" "Hwl". step. check "Hl". load_window "Hl" "Hend" "Hwl".
    step. step. step. branch_as false. step.
    step. check "Hl". load_window "Hl" "Hend" "Hwl". step. check "Hl". load_window "Hl" "Hptr" "Hwl".
    step. step. step. step. unwrap2. branch_eqn E.
    + step. step.
      goto_block "IH" "HK" 5%nat
        with (WrRoom (WrIn bb dq (mkPtr pa pc) sb sreg str d cnt) breg w written mode (pw_end w - pw_ptr w)).
      row_simpl. iFrame "Hstr HR". iSplit; [iPureIntro|iSplit; [iPureIntro|buf_close; exact Hw]].
      * branch_fact E. lia.
      * lia.
    + goto_block "IH" "HK" 4%nat with (WrRoom (WrIn bb dq (mkPtr pa pc) sb sreg str d cnt) breg w written mode cnt).
      row_simpl. iFrame "Hstr HR". iSplit; [iPureIntro|iSplit; [iPureIntro|buf_close; exact Hw]].
      * branch_fact E. lia.
      * lia.
Qed.

(** ## The contracts *)

(** A caller that appends a run of bytes uses this lemma. It says that
    the compiled function meets [write_bytes_spec] in every program
    that defines the function. *)
Lemma write_bytes_has_spec `{!Defines ge "__printf_buffer_write" glibc___printf_buffer_write} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_write") (write_bytes_spec k R).
Proof using Type*.
  eapply (blocks_has_spec _ _ _ write_blocks); [exact defines | reflexivity | reflexivity | | exact write_table].
  intros [[[[[[bb dq] p] sb] sreg] ys] n]. eexists _, (WrIn bb dq p sb sreg ys 0 n). split; [reflexivity|]. split.
  { destruct p. c_env_close. }
  cbn [fs_pre fs_post bs_pre bs_post write_bytes_spec]. unfold wr_pre, wr_post, wr_ok.
  cbn [wr_buf wr_dq wr_p wr_sb wr_sreg wr_str wr_done wr_count].
  iIntros "(-> & Hout & Hrun)". iDestruct "Hrun" as "(%Hrun & Hrun)".
  iFrame "Hout Hrun". iSplit; [iPureIntro; split; [lia | exact Hrun]|]. iIntros (r) "$".
Qed.

(** A contract follows from another contract of the same function
    when its precondition gives the other one's for some logical
    input, and takes the other one's postcondition back. The input may
    be one that the precondition's own resources name, such as the
    object of a string. The first premise finds an input with the same
    arguments without any resource, so that the call itself is well
    formed. *)
Lemma has_spec_open n s s' :
  HasSpec registry (os_wi w0) ge n s ->
  (forall y, (exists x, fs_args s' y = fs_args s x) /\
     (fs_pre s' y ⊢ ∃ x, ⌜fs_args s' y = fs_args s x⌝ ∗ fs_pre s x ∗ ∀ v, fs_post s x v -∗ fs_post s' y v)) ->
  HasSpec registry (os_wi w0) ge n s'.
Proof using Type.
  intros Hs Hweak y. destruct (Hweak y) as [[x0 Hargs0] Hpre].
  destruct (Hs x0) as (gf & Hg & Hfr & _).
  exists gf. rewrite Hargs0. split; [exact Hg|]. split; [exact Hfr|].
  intros fr Φ Hcall. iIntros "HP HK". iDestruct (Hpre with "HP") as (x) "(%Hargs & HP & HW)".
  destruct (Hs x) as (gf' & Hg' & _ & Ht). rewrite Hg in Hg'. injection Hg' as <-.
  rewrite -Hargs0 Hargs in Hcall. iApply (Ht fr Φ Hcall with "HP"). iIntros (v) "HQ". iApply "HK". iApply ("HW" with "HQ").
Qed.

(** A caller that appends the first bytes of a string uses this lemma.
    It says that the compiled function meets [write_spec], because a
    string lends those bytes as a run. *)
Lemma write_has_spec `{!Defines ge "__printf_buffer_write" glibc___printf_buffer_write} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_write") (write_spec k R).
Proof using Type*.
  eapply (has_spec_open _ (write_bytes_spec k R)); [exact write_bytes_has_spec|].
  intros [[[[bb dq] p] str] n]. split; [exists (bb, dq, p, 0, mkRegion 0 0 Heap Live, [], n); reflexivity|].
  cbn [fs_pre fs_post fs_args write_spec write_bytes_spec]. iIntros "(%Hn & Hout & Hstr)".
  iDestruct (word_string_run dq p str n Hn with "Hstr") as (sb sreg ys) "(%Hlen & Hrun & Hback)".
  iExists (bb, dq, p, sb, sreg, ys, n). iFrame "Hout Hrun". iSplit; [done|]. iSplit; [iPureIntro; lia|].
  iIntros (v) "($ & $ & Hrun)". iApply ("Hback" with "Hrun").
Qed.

End write.
