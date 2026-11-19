(** A call of `c: fprintf` ends by counting what it printed. The
    function `c: __printf_buffer_done` adds the bytes in the buffer's
    window to the count of bytes already flushed, and it returns the
    sum as an int. It returns -1 when the buffer has failed. It also
    returns -1 when the sum does not fit an int, and it then sets errno
    to EOVERFLOW. For a buffer that prints to a stream, the function
    `c: __printf_buffer_to_file_done` first flushes the window to the
    stream and then counts.

    This module states a contract for each of the two functions and
    proves that the compiled code meets it. Both contracts give the
    buffer back as they got it, so the caller can take the stream out
    of the buffer's invariant afterwards. *)

From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_done_os Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Interval
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers MemchrLast DcigettextExit
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec PrintfCountBits
  PrintfBufferDone PrintfBufferCount PrintfBufferFileSrc PrintfBufferFileNames PrintfFlush.
Import ListNotations ProgramAbbreviations SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## Counting *)

(** The record [bd_in] is the logical input of
    `c: __printf_buffer_done`. It names the buffer, the region of the
    buffer's object, the window, the count of flushed bytes, the mode
    and the object of errno. *)
Record bd_in : Type := BdIn {
  bd_buf : Z; bd_breg : region; bd_win : pwin; bd_written : Z; bd_mode : Z; bd_eb : Z
}.

Section done.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: __printf_buffer_done (buf)` returns an int and changes nothing
    but errno. The count of flushed bytes must be a 64-bit number,
    which every flush leaves. The function stores to errno through the
    global `c: __libc_errno`, so the contract asks that this global is
    the errno cell of the thread. *)
Definition buffer_done_spec : fspec Σ :=
  FSpec bd_in (fun x => [WPtr (mkPtr (bd_buf x) (Obj (bd_buf x)))])
    (fun x =>
       ⌜0 <= bd_written x < 2 ^ 64 /\ ow_errno w0 = Some (mkPtr (bd_eb x) (Obj (bd_eb x))) /\
        lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (bd_eb x) (Obj (bd_eb x)))⌝ ∗
       printf_buf (bd_buf x) (bd_breg x) (bd_win x) (bd_written x) (bd_mode x) ∗ errno_any (bd_eb x))%I
    (fun x o =>
       ∃ n, ⌜o = Ret (WInt n) /\ 0 <= n < 2 ^ 32⌝ ∗
       printf_buf (bd_buf x) (bd_breg x) (bd_win x) (bd_written x) (bd_mode x) ∗ errno_any (bd_eb x))%I.

(** To count the bytes in the window, the function loads two pointers
    from the buffer: the write pointer and the write base. A load of a
    pointer checks two objects. The buffer that holds the pointer must
    be alive, and so must the object that the pointer points into. The
    rules for the count therefore ask for a share of each lifetime.
    This lemma splits a buffer into those two shares and the four
    fields that the function reads, and it puts the buffer together
    again from the same parts. The window may lie in the buffer's own
    object. Both shares are then halves of the buffer's lifetime. *)
Lemma printf_buf_count bb breg w written mode :
  printf_buf bb breg w written mode ⊢ ∃ dq1 dq2,
    let db := pw_obj w in let bo := pw_base w - pw_obj w in let used := pw_ptr w - pw_base w in
    let cells := (liveq dq1 bb breg ∗ liveq dq2 db (pw_reg w) ∗ int_cell bb 32 mode ∗
      pcell bb 0 (mkPtr (db + bo) (Obj db)) ∗ pcell bb 8 (mkPtr (db + bo + used) (Obj db)) ∗
      icell bb 24 written)%I in
    ⌜pwin_ok w /\ 0 < bb /\ bb mod 8 = 0 /\ bb + 40 <= r_end breg /\ r_end breg <= 2 ^ 63⌝ ∗
    cells ∗ (cells -∗ printf_buf bb breg w written mode).
Proof using Type.
  iIntros "Hbuf". buf_open "Hbuf". pose proof Hw as (W1 & W2 & W3 & W4 & W5 & W6 & W7). cbn zeta.
  replace (pw_obj w + (pw_base w - pw_obj w) + (pw_ptr w - pw_base w)) with (pw_ptr w) by lia.
  replace (pw_obj w + (pw_base w - pw_obj w)) with (pw_base w) by lia.
  unfold printf_buf, win_live. destruct (numbers.Z.eq_dec (pw_obj w) bb) as [Heq|Hne].
  - iDestruct "Hwl" as %Hreg. iEval (rewrite /live pts_ptsq -Qp.half_half ptsq_split) in "Hl". iDestruct "Hl" as "[Hl Hl']".
    iExists (DfracOwn (1/2)), (DfracOwn (1/2)). iEval (rewrite -{1}Heq -Hreg) in "Hl'".
    iFrame "Hl Hl' Hmode Hbase Hptr Hwr". iSplit; [iPureIntro; intuition lia|].
    iIntros "(Hl & Hl' & Hmode & Hbase & Hptr & Hwr)". iEval (rewrite /liveq Heq Hreg) in "Hl'". iCombine "Hl Hl'" as "Hl".
    iEval (rewrite /liveq -ptsq_split Qp.half_half -pts_ptsq) in "Hl".
    iAssert (⌜pw_reg w = breg⌝)%I as "Hwl"; [done|]. buf_close. exact Hw.
  - iExists (DfracOwn 1), (DfracOwn 1). iEval (rewrite /live pts_ptsq) in "Hl". iEval (rewrite /live pts_ptsq) in "Hwl".
    iFrame "Hl Hwl Hmode Hbase Hptr Hwr". iSplit; [iPureIntro; intuition lia|].
    iIntros "(Hl & Hwl & Hmode & Hbase & Hptr & Hwr)". iEval (rewrite /liveq -pts_ptsq) in "Hl". iEval (rewrite /liveq -pts_ptsq) in "Hwl".
    buf_close. exact Hw.
Qed.

(** A count that does not fit an int fails. The function stores
    EOVERFLOW to errno and returns -1. The store is safe because the
    errno cell of a thread is alive as long as the thread runs. *)
Lemma wp_buffer_done_overflow fr bb breg db dreg bo used written mode dq1 dq2 eb bs Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= used -> db + bo + used <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  0 <= written < 2 ^ 64 -> 2 ^ 31 <= written + used -> mode <> 0 -> length bs = 4%nat ->
  liveq dq1 bb breg -∗ liveq dq2 db dreg -∗ int_cell bb 32 mode -∗
  pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
  pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗ icell bb 24 written -∗ bytes eb 0 bs -∗
  ▷ (liveq dq1 bb breg -∗ liveq dq2 db dreg -∗ int_cell bb 32 mode -∗
     pcell bb 0 (mkPtr (db + bo) (Obj db)) -∗
     pcell bb 8 (mkPtr (db + bo + used) (Obj db)) -∗ icell bb 24 written -∗
     bytes eb 0 (le_bytes 75 4) -∗ Φ (Ret (WInt 4294967295))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Herr Hge Hbb Hal Hend Hreg Hdb Hbo Hused Hdend Hdreg Hw Htotal Hmode Hbs.
  injection Hfr as <-. iIntros "Hl Hd [%Hm Hmode] Hbase Hptr Hwritten Heb HK".
  step. step. norm.
  check_read_dq "Hl" by ar.
  iNext. iIntros "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hmode");
    [reflexivity | reflexivity | reflexivity |
     unfold int_bytes;
     rewrite of_bytes_int; [cbn; rewrite !(Z.mod_small mode (2 ^ 32) Hm); reflexivity|exact Hm] |
     left; reflexivity | ar |].
  iNext. iIntros "Hl Hmode". step. branch_as true. step. step. norm.
  iApply (MemchrLast.wp_half_check_read_dq registry (os_wi w0) ge with "Hl");
    [reflexivity | reflexivity | reflexivity | left; reflexivity | ar | ar | lia | ar | ar |].
  iNext. iIntros "Hl".
  load_pointer_dq "Hl Hptr Hd" by ar.
  iNext. iIntros "Hl Hptr Hd".
  iApply (MemchrLast.wp_half_check_read_dq registry (os_wi w0) ge with "Hl");
    [reflexivity | reflexivity | reflexivity | left; reflexivity | ar | ar | lia | ar | ar |].
  iNext. iIntros "Hl".
  load_pointer_dq "Hl Hbase Hd" by ar.
  iNext. iIntros "Hl Hbase Hd". step. step. step. step. norm.
  iApply (wp_raw_load_read_dq with "Hl Hwritten");
    [reflexivity | reflexivity | left; reflexivity | ar |].
  iNext. iIntros "Hl Hwritten".
  step. step. step. step. step. step. step. step.
  iApply wp_branch; [GlibcTactics.vx|iNext].
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    assert (E : (n =? 0) = false) end.
  { replace (db + bo + used - (db + bo)) with used by lia.
    rewrite !(Z.mod_small written (2 ^ 64) Hw).
    rewrite !(Z.mod_small used (2 ^ 64) ltac:(lia)).
    rewrite !Z.mod_mod; try lia.
    pose proof (printf_count_overflows written used Hw ltac:(lia) Htotal) as Hoverflow.
    unfold printf_count_overflow in Hoverflow.
    set (total := (written + used) mod 2 ^ 64) in *.
    assert (Hnarrow : sign_extension (2 ^ 32) (2 ^ 31) (total mod 2 ^ 32) =
      sign_extension (2 ^ 32) (2 ^ 31) total).
    { unfold sign_extension. rewrite Z.mod_mod; [reflexivity|lia]. }
    rewrite Hnarrow.
    set (narrowed := sign_extension (2 ^ 32) (2 ^ 31) total) in *.
    rewrite printf_signed64_int; [|apply sign_extension_range; lia].
    change ((63 mod 2 ^ 32) mod 64) with 63.
    destruct (total <? written);
      try change (1 mod 2 ^ 32) with 1;
      try change (1 mod 2 ^ 64) with 1;
      try change (0 mod 2 ^ 32) with 0;
      try change (0 mod 2 ^ 64) with 0;
      destruct (negb (total =? narrowed mod 2 ^ 64));
      destruct (negb (0 =? (narrowed / 2 ^ 63) mod 2 ^ 64));
      destruct (negb (1 =? (narrowed / 2 ^ 63) mod 2 ^ 64));
      cbn in Hoverflow |- *; try discriminate; reflexivity. }
  rewrite E. cbn [edge_label]. step.
  step_global Hge. iApply (wp_dci_errno_check eb Herr); [vx|]. iNext.
  iApply (wp_dci_errno_store eb Herr with "Heb"); [vx | vx | exact Hbs|]. iNext. iIntros "Heb".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply ("HK" with "Hl Hd [Hmode] Hbase Hptr Hwritten Heb"). iSplit; [done|iExact "Hmode"].
Qed.

(** The compiled function meets its contract. A failed buffer returns
    at once. Otherwise the sum of the two counts either fits an int or
    it does not, and the two rules above cover the two cases. *)
Lemma buffer_done_has_spec `{!Defines ge "__printf_buffer_done" Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_done") buffer_done_spec.
Proof using Type.
  intros [bb breg w written mode eb]. exists Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. cbn [fs_args fs_pre fs_post buffer_done_spec bd_buf bd_breg bd_win bd_written bd_mode bd_eb] in *.
  iIntros "((%Hwr & %Herr & %Hge) & Hbuf & Herrno) HK".
  destruct (Z.eq_dec mode 0) as [->|Hmode].
  - buf_open "Hbuf". iApply (wp_printf_buffer_done_failed _ bb breg with "Hl Hmode"); try first [exact Hfr | lia].
    iNext. iIntros "Hl Hmode". iApply "HK". iExists 4294967295. iFrame "Herrno". iSplit; [iPureIntro; split; [reflexivity|lia]|].
    buf_close. exact Hw.
  - iDestruct (printf_buf_count with "Hbuf") as (dq1 dq2) "(%Hf & (Hl & Hd & Hmode & Hbase & Hptr & Hwritten) & Hback)". cbn zeta.
    destruct Hf as ((W1 & W2 & W3 & W4 & W5 & W6 & W7) & B1 & B2 & B3 & B4).
    destruct (Z_lt_le_dec (written + (pw_ptr w - pw_base w)) (2 ^ 31)) as [Hfit|Hbig].
    + iApply (wp_printf_buffer_done_count _ bb breg (pw_obj w) (pw_reg w) (pw_base w - pw_obj w) (pw_ptr w - pw_base w) written mode dq1 dq2
        with "Hl Hd Hmode Hbase Hptr Hwritten"); try first [exact Hfr | lia].
      iNext. iIntros "Hl Hd Hmode Hbase Hptr Hwritten". iApply "HK". iExists _. iFrame "Herrno".
      iSplit; [iPureIntro; split; [reflexivity|lia]|]. iApply "Hback". iFrame.
    + iDestruct "Herrno" as (bs cs [Hbs Hcs]) "Hp". iEval (rewrite pts_app) in "Hp". iDestruct "Hp" as "[Heb Hea]".
      iApply (wp_buffer_done_overflow _ bb breg (pw_obj w) (pw_reg w) (pw_base w - pw_obj w) (pw_ptr w - pw_base w) written mode dq1 dq2 eb bs
        with "Hl Hd Hmode Hbase Hptr Hwritten Heb"); try first [exact Hfr | exact Herr | exact Hge | exact Hbs | lia].
      iNext. iIntros "Hl Hd Hmode Hbase Hptr Hwritten Heb". iApply "HK". iExists 4294967295.
      iSplit; [iPureIntro; split; [reflexivity|lia]|]. iSplitR "Heb Hea"; [iApply "Hback"; iFrame|].
      iExists (le_bytes 75 4), cs. iSplit; [done|]. rewrite pts_app. iFrame.
Qed.

End done.

(** ## Finishing a print to a stream *)

Module S := PrintfBufferFileSrc.fn___printf_buffer_to_file_done.
Import PrintfBufferFileNames.fn___printf_buffer_to_file_done.

Section file_done.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (R : Z -> region -> Z * region * Z * Z -> iProp Σ).

(** `c: __printf_buffer_to_file_done (buf)` returns the number of
    bytes printed, or -1. Its logical input is the buffer and the
    object of errno. The contract takes a usable buffer in the mode of
    a file-backed buffer and gives one back. The count may set errno,
    so the buffer's invariant must lend errno, as it does for the
    formatter. *)
Definition file_done_spec : fspec Σ :=
  FSpec (Z * Z) (fun x => [WPtr (mkPtr x.1 (Obj x.1))])
    (fun x =>
       ⌜ow_errno w0 = Some (mkPtr x.2 (Obj x.2)) /\
        lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr x.2 (Obj x.2))⌝ ∗
       printf_out 4 R x.1 ∗ lends_errno R x.1 x.2)%I
    (fun x o => ∃ n, ⌜o = Ret (WInt n) /\ 0 <= n < 2 ^ 32⌝ ∗ printf_out 4 R x.1)%I.

Context `{!HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush_to_file") (flush_to_file_spec R)}.
Context `{!HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_done") buffer_done_spec}.

Definition done_cuts : list (string * cut_sig) :=
  Eval vm_compute in cut_table S.temp_keys S.live_in.

Definition done_blocks : list bspec :=
  [BSpec "start" None (cut_in done_cuts "start") (Z * Z) (fun x => [("buf", WPtr (mkPtr x.1 (Obj x.1)))])
     (fs_pre file_done_spec) (fs_post file_done_spec)].

(** The function has one path for a failed buffer and one for a buffer
    that has not failed. On the second path it calls the flush and then
    the count, and the count borrows errno from the buffer's
    invariant. *)
Lemma done_table : ⊢ blocks_hold Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done done_blocks.
Proof using Type*.
  apply blocks_close. iIntros "#IH". iSplit; [|done]. iModIntro.
  iIntros ([bb eb] e from Φ) "_ %He H HK"; cbn [bs_sig bs_vals bs_label bs_post bs_pre fs_pre fs_post file_done_spec fst snd] in *; c_env_open He.
  iDestruct "H" as "((%Herr & %Hge) & Hout & #Hlend)". iDestruct "Hout" as (br w written mode) "(%Hmd & Hbuf & HR)".
  buf_open "Hbuf". block_enter. step. check "Hl". load_mode "Hl" "Hmode". step.
  destruct Hmd as [-> | ->]; branch.
  - step. iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK". iExists 4294967295. iSplit; [iPureIntro; split; [reflexivity|lia]|].
    iExists br, w, written, mode_failed. iFrame "HR". iSplit; [iPureIntro; by left|]. buf_close. exact Hw.
  - clear Hmode_range.
    iAssert (fs_pre (flush_to_file_spec R) bb) with "[Hl Hbase Hptr Hend Hwr Hmode Hwl Hwin HR]" as "Hpre".
    { iExists br, w, written. iFrame "HR". buf_close. exact Hw. }
    step. call_callee with bb giving "Hpre"; first iExact "Hpre".
    iDestruct "Hpost" as (br' w' written' mode') "((-> & %Hwr' & %Hmd') & Hbuf & HR)". block_resume.
    iDestruct ("Hlend" with "HR") as "[Herrno Hback]".
    iAssert (fs_pre buffer_done_spec (BdIn bb br' w' written' mode' eb)) with "[Hbuf Herrno]" as "Hpre".
    { cbn [fs_pre buffer_done_spec bd_buf bd_breg bd_win bd_written bd_mode bd_eb]. iFrame "Hbuf Herrno". done. }
    call_callee with (BdIn bb br' w' written' mode' eb) giving "Hpre"; first iExact "Hpre".
    iDestruct "Hpost" as (n) "((-> & %Hn) & Hbuf & Herrno)". cbn [bd_buf bd_breg bd_win bd_written bd_mode bd_eb]. block_resume.
    iDestruct ("Hback" with "Herrno") as "HR".
    iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK". iExists n.
    iSplit; [iPureIntro; rewrite Z.mod_mod; [|lia]; rewrite Z.mod_small; [done|lia]|].
    iExists br', w', written', mode'. iFrame "Hbuf HR". iPureIntro. destruct Hmd' as [-> | (-> & _)]; [by left | by right].
Qed.

Lemma file_done_has_spec `{!Defines ge "__printf_buffer_to_file_done" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_to_file_done") file_done_spec.
Proof using Type*.
  eapply (blocks_has_spec _ _ _ done_blocks); [exact defines | reflexivity | reflexivity | | exact done_table].
  intros [bb eb]. eexists _, (bb, eb). split; [reflexivity|]. split; [c_env_close|]. cbn [bs_pre bs_post]. iIntros "$" (r) "$".
Qed.

End file_done.
