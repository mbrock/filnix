(** The safety proof of hi_atexit starts at `c: main`, in a state that
    [HiAtexitPrepare](HiAtexitPrepare.v) builds by host writes. The proof
    of glibc's startup code ends at the same place, the call of `c: main`
    from `c: __libc_start_call_main`. This module connects the two. It
    says what startup must hold when it calls `c: main`, and it proves
    that this is enough for main's existing proof.

    ## Where main's state comes from

    Main's precondition [hi_main_state] has three sources. Most of it is
    memory that startup never writes, so it still holds the linked
    image's contents; [hi_start_kept_ps] lists those pieces. Three
    startup calls write the rest. `c: _IO_stdfiles_init` links the
    streams backwards and gives back their lives. `c: __libc_early_init`
    sets the single-thread flag and leaves `c: errno` with some value.
    `c: __libc_start_call_main` gives main the thread's cleanup fields.
    The world facts come from the final world of startup, whose errno
    cell is the image's `c: __libc_errno`. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Logic MemLogic Language.
From Glibc Require Import OsBlocks OsWorld OsRegistry OsStart FileInv LibioStdfiles StartCallMainSpec
  HiAtexitBase HiAtexitGe HiAtexitModule HiAtexitInitial HiAtexitInitialAlloc HiAtexitInitialStdout
  HiAtexitInitialExit HiAtexitEntryList HiAtexitEntryFields HiAtexitWorld HiAtexitStdout HiAtexitExit HiAtexitMain
  LibioDefaultXsputnBuf LibioXsputnBase.
From Glibc Require LibioFlushInv LibioPutsInv LibioPutsLock LibioXsputnSetp.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv LibioStdfiles.
Import LibioPutsLock LibioPutsInv LibioXsputnSetp LibioXsputnBase LibioDefaultXsputnBuf.
Open Scope Z_scope.

(** ## The memory that startup keeps *)

(** This list holds stdout's fields that no startup call touches. The stream
    constructor returns the stream's life, and `c: check_stdfiles_vtables`
    returns its pointer to the jump table at offset 216. *)
Definition hi_stdout_kept_ps : list (piece * pval) :=
  drop (S (length (hi_pointer_ps 72240 216 (mkPtr (73504 + 336) (Ro 73504))))) hi_stdout_ps.

(** These are the three standard streams, stderr, stdout and stdin. *)
Definition hi_streams : list ptr :=
  [mkPtr 71760 (Obj 71760); mkPtr 72240 (Obj 72240); mkPtr 72000 (Obj 72000)].

(** Most of the memory that main uses is never touched during startup,
    so it still holds what the linker put there. This list names that
    memory: the exit handlers, the allocator's cache, stdout's fields
    and lock, the jump tables' contents, main's string, and the fields
    of stderr and stdin. A piece that some startup call owns or borrows
    belongs to that call instead, even when the call gives it back
    unchanged. So the list leaves out the streams' lives, stdout's
    pointer to its jump table, the life of `c: __io_vtables` and the
    life of the allocator's parameters `c: mp_`. *)
Definition hi_start_kept_ps : list (piece * pval) :=
  concat [hi_initial_exit_ps; tail hi_allocator_ps; hi_stdout_kept_ps; tail hi_entry_vtables_ps;
    hi_entry_program_ps; tail (hi_entry_stream_ps 71760 72576 4222427270 2);
    tail (hi_entry_stream_ps 72000 72512 4222427272 0)].

(** The linked image holds every kept piece. *)
Lemma hi_start_kept_agree : all_agree hi_m0 hi_start_kept_ps.
Proof. apply hi_m0_pieces. vm_cast_no_check (eq_refl true). Qed.

(** No piece is listed twice. *)
Lemma hi_start_kept_nodup : NoDup hi_start_kept_ps.*1.
Proof. apply hi_unique_sound. vm_compute. reflexivity. Qed.

(** ## What main is given *)

(** A list of pieces built from groups loses its first group, when that
    group is one piece, by dropping its first element. *)
Lemma tail_concat_one (a : piece * pval) l : tail (concat ([a] :: l)) = concat l.
Proof. reflexivity. Qed.

(** It loses its first two groups, when the first is one piece, by
    dropping one more element than the second group has. *)
Lemma drop_concat_two (a : piece * pval) l1 l : drop (S (length l1)) (concat ([a] :: l1 :: l)) = concat l.
Proof. cbn [concat app drop]. rewrite -/(concat _). apply drop_app_length. Qed.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Main needs the streams linked, the program marked single-threaded
    and a place for `c: errno`, and startup sets up each of them. So when
    startup calls `c: main`, it holds the untouched pieces, the linked
    streams with their lives, the flag set to one and errno with some
    value. It also holds three pieces that startup calls borrowed and
    gave back: the allocator's parameters, the jump tables and stdout's
    pointer into them. *)
Definition hi_start_post : iProp Σ :=
  pts hi_start_kept_ps ∗ io_list_inv hge hi_streams ∗ ([∗ list] f ∈ hi_streams, stream_live f) ∗
  live 76240 (mkRegion 76240 76248 GlobalData Live) ∗ ibyte 76240 0 1 ∗ errno_any 70608 ∗
  live 68800 hi_mp_reg ∗ live 73504 (mkRegion 73504 75856 GlobalData Live) ∗
  pcell 72240 216 (mkPtr (73504 + 336) (Ro 73504)).

(** Stdout gets its life from the stream constructor and its other
    fields from the image. *)
Lemma hi_start_stdout_own w : In 1 (ow_fds w) ->
  stream_live (mkPtr 72240 (Obj 72240)) -∗ pcell 72240 216 (mkPtr (73504 + 336) (Ro 73504)) -∗
  pts hi_stdout_kept_ps -∗ errno_any 70608 -∗
  hi_stdout_before w 70608 73504 (mkPtr 72240 (Obj 72240)) 0 None.
Proof using Type.
  intros Hfd. iIntros "Hlv Hvtp". iDestruct "Hlv" as (fb freg (Heq & Hfb & Hal & Hend & Htop)) "Hl".
  injection Heq as <-.
  rewrite /hi_stdout_kept_ps /hi_stdout_ps drop_concat_two hi_pts_concat. cbn [big_opL].
  iIntros "(Hbuf & Hfl & Hf2 & Hfd & Htw & Hoff & Hcol & Hmode & Hsaved & Hlp &
    Hlk & Hlk0 & Hlk4 & Hlk8 & _) Herr".
  iExists 72240, freg, None, null, null, 72544, 4222427268, 0, 1, 0, (2 ^ 64 - 1).
  iSplitR; [iPureIntro; repeat split; assumption || lia|]. iFrame "Hl Hvtp".
  iSplitL "Hbuf".
  - iEval (rewrite hi_pts_concat; cbn [big_opL]) in "Hbuf".
    iDestruct "Hbuf" as "(Hr & Hre & Hrb & Hwb & Hb & Hbe & Hwp & Hwe & _)".
    unfold wbuf, wcells, wroom, nb_base, nb_end. iFrame. done.
  - iSplitL "Hfl Hf2 Hfd Htw Hoff Hcol Hmode Herr".
    + unfold xfields_body. iFrame "Htw Hoff Hcol Herr".
      iSplitR; [iPureIntro; split_and!; try assumption; vm_compute; intuition congruence|].
      unfold int_cell. iFrame "Hfl Hf2 Hfd Hmode".
      iPureIntro. vm_compute. intuition congruence.
    + rewrite /hi_stdout_tail. iFrame "Hlp".
      iEval (rewrite hi_pts_concat; cbn [big_opL]) in "Hsaved".
      iDestruct "Hsaved" as "(H72 & H80 & H96 & _)". iFrame "H72 H80 H96".
      iExists 72544, hi_stdout_lock_reg. iSplitR; [done|].
      unfold lock_state. iFrame "Hlk Hlk8".
      iSplitR; [iPureIntro; vm_compute; intuition congruence|].
      unfold int_cell. iFrame "Hlk0 Hlk4". iPureIntro. vm_compute. intuition congruence.
Qed.

(** An idle stream gets its life from the stream constructor and its
    other fields from the image. *)
Lemma hi_start_stream_own fb lk fl fd :
  lk mod 8 = 0 -> lk + 16 <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 -> 0 <= fd < 2 ^ 31 ->
  stream_live (mkPtr fb (Obj fb)) -∗ pts (tail (hi_entry_stream_ps fb lk fl fd)) -∗
  LibioFlushInv.stream_life (mkPtr fb (Obj fb)) ∗ LibioFlushInv.exit_stream false (mkPtr fb (Obj fb)).
Proof using Type.
  intros Hlkmod Hlkbound Hfl Hbits Hfd. iIntros "Hlv".
  rewrite /hi_entry_stream_ps. rewrite tail_concat_one hi_pts_concat. cbn [big_opL].
  iIntros "(Hfl & Hf2 & Hfd & Hmd & Hlp & Hlk & Hlk0 & Hlk4 & Hlk8 & Hptrs & _)".
  iSplitL "Hlv"; [rewrite /stream_live /LibioFlushInv.stream_life; iExact "Hlv"|].
  iExists fb, fl, 0, fd, 0, lk, (mkRegion lk (lk + 16) GlobalData Live),
    CNone, (mkRegion 0 0 Heap Live), 0, 0, 0, 0.
  iSplitR; [iPureIntro; repeat split; try assumption; cbn; lia|].
  iEval (rewrite hi_pts_concat; cbn [big_opL]) in "Hptrs".
  iDestruct "Hptrs" as "(H8 & H16 & H32 & H40 & H80 & _)".
  rewrite /lock_state /int_cell.
  iFrame "Hfl Hf2 Hfd Hmd Hlp Hlk Hlk0 Hlk4 Hlk8 H8 H16 H32 H40 H80".
  iPureIntro. cbn. repeat split; try assumption; lia.
Qed.

(** What startup holds when it calls `c: main`, together with the
    thread's cleanup fields, is main's whole precondition. *)
Lemma hi_start_post_main w : In 1 (ow_fds w) ->
  hi_start_post -∗ tcb_cleanup_inv (ow_self w) ==∗ hi_main_state w.
Proof using Type.
  intros Hfd. rewrite /hi_start_post /hi_start_kept_ps hi_pts_concat. cbn [big_opL].
  iIntros "((Hex & Halloc & Hout & Hvt & Hprog & Hse & Hsi & _) & Hio & (Lse & Lso & Lsi & _) & Hsl & Hsb & Herr &
    Lmp & Lvt & Hvtp) Htcb".
  iDestruct (hi_initial_exit_own with "Hex") as "[Hinv Hlock]".
  iDestruct (hi_allocator_own with "[Lmp Halloc]") as "HM".
  { iDestruct (pts_app with "[$Lmp $Halloc]") as "H". iExact "H". }
  iDestruct (hi_start_stdout_own w Hfd with "Lso Hvtp Hout Herr") as "Hout".
  iDestruct (hi_entry_program_own with "Hprog") as "(Hso & Hsoc & Hstr)".
  iDestruct (hi_start_stream_own with "Lse Hse") as "Hse"; [vm_compute; intuition congruence..|].
  iDestruct (hi_start_stream_own with "Lsi Hsi") as "Hsi"; [vm_compute; intuition congruence..|].
  iMod (hi_entry_vtables_own with "[Lvt Hvt]") as "Hvt".
  { rewrite /hi_entry_vtables_ps pts_app. iFrame. }
  iMod (hi_entry_single_own with "[Hsl Hsb]") as "Hs".
  { rewrite /hi_entry_single_ps (pts_app [_] [_]). iFrame. }
  iModIntro. rewrite /hi_main_state. cbn [big_opL hi_exit_streams].
  iFrame "Hvt Hs Htcb Hso Hsoc Hout HM Hio Hstr Hinv Hlock Hse Hsi".
Qed.

End resources.

(** ## Main's contract

    Main takes no arguments and never returns, because it ends in
    `c: exit`. Its precondition is [hi_main_state]. *)
Section spec.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** This is the contract of hi_atexit's `c: main` in world w. *)
Definition hi_main_spec (w : os_world) : fspec Σ :=
  FSpec unit (fun _ => []) (fun _ => hi_main_state w) (fun _ _ => False)%I.

(** Main prints through stdout, which reports errors in `c: errno`, and
    it exits holding a lock in the current thread's name. So main keeps
    its contract whenever errno lives at the image's address and some
    thread is running. *)
Lemma hi_main_has_spec w :
  ow_errno w = Some (mkPtr 70608 (Obj 70608)) -> 0 < ptr_addr (ow_self w) < 2 ^ 64 ->
  HasSpec glibc_os_registry (os_wi w) hge (TAtom "main") (hi_main_spec w).
Proof using Type.
  intros He Hself x. exists hi_main_fn. split; [exact hi_find_main|].
  split; [eexists; exact hi_main_call|]. intros fr Φ Hfr. rewrite hi_main_call in Hfr. injection Hfr as <-.
  iIntros "H _". iApply (hi_main_wp w Φ with "H"); [exact He | lia | |].
  - apply hi_loop_env. exact He.
  - apply hi_exit_lock_env; [exact He | exact Hself].
Qed.

(** When `c: main` cannot return, `c: exit` is never reached, so its
    contract with no allowed status holds for the linked `c: exit`. *)
Lemma hi_exit_never_false w :
  HasSpec glibc_os_registry (os_wi w) hge (TAtom "__GI_exit") (exit_never_spec (fun _ => False%I)).
Proof using Type.
  intros st. eexists. split; [vm_compute; reflexivity|].
  split; [eexists; reflexivity|]. intros fr Φ _. cbn [fs_pre exit_never_spec]. iIntros "[]".
Qed.

End spec.

(** ## The world after startup *)

(** Main's contract needs two facts about the world it runs in. When
    startup ends, the thread object tb names the thread, and `c: errno`
    lives where the image puts `c: __libc_errno`. The descriptors are
    those that the process started with. *)
Lemma hi_final_world_facts w0 tb :
  lookup (TAtom "__libc_errno") hi_globals = Some (ow_errno_cell w0) -> 0 < tb < 2 ^ 64 ->
  ow_errno (start_world w0 (mkPtr tb (Obj tb)) true true) = Some (mkPtr 70608 (Obj 70608)) /\
  0 < ptr_addr (ow_self (start_world w0 (mkPtr tb (Obj tb)) true true)) < 2 ^ 64 /\
  ow_fds (start_world w0 (mkPtr tb (Obj tb)) true true) = ow_fds w0.
Proof.
  intros He Htb. cbn [start_world ow_errno ow_self ow_fds ptr_addr].
  split; [|split; [exact Htb | reflexivity]].
  assert (E : lookup (TAtom "__libc_errno") hi_globals = Some (mkPtr 70608 (Obj 70608)))
    by (vm_compute; reflexivity).
  rewrite E in He. injection He as <-. reflexivity.
Qed.
