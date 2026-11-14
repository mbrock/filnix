(** Registering and running exit callbacks must not invalidate the
    thread's error cell or its identity. This file proves that writes
    to the callback array and exit locks leave both intact. The result
    applies to every state satisfying the OS invariant, not just the
    concrete entry image. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Pieces Heap.
From Glibc Require Import OsWorld AtexitLogic ExitRun HiAtexitBase HiAtexitGe
  HiAtexitCloseIt HiAtexitExitEnv.
From Glibc Require AtexitLogic ExitRun ExitRunTail.
Open Scope Z_scope.
Import ExitRun ExitRunTail AtexitLogic.

(** Updating another object's pieces cannot change errno's liveness
    kind. Physical stores also leave every registered region unchanged,
    so neither errno's region nor the thread cookie is invalidated. *)
Lemma hi_exit_os_ignores w0 b e :
  ow_errno w0 = Some (mkPtr 68176 (Obj 68176)) -> b <> 68176 ->
  wi_ignores (os_wi w0) b e.
Proof.
  intros He Hne m wd h ps a n x c Ha Hn Hids Hw.
  assert (Hlife : forall eb, ow_errno wd = Some (mkPtr eb (Obj eb)) ->
    errno_life_global h eb -> errno_life_global (overwrite ps h) eb).
  { intros eb Heb Hg. pose proof (proj1 Hw) as ->.
    rewrite He in Heb. injection Heb as <-.
    apply errno_life_overwrite; [|exact Hg]. intros reg' Hin.
    assert (Hin' : PLive 68176 ∈ ps.*1).
    { apply list_elem_of_fmap. exists (PLive 68176, VLive reg'). split; [reflexivity|exact Hin]. }
    pose proof (Hids _ Hin') as Hid. cbn in Hid. congruence. }
  split; (split; [exact (proj1 Hw)|]);
    apply (os_inv_step m _ wd h); try exact (proj2 Hw).
  all: try (intros b' Hb; exact Hb).
  all: intros eb reg Heb [Hreg Hlive] Hkind Hg; split; [exact Hreg|].
  all: apply (Hlife eb Heb Hg).
Qed.

(** All handler-loop writes preserve the fixed OS interpretation.
    The two external-call lookups are checked in the actual program. *)
Lemma hi_loop_env w0 :
  ow_errno w0 = Some (mkPtr 68176 (Obj 68176)) -> loop_env w0 hge hi_exit_objs.
Proof.
  intros He. unfold loop_env.
  split; [exact hi_exit_layout|]. split; [exact hi_exit_globals|].
  split.
  - unfold exit_wi.
    split; [apply hi_exit_os_ignores; [exact He|vm_compute; discriminate]|].
    split; apply hi_exit_os_ignores; [exact He|vm_compute; discriminate|exact He|vm_compute; discriminate].
  - split; [apply hi_exit_os_ignores; [exact He|vm_compute; discriminate]|].
    split; [apply hi_exit_os_ignores; [exact He|vm_compute; discriminate]|].
    split; vm_compute; reflexivity.
Qed.

(** The lock and error cell occupy different objects. Updating the
    lock cannot change the error cell or thread cookie. The cookie
    call resolves to the actual external function. *)
Lemma hi_exit_lock_env w0 :
  ow_errno w0 = Some (mkPtr 68176 (Obj 68176)) ->
  0 < ptr_addr (ow_self w0) < 2 ^ 64 ->
  exit_lock_env w0 hge 73728 (mkRegion 73728 73744 GlobalData Live).
Proof.
  intros He Hself. unfold exit_lock_env.
  split; [lia|]. split; [reflexivity|]. split; [cbn; lia|].
  split; [vm_compute; reflexivity|].
  split; [apply hi_exit_os_ignores; [exact He|lia]|].
  split; [exact Hself|]. split; vm_compute; reflexivity.
Qed.
