(** Overflow rewinds the narrow buffer before it starts writing wide
    characters. Its narrow write end is the physical end, including on
    a line-buffered stream. This file checks the resulting narrow
    fields against the wide stream invariant. *)

From Stdlib Require Import String ZArith List Lia.
From iris.proofmode Require Import proofmode.
From Nanofil Require Import Term Syntax Values Memory Runtime.
From Glibc Require Import FileInv LibioWIdle LibioLogic LibioOverflowBase.
Import ListNotations FileInv.
Open Scope Z_scope.

Definition wo_state st fl f2 b stop := mkFstate (Z.lor fl 2048)
  [b;b;b;b;b;stop;b;stop;fs_ptr st 8;fs_ptr st 9;fs_ptr st 10;fs_ptr st 11]
  (fs_fileno st) f2 (fs_old_offset st) (fs_column st) (fs_lock st) (fs_offset st) (fs_codecvt st) (fs_wide st)
  (fs_freeres_list st) (fs_freeres_buf st) (fs_mode st) (fs_total st) (fs_vtable st).

(** By the time overflow switches to writing, the narrow buffer has
    storage. Its owner bit distinguishes the short buffer from a heap
    allocation, which close must free. *)
Definition wo_storage fb nb fl b stop := match nb with
  | NbShort => b = mkPtr (fb+131) (Obj fb) /\ stop = mkPtr (fb+132) (Obj fb) /\ has fl io_user_buf = true
  | NbHeap bb sz => b = mkPtr bb (Obj bb) /\ stop = mkPtr (bb+sz) (Obj bb) /\ 0 < sz /\ has fl io_user_buf = false
  | _ => False end.

(** Installing a buffer can change the user-buffer and line-buffered
    flags. The switch also sets the putting flag. All of the other
    flag tests in the idle invariant retain their values. *)
Lemma wo_state_ok ge vb fp fb fr st nb wd w tw tm nb' w' fl f2 b stop :
  wide_file_ok ge vb fp 1 fb fr st nb wd w tw tm -> wo_storage fb nb' fl b stop ->
  0 <= fl < 2^32 -> (forall m, Z.land 513 m = 0 -> Z.land fl m = Z.land (fs_flags st) m) ->
  (forall m, (m = 2 \/ m = 32 \/ m = io_need_lock) -> Z.land f2 m = Z.land (fs_flags2 st) m) ->
  wbuf_user_ok w' f2 -> wide_file_ok ge vb fp 1 fb fr (wo_state st fl f2 b stop) nb' wd w' tw tm.
Proof.
  intros P Storage Range Bits Bits2 User.
  destruct P as (Fp & Fa & Fb & Fe & Fr & Flags & Idle & Mode & Vt & _ & _ & _ & Wd & Cv & Tw & Tm & _).
  destruct Flags as (_ & Magic & File & Backup & Lock & Need).
  destruct Idle as (_ & Fd & _ & Save & Back & Mark & _ & _ & _ & _ & Nw & App & Linked & F2 & F32 & Col & Lk).
  specialize (Nw ltac:(lia)).
  assert (Masks : forall m, Z.land 2048 m = 0 -> Z.land 513 m = 0 ->
    Z.land (Z.lor fl 2048) m = Z.land (fs_flags st) m) by (intros; rewrite land_lor_const; auto).
  assert (Owner : has (Z.lor fl 2048) io_user_buf = has fl io_user_buf) by (unfold has; rewrite land_lor_const //).
  assert (No : has (Z.lor fl 2048) io_no_writes = false) by (unfold has in *; rewrite Masks; try reflexivity; exact Nw).
  unfold wide_file_ok, wflags_ok, widle_ok, with_mode0, wshort_ok, wo_state, fs_ptr, has in *.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_mode fs_column fs_lock fs_vtable fs_wide fs_codecvt nth] in *.
  split_and!; try solve [assumption|reflexivity|lia|apply lor_lt32; lia|rewrite Masks; try reflexivity; assumption|
    rewrite Bits2; auto|intros; assumption|congruence].
  all: destruct nb' as [| |bb sz|]; cbn [wo_storage] in Storage; try contradiction;
    destruct Storage as (-> & -> & Rest); cbn [buf_ptrs_ok nth take ptr_addr ptr_cap] in *;
    repeat constructor; try assumption; try congruence; try lia; try (rewrite Owner; tauto).
  all: cbn [ptr_addr]; lia.
Qed.
