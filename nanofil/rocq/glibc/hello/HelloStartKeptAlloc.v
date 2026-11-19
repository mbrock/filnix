(** When startup reaches GNU Hello's `c: main`, the allocator's idle
    cache and the exit state still hold what the linker put there,
    because no call of startup writes them. Main's proof needs both: the
    allocator's largest cached size and its empty cache, and an empty
    handler array with free locks. This module lists those pieces of the
    initial memory, shows that Hello's image holds them, and turns them
    into the assertions that main's proof uses. The kept frame that
    startup hands to main includes both lists.

    The life of `c: mp_` is not here, because early init borrows it and
    so it is in the early list of [HelloImageEarly](HelloImageEarly.v).
    Every address is read from the loader's symbols, so a relink of
    Hello changes no line here. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv HelloGlibcDebts StartImageUnique ImageErase ImageEraseMem
  ImagePieces HelloImageModule HelloImageLoad HelloImageCtors HelloImageLayout.
From Glibc Require AllocLogic AtexitLogic ExitRun.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** ## The pieces *)

(** The allocator's largest cached size is 1041. The thread's cache
    pointer names the read-only dummy cache, whose 64 bins are null. *)
Definition hello_alloc_kept_ps : list (piece * pval) :=
  List.concat [cell (img_a "glibc_malloc#mp_") 120 1041;
    [(PLive (img_a "tcache"), VLive (img_gd "tcache"))];
    hello_pointer_ps (img_a "tcache") 0
      (mkPtr (img_a "glibc_malloc#__tcache_dummy") (Ro (img_a "glibc_malloc#__tcache_dummy")));
    [(PLive (img_a "glibc_malloc#__tcache_dummy"), VLive (img_gd "glibc_malloc#__tcache_dummy"))];
    List.concat (map (fun i => hello_pointer_ps (img_a "glibc_malloc#__tcache_dummy") (152 + 8 * i) null)
      (seqZ 0 64))].

(** Each unused handler slot starts with four zero words, and the last
    three have empty capabilities. *)
Definition hello_exit_slot_ps (i : Z) : list (piece * pval) :=
  List.concat [cell (img_a "glibc_cxa_atexit#initial") (16 + 32 * i) 0;
    hello_pointer_ps (img_a "glibc_cxa_atexit#initial") (16 + 32 * i + 8) null;
    hello_pointer_ps (img_a "glibc_cxa_atexit#initial") (16 + 32 * i + 16) null;
    hello_pointer_ps (img_a "glibc_cxa_atexit#initial") (16 + 32 * i + 24) null].

(** The handler array is empty, its lock is free, no exit has started,
    no handler was ever registered, and the recursive exit lock is free. *)
Definition hello_exit_kept_ps : list (piece * pval) :=
  List.concat [
    [(PLive (img_a "__exit_funcs_lock"), VLive (img_gd "__exit_funcs_lock"))];
    byte_ps (img_a "__exit_funcs_lock") 0 [0; 0; 0; 0];
    [(PLive (img_a "__exit_funcs_done"), VLive (img_gd "__exit_funcs_done"))];
    [(PByte (img_a "__exit_funcs_done") 0, VByte 0)];
    [(PLive (img_a "__new_exitfn_called"), VLive (img_gd "__new_exitfn_called"))];
    cell (img_a "__new_exitfn_called") 0 0;
    [(PLive (img_a "__exit_funcs"), VLive (img_gd "__exit_funcs"))];
    hello_pointer_ps (img_a "__exit_funcs") 0
      (mkPtr (img_a "glibc_cxa_atexit#initial") (Obj (img_a "glibc_cxa_atexit#initial")));
    [(PLive (img_a "glibc_cxa_atexit#initial"), VLive (img_gd "glibc_cxa_atexit#initial"))];
    hello_pointer_ps (img_a "glibc_cxa_atexit#initial") 0 null; cell (img_a "glibc_cxa_atexit#initial") 8 0;
    List.concat (map hello_exit_slot_ps (seqZ 0 32));
    [(PLive (img_a "glibc_exit#__exit_lock"), VLive (img_gd "glibc_exit#__exit_lock"))];
    byte_ps (img_a "glibc_exit#__exit_lock") 0 [0; 0; 0; 0]; byte_ps (img_a "glibc_exit#__exit_lock") 4 [0; 0; 0; 0];
    hello_pointer_ps (img_a "glibc_exit#__exit_lock") 8 null].

(** ## The check on a smaller copy

    The lists are checked in a copy of the image that keeps only these
    nine objects and blanks every other one. *)

Definition hello_kept_alloc_names : list string :=
  ["glibc_malloc#mp_"; "tcache"; "glibc_malloc#__tcache_dummy"; "__exit_funcs_lock"; "__exit_funcs_done";
   "__new_exitfn_called"; "__exit_funcs"; "glibc_cxa_atexit#initial"; "glibc_exit#__exit_lock"]%string.

Definition hello_kept_alloc_keep (n : name) : bool := existsb (name_eqb n) (map TAtom hello_kept_alloc_names).

Definition hello_kept_alloc_skel : module := Eval vm_compute in erase hello_kept_alloc_keep hello_image_module.
Lemma hello_kept_alloc_skel_eq : erase hello_kept_alloc_keep hello_image_module = hello_kept_alloc_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_kept_alloc_kept : module := Eval vm_compute in kept_objects hello_kept_alloc_keep hello_image_module.
Lemma hello_kept_alloc_kept_incl : incl hello_kept_alloc_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_kept_alloc_keep hello_image_module = hello_kept_alloc_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_kept_alloc_check :
  match initial_memory hello_kept_alloc_skel with
  | Some (g, m') => pieces_ok hello_kept_alloc_keep hello_kept_alloc_kept g m' (hello_alloc_kept_ps ++ hello_exit_kept_ps)
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The lists in the real memory *)

(** Hello starts with both lists, in whatever memory the loader builds
    for it. *)
Lemma hello_alloc_exit_kept_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_alloc_kept_ps /\ all_agree m hello_exit_kept_ps.
Proof.
  intros E.
  destruct (image_pieces hello_kept_alloc_keep hello_kept_alloc_kept hello_image_module g m
    (hello_alloc_kept_ps ++ hello_exit_kept_ps) hello_kept_alloc_kept_incl E hello_image_names hello_image_zero)
    as (m' & E' & _ & P).
  pose proof hello_kept_alloc_check as C. rewrite <- hello_kept_alloc_skel_eq, E' in C.
  apply all_agree_app. exact (P C).
Qed.

Lemma hello_alloc_kept_agree g m : initial_memory hello_image_module = Some (g, m) -> all_agree m hello_alloc_kept_ps.
Proof. intros E. exact (proj1 (hello_alloc_exit_kept_agree g m E)). Qed.

Lemma hello_exit_kept_agree g m : initial_memory hello_image_module = Some (g, m) -> all_agree m hello_exit_kept_ps.
Proof. intros E. exact (proj2 (hello_alloc_exit_kept_agree g m E)). Qed.

(** No piece appears twice in the two lists together. *)
Lemma hello_alloc_exit_kept_nodup : NoDup (hello_alloc_kept_ps ++ hello_exit_kept_ps).*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.

(** ## What the pieces give main's proof

    The objects are the ones of [hello_image_objs], the record that
    Hello's proof is stated over. *)

Section own.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

Local Notation o := hello_image_objs.

Local Lemma kept_pts_concat pss : pts (List.concat pss) ⊣⊢ [∗ list] ps ∈ pss, pts ps.
Proof using Type. induction pss as [|ps pss IH]; cbn [List.concat]; rewrite ?pts_app ?IH; done. Qed.

(** Given the life of `c: mp_`, the allocator pieces give the idle
    cache whole. *)
Lemma hello_alloc_kept_own :
  live (ho_mp o) (ho_mpreg o) -∗ pts hello_alloc_kept_ps -∗
  AllocLogic.tcache_idle (DfracOwn 1) (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o).
Proof using Type.
  rewrite /hello_alloc_kept_ps kept_pts_concat. cbn [big_opL].
  iIntros "Hmp (Hmax & Htc & Htcp & Hdm & Hbins & _)".
  rewrite /AllocLogic.tcache_idle.
  iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iFrame "Hmp Hmax Htc Htcp Hdm".
  rewrite kept_pts_concat big_sepL_fmap /pcellq /null. done.
Qed.

Lemma hello_exit_slots_own ns : pts (List.concat (map hello_exit_slot_ps ns)) ⊢
  [∗ list] i ∈ ns, AtexitLogic.spare (img_a "glibc_cxa_atexit#initial") (16 + 32 * i).
Proof using Type.
  rewrite kept_pts_concat big_sepL_fmap. iIntros "Hslots".
  iApply (big_sepL_mono with "Hslots"). iIntros (k i Hin) "Hslot".
  rewrite /hello_exit_slot_ps kept_pts_concat. cbn [big_opL].
  iDestruct "Hslot" as "(Hv & Hx & Hy & Hz & _)". iExists 0, null, null, null.
  rewrite /AtexitLogic.slot. iFrame.
Qed.

(** The exit pieces give an empty handler array that was never used,
    and a free recursive exit lock. *)
Lemma hello_exit_kept_own : pts hello_exit_kept_ps ⊢
  AtexitLogic.exit_funcs_inv (ho_x o) [] 0 ∗ ExitRun.exit_lock_free (ho_el o) (ho_elr o).
Proof using Type.
  rewrite /hello_exit_kept_ps kept_pts_concat. cbn [big_opL].
  iIntros "(Hll & Hlb & Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hil & Hnext & Hidx & Hslots &
    Hel & He0 & He4 & He8 & _)".
  iDestruct (hello_exit_slots_own with "Hslots") as "Hspares".
  iSplitR "Hel He0 He4 He8"; last first.
  { rewrite /ExitRun.exit_lock_free. iFrame. }
  rewrite /AtexitLogic.exit_funcs_inv /AtexitLogic.exit_block.
  cbn [AtexitLogic.xo_lock AtexitLogic.xo_lock_reg AtexitLogic.xo_done AtexitLogic.xo_done_reg AtexitLogic.xo_called AtexitLogic.xo_called_reg AtexitLogic.xo_funcs AtexitLogic.xo_funcs_reg
    AtexitLogic.xo_init AtexitLogic.xo_init_reg ho_x hello_image_objs List.length].
  iSplitR; [iPureIntro; split; [lia|vm_compute; intuition congruence]|].
  iFrame "Hll Hlb Hdl Hdb Hcl Hcc Hfl Hfc Hil Hnext Hidx Hspares".
  done.
Qed.

End own.
