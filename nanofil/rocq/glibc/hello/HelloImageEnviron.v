(** Glibc's `c: getenv` reads two globals: `c: __environ`, the pointer to
    the environment array, and `c: __environ_counter`, which it reads
    before it scans the array. Startup's constructor `c: _init_first`
    writes `c: __environ`, and the start lists of Hello already hold that
    global. No start list holds the counter, so this module adds it and
    shows that Hello's image holds it as eight zero bytes.

    The check runs on a copy of the image that keeps only the counter,
    as [HelloImageLsm](HelloImageLsm.v) does for the startup body's
    globals. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import StartImageUnique StartImageCpu HelloImageErase HelloImageEraseMem HelloImagePieces
  HelloImageModule HelloImageLoad.
Import ListNotations.
Open Scope Z_scope.

(** The counter starts as eight zero bytes in its own region. *)
Definition hello_environ_counter_ps : list (piece * pval) :=
  obj_ps (img_a "__environ_counter", img_gd "__environ_counter") (repeat 0 8%nat).

(** ## The check on a smaller copy *)

Definition hello_environ_keep (n : name) : bool := name_eqb n (TAtom "__environ_counter").

Definition hello_environ_skel : module := Eval vm_compute in erase hello_environ_keep hello_image_module.
Lemma hello_environ_skel_eq : erase hello_environ_keep hello_image_module = hello_environ_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_environ_kept : module := Eval vm_compute in kept_objects hello_environ_keep hello_image_module.
Lemma hello_environ_kept_incl : incl hello_environ_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_environ_keep hello_image_module = hello_environ_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_environ_check :
  match initial_memory hello_environ_skel with
  | Some (g, m') => pieces_ok hello_environ_keep hello_environ_kept g m' hello_environ_counter_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with the counter at zero, in whatever memory the loader
    builds for it. *)
Lemma hello_environ_counter_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_environ_counter_ps.
Proof.
  intros E.
  destruct (image_pieces hello_environ_keep hello_environ_kept hello_image_module g m hello_environ_counter_ps
    hello_environ_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_environ_check as C. rewrite <- hello_environ_skel_eq, E' in C. exact (P C).
Qed.

(** No piece occurs twice in the list. *)
Lemma hello_environ_counter_nodup : NoDup hello_environ_counter_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.
