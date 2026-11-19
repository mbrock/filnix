(** When Hello finishes, `c: close_stdout` closes standard output, and
    when a write fails it reports the error with glibc's `c: error`.
    Those two functions read and write a few globals that no start list
    holds yet. So do two functions that main calls earlier: setlocale
    counts the changes of the message catalogs, and a wide print takes
    the lock of the character conversions. This module lists those
    globals with what Hello's image holds in each, so that Hello's
    private state can own them from the start.

    Seven of the globals can change and two are constant text. Gnulib
    exits with status 1 when it fails, so the global that holds that
    status starts as 1. Every other changeable global starts as zero.
    The two texts are the message "write error" and the format "%s"
    that close_stdout uses when it reports. Checking the whole image
    would be slow, so the check reads a smaller image that holds only
    these objects. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import WordString LiteralWords ImageObjectPieces ImageErase ImageEraseMem ImagePieces
  HelloImageModule HelloImageLoad.
Import ListNotations.
Open Scope Z_scope.

(** These are the seven writable globals. *)
Definition hello_close_rw_names : list string :=
  ["exit_failure"; "closeout#ignore_EPIPE"; "closeout#file_name"; "error_message_count";
   "error_print_progname"; "__gconv_lock"; "_nl_msg_cat_cntr"]%string.

(** Each writable global fills its own region. Only `c: exit_failure`
    starts with a nonzero byte. The two globals of `c: error` form their
    own list, because every report of an error uses them, not only the
    reports that Hello's private state makes. *)
Definition hello_close_rw_ps : list (piece * pval) :=
  obj_ps (img_ob "exit_failure") [1; 0; 0; 0] ++
  obj_ps (img_ob "closeout#ignore_EPIPE") [0] ++
  obj_ps (img_ob "closeout#file_name") (repeat 0 8%nat) ++
  obj_ps (img_ob "__gconv_lock") (repeat 0 4%nat) ++
  obj_ps (img_ob "_nl_msg_cat_cntr") (repeat 0 4%nat).

(** `c: error` counts its reports in `c: error_message_count`, and it
    calls `c: error_print_progname` instead of printing the program's
    name when that pointer is not null. Hello never sets it. *)
Definition hello_error_objs_ps : list (piece * pval) :=
  obj_ps (img_ob "error_message_count") (repeat 0 4%nat) ++
  obj_ps (img_ob "error_print_progname") (repeat 0 8%nat).

(** These are the text and the format of the message that close_stdout
    reports when it cannot write. *)
Definition hello_write_error_text : list Z := [119; 114; 105; 116; 101; 32; 101; 114; 114; 111; 114].
Definition hello_percent_s_text : list Z := [37; 115].

Definition hello_close_ro_names : list string := ["closeout#str.53"; "closeout#str.55"]%string.

Definition hello_close_ro_ps : list (piece * pval) :=
  lit_ps (img_a "closeout#str.53") (img_gd "closeout#str.53") (lit_words hello_write_error_text) ++
  lit_ps (img_a "closeout#str.55") (img_gd "closeout#str.55") (lit_words hello_percent_s_text).

(** This is the list of close_stdout's own objects. *)
Definition hello_close_objs_ps : list (piece * pval) := hello_close_rw_ps ++ hello_close_ro_ps.

(** The check covers both lists. *)
Definition hello_close_all_ps : list (piece * pval) := hello_close_objs_ps ++ hello_error_objs_ps.

(** ## The check on a smaller copy *)

Definition hello_close_objs_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom (hello_close_rw_names ++ hello_close_ro_names)).

Definition hello_close_objs_skel : module := Eval vm_compute in erase hello_close_objs_keep hello_image_module.
Lemma hello_close_objs_skel_eq : erase hello_close_objs_keep hello_image_module = hello_close_objs_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_close_objs_kept : module := Eval vm_compute in kept_objects hello_close_objs_keep hello_image_module.
Lemma hello_close_objs_kept_incl : incl hello_close_objs_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_close_objs_keep hello_image_module = hello_close_objs_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_close_objs_check :
  match initial_memory hello_close_objs_skel with
  | Some (g, m') => pieces_ok hello_close_objs_keep hello_close_objs_kept g m' hello_close_all_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with these objects as listed, in whatever memory the
    loader builds for it. *)
Lemma hello_close_all_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_close_all_ps.
Proof.
  intros E.
  destruct (image_pieces hello_close_objs_keep hello_close_objs_kept hello_image_module g m hello_close_all_ps
    hello_close_objs_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_close_objs_check as C. rewrite <- hello_close_objs_skel_eq, E' in C. exact (P C).
Qed.

Lemma hello_close_objs_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_close_objs_ps.
Proof. intros E. exact (proj1 (proj1 (all_agree_app _ _ _) (hello_close_all_agree g m E))). Qed.

Lemma hello_error_objs_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_error_objs_ps.
Proof. intros E. exact (proj2 (proj1 (all_agree_app _ _ _) (hello_close_all_agree g m E))). Qed.
