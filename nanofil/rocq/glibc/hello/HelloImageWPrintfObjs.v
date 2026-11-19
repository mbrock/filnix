(** Glibc's wide formatter finds the handler for each character of a
    format through constant jump tables. Hello's greeting uses the
    format `%ls` followed by a newline, so the formatter reads one entry
    of each of three tables: the class of `l` and of `s` in the
    character table, and the handler in each of two rounds of the
    dispatch. These tables are constants of Hello's image. This module
    lists the bytes that the formatter reads, and checks them on a
    smaller image that holds only these objects. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap StringLogic.
From Glibc Require Import WordString ImageErase ImageEraseMem ImagePieces
  HelloImageModule HelloImageLoad HelloImageMbsObjs.
Import ListNotations.
Open Scope Z_scope.

(** To handle `%ls`, the formatter reads one byte for `l` and one for
    `s` in its character table, and then one four-byte entry in each of
    two dispatch tables. This list holds those bytes and the lives of
    the three tables. *)
Definition hello_wprintf_tables_ps : list (piece * pval) :=
  mbs_life "glibc_vfwprintf_internal#jump_table" ::
  byte_ps (img_addr "glibc_vfwprintf_internal#jump_table") 76 [11] ++
  byte_ps (img_addr "glibc_vfwprintf_internal#jump_table") 83 [21] ++
  mbs_life "glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278" ::
  byte_ps (img_addr "glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278") 44 [11; 0; 0; 0] ++
  mbs_life "glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282" ::
  byte_ps (img_addr "glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282") 84 [21; 0; 0; 0].

(** ## The check on a smaller copy *)

Definition hello_wprintf_names : list string :=
  ["glibc_vfwprintf_internal#jump_table"; "glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
   "glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282"]%string.

Definition hello_wprintf_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom hello_wprintf_names).

Definition hello_wprintf_skel : module := Eval vm_compute in erase hello_wprintf_keep hello_image_module.
Lemma hello_wprintf_skel_eq : erase hello_wprintf_keep hello_image_module = hello_wprintf_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_wprintf_kept : module := Eval vm_compute in kept_objects hello_wprintf_keep hello_image_module.
Lemma hello_wprintf_kept_incl : incl hello_wprintf_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_wprintf_keep hello_image_module = hello_wprintf_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_wprintf_check :
  match initial_memory hello_wprintf_skel with
  | Some (g, m') => pieces_ok hello_wprintf_keep hello_wprintf_kept g m' hello_wprintf_tables_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with these bytes as listed, in whatever memory the
    loader builds for it. *)
Lemma hello_wprintf_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_wprintf_tables_ps.
Proof.
  intros E.
  destruct (image_pieces hello_wprintf_keep hello_wprintf_kept hello_image_module g m hello_wprintf_tables_ps
    hello_wprintf_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_wprintf_check as C. rewrite <- hello_wprintf_skel_eq, E' in C. exact (P C).
Qed.
