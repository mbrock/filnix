(** When getopt reports a bad option, gettext translates the message
    and glibc's formatter prints it. The translation reads read-only
    constants, which [HelloImageKept](HelloImageKept.v) lists, and five
    writable globals: three read-write locks, the root of the cache of
    translations and the head of the list of bound domains. The
    formatter reads its two dispatch tables, the table of digits and
    three globals that hold the conversions a program registers.
    Gettext also reads the name of
    the message category in the global locale. No other start list holds
    these eleven objects or that name. This module lists them and shows
    what Hello's image holds in each. The five gettext globals are zero,
    so every lock is free, the cache is empty and no domain is bound.
    The three conversion globals are null, the tables hold their bytes,
    and the name is "C".

    To keep the check fast, it runs on a copy of the image that keeps
    only these objects. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import StartImageUnique StartImageCpu HelloImageErase HelloImageEraseMem HelloImagePieces
  HelloImageModule HelloImageLoad HelloStartKept HelloImageKept StartImageEarly.
Import ListNotations.
Open Scope Z_scope.

(** These are the five globals. *)
Definition hello_gettext_rw_names : list string :=
  ["_nl_state_lock"; "__libc_setlocale_lock"; "glibc_dcigettext#tree_lock"; "glibc_dcigettext#root";
   "_nl_domain_bindings"]%string.

(** Each global starts as zero bytes that fill its own region. *)
Definition hello_gettext_rw_ps : list (piece * pval) :=
  obj_ps (img_ob "_nl_state_lock") (repeat 0 56%nat) ++
  obj_ps (img_ob "__libc_setlocale_lock") (repeat 0 56%nat) ++
  obj_ps (img_ob "glibc_dcigettext#tree_lock") (repeat 0 56%nat) ++
  obj_ps (img_ob "glibc_dcigettext#root") (repeat 0 8%nat) ++
  obj_ps (img_ob "_nl_domain_bindings") (repeat 0 8%nat).

(** These are the formatter's two tables. *)
Definition hello_jump_table_bytes : list Z := Eval vm_compute in
  data_bytes hello_image_module "glibc_vfprintf_internal#jump_table".
Definition hello_step0_jumps_bytes : list Z := Eval vm_compute in
  data_bytes hello_image_module "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277".

(** The conversion `%d` reads the characters of the digits from this
    table. *)
Definition hello_lower_digits_bytes : list Z := Eval vm_compute in
  data_bytes hello_image_module "__GI__itoa_lower_digits".

(** These are the formatter's six objects. The tables hold their bytes
    and the three conversion globals hold null. *)
Definition hello_printf_names : list string :=
  ["glibc_vfprintf_internal#jump_table"; "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
   "__GI__itoa_lower_digits";
   "__printf_function_table"; "__printf_modifier_table"; "__printf_va_arg_table"]%string.

Definition hello_printf_ro_ps : list (piece * pval) :=
  obj_ps (img_ob "glibc_vfprintf_internal#jump_table") hello_jump_table_bytes ++
  obj_ps (img_ob "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") hello_step0_jumps_bytes ++
  obj_ps (img_ob "__GI__itoa_lower_digits") hello_lower_digits_bytes ++
  obj_ps (img_ob "__printf_function_table") (repeat 0 8%nat) ++
  obj_ps (img_ob "__printf_modifier_table") (repeat 0 8%nat) ++
  obj_ps (img_ob "__printf_va_arg_table") (repeat 0 8%nat).

(** Gettext also reads the name of the current locale's message
    category. The global locale keeps the thirteen category names from
    offset 128, so the name for LC_MESSAGES, category 5, is the pointer
    at offset 168. It points at the constant "C". The early list owns
    only the first word of the global locale, so this list adds the
    eight bytes of the name. *)
Definition hello_locale_names : list string := ["_nl_global_locale"; "_nl_C_name"]%string.
Definition hello_locale_slot_ps : list (piece * pval) :=
  ptr_ps (img_a "_nl_global_locale") 168 (mkPtr (img_a "_nl_C_name") (Ro (img_a "_nl_C_name"))).

(** This is the whole list of the module. *)
Definition hello_diag_objs_ps : list (piece * pval) :=
  hello_gettext_rw_ps ++ hello_printf_ro_ps ++ hello_locale_slot_ps.

(** ## The check on a smaller copy *)

Definition hello_diag_objs_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom (hello_gettext_rw_names ++ hello_printf_names ++ hello_locale_names)).

Definition hello_diag_objs_skel : module := Eval vm_compute in erase hello_diag_objs_keep hello_image_module.
Lemma hello_diag_objs_skel_eq : erase hello_diag_objs_keep hello_image_module = hello_diag_objs_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_diag_objs_kept : module := Eval vm_compute in kept_objects hello_diag_objs_keep hello_image_module.
Lemma hello_diag_objs_kept_incl : incl hello_diag_objs_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_diag_objs_keep hello_image_module = hello_diag_objs_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_diag_objs_check :
  match initial_memory hello_diag_objs_skel with
  | Some (g, m') => pieces_ok hello_diag_objs_keep hello_diag_objs_kept g m' hello_diag_objs_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with these objects as listed, in whatever memory the
    loader builds for it. *)
Lemma hello_diag_objs_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_diag_objs_ps.
Proof.
  intros E.
  destruct (image_pieces hello_diag_objs_keep hello_diag_objs_kept hello_image_module g m hello_diag_objs_ps
    hello_diag_objs_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_diag_objs_check as C. rewrite <- hello_diag_objs_skel_eq, E' in C. exact (P C).
Qed.

(** No piece occurs twice in the list. *)
Lemma hello_diag_objs_nodup : NoDup hello_diag_objs_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.

(** ## Hello's private start list *)

(** Hello starts with these eleven objects, the category's name and
    gettext's fifteen constants in its private state. *)
Definition hello_getopt_priv_ps : list (piece * pval) := hello_kept_ps ++ hello_diag_objs_ps.

(** The loader's image holds every one of those pieces. *)
Lemma hello_getopt_priv_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_getopt_priv_ps.
Proof.
  intros E. apply all_agree_app. split; [|exact (hello_diag_objs_agree g m E)].
  destruct hello_image_kept as (g' & m' & E' & _ & _ & _ & _ & Ak & _).
  rewrite E in E'. injection E' as <- <-. exact Ak.
Qed.
