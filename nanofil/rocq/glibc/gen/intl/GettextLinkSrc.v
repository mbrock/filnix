(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to its function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Glibc Require Import Unit_intl_dcgettext_os Unit_intl_dcigettext_os Unit_locale_localename_os Unit_misc_tsearch_os Unit_nptl_pthread_rwlock_rdlock_os Unit_nptl_pthread_rwlock_unlock_os Unit_string_memcpy_os Unit_string_mempcpy_os Unit_string_stpcpy_os.

From Glibc Require Import GettextLinkSrcFiles GettextLinkSrc01 GettextLinkSrc02 GettextLinkSrc03 GettextLinkSrc04 GettextLinkSrc05.
Module GettextLinkSrc.
Include GettextLinkSrcFiles.
Include GettextLinkSrc01.
Include GettextLinkSrc02.
Include GettextLinkSrc03.
Include GettextLinkSrc04.
Include GettextLinkSrc05.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  [("__GI___dcgettext", map b_label (fn_blocks Unit_intl_dcgettext_os.fn___GI___dcgettext)); ("glibc_dcigettext#transcmp", map b_label (fn_blocks Unit_intl_dcigettext_os.fn_glibc_dcigettext'23transcmp)); ("glibc_dcigettext#plural_eval_recurse", map b_label (fn_blocks Unit_intl_dcigettext_os.fn_glibc_dcigettext'23plural_eval_recurse)); ("__dcigettext", map b_label (fn_blocks Unit_intl_dcigettext_os.fn___dcigettext)); ("_nl_find_msg", map b_label (fn_blocks Unit_intl_dcigettext_os.fn__nl_find_msg)); ("glibc_dcigettext#get_output_charset", map b_label (fn_blocks Unit_intl_dcigettext_os.fn_glibc_dcigettext'23get_output_charset)); ("glibc_dcigettext#__bswap_32", map b_label (fn_blocks Unit_intl_dcigettext_os.fn_glibc_dcigettext'23__bswap_32)); ("__GI___stpcpy", map b_label (fn_blocks Unit_string_stpcpy_os.fn___GI___stpcpy)); ("__GI___mempcpy", map b_label (fn_blocks Unit_string_mempcpy_os.fn___GI___mempcpy)); ("__GI_memcpy", map b_label (fn_blocks Unit_string_memcpy_os.fn___GI_memcpy)); ("glibc_tsearch#maybe_split_for_insert", map b_label (fn_blocks Unit_misc_tsearch_os.fn_glibc_tsearch'23maybe_split_for_insert)); ("__GI___tsearch", map b_label (fn_blocks Unit_misc_tsearch_os.fn___GI___tsearch)); ("__GI___tfind", map b_label (fn_blocks Unit_misc_tsearch_os.fn___GI___tfind)); ("__current_locale_name", map b_label (fn_blocks Unit_locale_localename_os.fn___current_locale_name)); ("___pthread_rwlock_rdlock", map b_label (fn_blocks Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock)); ("___pthread_rwlock_unlock", map b_label (fn_blocks Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock))].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__GI___dcgettext", app (map fst fn___GI___dcgettext.block_src) (app (map fst fn___GI___dcgettext.live_in) (app (map fst fn___GI___dcgettext.live_out) (app (map fst fn___GI___dcgettext.footprint) (fn___GI___dcgettext.loop_heads))))); ("glibc_dcigettext#transcmp", app (map fst fn_glibc_dcigettext_transcmp.block_src) (app (map fst fn_glibc_dcigettext_transcmp.live_in) (app (map fst fn_glibc_dcigettext_transcmp.live_out) (app (map fst fn_glibc_dcigettext_transcmp.footprint) (fn_glibc_dcigettext_transcmp.loop_heads))))); ("glibc_dcigettext#plural_eval_recurse", app (map fst fn_glibc_dcigettext_plural_eval_recurse.block_src) (app (map fst fn_glibc_dcigettext_plural_eval_recurse.live_in) (app (map fst fn_glibc_dcigettext_plural_eval_recurse.live_out) (app (map fst fn_glibc_dcigettext_plural_eval_recurse.footprint) (fn_glibc_dcigettext_plural_eval_recurse.loop_heads))))); ("__dcigettext", app (map fst fn___dcigettext.block_src) (app (map fst fn___dcigettext.live_in) (app (map fst fn___dcigettext.live_out) (app (map fst fn___dcigettext.footprint) (fn___dcigettext.loop_heads))))); ("_nl_find_msg", app (map fst fn__nl_find_msg.block_src) (app (map fst fn__nl_find_msg.live_in) (app (map fst fn__nl_find_msg.live_out) (app (map fst fn__nl_find_msg.footprint) (fn__nl_find_msg.loop_heads))))); ("glibc_dcigettext#get_output_charset", app (map fst fn_glibc_dcigettext_get_output_charset.block_src) (app (map fst fn_glibc_dcigettext_get_output_charset.live_in) (app (map fst fn_glibc_dcigettext_get_output_charset.live_out) (app (map fst fn_glibc_dcigettext_get_output_charset.footprint) (fn_glibc_dcigettext_get_output_charset.loop_heads))))); ("glibc_dcigettext#__bswap_32", app (map fst fn_glibc_dcigettext___bswap_32.block_src) (app (map fst fn_glibc_dcigettext___bswap_32.live_in) (app (map fst fn_glibc_dcigettext___bswap_32.live_out) (app (map fst fn_glibc_dcigettext___bswap_32.footprint) (fn_glibc_dcigettext___bswap_32.loop_heads))))); ("__GI___stpcpy", app (map fst fn___GI___stpcpy.block_src) (app (map fst fn___GI___stpcpy.live_in) (app (map fst fn___GI___stpcpy.live_out) (app (map fst fn___GI___stpcpy.footprint) (fn___GI___stpcpy.loop_heads))))); ("__GI___mempcpy", app (map fst fn___GI___mempcpy.block_src) (app (map fst fn___GI___mempcpy.live_in) (app (map fst fn___GI___mempcpy.live_out) (app (map fst fn___GI___mempcpy.footprint) (fn___GI___mempcpy.loop_heads))))); ("__GI_memcpy", app (map fst fn___GI_memcpy.block_src) (app (map fst fn___GI_memcpy.live_in) (app (map fst fn___GI_memcpy.live_out) (app (map fst fn___GI_memcpy.footprint) (fn___GI_memcpy.loop_heads))))); ("glibc_tsearch#maybe_split_for_insert", app (map fst fn_glibc_tsearch_maybe_split_for_insert.block_src) (app (map fst fn_glibc_tsearch_maybe_split_for_insert.live_in) (app (map fst fn_glibc_tsearch_maybe_split_for_insert.live_out) (app (map fst fn_glibc_tsearch_maybe_split_for_insert.footprint) (fn_glibc_tsearch_maybe_split_for_insert.loop_heads))))); ("__GI___tsearch", app (map fst fn___GI___tsearch.block_src) (app (map fst fn___GI___tsearch.live_in) (app (map fst fn___GI___tsearch.live_out) (app (map fst fn___GI___tsearch.footprint) (fn___GI___tsearch.loop_heads))))); ("__GI___tfind", app (map fst fn___GI___tfind.block_src) (app (map fst fn___GI___tfind.live_in) (app (map fst fn___GI___tfind.live_out) (app (map fst fn___GI___tfind.footprint) (fn___GI___tfind.loop_heads))))); ("__current_locale_name", app (map fst fn___current_locale_name.block_src) (app (map fst fn___current_locale_name.live_in) (app (map fst fn___current_locale_name.live_out) (app (map fst fn___current_locale_name.footprint) (fn___current_locale_name.loop_heads))))); ("___pthread_rwlock_rdlock", app (map fst fn____pthread_rwlock_rdlock.block_src) (app (map fst fn____pthread_rwlock_rdlock.live_in) (app (map fst fn____pthread_rwlock_rdlock.live_out) (app (map fst fn____pthread_rwlock_rdlock.footprint) (fn____pthread_rwlock_rdlock.loop_heads))))); ("___pthread_rwlock_unlock", app (map fst fn____pthread_rwlock_unlock.block_src) (app (map fst fn____pthread_rwlock_unlock.live_in) (app (map fst fn____pthread_rwlock_unlock.live_out) (app (map fst fn____pthread_rwlock_unlock.footprint) (fn____pthread_rwlock_unlock.loop_heads)))))].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.

End GettextLinkSrc.
