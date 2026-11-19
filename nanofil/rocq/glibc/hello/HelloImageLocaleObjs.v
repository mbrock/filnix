(** Hello's main calls `c: setlocale (LC_ALL, "")` before anything
    else. In the C locale that call stores the same values that the
    loader put in the global locale, but it still stores them, so the
    proof must own every cell it writes. It also reads the names of the
    categories, which other calls read later. Startup never touches
    these cells, so no start list holds them. This module lists them
    with what Hello's image holds in each, so that Hello's private
    state can own them from the start.

    The global locale `c: _nl_global_locale` keeps a pointer to the
    data of each category, three pointers into the character tables,
    and a pointer to the name of each category. Startup owns its first
    word, and getopt's objects own the name of the message category.
    This list holds the other category pointers, the three table
    pointers and the other names. It also holds the six old globals
    `c: __ctype_b` and its kin, which point into the same tables.
    Checking the whole image would be slow, so the check reads a
    smaller image that holds only these objects. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import WordString ImageErase ImageEraseMem ImagePieces
  HelloImageModule HelloImageLoad ImageObjectPieces.
Import ListNotations.
Open Scope Z_scope.

(** This function gives the pointer k bytes into the read-only object n. *)
Definition ro_at (n : string) (k : Z) : ptr := mkPtr (img_addr n + k) (Ro (img_addr n)).

(** This list pairs each category whose data pointer the module holds
    with its index. Startup owns index 0, the character type, and index
    6 is LC_ALL, which has no data. *)
Definition hello_locale_cats : list (Z * string) :=
  [(1, "_nl_C_LC_NUMERIC"); (2, "_nl_C_LC_TIME"); (3, "_nl_C_LC_COLLATE"); (4, "_nl_C_LC_MONETARY");
   (5, "_nl_C_LC_MESSAGES"); (7, "_nl_C_LC_PAPER"); (8, "_nl_C_LC_NAME"); (9, "_nl_C_LC_ADDRESS");
   (10, "_nl_C_LC_TELEPHONE"); (11, "_nl_C_LC_MEASUREMENT"); (12, "_nl_C_LC_IDENTIFICATION")]%string.

(** The names of the categories start at offset 128. The name of the
    message category, index 5, belongs to getopt's objects. *)
Definition hello_locale_name_idx : list Z := [0; 1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12].

(** These are the cells of the global locale that this list holds. *)
Definition hello_global_locale_ps : list (piece * pval) :=
  let gl := img_addr "_nl_global_locale" in
  List.concat (map (fun c => ptr_ps gl (8 * c.1) (ro_at c.2 0)) hello_locale_cats) ++
  ptr_ps gl 104 (ro_at "_nl_C_LC_CTYPE_class" 256) ++
  ptr_ps gl 112 (ro_at "_nl_C_LC_CTYPE_tolower" 512) ++
  ptr_ps gl 120 (ro_at "_nl_C_LC_CTYPE_toupper" 512) ++
  List.concat (map (fun i => ptr_ps gl (128 + 8 * i) (ro_at "_nl_C_name" 0)) hello_locale_name_idx).

(** Each old table global is one pointer with its own life. *)
Definition hello_ctype_globals : list (string * string * Z) :=
  [("__ctype_b", "_nl_C_LC_CTYPE_class", 256); ("__ctype_toupper", "_nl_C_LC_CTYPE_toupper", 512);
   ("__ctype_tolower", "_nl_C_LC_CTYPE_tolower", 512); ("__ctype32_b", "_nl_C_LC_CTYPE_class32", 0);
   ("__ctype32_toupper", "_nl_C_LC_CTYPE_toupper", 512); ("__ctype32_tolower", "_nl_C_LC_CTYPE_tolower", 512)]%string.

Definition hello_ctype_globals_ps : list (piece * pval) :=
  List.concat (map (fun g => (PLive (img_obj g.1.1).1, VLive (img_obj g.1.1).2) ::
    ptr_ps (img_addr g.1.1) 0 (ro_at g.1.2 g.2)) hello_ctype_globals).

(** This is the whole list of the module. *)
Definition hello_locale_objs_ps : list (piece * pval) := hello_global_locale_ps ++ hello_ctype_globals_ps.

(** ## The check on a smaller copy *)

(** The check keeps the objects of the list and every object a pointer
    of the list names. *)
Definition hello_locale_objs_names : list string :=
  ["_nl_global_locale"; "_nl_C_LC_CTYPE_class"; "_nl_C_LC_CTYPE_tolower"; "_nl_C_LC_CTYPE_toupper";
   "_nl_C_LC_CTYPE_class32"; "_nl_C_name"]%string ++ map snd hello_locale_cats ++ map (fun g => g.1.1) hello_ctype_globals.

Definition hello_locale_objs_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom hello_locale_objs_names).

Definition hello_locale_objs_skel : module := Eval vm_compute in erase hello_locale_objs_keep hello_image_module.
Lemma hello_locale_objs_skel_eq : erase hello_locale_objs_keep hello_image_module = hello_locale_objs_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_locale_objs_kept : module := Eval vm_compute in kept_objects hello_locale_objs_keep hello_image_module.
Lemma hello_locale_objs_kept_incl : incl hello_locale_objs_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_locale_objs_keep hello_image_module = hello_locale_objs_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_locale_objs_check :
  match initial_memory hello_locale_objs_skel with
  | Some (g, m') => pieces_ok hello_locale_objs_keep hello_locale_objs_kept g m' hello_locale_objs_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The list in the real memory *)

(** Hello starts with these cells as listed, in whatever memory the
    loader builds for it. *)
Lemma hello_locale_objs_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_locale_objs_ps.
Proof.
  intros E.
  destruct (image_pieces hello_locale_objs_keep hello_locale_objs_kept hello_image_module g m hello_locale_objs_ps
    hello_locale_objs_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_locale_objs_check as C. rewrite <- hello_locale_objs_skel_eq, E' in C. exact (P C).
Qed.
