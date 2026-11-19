(** When closing standard output fails, Hello asks glibc to print the
    error that the close left in errno. The number selects a pointer
    from a table. Two slots hold null instead of a message. In that
    case, or when the number falls outside the table, glibc formats
    the number itself. This module lists the slots, the messages and
    the literals that both paths read. It checks them against the
    memory that the loader builds for Hello. *)

From Stdlib Require Import String ZArith List.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Pieces Heap.
From Glibc Require Import LiteralWords.
From Glibc Require Import ImageData.
From Glibc Require Import ErrlistDataCode ErrlistFacts WordString
  HelloImageLoad HelloImageModule ImageErase ImageEraseMem ImagePieces
   ImageObjectPieces.
Import ListNotations.
Open Scope Z_scope.

(** Each initializer occupies one slot, including each null pointer.
    The index therefore remains the error number even after a hole. *)
Definition err_slot_names : list (option string) := Eval vm_compute in
  map (fun d => match d with Sym (TAtom s) 0 => Some s | _ => None end)
    (errlist_initializer errlistdata_module "_sys_errlist_internal").

Definition err_messages : list (option (Z * region * list Z)) := Eval vm_compute in
  map (option_map (fun s => (img_obj s, upto_zero (data_bytes errlistdata_module s)))) err_slot_names.

Definition err_table := img_ob "_sys_errlist_internal".
Definition err_length := img_ob "_sys_errlist_internal_len".

(** A slot owns the pointer even when it is null. Only a non-null
    pointer has a target whose lifetime and bytes belong to the list. *)
Definition err_slot_ps (k : nat) (m : option (Z * region * list Z)) : list (piece * pval) :=
  let p := match m with Some (b, _, _) => mkPtr b (Ro b) | None => null end in
  ptr_ps err_table.1 (8 * Z.of_nat k) p ++
  match m with Some (b, r, bs) => lit_ps b r (lit_words bs) | None => [] end.

Definition err_formats : list (string * list Z) :=
  [("glibc__strerror#str.136"%string, [37;115;37;100]);
   ("glibc__strerror#str.137"%string, [85;110;107;110;111;119;110;32;101;114;114;111;114;32]);
   ("glibc_error#str.252"%string, [58;32;37;115])].

Definition hello_errlist_ps : list (piece * pval) :=
  [(PLive err_length.1, VLive err_length.2); (PLive err_table.1, VLive err_table.2)] ++
  cell err_length.1 0 134 ++ List.concat (imap err_slot_ps err_messages) ++
  flat_map (fun '(n, bs) => lit_ps (img_addr n) (img_obj n).2 (lit_words bs)) err_formats.

(** ## Checking the real memory

    To check an error message we need its bytes and the table entry
    that points to them. We can leave out the contents of the other
    globals because the loader still gives each global the same address. *)

Definition err_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom (["_sys_errlist_internal_len"; "_sys_errlist_internal"]%string ++
    omap id err_slot_names ++ map fst err_formats)).

Definition err_skel : module := Eval vm_compute in erase err_keep hello_image_module.
Lemma err_skel_eq : erase err_keep hello_image_module = err_skel.
Proof. vm_compute. reflexivity. Qed.

Definition err_kept : module := Eval vm_compute in kept_objects err_keep hello_image_module.
Lemma err_kept_incl : incl err_kept hello_image_module.
Proof.
  assert (E : kept_objects err_keep hello_image_module = err_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma err_image_check :
  match initial_memory err_skel with
  | Some (g, m) => pieces_ok err_keep err_kept g m hello_errlist_ps
  | None => false end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The loader gives every listed piece its expected value. *)
Lemma hello_errlist_agree g m : initial_memory hello_image_module = Some (g, m) -> all_agree m hello_errlist_ps.
Proof.
  intros Hi. destruct (image_pieces err_keep err_kept _ g m hello_errlist_ps err_kept_incl Hi
    hello_image_names hello_image_zero) as (m' & Hm & _ & H).
  apply H. pose proof err_image_check as C. rewrite <- err_skel_eq, Hm in C. exact C.
Qed.
