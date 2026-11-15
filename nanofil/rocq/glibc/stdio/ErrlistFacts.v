(** Error number 2 means "No such file or directory" in glibc's error
    table. This file checks the message bytes and the libc translation
    domain against the generated data. These checks do not grant permission
    to read that data in a running program. *)
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values.
From Glibc Require Import ErrlistDataCode StrerrorCode.
Import ListNotations.
Open Scope Z_scope.

Definition enoent_chars : list Z :=
  [78;111;32;115;117;99;104;32;102;105;108;101;32;111;114;32;100;105;114;101;99;116;111;114;121].

(** This projection keeps the initializer of a named data object. *)
Definition errlist_initializer (md : module) (n : string) : list data_item :=
  match List.find (fun i => match i with IData s _ _ _ => name_eqb s (TAtom n) | _ => false end) md with
  | Some (IData _ _ _ xs) => xs | _ => [] end.

Example enoent_table_entry :
  nth_error (errlist_initializer errlistdata_module "_sys_errlist_internal") 2 =
    Some (Sym (TAtom "glibc_errlist_data_gen#str.249") 0).
Proof. vm_compute. reflexivity. Qed.

Example enoent_text_bytes :
  errlist_initializer errlistdata_module "glibc_errlist_data_gen#str.249" =
    map (Item Wb) (enoent_chars ++ [0]).
Proof. vm_compute. reflexivity. Qed.

Example errlist_length :
  errlist_initializer errlistdata_module "_sys_errlist_internal_len" = [Item Wl 134] /\
  items_size (errlist_initializer errlistdata_module "_sys_errlist_internal") = 134 * 8.
Proof. vm_compute. split; reflexivity. Qed.

Example errlist_holes :
  map (fun i => nth_error (errlist_initializer errlistdata_module "_sys_errlist_internal") i) [41;58]%nat =
    [Some (Zero 8); Some (Zero 8)].
Proof. vm_compute. reflexivity. Qed.

Example strerror_domain_bytes :
  errlist_initializer strerror_module "__GI__libc_intl_domainname" = [Str [108;105;98;99]; Zero 1].
Proof. vm_compute. reflexivity. Qed.
