(** When getopt reports a bad option, glibc translates the message and
    prints it to stderr. [HelloGetoptDiagLock](HelloGetoptDiagLock.v)
    proves this from the real code, given facts about the linked
    program: where gettext's globals and locks lie, which code its calls
    reach, and how large its objects are. This module proves those facts
    for Hello's image by computation. The caller still supplies two
    parts that do not depend on the image: the cells of the current
    locale, and what the formatter returns after a print. *)

From Glibc Require Import Unit_stdioZ2dcommon_fxprintf_os Unit_string_strchr_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcTactics GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Logic.
From Glibc Require Import OsWorld OsRegistry FileInv DcigettextRoute HelloGettextLink
  HelloImageGettextLink HelloImageModule HelloImageLoad StartPtmallocInitSpec HelloImageEarly HelloGetoptDiagLock.
Import ListNotations.
Open Scope Z_scope.

(** ## The objects that gettext reads

    Each name below is the place of one global in Hello's image, with
    the region that the loader registers there. *)

(** A translation takes three read locks. They guard the state of the
    bindings, the current locale and the cache of translations. *)
Definition hello_lk1 : Z * region := Eval vm_compute in img_obj "_nl_state_lock".
Definition hello_lk2 : Z * region := Eval vm_compute in img_obj "__libc_setlocale_lock".
Definition hello_lkt : Z * region := Eval vm_compute in img_obj "glibc_dcigettext#tree_lock".

(** This cell holds the root of the translation cache. *)
Definition hello_root : Z * region := Eval vm_compute in img_obj "glibc_dcigettext#root".

(** These objects hold the head of the list of bound domains, the
    table of category indexes and the flag that marks a privileged
    process. *)
Definition hello_db : Z * region := Eval vm_compute in img_obj "_nl_domain_bindings".
Definition hello_ib : Z * region := Eval vm_compute in img_obj "_nl_category_name_idxs".
Definition hello_sec : Z * region := Eval vm_compute in img_obj "__libc_enable_secure".

(** This function returns the pointer that the image gives a symbol. *)
Definition hello_sym (n : string) : ptr :=
  match Term.lookup (TAtom n) img_globals with Some p => p | None => null end.

(** The cache compares its entries with a function from the image.
    The image also holds the default directory, the category names, the
    two literals of a catalog's file name and the C library's message
    domain. *)
Definition hello_tc : ptr := Eval vm_compute in hello_sym "glibc_dcigettext#transcmp".
Definition hello_dd : ptr := Eval vm_compute in hello_sym "__GI__nl_default_dirname".
Definition hello_nb : ptr := Eval vm_compute in hello_sym "_nl_category_names".
Definition hello_p276 : ptr := Eval vm_compute in hello_sym "glibc_dcigettext#str.276".
Definition hello_p277 : ptr := Eval vm_compute in hello_sym "glibc_dcigettext#str.277".
Definition hello_dom : ptr := Eval vm_compute in hello_sym "__GI__libc_intl_domainname".

(** This is the lock object at a place, as the lock calls receive it. *)
Definition lock_ptr (q : Z * region) : ptr := mkPtr q.1 (Obj q.1).

(** ## The facts *)

(** Gettext's rules name errno by the address eb. After startup, errno
    lives at the address that early startup records, and that address is
    the place of `c: __libc_errno` in the image. *)
Lemma hello_dgx_eb : pm_eb hello_pm_objs = img_a "__libc_errno".
Proof. vm_compute. reflexivity. Qed.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).

(** This is the linked Hello program in world w. *)
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
Local Abbreviation P := (program_of w glibc_os_registry hge).

(** Gettext must find its globals in place, and its calls must reach
    the right code. Hello's image meets each of these facts. The
    category byte k is any byte, and the stream fp is any pointer. *)
Lemma hello_dlk_image k fp :
  0 <= k < 256 -> 0 <= ptr_addr fp < 2 ^ 64 ->
  hello_gettext_link hge /\
  find_fn hge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) /\
  find_fn hge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) /\
  dlk_place (lock_ptr hello_lk1) hello_lk1.1 hello_lk1.2 /\
  dlk_place (lock_ptr hello_lk2) hello_lk2.1 hello_lk2.2 /\
  dlk_place (lock_ptr hello_lkt) hello_lkt.1 hello_lkt.2 /\
  (0 < hello_root.1 /\ 0 <= 0 /\ (hello_root.1 + 0) mod 8 = 0 /\ hello_root.1 + 0 + 8 <= r_end hello_root.2 /\
   r_end hello_root.2 <= 2 ^ 48) /\
  dci_globals (glibc_program := P) (img_a "__libc_errno") (lock_ptr hello_lk1) (lock_ptr hello_lk2)
    (lock_ptr hello_lkt) (mkPtr (hello_root.1 + 0) (Obj hello_root.1)) hello_tc hello_dd hello_db.1
    (ptr_addr hello_nb) (ptr_cap hello_nb) hello_ib.1 (Ro hello_ib.1) hello_p276 hello_p277 hello_sec.1 /\
  dci_bounds hello_db.1 hello_db.2 (ptr_addr hello_nb) hello_ib.1 (Ro hello_ib.1) hello_ib.2 k
    hello_sec.1 hello_sec.2 /\
  find_fn hge (TAtom "__fxprintf_nocancel") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf_nocancel) /\
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals hge) = Some hello_dom /\
  0 <= ptr_addr fp < 2 ^ 64.
Proof using Type.
  intros Hk Hfp. split.
  { destruct hello_image_memory as (g & m & Hi). destruct (hello_loaded_tables g m Hi) as [Eg _]. subst g.
    exact (hello_image_gettext_link _ _ fr Hi). }
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [unfold dlk_place; vm_compute; intuition congruence|].
  split; [unfold dlk_place; vm_compute; intuition congruence|].
  split; [unfold dlk_place; vm_compute; intuition congruence|].
  split; [vm_compute; intuition congruence|].
  split.
  { unfold dci_globals. cbn [program_ge program_of ge_globals]. split_and!; vm_compute; reflexivity. }
  split.
  { unfold dci_bounds, hello_db, hello_ib, hello_sec, hello_nb. cbn.
    split_and!; first [reflexivity | right; reflexivity | lia]. }
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. exact Hfp.
Qed.

End image.
