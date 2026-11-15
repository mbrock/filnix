From Glibc Require Import GlibcProgram.
(** HelloGettextLink.v checks gettext's link record against an image
    linked from gettext alone. That image does not show what Hello's own
    link does, because Hello links many more units, and one of them could
    define a name that gettext calls. This module checks the record
    against an image linked from Hello's main instead.

    That image holds GNU Hello and the 321 user glibc units that it
    reaches. It is too large to decode within the compile budget, so the
    fixture HelloGettextImageCode.v keeps only the names that gettext
    calls and the targets of their aliases, with their terms unchanged.
    The generator refuses the selection unless each kept name has exactly
    one item in the whole image, and unless that item is the term the
    gettext image has. Those two checks belong to the producer: Rocq sees
    the selection, not the whole image, and the fixture records the
    hashes of both.

    As with the gettext image, the caller must still show that no global
    variable is named memmove. Hello's main link record already says
    where malloc and free live, so the selection leaves them out. *)
From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Semantics.
From Glibc Require Import MemFwdCode HiAtexitModule StpcpyCode TfindCode LocalenameCode RdlockCode RwunlockCode.
From Glibc Require Import DcgettextCode DcigettextCode GettextLinkCode HelloGettextImageCode HelloGettextLink.
Import ListNotations.

(** ## What Hello's link gives gettext

    We want to know whether Hello's own link gives gettext the functions
    that its proofs assumed. In the selection it does, and memmove stays
    undefined. Only the list of globals is left for the caller. *)
Lemma hello_gettext_link_hello_image gl fr :
  lookup (TAtom "zmemmove") gl = None -> hello_gettext_link (mkGenv hellogettextimage_module gl fr).
Proof. intros H. constructor; try (vm_compute; reflexivity). split; [vm_compute; reflexivity | exact H]. Qed.

(** ## Controls

    These names are the ones that the selection keeps. For each of
    them, a direct lookup and an alias lookup give the same answer in
    Hello's image as in the gettext image, so the two links agree on
    every name that gettext calls. *)
Definition hello_image_names : list string :=
  ["__GI_mempcpy"; "__GI___mempcpy"; "__GI_memcpy"; "__GI___dcgettext"; "__dcigettext";
   "__GI_stpcpy"; "__GI___stpcpy"; "__GI___tfind"; "__current_locale_name";
   "__GI___pthread_rwlock_rdlock"; "___pthread_rwlock_rdlock";
   "__GI___pthread_rwlock_unlock"; "___pthread_rwlock_unlock"]%string.

Example hello_image_agrees :
  Forall (fun n => find_direct (TAtom n) hellogettextimage_module = find_direct (TAtom n) gettextlink_module /\
                   find_alias (TAtom n) hellogettextimage_module = find_alias (TAtom n) gettextlink_module)
    hello_image_names.
Proof. repeat constructor; vm_compute; reflexivity. Qed.

(** The selection keeps the weak stpcpy alias and the two lock aliases,
    and it keeps nothing that memmove, malloc or free could find. A
    selection that dropped an alias, or kept an allocator, fails here. *)
Example hello_image_shape :
  find_alias (TAtom "__GI_stpcpy") hellogettextimage_module = Some (TAtom "__GI___stpcpy") /\
  find_alias (TAtom "__GI___pthread_rwlock_rdlock") hellogettextimage_module = Some (TAtom "___pthread_rwlock_rdlock") /\
  find_alias (TAtom "__GI___pthread_rwlock_unlock") hellogettextimage_module = Some (TAtom "___pthread_rwlock_unlock") /\
  find_direct (TAtom "zmemmove") hellogettextimage_module = None /\ find_alias (TAtom "zmemmove") hellogettextimage_module = None /\
  find_direct (TAtom "malloc") hellogettextimage_module = None /\ find_alias (TAtom "malloc") hellogettextimage_module = None /\
  find_direct (TAtom "free") hellogettextimage_module = None /\ find_alias (TAtom "free") hellogettextimage_module = None /\
  length hellogettextimage_module = length hello_image_names.
Proof. repeat split; vm_compute; reflexivity. Qed.
