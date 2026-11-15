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

    The caller must still show that no global variable is named
    memmove. Malloc and free are left out, because Hello's main link
    record already says where they live. *)
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

(** ## Using the selection in a larger program

    A proof about all of Hello cannot cite the lemma above, because it
    runs in a larger module. The lemma below lets it use the selection
    anyway. The caller shows that its module answers each lookup for
    the kept names just as the selection does, and then gettext gets
    the same functions. The producer found that Hello's link agrees,
    but Rocq has not checked this, so it stays the caller's premise. *)

(** A module agrees with another on a name when a direct lookup and an
    alias lookup give the same answers in both. *)
Definition lookup_agrees (md md' : module) (n : string) : Prop :=
  find_direct (TAtom n) md = find_direct (TAtom n) md' /\ find_alias (TAtom n) md = find_alias (TAtom n) md'.

(** A call finds the same function in two modules that agree on the
    called name and on the target of its alias. *)
Lemma find_fn_agrees ge md n :
  find_direct n (ge_module ge) = find_direct n md -> find_alias n (ge_module ge) = find_alias n md ->
  (forall t, find_alias n md = Some t -> find_direct t (ge_module ge) = find_direct t md) ->
  find_fn ge n = find_fn (mkGenv md (ge_globals ge) (ge_free ge)) n.
Proof.
  intros Hd Ha Ht. unfold find_fn; cbn. rewrite Hd, Ha.
  destruct (find_direct n md); [reflexivity |].
  destruct (find_alias n md) eqn:E; cbn; [apply Ht; reflexivity | reflexivity].
Qed.

(** A program whose module agrees with the selection on every kept
    name meets gettext's record, provided that it also leaves memmove
    without a function or a global. *)
Lemma hello_gettext_link_of_agree ge :
  Forall (lookup_agrees (ge_module ge) hellogettextimage_module) hello_image_names ->
  find_fn ge (TAtom "zmemmove") = None -> lookup (TAtom "zmemmove") (ge_globals ge) = None ->
  hello_gettext_link ge.
Proof.
  intros Hagree Hz Hg. rewrite Forall_forall in Hagree.
  destruct (hello_gettext_link_hello_image (ge_globals ge) (ge_free ge) Hg).
  refine (mkHelloGettextLink _ _ _ _ _ _ _ _ _ _ (conj Hz Hg));
    erewrite find_fn_agrees; try eassumption;
    try (intros t Ht; vm_compute in Ht; first [discriminate Ht | injection Ht as <-]);
    first [refine (proj1 (Hagree _ _)) | refine (proj2 (Hagree _ _))];
    cbn; repeat (first [left; reflexivity | right]).
Qed.

(** ### Trying the lemma on made-up modules

    We want the lemma to accept a larger module and to refuse one that
    runs other code. A module with an extra function and an extra alias
    is accepted. A module whose stpcpy alias points elsewhere is
    refused, and so is a module whose stpcpy runs mempcpy's code. *)
Definition hello_image_unrelated : func := mkFunc (TAtom "hello_unrelated") (TAtom "export") (RClass W) [] [].

Definition hello_image_extended : module :=
  IFunc hello_image_unrelated :: hellogettextimage_module ++ [IAlias (TAtom "hello_unrelated_alias") (TAtom "weak") (TAtom "hello_unrelated")].

Example hello_image_extended_link gl fr :
  lookup (TAtom "zmemmove") gl = None -> hello_gettext_link (mkGenv hello_image_extended gl fr).
Proof.
  intros H. apply hello_gettext_link_of_agree; [| vm_compute; reflexivity | exact H].
  repeat constructor; vm_compute; reflexivity.
Qed.

Example hello_image_extended_differs : hello_image_extended <> hellogettextimage_module.
Proof. intros H. apply (f_equal (@length item)) in H. vm_compute in H. discriminate H. Qed.

Definition hello_image_retarget : module :=
  map (fun i => match i with
                | IAlias (TAtom "__GI_stpcpy") lk _ => IAlias (TAtom "__GI_stpcpy") lk (TAtom "__GI___mempcpy")
                | _ => i end) hellogettextimage_module.

Definition hello_image_rebody : module :=
  map (fun i => match i with
                | IFunc f => if name_eqb (fn_name f) (TAtom "__GI___stpcpy")
                             then IFunc (mkFunc (fn_name f) (fn_linkage f) (fn_ret f) (fn_params f) (fn_blocks glibc_mempcpy))
                             else i
                | _ => i end) hellogettextimage_module.

Example hello_image_changed_stpcpy :
  ~ Forall (lookup_agrees hello_image_retarget hellogettextimage_module) hello_image_names /\
  ~ Forall (lookup_agrees hello_image_rebody hellogettextimage_module) hello_image_names.
Proof.
  split; intros H; rewrite Forall_forall in H.
  - destruct (H "__GI_stpcpy"%string ltac:(cbn; tauto)) as [_ Ha]. vm_compute in Ha. discriminate Ha.
  - destruct (H "__GI___stpcpy"%string ltac:(cbn; tauto)) as [Hd _]. vm_compute in Hd. discriminate Hd.
Qed.
