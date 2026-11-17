From Glibc Require Import GlibcProgram.
(** When the privilege flag is nonzero, glibc's `c: __dcigettext` calls
    strchr, and strchr calls strchrnul. DcigettextSecure.v proves that
    branch only for a program that links `__GI_strchr` and
    `__GI___strchrnul` to the captured bodies of the string fixture. This
    module checks that GNU Hello's own link does so.

    The image linked from gettext alone does not define strchr, so it
    cannot serve as the reference here. The fixture HelloStrchrImageCode.v
    is the image linked from Hello's main, restricted to the two names.
    The generator refused the selection unless each name has exactly one
    item in the whole image and that item is the same term as in the
    image of the string fixture Strchr. Those two checks belong to the
    producer, and the fixture records the hashes of both images. Rocq
    checks here that the selected bodies are the captured ones. *)
From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Semantics.
From Glibc Require Import StrchrCode HelloStrchrImageCode HelloGettextImage DcigettextSecure.
Import ListNotations.

(** ## What Hello's link gives the privileged branch *)

(** In the selection both names find the captured functions. *)
Lemma hello_strchr_image_links gl fr :
  find_fn (mkGenv hellostrchrimage_module gl fr) (TAtom "__GI_strchr") = Some (Defined glibc_strchr) /\
  find_fn (mkGenv hellostrchrimage_module gl fr) (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul).
Proof. split; vm_compute; reflexivity. Qed.

(** These are the names that the selection keeps. *)
Definition hello_strchr_names : list string := ["__GI_strchr"; "__GI___strchrnul"]%string.

(** Both names are functions in the selection, so neither lookup goes
    through an alias, and the selection keeps nothing else. *)
Example hello_strchr_shape :
  find_alias (TAtom "__GI_strchr") hellostrchrimage_module = None /\
  find_alias (TAtom "__GI___strchrnul") hellostrchrimage_module = None /\
  length hellostrchrimage_module = length hello_strchr_names.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ## Using the selection in a larger program

    A proof about all of Hello runs in Hello's whole module, not in the
    selection. If that module answers each lookup of the two names as
    the selection does, then both calls find the captured functions. The
    producer checked this agreement, but Rocq has not, so the caller must
    still state it. *)
Lemma hello_strchr_links_of_agree ge :
  Forall (lookup_agrees (ge_module ge) hellostrchrimage_module) hello_strchr_names ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) /\
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul).
Proof.
  intros Hagree. rewrite Forall_forall in Hagree.
  destruct (hello_strchr_image_links (ge_globals ge) (ge_free ge)) as [Hs Hn].
  destruct (Hagree "__GI_strchr"%string ltac:(cbn; tauto)) as [Hsd Hsa].
  destruct (Hagree "__GI___strchrnul"%string ltac:(cbn; tauto)) as [Hnd Hna].
  split; [rewrite <- Hs | rewrite <- Hn]; apply find_fn_agrees; try assumption;
    intros t Ht; vm_compute in Ht; discriminate Ht.
Qed.

(** When the flag is nonzero, gettext calls these two functions. So a
    caller that shows the agreement may run gettext with that flag. *)
Section program.
Import ProgramAbbreviations.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Lemma dci_strchr_links_of_agree :
  Forall (lookup_agrees (ge_module ge) hellostrchrimage_module) hello_strchr_names -> dci_strchr_links.
Proof using Type. exact (hello_strchr_links_of_agree ge). Qed.
End program.

(** ### Trying the lemma on made-up modules

    A module with an extra function and an extra alias is accepted. A
    module whose strchr runs strchrnul's code is refused, and so is a
    module that makes strchr an alias of strchrnul. *)
Definition hello_strchr_extended : module :=
  IFunc hello_image_unrelated :: hellostrchrimage_module ++
  [IAlias (TAtom "hello_unrelated_alias") (TAtom "weak") (TAtom "hello_unrelated")].

Example hello_strchr_extended_links gl fr :
  find_fn (mkGenv hello_strchr_extended gl fr) (TAtom "__GI_strchr") = Some (Defined glibc_strchr) /\
  find_fn (mkGenv hello_strchr_extended gl fr) (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul).
Proof. apply hello_strchr_links_of_agree. repeat constructor; vm_compute; reflexivity. Qed.

Example hello_strchr_extended_differs : hello_strchr_extended <> hellostrchrimage_module.
Proof. intros H. apply (f_equal (@length item)) in H. vm_compute in H. discriminate H. Qed.

Definition hello_strchr_rebody : module :=
  map (fun i => match i with
                | IFunc f => if name_eqb (fn_name f) (TAtom "__GI_strchr")
                             then IFunc (mkFunc (fn_name f) (fn_linkage f) (fn_ret f) (fn_params f) (fn_blocks glibc_strchrnul))
                             else i
                | _ => i end) hellostrchrimage_module.

Definition hello_strchr_realias : module :=
  IAlias (TAtom "__GI_strchr") (TAtom "weak") (TAtom "__GI___strchrnul") ::
  filter (fun i => match i with
                   | IFunc f => negb (name_eqb (fn_name f) (TAtom "__GI_strchr"))
                   | _ => true end) hellostrchrimage_module.

Example hello_strchr_changed gl fr :
  ~ Forall (lookup_agrees hello_strchr_rebody hellostrchrimage_module) hello_strchr_names /\
  ~ Forall (lookup_agrees hello_strchr_realias hellostrchrimage_module) hello_strchr_names /\
  find_fn (mkGenv hello_strchr_rebody gl fr) (TAtom "__GI_strchr") <> Some (Defined glibc_strchr) /\
  find_fn (mkGenv hello_strchr_realias gl fr) (TAtom "__GI_strchr") <> Some (Defined glibc_strchr).
Proof.
  repeat split; try (intros H; rewrite Forall_forall in H;
    destruct (H "__GI_strchr"%string ltac:(cbn; tauto)) as [Hd _]; vm_compute in Hd; discriminate Hd);
  vm_compute; discriminate.
Qed.
