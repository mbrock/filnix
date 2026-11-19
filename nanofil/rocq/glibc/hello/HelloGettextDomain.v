(** Gettext reads the domain "libc" when strerror translates a libc message.
    The existing StrerrorCode capture contains that string and its terminator.
    This file turns supplied literal pieces into the read-only string needed
    by dci_reads, after the caller supplies its actual symbol lookup and bounds.

    The checks load only the captured strerror module, without Hello or
    the rest of glibc. They neither locate the string in a complete program
    nor show that startup gives a caller permission to read it. *)
From Glibc Require Import LiteralWords ImageData LiteralLogic GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Pieces Heap Logic MemLogic.
From Glibc Require Import FileInv WordString StrerrorCode.
Import ListNotations FileInv Fix.ML0 Fix.LG0.
Open Scope Z_scope.

(** The text excludes the NUL that lit_words adds. *)
Definition libc_domain_text : list Z := [108;105;98;99].

(** Glibc gives this string an internal name for calls within the library.
    The captured compiler directives rename _libc_intl_domainname to
    __GI__libc_intl_domainname. This lookup uses that recorded name directly. *)
Definition libc_domain_at (gs : list (name * ptr)) b : Prop :=
  Term.lookup (TAtom "__GI__libc_intl_domainname") gs = Some (mkPtr b (Ro b)).

(** These pieces include the object's lifetime and its padded word. *)
Definition libc_domain_ps b reg : list (piece * pval) :=
  lit_ps b reg (lit_words libc_domain_text).

Section own.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Supplying the pieces does not establish their location in a program.
    The caller supplies that lookup and an aligned object large enough for
    the padded word. Freezing the pieces then gives exactly the domain
    string conjunct, without any of gettext's other resources. *)
Lemma libc_domain_own b reg :
  libc_domain_at (Semantics.ge_globals program_ge) b -> lit_fit (b,reg) libc_domain_text ->
  pts (libc_domain_ps b reg) ==∗
  word_string DfracDiscarded (mkPtr b (Ro b)) libc_domain_text.
Proof using Type.
  intros Hlookup (Hb & H8 & Hfit & Htop). iIntros "H".
  iApply (lit_own with "H"); [exact Hb | exact H8 | exact Hfit | exact Htop | reflexivity].
Qed.
End own.

(** Loading the captured module produces its symbol table and memory.
    The equality below checks that loading succeeds, rather than returning
    the empty memory used when loading fails. *)
Definition strerror_domain_globals : list (name * ptr) := Eval vm_compute in
  match initial_memory strerror_module with Some (g,_) => g | None => [] end.
Definition strerror_domain_memory : mem :=
  match initial_memory strerror_module with Some (_,m) => m | None => empty_mem end.

Lemma strerror_domain_image :
  initial_memory strerror_module = Some (strerror_domain_globals,strerror_domain_memory).
Proof.
  assert (H : option_map fst (initial_memory strerror_module) = Some strerror_domain_globals)
    by (vm_compute; reflexivity).
  unfold strerror_domain_memory.
  destruct (initial_memory strerror_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The loader places the five bytes in an eight-byte read-only object. *)
Lemma libc_domain_image_at : libc_domain_at strerror_domain_globals 65648.
Proof. vm_compute. reflexivity. Qed.

Lemma libc_domain_image_fit : lit_fit (65648,gd 65648 65656) libc_domain_text.
Proof. unfold lit_fit; vm_compute; split_and!; first [reflexivity | discriminate]. Qed.

Lemma libc_domain_image_bytes :
  map (fun off => load_bytes strerror_domain_memory (65648 + off) 1) [0;1;2;3;4] =
  [108;105;98;99;0].
Proof. unfold strerror_domain_memory. vm_compute. reflexivity. Qed.

(** Agreement checks the actual loader memory, including the lifetime and
    padded word. Distinctness follows structurally from the literal pieces. *)
Lemma libc_domain_image_agrees :
  all_agree strerror_domain_memory (libc_domain_ps 65648 (gd 65648 65656)) /\
  NoDup (libc_domain_ps 65648 (gd 65648 65656)).*1.
Proof.
  split.
  - apply checked_pieces_all_agree. unfold strerror_domain_memory. vm_compute. reflexivity.
  - apply lit_ps_nodup.
Qed.

(** Changing a character or removing the terminator from the entire word
    fails agreement with the captured image. *)
Lemma libc_domain_changed_refused :
  forallb (fun lv => bool_decide (checked_piece strerror_domain_memory lv.1 lv.2))
    (lit_ps 65648 (gd 65648 65656) (lit_words [108;105;98;100])) = false.
Proof. unfold strerror_domain_memory. vm_compute. reflexivity. Qed.

Lemma libc_domain_no_nul_refused :
  forallb (fun lv => bool_decide (checked_piece strerror_domain_memory lv.1 lv.2))
    (lit_ps 65648 (gd 65648 65656) [of_bytes [108;105;98;99;1;1;1;1]]) = false.
Proof. unfold strerror_domain_memory. vm_compute. reflexivity. Qed.

(** Five bytes hold the text and NUL, but not the word read by word_string.
    Such a shortened region neither agrees with the image nor fits the word. *)
Lemma libc_domain_short_refused :
  forallb (fun lv => bool_decide (checked_piece strerror_domain_memory lv.1 lv.2))
    (libc_domain_ps 65648 (gd 65648 65653)) = false /\
  ~ lit_fit (65648,gd 65648 65653) libc_domain_text.
Proof.
  split; [unfold strerror_domain_memory; vm_compute; reflexivity|].
  intros (_ & _ & H & _). vm_compute in H. apply H. reflexivity.
Qed.

(** Moving the proposed object changes both the lookup and the pieces.
    Neither claim holds at this different aligned address. *)
Lemma libc_domain_wrong_place_refused :
  ~ libc_domain_at strerror_domain_globals 65664 /\
  forallb (fun lv => bool_decide (checked_piece strerror_domain_memory lv.1 lv.2))
    (libc_domain_ps 65664 (gd 65664 65672)) = false.
Proof.
  split; [vm_compute; discriminate|].
  unfold strerror_domain_memory. vm_compute. reflexivity.
Qed.
