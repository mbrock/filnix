(** When gettext looks for a message catalog, it builds a file name from
    the directory, the locale, the category and the domain. It joins them
    with the string "/" and ends the name with ".mo". The translation
    route in DcigettextRoute.v reads both strings through the resource
    dci_reads, which asks for them as read-only strings at the objects
    that the symbols str.276 and str.277 name.

    The literal ownership rules turn the loader pieces for these strings
    into the shares that gettext reads. A separate check loads the
    dcigettext module alone and compares its initialized bytes with
    both suffixes. *)

From Glibc Require Import LiteralWords ImageData LiteralLogic GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv WordString DcigettextCode Fix.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Import FileInv Fix.ML0 Fix.LG0.

(** ## The two strings

    The separator is the single byte 47, and the suffix is the three
    bytes 46, 109 and 111. *)

(** These are the symbols of the separator and the suffix. *)
Definition dci_suffix_names : list string := ["glibc_dcigettext#str.276"; "glibc_dcigettext#str.277"]%string.

(** These are their texts without terminators. *)
Definition dci_suffix_texts : list (list Z) := [[47]; [46; 109; 111]].

(** Both texts have checked words. *)
Lemma dci_suffix_texts_ok : Forall (fun s => lit_ok s = true) dci_suffix_texts.
Proof. repeat constructor. Qed.

(** These are the pieces of the two strings at the objects bs. *)
Definition dci_suffix_ps (bs : list (Z * region)) : list (piece * pval) := lits_ps bs dci_suffix_texts.

(** A symbol table places the strings at bs when each symbol names the
    read-only object at the matching base. *)
Definition dci_suffix_at (gs : list (name * ptr)) (bs : list (Z * region)) : Prop :=
  Forall2 (fun n br => Term.lookup (TAtom n) gs = Some (mkPtr br.1 (Ro br.1))) dci_suffix_names bs.

Section own.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## Freezing the strings

    The route needs the two strings as read-only strings that it may read
    on every call, so the frozen form uses discarded fractions. *)

(** Startup can hand over the raw pieces of the two strings, but the
    route reads strings. When each object fits its string, the pieces
    freeze into the two strings that the route asks for. *)
Lemma dci_suffix_own b1 r1 b2 r2 : lit_fit (b1, r1) [47] -> lit_fit (b2, r2) [46; 109; 111] ->
  pts (dci_suffix_ps [(b1, r1); (b2, r2)]) ==∗
  □ (word_string DfracDiscarded (mkPtr b1 (Ro b1)) [47] ∗ word_string DfracDiscarded (mkPtr b2 (Ro b2)) [46; 109; 111]).
Proof using Type.
  intros H1 H2. iIntros "H". unfold dci_suffix_ps.
  iMod (lits_own with "H") as "#H"; [exact (List.Forall2_cons _ _ H1 (List.Forall2_cons _ _ H2 (List.Forall2_nil _))) | exact dci_suffix_texts_ok|].
  rewrite !big_sepL2_cons. iDestruct "H" as "(H1 & H2 & _)". iModIntro. iModIntro. iSplit; [iExact "H1" | iExact "H2"].
Qed.

(** A printer or copier checks that a string's object is live before it
    reads. A frozen read-only string holds a copyable share of that
    liveness at its own base. *)
Lemma ro_string_live b s : word_string DfracDiscarded (mkPtr b (Ro b)) s ⊢ ∃ reg, liveq DfracDiscarded b reg.
Proof using Type.
  iIntros "Hw". iDestruct "Hw" as (b' reg ws Hsh) "[Hl _]".
  destruct (ss_cap _ _ _ _ _ Hsh) as [E|E]; [discriminate|]. cbn in E. injection E as <-.
  iExists reg. iExact "Hl".
Qed.

End own.

(** ## The dcigettext module's image

    The loader lays out the dcigettext module on its own. The symbols and
    the memory below come from that computation, and the lemmas after
    them check the two strings against it. *)

(** The loader computes these symbols from the module. *)
Definition dcigettext_globals : list (name * ptr) := Eval vm_compute in
  match initial_memory dcigettext_module with Some (g, _) => g | None => [] end.

(** This is the memory that the loader builds for the module. *)
Definition dcigettext_memory : mem :=
  match initial_memory dcigettext_module with Some (_, m) => m | None => empty_mem end.

(** The loader succeeds on the module rather than falling back to empty
    memory. *)
Lemma dcigettext_initial_memory : initial_memory dcigettext_module = Some (dcigettext_globals, dcigettext_memory).
Proof.
  assert (H : option_map fst (initial_memory dcigettext_module) = Some dcigettext_globals) by (vm_compute; reflexivity).
  unfold dcigettext_memory. destruct (initial_memory dcigettext_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** These are the objects of the separator and the suffix in that image. *)
Definition dci_suffix_fixture : list (Z * region) := [(66272, gd 66272 66280); (66304, gd 66304 66312)].

(** The module's symbols name those objects. *)
Lemma dci_suffix_fixture_at : dci_suffix_at dcigettext_globals dci_suffix_fixture.
Proof. repeat (apply List.Forall2_cons; [vm_compute; reflexivity|]). apply List.Forall2_nil. Qed.

(** Each string fits its object. *)
Lemma dci_suffix_fixture_fit : Forall2 lit_fit dci_suffix_fixture dci_suffix_texts.
Proof.
  repeat (apply List.Forall2_cons; [unfold lit_fit; vm_compute; split_and!; first [reflexivity | discriminate]|]).
  apply List.Forall2_nil.
Qed.

(** Every piece of the two strings agrees with the image, and their keys
    are distinct. *)
Lemma dci_suffix_fixture_agrees :
  all_agree dcigettext_memory (dci_suffix_ps dci_suffix_fixture) /\ NoDup (dci_suffix_ps dci_suffix_fixture).*1.
Proof.
  split.
  - apply checked_pieces_all_agree. unfold dcigettext_memory. vm_compute. reflexivity.
  - apply lits_ps_keys. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(** ## Controls

    The checks below show that the computations above can fail. A
    changed separator or suffix, a shorter object or swapped symbols do
    not pass. *)

(** The image holds no backslash where the separator is. *)
Lemma dci_slash_changed_refused :
  forallb (fun lv => bool_decide (checked_piece dcigettext_memory lv.1 lv.2))
    (lit_ps 66272 (gd 66272 66280) (lit_words [92])) = false.
Proof. unfold dcigettext_memory. vm_compute. reflexivity. Qed.

(** The image holds no ".mp" where the suffix is. *)
Lemma dci_suffix_changed_refused :
  forallb (fun lv => bool_decide (checked_piece dcigettext_memory lv.1 lv.2))
    (lit_ps 66304 (gd 66304 66312) (lit_words [46; 109; 112])) = false.
Proof. unfold dcigettext_memory. vm_compute. reflexivity. Qed.

(** The image does not hold the suffix in a four-byte object, and the
    suffix's word would not fit one. *)
Lemma dci_suffix_short_refused :
  forallb (fun lv => bool_decide (checked_piece dcigettext_memory lv.1 lv.2))
    (lit_ps 66304 (gd 66304 66308) (lit_words [46; 109; 111])) = false /\
  ~ lit_fit (66304, gd 66304 66308) [46; 109; 111].
Proof.
  split; [unfold dcigettext_memory; vm_compute; reflexivity|].
  intros (_ & _ & H & _). vm_compute in H. apply H. reflexivity.
Qed.

(** The symbols str.276 and str.277 cannot trade places. *)
Lemma dci_suffix_swap_refused : ~ dci_suffix_at dcigettext_globals (rev dci_suffix_fixture).
Proof. intros H. pose proof (Forall2_lookup_lr _ _ _ 0 _ _ H eq_refl eq_refl) as E. vm_compute in E. discriminate. Qed.
