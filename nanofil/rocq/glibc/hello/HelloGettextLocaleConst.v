From Glibc Require Import GlibcProgram.
(** When gettext builds the file name of a message catalog, it needs the
    name of the category. It looks up byte 5 of _nl_category_name_idxs,
    which holds the offset of "LC_MESSAGES" inside the table
    _nl_category_names, and it reads the name at that offset. It then
    checks whether the locale name is "C". The translation route in
    DcigettextRoute.v takes those reads as the resource dci_reads with the
    table base, the offset and the strings as parameters. Nothing has
    built them so far.

    glibc's locale/setlocale.c defines the table and the offsets, and
    locale/C_name.c defines the string "C". The module LocaleConstCode.v
    holds just those three constants. This file builds the read-only
    shares that dci_reads asks for from loader pieces. It owns only the
    two words of the table around "LC_MESSAGES" and byte 5 of the
    offsets, not the whole objects.

    The string "C" here is the constant object _nl_C_name. The route
    reads its locale name from entry 5 of the thread's mutable locale,
    and nothing here shows that this entry points at _nl_C_name when the
    route runs. The checks below use the loader image of LocaleConstCode
    alone, which shows neither where a program linking Hello with glibc
    puts the constants nor that startup hands their pieces over. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv StrlenLogic WordString LocaleConstCode HelloGetoptTable HelloGetoptDiagMsgs.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Import FileInv FileInv.ML FileInv.LG.

(** ## The category name inside the table

    The table packs the twelve category names one after another, so
    "LC_MESSAGES" starts at offset 51, which is not a word boundary. A
    string at an interior address reads whole words, so the reader needs
    the words at offsets 48 and 56. They also hold the end of "LC_TIME"
    before the name and the first letter of "LC_PAPER" after its
    terminator. *)

(** This is the name "LC_MESSAGES" without its terminator. *)
Definition lc_messages : list Z := [76; 67; 95; 77; 69; 83; 83; 65; 71; 69; 83].

(** This is the offset of the name in the table. *)
Definition lc_messages_off : Z := 51.

(** These are bytes 48 to 63 of the table. *)
Definition lc_window : list Z := [77; 69; 0; 76; 67; 95; 77; 69; 83; 83; 65; 71; 69; 83; 0; 76].

(** These are the two little-endian words that hold those bytes. *)
Definition lc_words : list Z := [4993752304466281805; 5476468703895835475].

(** The words spell the window. *)
Lemma lc_words_bytes : wbytes lc_words = lc_window.
Proof. vm_compute. reflexivity. Qed.

(** These are the table's pieces that the reader needs: its lifetime and
    the two words. *)
Definition lc_name_ps (nb : Z) (reg : region) : list (piece * pval) :=
  (PLive nb, VLive reg) :: words_ps nb 48 lc_words.

(** A table at a positive 8-byte boundary, whose object holds both words
    below the top of the address space, has the name at offset 51 in the
    shape that the string routines read. *)
Lemma lc_name_shape nb reg : 0 < nb -> nb mod 8 = 0 -> nb + 64 <= r_end reg -> r_end reg <= 2 ^ 48 ->
  str_shape (mkPtr (nb + lc_messages_off) (Ro nb)) nb reg lc_words lc_messages.
Proof.
  intros H0 H8 Hfit Hsp. unfold lc_messages_off.
  assert (Hm : (nb + 51) mod 8 = 3) by (rewrite Z.add_mod; [rewrite H8|]; reflexivity || lia).
  assert (Hw : wstart (mkPtr (nb + 51) (Ro nb)) = nb + 48) by (unfold wstart; cbn [ptr_addr]; rewrite Hm; lia).
  constructor; cbn [ptr_addr ptr_cap].
  - right. reflexivity.
  - exact H0.
  - exact H8.
  - lia.
  - rewrite Hw. cbn. lia.
  - exact Hsp.
  - rewrite Hm. reflexivity.
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - rewrite Hm lc_words_bytes. reflexivity.
  - apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(** ## The offset of the category

    Before gettext can find the name, it must learn where the name
    starts. Byte 5 of the offsets holds that position, 51, so the reader
    needs the lifetime of the offsets object and that one byte. *)

(** These are the offsets' pieces that the reader needs. *)
Definition lc_idx_ps (ib : Z) (reg : region) : list (piece * pval) :=
  (PLive ib, VLive reg) :: byte_ps ib 5 [lc_messages_off].

(** This is the string "C" without its terminator. *)
Definition lc_c : list Z := [67].

(** These are all the pieces at the three bases. *)
Definition lc_ps (nb : Z) (nr : region) (ib : Z) (ir : region) (cb : Z) (cr : region) : list (piece * pval) :=
  lc_name_ps nb nr ++ lc_idx_ps ib ir ++ lit_ps cb cr (lit_words lc_c).

(** A symbol table places the constants when each symbol names the
    read-only object at the matching base. *)
Definition lc_at (gs : list (name * ptr)) (nb ib cb : Z) : Prop :=
  Term.lookup (TAtom "_nl_category_names") gs = Some (mkPtr nb (Ro nb)) /\
  Term.lookup (TAtom "_nl_category_name_idxs") gs = Some (mkPtr ib (Ro ib)) /\
  Term.lookup (TAtom "_nl_C_name") gs = Some (mkPtr cb (Ro cb)).

(** The three objects fit what the reader needs when each starts at a
    positive 8-byte boundary and holds the pieces below the top of the
    address space. *)
Definition lc_fit (nb : Z) (nr : region) (ib : Z) (ir : region) (cb : Z) (cr : region) : Prop :=
  (0 < nb /\ nb mod 8 = 0 /\ nb + 64 <= r_end nr /\ r_end nr <= 2 ^ 48) /\
  (0 < ib /\ ib + 6 <= r_end ir /\ r_end ir <= 2 ^ 48) /\
  lit_fit (cb, cr) lc_c.

(** The route also checks bounds on the table and the offsets. A fitting
    placement gives the ones that concern these objects, with the offset
    51 in place of the route's k. *)
Lemma lc_bounds nb nr ib ir cb cr : lc_fit nb nr ib ir cb cr ->
  (Ro ib = Obj ib \/ Ro ib = Ro ib) /\ (0 < ib /\ ib + 6 <= r_end ir /\ r_end ir <= 2 ^ 48) /\
  (0 <= lc_messages_off < 256 /\ 0 <= nb /\ nb + lc_messages_off < 2 ^ 48).
Proof. unfold lc_messages_off. intros ((? & ? & ? & ?) & (? & ? & ?) & _). split_and!; auto; lia. Qed.

(** ## Distinct keys

    Every key of these pieces belongs to one of the three bases, so the
    pieces stay apart from other startup pieces whose keys avoid those
    bases. *)

(** The table's keys belong to its base and are distinct. *)
Lemma lc_name_keys nb nr : NoDup (lc_name_ps nb nr).*1 /\ forall k, k ∈ (lc_name_ps nb nr).*1 -> piece_id k = nb.
Proof.
  unfold lc_name_ps. cbn [fmap list_fmap fst]. rewrite (words_ps_keys nb 48 lc_words). split.
  - apply NoDup_cons. split.
    + intros Hin. apply list_elem_of_fmap in Hin as (? & ? & _). discriminate.
    + apply NoDup_fmap_2; [intros x y E; congruence | apply NoDup_seqZ].
  - intros k [->|Hk]%elem_of_cons; [done|]. apply list_elem_of_fmap in Hk as (o & -> & _). done.
Qed.

(** The offsets' two keys belong to their base and are distinct. *)
Lemma lc_idx_keys ib ir : NoDup (lc_idx_ps ib ir).*1 /\ forall k, k ∈ (lc_idx_ps ib ir).*1 -> piece_id k = ib.
Proof.
  cbn. split.
  - apply NoDup_cons. split; [intros [E|E]%elem_of_cons; [discriminate | inversion E] | apply NoDup_singleton].
  - intros k [->|[->|E]%elem_of_cons]%elem_of_cons; [done | done | inversion E].
Qed.

(** Every key belongs to one of the three bases. *)
Lemma lc_ps_ids nb nr ib ir cb cr k : k ∈ (lc_ps nb nr ib ir cb cr).*1 -> piece_id k ∈ [nb; ib; cb].
Proof.
  unfold lc_ps. rewrite !fmap_app. intros Hk.
  apply elem_of_app in Hk as [Hk|Hk]; [|apply elem_of_app in Hk as [Hk|Hk]].
  - rewrite (proj2 (lc_name_keys nb nr) k Hk). by left.
  - rewrite (proj2 (lc_idx_keys ib ir) k Hk). right; by left.
  - rewrite (lit_ps_ids _ _ _ k Hk). right; right; by left.
Qed.

(** At three distinct bases, all the keys are distinct. *)
Lemma lc_ps_nodup nb nr ib ir cb cr : NoDup [nb; ib; cb] -> NoDup (lc_ps nb nr ib ir cb cr).*1.
Proof.
  intros Hb. apply NoDup_cons in Hb as [Hn Hb]. apply NoDup_cons in Hb as [Hi _].
  destruct (lc_name_keys nb nr) as [Nn In]. destruct (lc_idx_keys ib ir) as [Ni Ii].
  unfold lc_ps. rewrite !fmap_app. apply NoDup_app. split_and!; [exact Nn| |apply NoDup_app; split_and!].
  - intros k Hk1 Hk2. apply Hn. rewrite -(In k Hk1).
    apply elem_of_app in Hk2 as [Hk2|Hk2]; [rewrite (Ii k Hk2) | rewrite (lit_ps_ids _ _ _ k Hk2)];
      apply elem_of_cons; [by left | right; by left].
  - exact Ni.
  - intros k Hk1 Hk2. apply Hi. rewrite -(Ii k Hk1) (lit_ps_ids _ _ _ k Hk2). by left.
  - apply lit_ps_nodup.
Qed.

Section own.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## Freezing the shares

    Every translation reads the name, its position and the string "C",
    and none of them ever changes. A read-only share that can be copied
    therefore serves every call. The route already lets its caller
    choose the share, so these shares fit it as they are. *)

(** The loader leaves raw bytes in memory, but the route wants strings
    it can read. This lemma turns the bytes into the three shares that
    the route reads when each object is large enough. *)
Lemma lc_own nb nr ib ir cb cr : lc_fit nb nr ib ir cb cr ->
  pts (lc_ps nb nr ib ir cb cr) ==∗
  □ (word_string DfracDiscarded (mkPtr (nb + lc_messages_off) (Ro nb)) lc_messages ∗
     liveq DfracDiscarded ib ir ∗ bytesq DfracDiscarded ib 5 [lc_messages_off] ∗
     word_string DfracDiscarded (mkPtr cb (Ro cb)) lc_c).
Proof.
  intros ((Hn0 & Hn8 & Hne & Hnr) & _ & (Hc0 & Hc8 & Hce & Hcr)). unfold lc_ps. rewrite !pts_app.
  iIntros "(Hn & Hi & Hc)".
  iAssert (word_string (DfracOwn 1) (mkPtr (nb + lc_messages_off) (Ro nb)) lc_messages) with "[Hn]" as "Hn".
  { iExists nb, nr, lc_words. iSplit; [iPureIntro; exact (lc_name_shape nb nr Hn0 Hn8 Hne Hnr)|].
    replace (wstart (mkPtr (nb + lc_messages_off) (Ro nb)) - nb) with 48.
    - rewrite /lc_name_ps pts_ptsq (ptsq_app _ [_]). iExact "Hn".
    - unfold wstart, lc_messages_off. cbn [ptr_addr].
      assert (Hm : (nb + 51) mod 8 = 3) by (rewrite Z.add_mod; [rewrite Hn8|]; reflexivity || lia). lia. }
  iMod (word_string_persist with "Hn") as "#Hn".
  rewrite pts_ptsq. iMod (ptsq_persist with "Hi") as "#Hi". rewrite /lc_idx_ps (ptsq_app _ [_]).
  iDestruct "Hi" as "[Hl Hb]".
  iMod (lit_own with "Hc") as "#Hc"; [exact Hc0 | exact Hc8 | exact Hce | exact Hcr | reflexivity|].
  iModIntro. iModIntro. rewrite /liveq /bytesq. iSplitR; [iExact "Hn"|]. iSplitR; [iExact "Hl"|].
  iSplitR; [iExact "Hb" | iExact "Hc"].
Qed.

End own.

(** ## The module's image

    The loader lays out LocaleConstCode on its own. The symbols and the
    memory below come from that computation, and the lemmas after them
    check the constants against it. *)

(** The module holds the three constants and its root table, with the
    sizes and alignments of glibc's definitions: 13 offsets, 137 bytes of
    names and the 2 bytes of "C", each aligned to 1. *)
Lemma localeconst_data :
  map (fun i => match i with IData n _ a xs => Some (n, a, items_size xs) | _ => None end) localeconst_module =
  [Some (TAtom "localeconst_roots", 8, 24); Some (TAtom "_nl_category_name_idxs", 1, 13);
   Some (TAtom "_nl_category_names", 1, 137); Some (TAtom "_nl_C_name", 1, 2)].
Proof. vm_compute. reflexivity. Qed.

(** The loader computes these symbols from the module. *)
Definition localeconst_globals : list (name * ptr) := Eval vm_compute in
  match initial_memory localeconst_module with Some (g, _) => g | None => [] end.

(** This is the memory that the loader builds for the module. *)
Definition localeconst_memory : mem :=
  match initial_memory localeconst_module with Some (_, m) => m | None => empty_mem end.

(** The loader succeeds on the module rather than falling back to empty
    memory. *)
Lemma localeconst_initial_memory : initial_memory localeconst_module = Some (localeconst_globals, localeconst_memory).
Proof.
  assert (H : option_map fst (initial_memory localeconst_module) = Some localeconst_globals) by (vm_compute; reflexivity).
  unfold localeconst_memory. destruct (initial_memory localeconst_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** These are the pieces at the image's objects. *)
Definition lc_fixture_ps : list (piece * pval) :=
  lc_ps 65616 (gd 65616 65760) 65584 (gd 65584 65600) 65776 (gd 65776 65784).

(** The module's symbols name the three objects. *)
Lemma lc_fixture_at : lc_at localeconst_globals 65616 65584 65776.
Proof. vm_compute. split_and!; reflexivity. Qed.

(** The objects fit, their regions are the image's, and the pieces agree
    with the image with distinct keys. *)
Lemma lc_fixture :
  lc_fit 65616 (gd 65616 65760) 65584 (gd 65584 65600) 65776 (gd 65776 65784) /\
  object_region 65616 (m_regions localeconst_memory) = Some (gd 65616 65760) /\
  object_region 65584 (m_regions localeconst_memory) = Some (gd 65584 65600) /\
  object_region 65776 (m_regions localeconst_memory) = Some (gd 65776 65784) /\
  all_agree localeconst_memory lc_fixture_ps /\ NoDup lc_fixture_ps.*1.
Proof.
  split_and!.
  - unfold lc_fit, lit_fit. vm_compute. split_and!; first [reflexivity | discriminate].
  - unfold localeconst_memory. vm_compute. reflexivity.
  - unfold localeconst_memory. vm_compute. reflexivity.
  - unfold localeconst_memory. vm_compute. reflexivity.
  - apply checked_pieces_all_agree. unfold localeconst_memory. vm_compute. reflexivity.
  - apply lc_ps_nodup. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(** ## Controls

    A check that cannot fail proves nothing. Each lemma below feeds the
    checks a wrong value and shows that they reject it: a name that
    starts one byte early, a position of 52, a name one letter short, a
    space in place of the terminator, swapped symbols and a table object
    that is too small. *)

(** At offset 51 the words have the name's shape, and at offset 50 they
    do not. *)
Lemma lc_offset_refused :
  str_shape_b (mkPtr (65616 + 51) (Ro 65616)) 65616 (gd 65616 65760) lc_words lc_messages = true /\
  str_shape_b (mkPtr (65616 + 50) (Ro 65616)) 65616 (gd 65616 65760) lc_words lc_messages = false.
Proof. vm_compute. split; reflexivity. Qed.

(** The image does not hold 52 in byte 5 of the offsets. *)
Lemma lc_index_refused :
  forallb (fun lv => bool_decide (checked_piece localeconst_memory lv.1 lv.2)) (lc_idx_ps 65584 (gd 65584 65600)) = true /\
  forallb (fun lv => bool_decide (checked_piece localeconst_memory lv.1 lv.2))
    [(PLive 65584, VLive (gd 65584 65600)); (PByte 65584 5, VByte 52)] = false.
Proof. unfold localeconst_memory. vm_compute. split; reflexivity. Qed.

(** A name cut short by one letter is refused, because the reader finds
    a letter where it needs the terminator. *)
Lemma lc_truncated_refused :
  str_shape_b (mkPtr (65616 + 51) (Ro 65616)) 65616 (gd 65616 65760) lc_words (removelast lc_messages) = false.
Proof. vm_compute. reflexivity. Qed.

(** The image does not hold a space where the name's terminator is. *)
Lemma lc_nul_refused :
  forallb (fun lv => bool_decide (checked_piece localeconst_memory lv.1 lv.2))
    ((PLive 65616, VLive (gd 65616 65760)) :: words_ps 65616 48 [4993752304466281805; 5485475903150576467]) = false.
Proof. unfold localeconst_memory. vm_compute. reflexivity. Qed.

(** The table and the offsets cannot trade symbols. *)
Lemma lc_swap_refused : ~ lc_at localeconst_globals 65584 65616 65776.
Proof. intros (H & _). vm_compute in H. discriminate. Qed.

(** A table object that ends before the name's second word does not fit,
    and the image does not hold the table in it. *)
Lemma lc_short_refused :
  ~ lc_fit 65616 (gd 65616 65656) 65584 (gd 65584 65600) 65776 (gd 65776 65784) /\
  forallb (fun lv => bool_decide (checked_piece localeconst_memory lv.1 lv.2)) (lc_name_ps 65616 (gd 65616 65656)) = false.
Proof.
  split; [intros ((_ & _ & H & _) & _); vm_compute in H; apply H; reflexivity|].
  unfold localeconst_memory. vm_compute. reflexivity.
Qed.
