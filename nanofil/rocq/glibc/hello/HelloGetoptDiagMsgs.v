From Glibc Require Import GlibcProgram.
(** When getopt reports a bad option, it passes one of nine format
    strings to gettext and then to the printer. The diagnostic rules in
    HelloGetoptDiagGettext.v, HelloGetoptDiagTcb.v and HelloGetoptDiagLock.v
    take a resource Lm that lends a lifetime share of each of those
    strings, and they leave Lm as a parameter. This file builds such an
    Lm from loader pieces. It freezes the pieces of the nine literals into
    persistent strings, and it proves that those strings lend what both
    diagnostic rules ask for when a symbol table places them.

    The file also checks the pieces against the loader image of the getopt
    module alone. They agree with that image, and their keys are distinct
    from the keys of the parser's starting pieces in HelloGetoptStart.v.
    This does not show that a program linking Hello with glibc puts the
    strings at these addresses, and it does not show that startup hands
    the pieces over. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv WordString GetoptModule GetoptInitial GetoptDiag GetoptLongDiag
  HelloGetoptTable HelloGetoptStart HelloGetoptDiagGettext.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Import FileInv FileInv.ML FileInv.LG.

(** ## The nine messages

    getopt prints a message when a user gives it an option it does not
    know or leaves out a required argument. Short options use two
    messages and long options use five, and an ambiguous long option also
    prints each candidate and then a newline. The byte lists below spell
    those nine strings without their terminators, as the getopt module's
    data holds them. *)

(** This is message 138, "%s: option '%s%s' is ambiguous\n". *)
Definition t138 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 32; 105; 115; 32;
   97; 109; 98; 105; 103; 117; 111; 117; 115; 10].

(** Message 139 is the heading that getopt prints before it lists the
    candidates of an ambiguous option. *)
Definition t139 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 32; 105; 115; 32;
   97; 109; 98; 105; 103; 117; 111; 117; 115; 59; 32; 112; 111; 115; 115; 105; 98; 105; 108; 105;
   116; 105; 101; 115; 58].

(** This is message 140, " '%s%s'". *)
Definition t140 : list Z :=
  [32; 39; 37; 115; 37; 115; 39].

(** This is message 141, "\n". *)
Definition t141 : list Z :=
  [10].

(** This is message 142, "%s: unrecognized option '%s%s'\n". *)
Definition t142 : list Z :=
  [37; 115; 58; 32; 117; 110; 114; 101; 99; 111; 103; 110; 105; 122; 101; 100; 32; 111; 112; 116;
   105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 10].

(** This is message 143, "%s: option '%s%s' doesn't allow an argument\n". *)
Definition t143 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 32; 100; 111; 101;
   115; 110; 39; 116; 32; 97; 108; 108; 111; 119; 32; 97; 110; 32; 97; 114; 103; 117; 109; 101;
   110; 116; 10].

(** This is message 144, "%s: option '%s%s' requires an argument\n". *)
Definition t144 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 39; 37; 115; 37; 115; 39; 32; 114; 101; 113;
   117; 105; 114; 101; 115; 32; 97; 110; 32; 97; 114; 103; 117; 109; 101; 110; 116; 10].

(** This is message 148, "%s: invalid option -- '%c'\n". *)
Definition t148 : list Z :=
  [37; 115; 58; 32; 105; 110; 118; 97; 108; 105; 100; 32; 111; 112; 116; 105; 111; 110; 32; 45; 45;
   32; 39; 37; 99; 39; 10].

(** This is message 149, "%s: option requires an argument -- '%c'\n". *)
Definition t149 : list Z :=
  [37; 115; 58; 32; 111; 112; 116; 105; 111; 110; 32; 114; 101; 113; 117; 105; 114; 101; 115; 32;
   97; 110; 32; 97; 114; 103; 117; 109; 101; 110; 116; 32; 45; 45; 32; 39; 37; 99; 39; 10].

(** These are the symbols of the nine strings, in the order of the texts
    below. *)
Definition dgx_msg_names : list string :=
  ["glibc_getopt#str.138"; "glibc_getopt#str.139"; "glibc_getopt#str.140"; "glibc_getopt#str.141";
   "glibc_getopt#str.142"; "glibc_getopt#str.143"; "glibc_getopt#str.144"; "glibc_getopt#str.148";
   "glibc_getopt#str.149"]%string.

(** These are the nine texts in the same order. *)
Definition dgx_msg_texts : list (list Z) := [t138; t139; t140; t141; t142; t143; t144; t148; t149].

(** Each text has checked words. *)
Lemma dgx_msg_texts_ok : Forall (fun s => lit_ok s = true) dgx_msg_texts.
Proof.
  assert (H : forallb lit_ok dgx_msg_texts = true) by (vm_compute; reflexivity).
  apply Forall_forall. intros s Hs. rewrite forallb_forall in H. apply H, list_elem_of_In, Hs.
Qed.

(** The loader writes each string into its own object. This function
    lists the pieces that hold the texts ts in the objects bs, taking one
    literal after another. *)
Definition lits_ps (bs : list (Z * region)) (ts : list (list Z)) : list (piece * pval) :=
  List.concat (zip_with (fun br s => lit_ps br.1 br.2 (lit_words s)) bs ts).

(** These are the pieces of the nine messages at the objects bs. *)
Definition dgx_msg_ps (bs : list (Z * region)) : list (piece * pval) := lits_ps bs dgx_msg_texts.

(** A symbol table places the messages at bs when each symbol names the
    read-only object at the matching base. *)
Definition dgx_msg_at (gs : list (name * ptr)) (bs : list (Z * region)) : Prop :=
  Forall2 (fun n br => Term.lookup (TAtom n) gs = Some (mkPtr br.1 (Ro br.1))) dgx_msg_names bs.

(** A literal fits its object when the object starts at a positive 8-byte
    boundary and holds all its words below the top of the address space. *)
Definition lit_fit (br : Z * region) (s : list Z) : Prop :=
  0 < br.1 /\ br.1 mod 8 = 0 /\ br.1 + 8 * Z.of_nat (List.length (lit_words s)) <= r_end br.2 /\
  r_end br.2 <= 2 ^ 48.

(** ## Distinct keys

    The keys of a literal's pieces all belong to its base, so literals at
    distinct bases have disjoint keys. This proof works on the structure of
    the lists, so it never decides distinctness over all the bytes. *)

(** Every key of a literal's pieces belongs to its base. *)
Lemma lit_ps_ids b reg ws k : k ∈ (lit_ps b reg ws).*1 -> piece_id k = b.
Proof.
  cbn [lit_ps fmap list_fmap fst]. rewrite (words_ps_keys b 0 ws).
  intros [->|Hk]%elem_of_cons; [done|]. apply list_elem_of_fmap in Hk as (o & -> & _). done.
Qed.

(** Literals at distinct bases have distinct keys, and each key belongs to
    one of the bases. *)
Lemma lits_ps_keys bs ts : NoDup bs.*1 ->
  NoDup (lits_ps bs ts).*1 /\ forall k, k ∈ (lits_ps bs ts).*1 -> piece_id k ∈ bs.*1.
Proof.
  unfold lits_ps. revert ts. induction bs as [|[b reg] bs IH]; intros [|s ts] Hnd.
  - split; [constructor | intros k Hk; inversion Hk].
  - split; [constructor | intros k Hk; inversion Hk].
  - split; [constructor | intros k Hk; inversion Hk].
  - cbn [zip_with List.concat fmap list_fmap fst] in *. apply NoDup_cons in Hnd as [Hb Hnd].
    destruct (IH ts Hnd) as [IHn IHk]. rewrite fmap_app. split.
    + apply NoDup_app. split_and!; [apply lit_ps_nodup| |exact IHn].
      intros k Hk1 Hk2. apply lit_ps_ids in Hk1. apply IHk in Hk2. rewrite Hk1 in Hk2. exact (Hb Hk2).
    + intros k [Hk|Hk]%elem_of_app.
      * apply lit_ps_ids in Hk. rewrite Hk. apply elem_of_cons. by left.
      * apply elem_of_cons. right. exact (IHk k Hk).
Qed.

Section own.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## Frozen strings

    Lm holds the nine strings with discarded fractions, so it is
    persistent and a lender never runs out. *)

(** The messages placed at the objects bs are read-only strings, and
    this resource holds all nine. *)
Definition dgx_msgs (bs : list (Z * region)) : iProp Σ :=
  [∗ list] br; s ∈ bs; dgx_msg_texts, word_string DfracDiscarded (mkPtr br.1 (Ro br.1)) s.

#[global] Instance dgx_msgs_persistent bs : Persistent (dgx_msgs bs).
Proof. unfold dgx_msgs. apply _. Qed.

(** The pieces of fitting literals with checked words freeze into their
    strings. *)
Lemma lits_own bs ts : Forall2 lit_fit bs ts -> Forall (fun s => lit_ok s = true) ts ->
  pts (lits_ps bs ts) ==∗ [∗ list] br; s ∈ bs; ts, word_string DfracDiscarded (mkPtr br.1 (Ro br.1)) s.
Proof using Type.
  unfold lits_ps. induction 1 as [|[b reg] s bs ts Hf _ IH]; intros Hok; [by iIntros "_ !>"|].
  apply Forall_cons in Hok as [Hs Hok]. destruct Hf as (H0 & H8 & He & Hr).
  cbn [zip_with List.concat]. rewrite pts_app. iIntros "[H Hs]".
  iMod (lit_own with "H") as "#H"; try assumption. iMod (IH Hok with "Hs") as "Hs".
  iModIntro. rewrite big_sepL2_cons. iFrame "H Hs".
Qed.

(** Startup can hand over the raw pieces of the nine messages, and the
    rules want strings. When every object fits its message, the pieces
    freeze into those strings. HelloGetoptStart.v asks extra startup
    pieces for exactly this kind of frozen resource. *)
Lemma dgx_msgs_own bs : Forall2 lit_fit bs dgx_msg_texts -> pts (dgx_msg_ps bs) ==∗ □ dgx_msgs bs.
Proof using Type.
  intros Hf. iIntros "H". iMod (lits_own with "H") as "#H"; [exact Hf | exact dgx_msg_texts_ok|].
  iModIntro. iModIntro. iExact "H".
Qed.

(** ## Lending a message's lifetime

    Before printing a message, the printer checks that the message's
    object is still live. Each frozen string holds a copyable share of
    that liveness, so the resource can lend it and keep it at once. *)

(** A rule names its message by a symbol. When the symbol table places
    the messages at bs, the resource lends the lifetime of whichever of the
    nine strings a symbol names. *)
Lemma dgx_msgs_lend gs bs n p : dgx_msg_at gs bs -> n ∈ dgx_msg_names -> Term.lookup (TAtom n) gs = Some p ->
  dgx_msgs bs ⊢ ∃ dq reg, live_capq dq (ptr_cap p) reg ∗ (live_capq dq (ptr_cap p) reg -∗ dgx_msgs bs).
Proof using Type.
  intros Hat Hn Hp. apply list_elem_of_lookup_1 in Hn as (k & Hk).
  destruct (Forall2_lookup_l _ _ _ _ _ Hat Hk) as ([b reg] & Hb & Hl). rewrite Hp in Hl. injection Hl as ->.
  destruct (lookup_lt_is_Some_2 dgx_msg_texts k) as [s Hs].
  { pose proof (Forall2_length _ _ _ Hat) as E. pose proof (lookup_lt_Some _ _ _ Hb) as Hlt.
    unfold dgx_msg_texts. unfold dgx_msg_names in E. cbn [Datatypes.length] in *. lia. }
  iIntros "#H". iPoseProof "H" as "Hc". unfold dgx_msgs.
  iDestruct (big_sepL2_lookup with "Hc") as "Hw"; [exact Hb | exact Hs|].
  iDestruct "Hw" as (b' reg' ws Hsh) "[Hl _]". destruct (ss_cap _ _ _ _ _ Hsh) as [E|E]; [discriminate|].
  cbn in E. injection E as <-. iExists DfracDiscarded, reg'. cbn [ptr_cap live_capq]. rewrite /liveq.
  iSplitL "Hl"; [iExact "Hl"|]. iIntros "_". iExact "H".
Qed.

(** The rule for short options prints the strings str.148 and str.149,
    and the resource can lend both. *)
Lemma dgx_msgs_lends_diag g bs : dgx_msg_at (Semantics.ge_globals g) bs -> dgx_lends (dgx_msgs bs) (diag_msg g).
Proof.
  intros Hat fmt [H|H]; (eapply dgx_msgs_lend; [exact Hat| |exact H]); apply list_elem_of_In;
    cbn [In dgx_msg_names]; intuition.
Qed.

(** The rule for long options prints five messages. For an ambiguous
    option it also prints a candidate string and a newline, which it names
    f140 and f141. The resource lends all seven strings when the symbols
    str.140 and str.141 name f140 and f141. *)
Lemma dgx_msgs_lends_ldiag g bs f140 f141 : dgx_msg_at (Semantics.ge_globals g) bs ->
  Term.lookup (TAtom "glibc_getopt#str.140") (Semantics.ge_globals g) = Some f140 ->
  Term.lookup (TAtom "glibc_getopt#str.141") (Semantics.ge_globals g) = Some f141 ->
  dgx_lends (dgx_msgs bs) (fun p => ldiag_msg g p \/ p = f140 \/ p = f141).
Proof.
  intros Hat H140 H141 fmt [H | [-> | ->]].
  - apply List.Exists_exists in H as (n & Hin & Hn). eapply dgx_msgs_lend; [exact Hat| |exact Hn].
    apply list_elem_of_In. cbn [In] in Hin. cbn [In dgx_msg_names]. intuition.
  - eapply dgx_msgs_lend; [exact Hat| |exact H140]. apply list_elem_of_In. cbn [In dgx_msg_names]. intuition.
  - eapply dgx_msgs_lend; [exact Hat| |exact H141]. apply list_elem_of_In. cbn [In dgx_msg_names]. intuition.
Qed.

End own.

(** ## The getopt module's image

    The loader image of the getopt module alone puts the nine strings at
    the read-only objects below. A program that links Hello with glibc
    may put them elsewhere, which is why the lemmas above take any bases. *)

(** These are the objects of the nine strings in that image. *)
Definition dgx_msg_fixture : list (Z * region) :=
  [(65792, gd 65792 65824); (65840, gd 65840 65888); (65904, gd 65904 65912);
   (65936, gd 65936 65944); (65968, gd 65968 66000); (66016, gd 66016 66064);
   (66080, gd 66080 66120); (66240, gd 66240 66272); (66288, gd 66288 66336)].

(** The module's symbols name those objects. *)
Lemma dgx_msg_fixture_at : dgx_msg_at getopt_globals dgx_msg_fixture.
Proof. repeat (apply List.Forall2_cons; [vm_compute; reflexivity|]). apply List.Forall2_nil. Qed.

(** Each string fits its object. *)
Lemma dgx_msg_fixture_fit : Forall2 lit_fit dgx_msg_fixture dgx_msg_texts.
Proof.
  repeat (apply List.Forall2_cons; [unfold lit_fit; vm_compute; split_and!; first [reflexivity | discriminate]|]).
  apply List.Forall2_nil.
Qed.

(** Every piece of the nine strings agrees with the image. *)
Lemma dgx_msg_fixture_agrees : all_agree getopt_memory (dgx_msg_ps dgx_msg_fixture).
Proof. apply checked_pieces_all_agree. unfold getopt_memory. vm_cast_no_check (eq_refl true). Qed.

(** These are the bases of the parser's starting pieces in the image. *)
Definition getopt_start_fixture_ps : list (piece * pval) :=
  getopt_start_ps 65584 getopt_private_region 65696 (gd 65696 65704) 65760 (gd 65760 65768)
    66176 (gd 66176 66184) 66208 (gd 66208 66216) 66352 (gd 66352 66360).

(** The parser's starting pieces and the nine strings agree with the image
    together, and all their keys are distinct. The starting pieces already
    hold getopt's three option literals, so this also covers those. *)
Lemma dgx_msg_start_fixture :
  all_agree getopt_memory (getopt_start_fixture_ps ++ dgx_msg_ps dgx_msg_fixture) /\
  NoDup (getopt_start_fixture_ps ++ dgx_msg_ps dgx_msg_fixture).*1.
Proof.
  destruct getopt_start_fixture as [Ha Hn]. split.
  - apply all_agree_app. split; [exact Ha | exact dgx_msg_fixture_agrees].
  - assert (Hb : NoDup dgx_msg_fixture.*1) by (apply (bool_decide_unpack _); vm_compute; exact I).
    destruct (lits_ps_keys _ dgx_msg_texts Hb) as [Hm Hk].
    assert (Hs : forallb (fun k => bool_decide (piece_id k ∈ [65584; 65696; 65760; 66176; 66208; 66352]))
      getopt_start_fixture_ps.*1 = true) by (vm_compute; reflexivity).
    assert (Hd : Forall (fun z => z ∉ dgx_msg_fixture.*1) [65584; 65696; 65760; 66176; 66208; 66352])
      by (apply (bool_decide_unpack _); vm_compute; exact I).
    rewrite fmap_app. apply NoDup_app. split_and!; [exact Hn| |exact Hm].
    intros k Hk1 Hk2. rewrite forallb_forall in Hs. apply list_elem_of_In in Hk1.
    apply Hs, bool_decide_eq_true in Hk1. rewrite Forall_forall in Hd. exact (Hd _ Hk1 (Hk k Hk2)).
Qed.

(** The pieces can be allocated from the image rather than assumed, so Lm
    can be built at the image's addresses. *)
Lemma dgx_msgs_allocatable Σ `{!gen_heapGpreS piece pval Σ} :
  ⊢ |==> ∃ Hh : gen_heapGS piece pval Σ,
    @pts Σ Hh (dgx_msg_ps dgx_msg_fixture).
Proof.
  iMod (gen_heap_init (list_to_map (dgx_msg_ps dgx_msg_fixture) : gmap piece pval)) as (Hh) "(_ & Hpts & _)".
  iExists Hh. rewrite /pts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v)); [iExact "Hpts"|].
  apply lits_ps_keys. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Section fixture.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** This lemma shows that the general lemmas can be used at real
    addresses. In the getopt module's image, the message pieces become the
    nine strings, and a program that uses the module's symbols can lend
    every string that the two rules print. *)
Lemma dgx_msg_fixture_own g : Semantics.ge_globals g = getopt_globals ->
  (⊢ pts (dgx_msg_ps dgx_msg_fixture) ==∗ □ dgx_msgs dgx_msg_fixture) /\
  dgx_lends (dgx_msgs dgx_msg_fixture) (diag_msg g) /\
  dgx_lends (dgx_msgs dgx_msg_fixture)
    (fun p => ldiag_msg g p \/ p = mkPtr 65904 (Ro 65904) \/ p = mkPtr 65936 (Ro 65936)).
Proof.
  intros Eg. pose proof dgx_msg_fixture_at as Hat. rewrite -Eg in Hat. split_and!.
  - exact (dgx_msgs_own _ dgx_msg_fixture_fit).
  - exact (dgx_msgs_lends_diag g _ Hat).
  - apply (dgx_msgs_lends_ldiag g _ _ _ Hat); rewrite Eg; vm_compute; reflexivity.
Qed.

End fixture.

(** ## Controls

    The checks below show that the computations above can fail. A changed
    newline, a shortened object or a swapped symbol does not pass, and a
    supply that leaves out a message cannot be placed. *)

(** The image does not hold a different byte where the newline is. *)
Lemma dgx_msg_changed_refused :
  forallb (fun lv => bool_decide (checked_piece getopt_memory lv.1 lv.2))
    (lit_ps 65936 (gd 65936 65944) (lit_words [11])) = false.
Proof. unfold getopt_memory. vm_compute. reflexivity. Qed.

(** The image does not hold the ambiguity list's heading in a shorter
    object. *)
Lemma dgx_msg_region_refused :
  forallb (fun lv => bool_decide (checked_piece getopt_memory lv.1 lv.2))
    (lit_ps 65840 (gd 65840 65880) (lit_words t139)) = false.
Proof. unfold getopt_memory. vm_compute. reflexivity. Qed.

(** The symbols str.148 and str.149 cannot trade places. *)
Lemma dgx_msg_swap_refused :
  ~ dgx_msg_at getopt_globals (firstn 7 dgx_msg_fixture ++ [(66288, gd 66288 66336); (66240, gd 66240 66272)]).
Proof.
  intros H. pose proof (Forall2_lookup_lr _ _ _ 7 _ _ H eq_refl eq_refl) as E. vm_compute in E. discriminate.
Qed.

(** A supply without the newline cannot be placed. *)
Lemma dgx_msg_missing_refused : ~ dgx_msg_at getopt_globals (firstn 3 dgx_msg_fixture ++ skipn 4 dgx_msg_fixture).
Proof. intros H. apply Forall2_length in H. vm_compute in H. discriminate. Qed.
