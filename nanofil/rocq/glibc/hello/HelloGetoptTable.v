(** Hello passes getopt_long the option string "g:t" and a table of four
    long options. The rule for the call needs read-only ownership of that
    table and of the option names, laid out the way glibc reads them. The
    startup promise of Hello only shares each literal as some string, which
    names neither the table's cells nor its bytes. This file states the
    ownership that the call needs as lists of loader pieces. It checks that
    the pieces agree with the loader image of Hello, and it turns them into
    the option table and the strings. It does not say that startup hands
    those pieces over. *)

From Glibc Require Import ImageData LongOption LongOptionTable.
From Glibc Require Import LiteralWords LiteralLogic.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv WordString StrlenLogic
   GetoptInitial HelloImage_hello.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Import FileInv Fix.ML0 Fix.LG0.

(** ## Pieces of an option table

    An entry of glibc's table is 32 bytes long. The name pointer, the flag
    pointer and their capabilities, the argument kind and the value make up
    the pieces that getopt reads. Padding is not claimed. A null name after
    the entries ends the table. *)

(** These are the read pieces of the entry x at offset o of the object tb. *)
Definition entry_ps (tb o : Z) (x : lopt) : list (piece * pval) :=
  ((PAux tb o, VAux (ptr_cap (lo_name x))) :: cell tb o (ptr_addr (lo_name x))) ++
  byte_ps tb (o + 8) (le_bytes (lo_has x) 4) ++
  ((PAux tb (o + 16), VAux (ptr_cap (lo_flag x))) :: cell tb (o + 16) (ptr_addr (lo_flag x))) ++
  byte_ps tb (o + 24) (le_bytes (lo_val x) 4).

(** These are the pieces of the entries os from offset o on. *)
Fixpoint entries_ps (tb o : Z) (os : list lopt) : list (piece * pval) :=
  match os with
  | [] => []
  | x :: r => entry_ps tb o x ++ entries_ps tb (o + 32) r
  end.

(** The table owns its object's life, its entries and its null name. *)
Definition table_ps (tb : Z) (treg : region) (os : list lopt) : list (piece * pval) :=
  [(PLive tb, VLive treg)] ++ entries_ps tb 0 os ++
  ((PAux tb (32 * Z.of_nat (List.length os)), VAux CNone) :: cell tb (32 * Z.of_nat (List.length os)) 0).

(** ## Hello's options

    Hello's table names four options: greeting, traditional, help and
    version. Only greeting takes an argument, and its value is 103, the
    code of 'g'. No entry stores its value through a flag. The definitions below give those entries
    for any placement of the four names. *)

(** The call reads five strings. The first option is "greeting". *)
Definition s_greeting : list Z := [103; 114; 101; 101; 116; 105; 110; 103].
(** The second option is "traditional". *)
Definition s_traditional : list Z := [116; 114; 97; 100; 105; 116; 105; 111; 110; 97; 108].
(** The third option is "help". *)
Definition s_help : list Z := [104; 101; 108; 112].
(** The fourth option is "version". *)
Definition s_version : list Z := [118; 101; 114; 115; 105; 111; 110].
(** The option string is "g:t". *)
Definition s_optstring : list Z := [103; 58; 116].

(** These are Hello's four entries, with names at the pointers n1 to n4. *)
Definition hello_los (n1 n2 n3 n4 : ptr) : list lopt :=
  [mkLopt n1 s_greeting 1 null 103; mkLopt n2 s_traditional 0 null 116;
   mkLopt n3 s_help 0 null 128; mkLopt n4 s_version 0 null 129].

(** The option string "g:t" and the table of hello's options make 103,
    the code of 'g', such a code. The table has four entries, and only
    the first one, with value 103, takes an argument. *)
Lemma str_code_g los :
  List.map (fun y => (lo_has y, lo_flag y, lo_val y)) los =
    [(1, null, 103); (0, null, 116); (0, null, 128); (0, null, 129)] ->
  str_code (drop (opt_skip [103; 58; 116]) [103; 58; 116]) los 103.
Proof.
  intros Hm. cbn. split_and!; try discriminate.
  - intros k Hk H58 H59 Hc. destruct k as [|[|[|k]]]; cbn in *; try lia; try (split; congruence).
    vm_compute in Hc. discriminate.
  - intros y Hy Hf Hv. apply list_elem_of_In in Hy.
    apply (in_map (fun y => (lo_has y, lo_flag y, lo_val y))) in Hy. rewrite Hm in Hy. cbn in Hy.
    destruct Hy as [Hy | [Hy | [Hy | [Hy | []]]]]; injection Hy as Hh _ Hval; try (symmetry; exact Hh);
      rewrite <- Hval in Hv; vm_compute in Hv; discriminate.
Qed.

(** The getopt_long rule asks four things of a table, and Hello's table
    meets them. Its entries store no flag, it is short, and no value is
    -1. The option code 103 always comes back with a string. *)
Lemma hello_los_facts n1 n2 n3 n4 (F : list ptr) :
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) (hello_los n1 n2 n3 n4) /\
  (List.length (hello_los n1 n2 n3 n4) < 2 ^ 31)%Z /\ no_neg1_val (hello_los n1 n2 n3 n4) /\
  str_code (drop (opt_skip s_optstring) s_optstring) (hello_los n1 n2 n3 n4) 103.
Proof.
  split_and!.
  - repeat apply Forall_cons_2; try apply Forall_nil_2; left; reflexivity.
  - cbn. lia.
  - unfold no_neg1_val. repeat apply Forall_cons_2; try apply Forall_nil_2; right; cbn; discriminate.
  - apply str_code_g. reflexivity.
Qed.

(** ## Agreement with the loader image

    The standalone fixture loads just the table and the five strings
    from the generated Hello object. This check exercises their bytes
    and relocations without loading the full glibc image. The startup
    proof checks the same pieces separately at the linked addresses. *)

(** The loader resolves the table's name pointers to the generated strings. *)
Local Definition hello_image : mem :=
  match initial_memory [item_hello'23parse_options'2elongopts'2e64;
    item_hello'23str'2e65; item_hello'23str'2e66; item_hello'23str'2e67;
    item_hello'23str'2e68; item_hello'23str'2e69] with
  | Some (_, m) => m | None => empty_mem
  end.

(** This is Hello's table with its names at the loader's addresses. *)
Definition hello_fixture_los : list lopt :=
  hello_los (mkPtr 65712 (Ro 65712)) (mkPtr 65744 (Ro 65744)) (mkPtr 65776 (Ro 65776)) (mkPtr 65808 (Ro 65808)).

(** These are all the pieces that the call reads, at the loader's
    addresses. *)
Definition hello_getopt_ps : list (piece * pval) :=
  table_ps 65536 (gd 65536 65696) hello_fixture_los ++
  lit_ps 65712 (gd 65712 65728) (lit_words s_greeting) ++
  lit_ps 65744 (gd 65744 65760) (lit_words s_traditional) ++
  lit_ps 65776 (gd 65776 65784) (lit_words s_help) ++
  lit_ps 65808 (gd 65808 65816) (lit_words s_version) ++
  lit_ps 65840 (gd 65840 65848) (lit_words s_optstring).

(** These definitions list the same pieces at any bases. The table lies at
    tb, the four names lie at b1 to b4 and the option string lies at b5. *)
Definition hello_tab_ps (tb : Z) (treg : region) (b1 b2 b3 b4 b5 : Z) (r1 r2 r3 r4 r5 : region) :
    list (piece * pval) :=
  table_ps tb treg (hello_los (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4))) ++
  lit_ps b1 r1 (lit_words s_greeting) ++ lit_ps b2 r2 (lit_words s_traditional) ++
  lit_ps b3 r3 (lit_words s_help) ++ lit_ps b4 r4 (lit_words s_version) ++ lit_ps b5 r5 (lit_words s_optstring).

(** Every piece agrees with the loader image. *)
Lemma hello_getopt_agrees : all_agree hello_image hello_getopt_ps.
Proof. apply checked_pieces_all_agree. vm_compute. reflexivity. Qed.

(** The pieces have distinct keys, so a heap can own them together. *)
Lemma hello_getopt_distinct : NoDup hello_getopt_ps.*1.
Proof.
  apply (NoDup_fmap_1 (fun p => match p with
    | PLive b => 4 * 512 * b | PByte b o => 4 * (512 * b + o) + 1
    | PAux b o => 4 * (512 * b + o) + 2 | _ => 3 end)).
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(** ## Literals at glibc's addresses

    getopt also reads three strings of its own: "--", "-" and "-W ". The
    loader image of the getopt module puts them at the read-only objects
    below. That image is laid out on its own, so these addresses are not
    the ones in a program that links Hello with glibc. *)

(** These pieces hold getopt's three strings in the image of its module. *)
Definition getopt_lit_ps : list (piece * pval) :=
  lit_ps 66176 (gd 66176 66184) (lit_words [45; 45]) ++ lit_ps 66208 (gd 66208 66216) (lit_words [45]) ++
  lit_ps 66352 (gd 66352 66360) (lit_words [45; 87; 32]).

(** The getopt module's loader puts the strings at those objects. *)
Lemma getopt_lit_layout :
  Term.lookup (TAtom "glibc_getopt#str.146") getopt_globals = Some (mkPtr 66176 (Ro 66176)) /\
  Term.lookup (TAtom "glibc_getopt#str.147") getopt_globals = Some (mkPtr 66208 (Ro 66208)) /\
  Term.lookup (TAtom "glibc_getopt#str.150") getopt_globals = Some (mkPtr 66352 (Ro 66352)).
Proof. vm_compute. split_and!; reflexivity. Qed.

(** Every piece agrees with that image. *)
Lemma getopt_lit_agrees : all_agree getopt_memory getopt_lit_ps.
Proof. apply checked_pieces_all_agree. unfold getopt_memory. vm_compute. reflexivity. Qed.

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** ## Building the table and the strings from pieces

    The getopt rule shares the table and the strings read-only. The lemmas
    below freeze owned pieces into that form: first a literal, then the
    entries of any table, then Hello's own placement. *)

(** The shared pieces of the entries from offset o on, with the names'
    strings, make the entries of the table. *)
Lemma entries_own tb o os :
  Forall (fun x => 0 <= lo_has x < 2 ^ 32 /\ 0 <= lo_val x < 2 ^ 32) os ->
  ptsq DfracDiscarded (entries_ps tb o os) -∗ ([∗ list] x ∈ os, word_string DfracDiscarded (lo_name x) (lo_str x)) -∗
  [∗ list] k ↦ x ∈ os, opt_entry tb (o + 32 * Z.of_nat k) x.
Proof using Type.
  revert o. induction os as [|x r IH]; intros o Hr; [by iIntros|].
  inversion Hr as [|? ? [Hh Hv] Hr']; subst. cbn [entries_ps]. rewrite /entry_ps !ptsq_app.
  iIntros "((Hn & Hh & Hf & Hv) & Hr) [Hw Hws]". rewrite big_sepL_cons. iSplitL "Hn Hh Hf Hv Hw".
  - rewrite Z.add_0_r. unfold opt_entry, pcellq, int_cellq, bytesq, int_bytes.
    iFrame "Hn Hw Hf". iSplitL "Hh"; [by iSplit | by iSplit].
  - iDestruct (IH (o + 32) Hr' with "Hr Hws") as "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k y _) "H". by replace (o + 32 * Z.of_nat (S k)) with (o + 32 + 32 * Z.of_nat k) by lia.
Qed.

(** Frozen shares of any table's pieces at a read-only object, with the
    names' strings, form the option table that getopt reads. *)
Lemma table_view tb treg os :
  0 < tb -> tb mod 8 = 0 -> tb + 32 * Z.of_nat (List.length os) + 8 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  Forall (fun x => 0 <= lo_has x < 2 ^ 32 /\ 0 <= lo_val x < 2 ^ 32) os ->
  ptsq DfracDiscarded (table_ps tb treg os) -∗ ([∗ list] x ∈ os, word_string DfracDiscarded (lo_name x) (lo_str x)) -∗
  opt_table (mkPtr tb (Ro tb)) os.
Proof using Type.
  intros Hb H8 Hfit Hsp Hr. iIntros "#H #Hws". rewrite /table_ps !ptsq_app.
  iDestruct "H" as "(Hl & He & Ht)". iExists tb, treg. cbn [ptr_addr ptr_cap].
  iSplit; [iPureIntro; split_and!; [right; reflexivity | lia | lia | exact H8 | lia | exact Hsp] |].
  iSplitL "Hl"; [iExact "Hl"|]. rewrite Z.sub_diag. iSplitL "He".
  - iApply (entries_own with "He Hws"). exact Hr.
  - iExact "Ht".
Qed.

(** The owned pieces of any table at a read-only object, with the names'
    strings, make the shared option table. *)
Lemma table_own tb treg os :
  0 < tb -> tb mod 8 = 0 -> tb + 32 * Z.of_nat (List.length os) + 8 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  Forall (fun x => 0 <= lo_has x < 2 ^ 32 /\ 0 <= lo_val x < 2 ^ 32) os ->
  pts (table_ps tb treg os) -∗ ([∗ list] x ∈ os, word_string DfracDiscarded (lo_name x) (lo_str x)) ==∗
  opt_table (mkPtr tb (Ro tb)) os.
Proof using Type.
  intros. iIntros "H #Hws". rewrite pts_ptsq.
  iMod (ptsq_persist with "H") as "#H". iModIntro. iApply (table_view with "H Hws"); assumption.
Qed.

(** A C string ends at its first zero byte, so a byte list that holds a
    zero starts with a string. *)
Lemma cstr_prefix (bs : list Z) : Forall (fun c => 0 <= c < 256) bs -> 0 ∈ bs ->
  exists s, take (S (List.length s)) bs = s ++ [0] /\ Forall (fun c => 0 < c < 256) s /\
    (List.length s < List.length bs)%nat.
Proof using Type*.
  induction bs as [|c bs IH]; intros Hr Hz; [inversion Hz|].
  inversion Hr as [|? ? Hc Hr']; subst.
  destruct (decide (c = 0)) as [->|Hne].
  - exists []. cbn. split_and!; [reflexivity | constructor | lia].
  - inversion Hz as [|? ? ? Hz']; subst; [congruence|].
    destruct (IH Hr' Hz') as (s & Hs & Hc' & Hl). exists (c :: s). cbn [List.length take app]. rewrite Hs.
    split_and!; [reflexivity | constructor; [lia | exact Hc'] | cbn; lia].
Qed.

(** A word below 2^48 has zero top bytes, so its bytes up to the first
    zero form a string of at most seven characters in that one word. *)
Lemma word_cstr_shape tb treg w : 0 < tb -> tb mod 8 = 0 -> tb + 8 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  0 <= w < 2 ^ 48 -> exists s, str_shape (mkPtr tb (Ro tb)) tb treg [w] s.
Proof using Type*.
  intros Hb H8 Hfit Hsp Hw.
  assert (H7 : byte_of w 7 = 0) by (unfold byte_of; rewrite Z.div_small; [reflexivity | lia]).
  destruct (cstr_prefix (wbytes [w])) as (s & Hs & Hc & Hl).
  - rewrite wbytes_cons. apply Forall_app. split; [|cbn; constructor].
    apply Forall_forall. intros c Hc. apply list_elem_of_fmap in Hc as (k & -> & _).
    unfold byte_of. pose proof (Z.mod_pos_bound (w / 2 ^ (8 * k)) 256 ltac:(lia)). lia.
  - rewrite wbytes_cons. apply elem_of_app. left. apply list_elem_of_fmap. exists 7.
    split; [symmetry; exact H7 | apply (bool_decide_unpack _); vm_compute; exact I].
  - rewrite wbytes_length in Hl. cbn [List.length] in Hl.
    assert (Hst : wstart (mkPtr tb (Ro tb)) = tb) by (unfold wstart; cbn; lia).
    exists s. split; cbn [ptr_addr ptr_cap].
    + right. reflexivity.
    + exact Hb.
    + exact H8.
    + lia.
    + rewrite Hst. cbn [List.length]. lia.
    + exact Hsp.
    + rewrite H8 Z.add_0_l. cbn [List.length].
      apply (Z.div_unique _ _ _ (Z.of_nat (List.length s))); lia.
    + constructor; [lia | constructor].
    + rewrite H8. cbn [Z.to_nat drop]. exact Hs.
    + exact Hc.
Qed.

(** The frozen pieces of a table also hold a string at its start: the
    bytes of the first name's address, up to its first zero byte. This is
    the share that Hello's read-only literals ask for, and it comes from
    the same pieces as the table, not from a second copy. *)
Lemma table_str tb treg x os :
  0 < tb -> tb mod 8 = 0 -> tb + 8 <= r_end treg -> r_end treg <= 2 ^ 48 -> 0 <= ptr_addr (lo_name x) < 2 ^ 48 ->
  ptsq DfracDiscarded (table_ps tb treg (x :: os)) ⊢ ∃ s, word_string DfracDiscarded (mkPtr tb (Ro tb)) s.
Proof using Type.
  intros Hb H8 Hfit Hsp Hw.
  destruct (word_cstr_shape tb treg (ptr_addr (lo_name x)) Hb H8 Hfit Hsp Hw) as [s Hs].
  rewrite /table_ps. iIntros "H". iDestruct (ptsq_app with "H") as "[Hl H]".
  iDestruct (ptsq_app with "H") as "[He _]". iDestruct (ptsq_app _ (entry_ps tb 0 x) with "He") as "[He _]".
  iDestruct (ptsq_app _ ((PAux tb 0, VAux (ptr_cap (lo_name x))) :: cell tb 0 (ptr_addr (lo_name x)))
    with "He") as "[He _]".
  iDestruct (ptsq_app _ [_] with "He") as "[_ Hc]".
  iExists s, tb, treg, [ptr_addr (lo_name x)]. iSplit; [iPureIntro; exact Hs|].
  replace (wstart (mkPtr tb (Ro tb)) - tb) with 0 by (unfold wstart; cbn; lia).
  rewrite /wwin. cbn [words_ps]. rewrite app_nil_r. iSplitL "Hl"; [iExact "Hl" | iExact "Hc"].
Qed.

(** Hello's table and option string can be shared as the getopt_long rule
    needs, wherever the names and the table lie. Each object must start
    at an 8-byte boundary and hold its words below 2^48. *)
Lemma hello_table_own_ro tb treg (b1 b2 b3 b4 b5 : Z) (r1 r2 r3 r4 r5 : region) :
  0 < tb -> tb mod 8 = 0 -> tb + 136 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  0 < b1 -> b1 mod 8 = 0 -> b1 + 16 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 16 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  0 < b4 -> b4 mod 8 = 0 -> b4 + 8 <= r_end r4 -> r_end r4 <= 2 ^ 48 ->
  0 < b5 -> b5 mod 8 = 0 -> b5 + 8 <= r_end r5 -> r_end r5 <= 2 ^ 48 ->
  pts (table_ps tb treg (hello_los (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4)))) -∗
  pts (lit_ps b1 r1 (lit_words s_greeting)) -∗ pts (lit_ps b2 r2 (lit_words s_traditional)) -∗
  pts (lit_ps b3 r3 (lit_words s_help)) -∗ pts (lit_ps b4 r4 (lit_words s_version)) -∗
  pts (lit_ps b5 r5 (lit_words s_optstring)) ==∗
  opt_table (mkPtr tb (Ro tb)) (hello_los (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4))) ∗
  word_string DfracDiscarded (mkPtr b5 (Ro b5)) s_optstring ∗ ∃ s, word_string DfracDiscarded (mkPtr tb (Ro tb)) s.
Proof using Type.
  intros. iIntros "Ht H1 H2 H3 H4 H5".
  iMod (lit_own with "H1") as "#H1"; try (assumption || reflexivity).
  iMod (lit_own with "H2") as "#H2"; try (assumption || reflexivity).
  iMod (lit_own with "H3") as "#H3"; try (assumption || reflexivity).
  iMod (lit_own with "H4") as "#H4"; try (assumption || reflexivity).
  iMod (lit_own with "H5") as "#H5"; try (assumption || reflexivity).
  rewrite pts_ptsq. iMod (ptsq_persist with "Ht") as "#Ht". iModIntro.
  iSplitR; [|iSplitR; [iExact "H5"|]].
  - iApply (table_view with "Ht [ ]"); try (assumption || cbn; lia).
    + repeat constructor; cbn; lia.
    + cbn. iFrame "H1 H2 H3 H4".
  - iApply (table_str tb treg (mkLopt (mkPtr b1 (Ro b1)) s_greeting 1 null 103) with "Ht"); cbn; lia.
Qed.

(** Hello's table and option string can be built from their pieces. *)
Lemma hello_table_own tb treg (b1 b2 b3 b4 b5 : Z) (r1 r2 r3 r4 r5 : region) :
  0 < tb -> tb mod 8 = 0 -> tb + 136 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  0 < b1 -> b1 mod 8 = 0 -> b1 + 16 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 16 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  0 < b4 -> b4 mod 8 = 0 -> b4 + 8 <= r_end r4 -> r_end r4 <= 2 ^ 48 ->
  0 < b5 -> b5 mod 8 = 0 -> b5 + 8 <= r_end r5 -> r_end r5 <= 2 ^ 48 ->
  pts (table_ps tb treg (hello_los (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4)))) -∗
  pts (lit_ps b1 r1 (lit_words s_greeting)) -∗ pts (lit_ps b2 r2 (lit_words s_traditional)) -∗
  pts (lit_ps b3 r3 (lit_words s_help)) -∗ pts (lit_ps b4 r4 (lit_words s_version)) -∗
  pts (lit_ps b5 r5 (lit_words s_optstring)) ==∗
  opt_table (mkPtr tb (Ro tb)) (hello_los (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4))) ∗
  word_string DfracDiscarded (mkPtr b5 (Ro b5)) s_optstring.
Proof using Type.
  intros. iIntros "Ht H1 H2 H3 H4 H5".
  iMod (hello_table_own_ro with "Ht H1 H2 H3 H4 H5") as "(Ht & H5 & _)"; try assumption.
  iModIntro. iSplitL "Ht"; [iExact "Ht" | iExact "H5"].
Qed.

(** At the loader's addresses, the pieces checked above give the table
    and the option string. *)
Lemma hello_getopt_own :
  pts hello_getopt_ps ==∗
  opt_table (mkPtr 65536 (Ro 65536)) hello_fixture_los ∗ word_string DfracDiscarded (mkPtr 65840 (Ro 65840)) s_optstring.
Proof using Type.
  rewrite /hello_getopt_ps. iIntros "H".
  iDestruct (pts_app with "H") as "[Ht H]". iDestruct (pts_app with "H") as "[H1 H]".
  iDestruct (pts_app with "H") as "[H2 H]". iDestruct (pts_app with "H") as "[H3 H]".
  iDestruct (pts_app with "H") as "[H4 H5]".
  iApply (hello_table_own with "Ht H1 H2 H3 H4 H5"); cbn; (reflexivity || lia).
Qed.

(** The pieces of getopt's three strings also make read-only strings. This
    holds at any read-only objects that start at 8-byte boundaries. *)
Lemma getopt_lits_own b1 b2 b3 (r1 r2 r3 : region) :
  0 < b1 -> b1 mod 8 = 0 -> b1 + 8 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 8 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  pts (lit_ps b1 r1 (lit_words [45; 45])) -∗ pts (lit_ps b2 r2 (lit_words [45])) -∗
  pts (lit_ps b3 r3 (lit_words [45; 87; 32])) ==∗
  word_string DfracDiscarded (mkPtr b1 (Ro b1)) [45; 45] ∗ word_string DfracDiscarded (mkPtr b2 (Ro b2)) [45] ∗
  word_string DfracDiscarded (mkPtr b3 (Ro b3)) [45; 87; 32].
Proof using Type.
  intros. iIntros "H1 H2 H3".
  iMod (lit_own with "H1") as "#H1"; try (assumption || reflexivity).
  iMod (lit_own with "H2") as "#H2"; try (assumption || reflexivity).
  iMod (lit_own with "H3") as "#H3"; try (assumption || reflexivity).
  iModIntro. iFrame "H1 H2 H3".
Qed.

End own.

(** The pieces can be allocated from the image rather than assumed, so
    the ownership above can be built. This does not build the rest of the
    program's ownership. *)
Lemma hello_getopt_allocatable Σ `{!gen_heapGpreS piece pval Σ} :
  ⊢ |==> ∃ Hh : gen_heapGS piece pval Σ,
    @opt_table Σ Hh (mkPtr 65536 (Ro 65536)) hello_fixture_los ∗
    @word_string Σ Hh DfracDiscarded (mkPtr 65840 (Ro 65840)) s_optstring.
Proof.
  iMod (gen_heap_init (list_to_map hello_getopt_ps : gmap piece pval)) as (Hh) "(_ & Hpts & _)".
  iExists Hh. iApply hello_getopt_own.
  rewrite /pts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v));
    [iExact "Hpts" | exact hello_getopt_distinct].
Qed.
