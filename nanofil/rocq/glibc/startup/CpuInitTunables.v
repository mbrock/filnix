(** The call of `c: init_cpu_features` gives the tunable table back
    as one block, with a few bytes known. Later startup code reads
    single tunables through `c: __tunable_get_val`, whose contract
    owns one row at a time: its type code, its value and its
    `initialized` byte. This module takes those rows out of the block.

    The contract of [CpuInitSpec](CpuInitSpec.v) fixes the type codes
    and the cleared `initialized` bytes of the rows that later startup
    code reads. The value of a row is not fixed. It is whatever eight
    bytes the table holds, so each row comes out with some value v.
    The rest of the table stays owned as a remainder that no later
    proof needs to open. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic StringLogic MemLogic.
From Nanofil Require AbsRun AbsMem.
From Glibc Require Import FileInv OsBlocks OsWorld OsCpuid StartTunableGetValSpec CpuInitSpec.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** Later startup code reads these eleven rows. Each pair gives a row
    and its type code. *)
Definition icf_later_rows : list (Z * Z) :=
  [(14, 2); (15, 2); (17, 2); (18, 0); (19, 2); (21, 0); (22, 2); (23, 2); (24, 2); (25, 2); (27, 0)].

(** A row has three fields that a reader owns. Each pair gives the
    offset of a field in the table and its size in bytes. *)
Definition icf_row_fields (r : Z * Z) : list (Z * Z) :=
  [(fst r * 136 + 48, 4); (fst r * 136 + 88, 8); (fst r * 136 + 104, 1)].

(** ## Cutting windows out of a block

    A window is a range of bytes, given by its offset and its size.
    The lemmas of this section cut a list of windows out of an owned
    block of bytes. The windows must come in order and must not
    overlap. *)

(** The windows ws are in order from the offset o and end by e. *)
Fixpoint ordered (o e : Z) (ws : list (Z * Z)) : bool :=
  match ws with
  | [] => true
  | w :: ws' => (o <=? fst w) && (0 <=? snd w) && (fst w + snd w <=? e) && ordered (fst w + snd w) e ws'
  end.

(** A list from its element k on starts with that element. *)
Lemma drop_nth {A} (xs : list A) : forall k x, nth_error xs k = Some x -> drop k xs = x :: drop (S k) xs.
Proof. induction xs as [|y xs IH]; intros [|k] x H; cbn in *; try discriminate; [by injection H as -> | exact (IH k x H)]. Qed.

(** A window of a list equals ys when the list holds the elements of
    ys from the offset k on. *)
Lemma take_drop_known {A} (ys : list A) : forall xs k,
  (forall j y, nth_error ys j = Some y -> nth_error xs (k + j) = Some y) -> take (length ys) (drop k xs) = ys.
Proof.
  induction ys as [|y ys IH]; intros xs k H; cbn [length]; [reflexivity|].
  rewrite (drop_nth xs k y); [|rewrite -(Nat.add_0_r k); exact (H 0%nat y eq_refl)].
  cbn [take]. f_equal. apply IH. intros j z Hj. specialize (H (S j) z Hj). rewrite Nat.add_succ_r in H. exact H.
Qed.

Section split.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** This assertion owns the bytes of xs from the offset o on that lie
    outside the windows ws. *)
Fixpoint gaps (b o : Z) (ws : list (Z * Z)) (xs : list Z) : iProp Σ :=
  match ws with
  | [] => bytes b o (drop (Z.to_nat o) xs)
  | w :: ws' => bytes b o (take (Z.to_nat (fst w - o)) (drop (Z.to_nat o) xs)) ∗ gaps b (fst w + snd w) ws' xs
  end.

(** A block of bytes splits into the bytes outside the windows and
    the bytes of each window. *)
Lemma bytes_carve b xs : forall ws o,
  0 <= o -> ordered o (Z.of_nat (length xs)) ws = true ->
  bytes b o (drop (Z.to_nat o) xs) ⊣⊢
  gaps b o ws xs ∗ [∗ list] w ∈ ws, bytes b (fst w) (take (Z.to_nat (snd w)) (drop (Z.to_nat (fst w)) xs)).
Proof using Type.
  induction ws as [|[s n] ws IH]; intros o Ho Hord; cbn [gaps ordered fst snd] in *.
  - rewrite big_sepL_nil right_id. reflexivity.
  - apply andb_prop in Hord as [Hord Hrest]. apply andb_prop in Hord as [Hord He].
    apply andb_prop in Hord as [Hs Hn]. apply Z.leb_le in Hs, Hn, He.
    rewrite big_sepL_cons. cbn [fst snd].
    assert (E : drop (Z.to_nat o) xs =
                take (Z.to_nat (s - o)) (drop (Z.to_nat o) xs) ++
                take (Z.to_nat n) (drop (Z.to_nat s) xs) ++ drop (Z.to_nat (s + n)) xs).
    { rewrite -{1}(take_drop (Z.to_nat (s - o)) (drop (Z.to_nat o) xs)). f_equal. rewrite drop_drop.
      replace (Z.to_nat o + Z.to_nat (s - o))%nat with (Z.to_nat s) by lia.
      rewrite -{1}(take_drop (Z.to_nat n) (drop (Z.to_nat s) xs)). f_equal. rewrite drop_drop. f_equal. lia. }
    rewrite {1}E !bytes_app !length_take !length_drop.
    replace (o + Z.of_nat (Nat.min (Z.to_nat (s - o)) (length xs - Z.to_nat o))) with s by lia.
    replace (s + Z.of_nat (Nat.min (Z.to_nat n) (length xs - Z.to_nat s))) with (s + n) by lia.
    rewrite (IH (s + n)); [|lia|exact Hrest].
    iSplit; [iIntros "($ & $ & $ & $)" | iIntros "(($ & $) & $ & $)"].
Qed.

(** ## One row

    The three windows of a row become the three fields that the
    contract of `c: __tunable_get_val` owns. *)

(** Two byte pieces are equal when their offsets and their bytes are. *)
Lemma piece_eq b o o' x x' : o = o' -> x = x' -> (PByte b o, VByte x) = (PByte b o', VByte x').
Proof using Type. intros -> ->. reflexivity. Qed.

(** Eight owned bytes are an eight-byte cell that holds the number
    they spell in little-endian order. *)
Lemma bytes_icell b o ys :
  length ys = 8%nat -> Forall (fun x => 0 <= x < 256) ys -> bytes b o ys ⊢ ∃ v, icell b o v.
Proof using Type.
  intros L Hy. destruct ys as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|]]]]]]]]]; try discriminate.
  pose proof (fun i y => AbsMem.byte_of_of_bytes' [y0; y1; y2; y3; y4; y5; y6; y7] i y Hy) as E.
  iIntros "H". iExists (AbsRun.of_bytes' [y0; y1; y2; y3; y4; y5; y6; y7]).
  assert (Hl : byte_ps b o [y0; y1; y2; y3; y4; y5; y6; y7] =
               cell b o (AbsRun.of_bytes' [y0; y1; y2; y3; y4; y5; y6; y7])); [|by rewrite /icell /bytes Hl].
  rewrite !byte_ps_cons /cell. cbn [List.map].
  repeat (apply (f_equal2 cons);
    [apply piece_eq; [lia | symmetry;
       first [exact (E 0%nat _ eq_refl) | exact (E 1%nat _ eq_refl) | exact (E 2%nat _ eq_refl)
             | exact (E 3%nat _ eq_refl) | exact (E 4%nat _ eq_refl) | exact (E 5%nat _ eq_refl)
             | exact (E 6%nat _ eq_refl) | exact (E 7%nat _ eq_refl)]] |]).
  reflexivity.
Qed.

(** A later row lies inside the table. Its type code is below 256,
    and the contract fixes its type code and its `initialized` byte. *)
Definition later_row_ok (r : Z * Z) : Prop :=
  0 <= fst r /\ fst r * 136 + 136 <= 4896 /\ le_bytes (snd r) 4 = [snd r; 0; 0; 0] /\
  Forall (fun p => p ∈ icf_tunable_bytes) (icf_row_bytes (fst r) (snd r) true).

Lemma later_rows_ok : Forall later_row_ok icf_later_rows.
Proof using Type. unfold later_row_ok. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(** The windows of a later row hold a tunable entry with the type
    code of the row and some value. *)
Lemma row_entry tl xs r :
  later_row_ok r -> icf_tunables_ok xs ->
  ([∗ list] w ∈ icf_row_fields r, bytes tl (fst w) (take (Z.to_nat (snd w)) (drop (Z.to_nat (fst w)) xs))) ⊢
  ∃ v, tunable_entry tl (fst r) (snd r) v.
Proof using Type.
  destruct r as [id ty]. intros (Hid & Hend & Hle & Hin) (Lx & Hx & Hp). cbn [fst snd] in *.
  assert (P : forall o x, (o, x) ∈ icf_tunable_bytes -> nth_error xs (Z.to_nat o) = Some x).
  { intros o x Ho. rewrite Forall_forall in Hp. exact (Hp (o, x) (proj1 (list_elem_of_In _ _) Ho)). }
  unfold icf_row_bytes in Hin. cbn [app] in Hin.
  apply Forall_cons_iff in Hin as [H48 Hin]. apply Forall_cons_iff in Hin as [H49 Hin].
  apply Forall_cons_iff in Hin as [H50 Hin]. apply Forall_cons_iff in Hin as [H51 Hin].
  apply Forall_cons_iff in Hin as [H104 _]. apply P in H48, H49, H50, H51, H104.
  assert (E4 : take 4 (drop (Z.to_nat (id * 136 + 48)) xs) = le_bytes ty 4).
  { rewrite Hle. apply (take_drop_known [ty; 0; 0; 0]).
    intros [|[|[|[|[|j]]]]] y Hj; cbn in Hj; try discriminate; injection Hj as <-.
    - rewrite Nat.add_0_r. exact H48.
    - replace (Z.to_nat (id * 136 + 48) + 1)%nat with (Z.to_nat (id * 136 + 49)) by lia. exact H49.
    - replace (Z.to_nat (id * 136 + 48) + 2)%nat with (Z.to_nat (id * 136 + 50)) by lia. exact H50.
    - replace (Z.to_nat (id * 136 + 48) + 3)%nat with (Z.to_nat (id * 136 + 51)) by lia. exact H51. }
  assert (E1 : take 1 (drop (Z.to_nat (id * 136 + 104)) xs) = [0]).
  { apply (take_drop_known [0]). intros [|[|j]] y Hj; cbn in Hj; try discriminate; injection Hj as <-.
    rewrite Nat.add_0_r. exact H104. }
  cbn [icf_row_fields]. rewrite !big_sepL_cons big_sepL_nil. cbn [fst snd].
  change (Z.to_nat 4) with 4%nat. change (Z.to_nat 1) with 1%nat. rewrite E4 E1.
  iIntros "(Ht & Hv & Hi & _)". iDestruct (bytes_icell with "Hv") as (v) "Hv".
  { rewrite length_take length_drop Lx. lia. }
  { apply Forall_take, Forall_drop. exact Hx. }
  iExists v. rewrite /tunable_entry. iFrame "Ht Hv". rewrite /bytes /ibyte byte_ps_cons. iExact "Hi".
Qed.

(** ## The split *)

(** Owning one thing for each element of a flattened list is owning
    one thing for each element of each part. *)
Lemma big_sepL_flat_map {A B} (f : A -> list B) (Φ : B -> iProp Σ) l :
  ([∗ list] y ∈ flat_map f l, Φ y) ⊣⊢ [∗ list] x ∈ l, [∗ list] y ∈ f x, Φ y.
Proof using Type.
  induction l as [|x l IH]; cbn [flat_map]; [by rewrite !big_sepL_nil | by rewrite big_sepL_app big_sepL_cons IH].
Qed.

(** These are the windows of all later rows, in order. *)
Definition icf_later_fields : list (Z * Z) := flat_map icf_row_fields icf_later_rows.

(** This assertion owns what is left of the tunable table after the
    later rows are taken out: the bytes outside their fields, and all
    shadow slots. *)
Definition icf_tunables_rest (tl : Z) : iProp Σ :=
  ∃ xs cs, ⌜length xs = 4896%nat /\ length cs = 4896%nat⌝ ∗ gaps tl 0 icf_later_fields xs ∗ auxes tl 0 cs.

(** After the call of `c: init_cpu_features` the tunable table splits
    into one entry for each later row and the remainder. Each entry
    has the type code that [icf_later_rows] lists, some value, and a
    cleared `initialized` byte. *)
Lemma icf_tunables_split tl :
  icf_tunables tl ⊢
  ([∗ list] r ∈ icf_later_rows, ∃ v, tunable_entry tl (fst r) (snd r) v) ∗ icf_tunables_rest tl.
Proof using Type.
  iIntros "(%xs & %cs & [%Hok %Lc] & H)". rewrite pts_app. iDestruct "H" as "[Hx Hc]".
  pose proof Hok as (Lx & _).
  iDestruct (bytes_carve tl xs icf_later_fields 0 with "Hx") as "[Hg Hw]"; [lia | rewrite Lx; vm_compute; reflexivity |].
  iSplitL "Hw".
  - rewrite /icf_later_fields big_sepL_flat_map. iApply (big_sepL_impl with "Hw"). iIntros "!>" (k r Hr) "H".
    iApply (row_entry with "H"); [|exact Hok]. pose proof later_rows_ok as Hall. rewrite Forall_forall in Hall.
    apply Hall, list_elem_of_In, (list_elem_of_lookup_2 _ k). exact Hr.
  - iExists xs, cs. iFrame "Hg Hc". done.
Qed.

End split.
