(** C strings occupy consecutive bytes through a terminating NUL.
    These ownership assertions track those bytes and their enclosing object,
    and let callers borrow individual bytes or suffixes.
    The earlier libc calling rules live in
    [LibcStringLogic](../hello_contracts/LibcStringLogic.v). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Byte pieces

    A string proof must connect a list of expected bytes to the actual
    memory addresses that a C function reads. The following definitions
    assign one [piece] to each byte, so ownership can be split and
    reassembled without losing that connection. *)

(** Each expected byte receives its own object-relative location, which
    [byte_ps] lists consecutively from offset o in object b. *)
Definition byte_ps (b o : Z) (xs : list Z) : list (piece * pval) :=
  zip_with (fun i x => (PByte b i, VByte x)) (seqZ o (Z.of_nat (length xs))) xs.

(** A nonempty byte sequence separates into its first byte and the
    remaining sequence, whose starting offset advances by one. *)
Lemma byte_ps_cons b o x xs : byte_ps b o (x :: xs) = (PByte b o, VByte x) :: byte_ps b (o + 1) xs.
Proof.
  unfold byte_ps. cbn [length]. rewrite Nat2Z.inj_succ seqZ_cons; [|lia].
  rewrite Z.pred_succ. reflexivity.
Qed.

(** Looking up byte i in the sequence identifies its owned piece at
    offset o plus i within the same object. *)
Lemma byte_ps_lookup b o xs i x :
  xs !! i = Some x -> byte_ps b o xs !! i = Some (PByte b (o + Z.of_nat i), VByte x).
Proof.
  revert o i. induction xs as [|y xs IH]; intros o i H; [discriminate|].
  rewrite byte_ps_cons. destruct i as [|i]; cbn in H |- *.
  - injection H as ->. rewrite Z.add_0_r. reflexivity.
  - rewrite (IH (o + 1) i H). do 3 f_equal. lia.
Qed.

(** When the owned bytes agree with a live object's memory, each listed
    byte lies within the object and contains its expected value. *)
Lemma byte_ps_agree m b reg o xs i x :
  live_at m b reg -> all_agree m (byte_ps b o xs) -> xs !! i = Some x ->
  m_bytes m (b + (o + Z.of_nat i)) = x /\ 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg.
Proof.
  intros [E Lv] Ha Hx.
  pose proof (all_agree_elem _ _ _ _ Ha (list_elem_of_lookup_2 _ _ _ (byte_ps_lookup b o xs i x Hx)))
    as [_ Hin].
  destruct (Hin reg E Lv) as (Ho & He & Hv). auto.
Qed.

(** Consecutive nonzero bytes followed by a NUL form a C string, as
    [string_at_of] proves from the individual memory readings. *)
Lemma string_at_of m a bytes :
  Forall (fun x => 0 < x < 256) bytes ->
  (forall i x, (bytes ++ [0]) !! i = Some x -> m_bytes m (a + Z.of_nat i) = x) ->
  string_at m a bytes.
Proof.
  revert a. induction bytes as [|y bytes IH]; intros a Hf Hb.
  - cbn. rewrite <- (Z.add_0_r a). exact (Hb 0%nat 0 eq_refl).
  - apply Forall_cons_1 in Hf as [Hy Hf]. cbn. split; [exact Hy|]. split.
    + rewrite <- (Z.add_0_r a). exact (Hb 0%nat y eq_refl).
    + apply IH; [exact Hf|]. intros i x Hx.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply Hb. exact Hx.
Qed.

(** Concatenating two byte lists concatenates their pieces, with the
    second list beginning immediately after the first list's final byte. *)
Lemma byte_ps_app b o xs ys :
  byte_ps b o (xs ++ ys) = byte_ps b o xs ++ byte_ps b (o + Z.of_nat (length xs)) ys.
Proof.
  revert o. induction xs as [|x xs IH]; intros o; [cbn; rewrite Z.add_0_r; reflexivity|].
  cbn [app]. rewrite !byte_ps_cons IH. cbn [app length].
  replace (o + Z.of_nat (S (length xs))) with (o + 1 + Z.of_nat (length xs)) by lia. reflexivity.
Qed.

(** The locations in a byte sequence are consecutive byte offsets,
    independent of the values stored at those locations. *)
Lemma byte_ps_keys b o xs : (byte_ps b o xs).*1 = PByte b <$> seqZ o (Z.of_nat (length xs)).
Proof.
  revert o. induction xs as [|x xs IH]; intros o; [reflexivity|].
  rewrite byte_ps_cons. cbn [fmap list_fmap fst]. rewrite IH.
  cbn [length]. rewrite Nat2Z.inj_succ (seqZ_cons o); [|lia]. rewrite Z.pred_succ. reflexivity.
Qed.

(** ## Strings

    A valid string needs more than matching bytes: its pointer must
    authorize reads through the terminator within a live object. The
    following predicates combine these bounds with the byte sequence
    and connect them to the string contracts' requirements. *)

(** A string pointer must name its enclosing object and leave room for
    every nonzero byte followed by the terminating NUL.
    The predicate [string_ok] records these bounds, a positive object
    base, and an object end within the model's address space. *)
Definition string_ok (p : ptr) (b : Z) (reg : region) (bytes : list Z) : Prop :=
  (ptr_cap p = Obj b \/ ptr_cap p = Ro b) /\ 0 < b /\ b <= ptr_addr p /\
  ptr_addr p + Z.of_nat (length bytes) + 1 <= r_end reg /\ r_end reg <= 2 ^ 48 /\
  Forall (fun x => 0 < x < 256) bytes.

(** Owning a string requires its enclosing object's lifetime and all
    bytes through the terminator, which [string_ps] collects as pieces. *)
Definition string_ps (p : ptr) (b : Z) (reg : region) (bytes : list Z) : list (piece * pval) :=
  (PLive b, VLive reg) :: byte_ps b (ptr_addr p - b) (bytes ++ [0]).

(** Agreement between the string's pieces and memory determines each
    byte read from its pointer, including the final NUL byte. *)
Lemma string_bytes m p b reg bytes :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
  forall i x, (bytes ++ [0]) !! i = Some x -> m_bytes m (ptr_addr p + Z.of_nat i) = x.
Proof.
  intros _ [Hl Ha] i x Hx. cbn [fst snd agree_piece] in Hl.
  destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Ha Hx) as [Hv _].
  replace (ptr_addr p + Z.of_nat i) with (b + (ptr_addr p - b + Z.of_nat i)) by lia. exact Hv.
Qed.

(** A string with owned, matching bytes satisfies [terminated_length],
    giving length-based contracts a readable range with the expected terminator. *)
Lemma string_terminated m p b reg bytes :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
  terminated_length m p (Z.of_nat (length bytes)).
Proof.
  intros Hok Ha. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  destruct Hok as (Hc & H0 & H1 & H2 & H3 & Hf). destruct Ha as [[E Lv] _].
  assert (Hn : Z.of_nat (length bytes) < 2 ^ 64 - 1) by lia.
  split; [|exact Hn]. split; [lia|]. split; [lia|]. split; [exists b, reg; auto|].
  replace (Z.of_nat (length bytes) <? 2 ^ 64 - 1) with true by (symmetry; apply Z.ltb_lt; exact Hn).
  split; [apply (access_read _ b reg); [exact Hc | exact E | lia | lia | apply Z.mod_1_r]|]. split.
  - intros i Hi. destruct (lookup_lt_is_Some_2 bytes (Z.to_nat i) ltac:(lia)) as [x Hx].
    rewrite <- (Z2Nat.id i) by lia. rewrite (Hb (Z.to_nat i) x); [|by apply lookup_app_l_Some].
    exact (Forall_lookup_1 _ _ _ _ Hf Hx).
  - intros _. apply (Hb (length bytes) 0). rewrite lookup_app_r; [|lia].
    rewrite Nat.sub_diag. reflexivity.
Qed.

(** The same owned bytes also satisfy [c_string], giving the puts
    contract both a readable range and the complete string contents. *)
Lemma string_c_string m p b reg bytes :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) -> c_string m p bytes.
Proof.
  intros Hok Ha. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  pose proof Hok as (Hc & _ & H1 & H2 & _ & Hf). destruct Ha as [[E _] _]. split.
  - apply (access_read _ b reg); [exact Hc | exact E | lia | lia | apply Z.mod_1_r].
  - apply string_at_of; [exact Hf | exact Hb].
Qed.

(** Every owned location occurs only once in a string's piece list,
    so the assertion does not claim the same byte twice. *)
Lemma string_ps_nodup p b reg bytes : NoDup (string_ps p b reg bytes).*1.
Proof.
  unfold string_ps. cbn [fmap list_fmap fst]. rewrite byte_ps_keys. apply NoDup_cons_2.
  - rewrite list_elem_of_fmap. intros (o & E & _). discriminate E.
  - apply NoDup_fmap_2; [intros x y E; injection E as ->; reflexivity | apply NoDup_seqZ].
Qed.

(** The lifetime and byte pieces of a string all refer to the same
    enclosing object, as [string_ps_id] establishes for ownership reasoning. *)
Lemma string_ps_id p b reg bytes l v : (l, v) ∈ string_ps p b reg bytes -> piece_id l = b.
Proof.
  unfold string_ps. rewrite elem_of_cons. intros [H|H]; [injection H as -> _; reflexivity|].
  apply (list_elem_of_fmap_2 fst) in H. cbn [fst] in H. rewrite byte_ps_keys in H.
  apply list_elem_of_fmap in H as (o & -> & _). reflexivity.
Qed.

(** All pieces used to represent a string describe memory, rather than
    runtime bookkeeping, so memory-preservation rules apply to them. *)
Lemma string_ps_mem p b reg bytes l v : (l, v) ∈ string_ps p b reg bytes -> mem_piece l.
Proof.
  unfold string_ps. rewrite elem_of_cons. intros [H|H]; [injection H as -> _; exact I|].
  apply (list_elem_of_fmap_2 fst) in H. cbn [fst] in H. rewrite byte_ps_keys in H.
  apply list_elem_of_fmap in H as (o & -> & _). exact I.
Qed.

(** Splitting a string at byte i separates its preceding bytes from
    the suffix while retaining the same object lifetime.
    The lemma [string_ps_suffix] describes both piece lists without
    duplicating that lifetime when the suffix is lent to a caller. *)
Lemma string_ps_suffix p b reg bytes i :
  (i <= length bytes)%nat ->
  let q := mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p) in
  string_ps p b reg bytes =
    (PLive b, VLive reg) :: byte_ps b (ptr_addr p - b) (take i bytes) ++
      byte_ps b (ptr_addr q - b) (drop i bytes ++ [0]) /\
  string_ps q b reg (drop i bytes) = (PLive b, VLive reg) :: byte_ps b (ptr_addr q - b) (drop i bytes ++ [0]).
Proof.
  intros Hi q. split; [|reflexivity]. unfold string_ps. f_equal.
  rewrite <- (take_drop i bytes) at 1. rewrite <- app_assoc, byte_ps_app, length_take.
  cbn [ptr_addr q]. replace (ptr_addr p - b + Z.of_nat (Nat.min i (length bytes)))
    with (ptr_addr p + Z.of_nat i - b) by lia. reflexivity.
Qed.

(** Advancing within a string, including to its terminator, leaves a
    valid string suffix with the original pointer's object capability. *)
Lemma string_ok_suffix p b reg bytes i :
  (i <= length bytes)%nat -> string_ok p b reg bytes ->
  string_ok (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i bytes).
Proof.
  intros Hi (Hc & H0 & H1 & H2 & H3 & Hf). unfold string_ok. cbn [ptr_addr ptr_cap]. rewrite length_drop.
  split; [exact Hc|]. split; [exact H0|]. split; [lia|]. split; [lia|]. split; [exact H3|].
  apply Forall_drop. exact Hf.
Qed.

(** The module [StringLogicOn] builds string assertions over an existing
    program logic for any [[runtime]] R. *)
Module StringLogicOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

Section strings.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** A caller owns a C string through [string], which combines its
    pointer bounds with ownership of the object lifetime and terminated bytes. *)
Definition string (p : ptr) (b : Z) (reg : region) (bytes : list Z) : iProp Σ :=
  ⌜string_ok p b reg bytes⌝ ∗ pts (string_ps p b reg bytes).

(** String ownership guarantees that actual memory satisfies both
    length-based and content-based string contracts, as [string_facts] derives from the shared memory interpretation. *)
Lemma string_facts {world : Type} (wi : mem -> world -> gmap piece pval -> Prop) σ p b reg bytes :
  heap_interp wi σ -∗ string p b reg bytes -∗
  ⌜terminated_length (ls_mem σ) p (Z.of_nat (length bytes)) /\ c_string (ls_mem σ) p bytes⌝.
Proof.
  iIntros "Hσ [%Hok Hs]". iDestruct (pts_facts with "Hσ Hs") as %(Ha & _). iPureIntro.
  split; [exact (string_terminated _ _ _ _ _ Hok Ha) | exact (string_c_string _ _ _ _ _ Hok Ha)].
Qed.

(** A string can lend its lifetime and one byte for a load, including
    the terminator when i equals the string's length.
    The rule [string_byte] also supplies the means to rebuild full string
    ownership once the borrower returns both resources unchanged. *)
Lemma string_byte p b reg bytes i x :
  (bytes ++ [0]) !! i = Some x ->
  string p b reg bytes -∗
  ⌜string_ok p b reg bytes⌝ ∗ live b reg ∗ ibyte b (ptr_addr p - b + Z.of_nat i) x ∗
  (live b reg -∗ ibyte b (ptr_addr p - b + Z.of_nat i) x -∗ string p b reg bytes).
Proof.
  intros Hx. iIntros "[%Hok [Hl Hs]]". rewrite /live /ibyte /pts /=.
  iDestruct (big_sepL_lookup_acc with "Hs") as "[Hb Hk]"; [exact (byte_ps_lookup _ _ _ _ _ Hx)|].
  iSplit; [done|]. iSplitL "Hl"; [iFrame|]. iSplitL "Hb"; [iFrame|].
  iIntros "[Hl _] [Hb _]". iSplit; [done|]. iFrame "Hl". iApply ("Hk" with "Hb").
Qed.

(** A caller can borrow the string beginning at any byte through the
    terminator, while retaining the bytes before that position.
    Returning the borrowed suffix restores the original string ownership
    through [string_suffix], without duplicating the shared object's lifetime. *)
Lemma string_suffix p b reg bytes i :
  (i <= length bytes)%nat ->
  string p b reg bytes -∗
  string (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i bytes) ∗
  (string (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i bytes) -∗ string p b reg bytes).
Proof.
  intros Hi. destruct (string_ps_suffix p b reg bytes i Hi) as [Ep Eq].
  iIntros "[%Hok Hs]". rewrite /string Ep Eq /pts big_sepL_cons big_sepL_app.
  iDestruct "Hs" as "(Hl & Hpre & Hsuf)". iSplitL "Hl Hsuf".
  - iSplit; [iPureIntro; exact (string_ok_suffix _ _ _ _ _ Hi Hok)|]. rewrite big_sepL_cons. iFrame.
  - iIntros "[_ Hq]". rewrite big_sepL_cons. iDestruct "Hq" as "[Hl Hsuf]". iSplit; [done|]. iFrame.
Qed.

(** A bounded string read stops at either the terminator or the
    supplied limit, whichever it reaches first.
    The lemma [string_bounded] derives this [bounded_length] guarantee
    from owned bytes, providing the readable range required by strncmp. *)
Lemma string_bounded m p b reg bytes n :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) -> 0 <= n < 2 ^ 64 ->
  bounded_length m p n (Z.min (Z.of_nat (length bytes)) n).
Proof.
  intros Hok Ha Hn. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  destruct Hok as (Hc & H0 & H1 & H2 & H3 & Hf). destruct Ha as [[E Lv] _].
  split; [exact Hn|]. split; [lia|]. split; [exists b, reg; auto|]. split.
  - apply (access_read _ b reg); [exact Hc | exact E | lia | | apply Z.mod_1_r].
    destruct (Z.min _ n <? n); lia.
  - split.
    + intros i Hi. destruct (lookup_lt_is_Some_2 bytes (Z.to_nat i) ltac:(lia)) as [x Hx].
      rewrite <- (Z2Nat.id i) by lia. rewrite (Hb (Z.to_nat i) x); [|by apply lookup_app_l_Some].
      exact (Forall_lookup_1 _ _ _ _ Hf Hx).
    + intros Hk. assert (Z.min (Z.of_nat (length bytes)) n = Z.of_nat (length bytes)) as -> by lia.
      apply (Hb (length bytes) 0). rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

End strings.
End StringLogicOn.

(** The module [StringLogic] creates its own program-logic instance,
    then supplies the string assertions from [StringLogicOn]. *)
Module StringLogic (R : Runtime).
Module LG0 := Logic R.
Include StringLogicOn R LG0.
End StringLogic.
