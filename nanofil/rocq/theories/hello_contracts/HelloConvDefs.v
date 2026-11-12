(** * The pure part of GNU Hello's conversion proofs

    The definitions and lemmas of [HelloConv] that do not need the
    program logic: memory read as lists, spans of live objects, a block
    after a call, libc's private state, and the IR of gnulib's
    rpl_mbrtowc and rpl_mbsrtowcs. They live apart so that HelloMain,
    which uses a few of them, does not wait for the conversion's
    triples. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Memory read as lists *)

(** The n bytes of the memory m from the address a. *)
Definition mem_bytes (m : mem) (a : Z) (n : nat) : list Z :=
  (fun i => m_bytes m (a + Z.of_nat i)) <$> seq 0 n.

(** The n aux slots of the memory m from the address a. *)
Definition mem_auxes (m : mem) (a : Z) (n : nat) : list cap :=
  (fun i => m_aux m (a + Z.of_nat i)) <$> seq 0 n.

(** As `le_value(Bytes, U)`: the little-endian integer of the bytes
    xs. *)
Definition le_value (xs : list Z) : Z := fold_right (fun x acc => x + 256 * acc) 0 xs.

(** As many bytes as asked for. *)
Lemma length_mem_bytes m a n : length (mem_bytes m a n) = n.
Proof. unfold mem_bytes. rewrite length_fmap length_seq. reflexivity. Qed.

(** As many slots as asked for. *)
Lemma length_mem_auxes m a n : length (mem_auxes m a n) = n.
Proof. unfold mem_auxes. rewrite length_fmap length_seq. reflexivity. Qed.

(** The memory reads back the bytes xs it holds from a. *)
Lemma mem_bytes_of m a xs :
  (forall i x, xs !! i = Some x -> m_bytes m (a + Z.of_nat i) = x) -> mem_bytes m a (length xs) = xs.
Proof.
  intros H. apply list_eq. intros i. unfold mem_bytes. rewrite list_lookup_fmap.
  destruct (xs !! i) as [x|] eqn:E.
  - rewrite lookup_seq_lt; [|exact (lookup_lt_Some _ _ _ E)]. cbn. f_equal. exact (H i x E).
  - rewrite lookup_seq_ge; [reflexivity|]. exact (lookup_ge_None_1 _ _ E).
Qed.

(** A four-byte load is the little-endian value of the four bytes. *)
Lemma load_bytes_4 m a : load_bytes m a 4 = le_value (mem_bytes m a 4).
Proof. unfold load_bytes, le_value, mem_bytes. change (Z.to_nat 4) with 4%nat. cbn. ring. Qed.

(** The state bytes of [mbrtowc_pre] are the eight bytes at state. *)
Lemma mbstate_mem_bytes m p : mbstate_bytes m p = mem_bytes m (ptr_addr p) 8.
Proof. reflexivity. Qed.

(** ## Spans of live objects *)

(** Spans inside two different live objects are apart. *)
Lemma spans_apart_objects m b1 r1 b2 r2 p1 n1 p2 n2 :
  live_disjoint m -> live_at m b1 r1 -> live_at m b2 r2 -> b1 <> b2 ->
  b1 <= ptr_addr p1 -> ptr_addr p1 + n1 <= r_end r1 ->
  b2 <= ptr_addr p2 -> ptr_addr p2 + n2 <= r_end r2 ->
  spans_apart (mkSpan p1 n1) (mkSpan p2 n2).
Proof. intros Hd H1 H2 Hne. unfold spans_apart. cbn. destruct (Hd _ _ _ _ H1 H2 Hne); lia. Qed.

(** A span apart from an object's whole extent is apart from every span
    inside it. *)
Lemma spans_apart_within s b reg p n :
  spans_apart s (mkSpan (mkPtr b (Obj b)) (r_end reg - b)) ->
  b <= ptr_addr p -> ptr_addr p + n <= r_end reg -> spans_apart s (mkSpan p n).
Proof. unfold spans_apart. cbn. lia. Qed.

(** Apart spans share no address. *)
Lemma spans_apart_contains s t a : spans_apart s t -> span_contains s a -> ~ span_contains t a.
Proof. unfold spans_apart, span_contains. lia. Qed.

(** The bytes xs from offset o of the live object b, where they agree:
    in its bounds, and held by the memory. *)
Lemma byte_block_facts m b reg o xs :
  live_at m b reg -> all_agree m (byte_ps b o xs) -> xs <> [] ->
  0 <= o /\ b + o + Z.of_nat (length xs) <= r_end reg /\
  forall i x, xs !! i = Some x -> m_bytes m (b + o + Z.of_nat i) = x.
Proof.
  intros Hl Ha Hne. destruct xs as [|x0 xs']; [congruence|].
  destruct (byte_ps_agree m b reg o (x0 :: xs') 0 x0 Hl Ha eq_refl) as (_ & H0 & _).
  destruct (lookup_lt_is_Some_2 (x0 :: xs') (length xs') ltac:(cbn; lia)) as [y Hy].
  destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Ha Hy) as (_ & _ & H1). cbn [length] in *.
  split; [lia|]. split; [lia|].
  intros i x Hx. destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Ha Hx) as (Hv & _).
  rewrite <- Hv. f_equal. lia.
Qed.

(** ## A block after a call *)

(** The block of k bytes from offset o of the object b, live in m' with
    the region reg and in its bounds, holding what m' holds there,
    agrees with m'. *)
Lemma block_after m' b reg o k l v :
  live_at m' b reg -> 0 <= o -> b + o + Z.of_nat k <= r_end reg ->
  (l, v) ∈ block_ps b reg o (mem_bytes m' (b + o) k) (mem_auxes m' (b + o) k) -> agree_piece m' l v.
Proof.
  intros Hl Ho He Hin. unfold block_ps in Hin. apply elem_of_cons in Hin as [Hin|Hin].
  { injection Hin as -> ->. exact Hl. }
  assert (Hreg : registered m' b) by (destruct Hl as [E _]; unfold registered; congruence).
  apply elem_of_app in Hin as [Hin|Hin].
  - apply byte_ps_elem in Hin as (i & x & Hx & -> & ->).
    unfold mem_bytes in Hx. apply list_lookup_fmap_Some in Hx as (i' & -> & Hi).
    apply lookup_seq in Hi as [-> Hi]. cbn [agree_piece].
    split; [exact Hreg|]. intros reg' E L. destruct Hl as [E0 _]. rewrite E0 in E. injection E as <-.
    split; [lia|]. split; [lia|]. f_equal. lia.
  - apply aux_ps_elem in Hin as (i & c & Hc & -> & ->).
    unfold mem_auxes in Hc. apply list_lookup_fmap_Some in Hc as (i' & -> & Hi).
    apply lookup_seq in Hi as [-> Hi]. cbn [agree_piece].
    split; [exact Hreg|]. intros reg' E L. destruct Hl as [E0 _]. rewrite E0 in E. injection E as <-.
    split; [lia|]. split; [lia|]. left. f_equal. lia.
Qed.

(** A byte or aux piece of a live object, inside its bounds at an
    address inside the k bytes from offset o of the live object b, is
    among the keys of the block there. *)
Lemma block_key m b reg o xs cs l b' o' reg' :
  live_disjoint m -> live_at m b reg -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg ->
  length cs = length xs -> (l = PByte b' o' \/ l = PAux b' o') -> live_at m b' reg' -> 0 <= o' ->
  b' + o' < r_end reg' -> b + o <= b' + o' < b + o + Z.of_nat (length xs) ->
  l ∈ (byte_ps b o xs ++ aux_ps b o cs).*1.
Proof.
  intros Hd Hl Ho He Hc Hk Hl' Ho' He' Ha.
  assert (b' = b) as ->.
  { destruct (Z.eq_dec b' b) as [E|Hne]; [exact E|]. destruct (Hd _ _ _ _ Hl' Hl Hne); lia. }
  rewrite fmap_app. apply elem_of_app. replace o' with (o + (o' - o)) in Hk by lia.
  destruct Hk as [-> | ->]; [left; apply byte_ps_key | right; apply aux_ps_key]; lia.
Qed.

(** What owning a block of the bytes xs tells about the memory: its
    object is live, the bytes are in its bounds, and the memory holds
    them. *)
Lemma block_facts m h b reg o xs cs :
  agrees m h -> (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> xs <> [] ->
  live_at m b reg /\ 0 <= o /\ b + o + Z.of_nat (length xs) <= r_end reg /\
  forall i x, xs !! i = Some x -> m_bytes m (b + o + Z.of_nat i) = x.
Proof.
  intros Ha Hlk Hne.
  assert (Hl : live_at m b reg).
  { apply (Ha (PLive b) (VLive reg)), Hlk. apply elem_of_cons. left. reflexivity. }
  assert (Hx : all_agree m (byte_ps b o xs)).
  { apply all_agree_intro. intros l v Hin. apply Ha, Hlk. unfold block_ps.
    apply elem_of_cons. right. apply elem_of_app. left. exact Hin. }
  split; [exact Hl|]. exact (byte_block_facts m b reg o xs Hl Hx Hne).
Qed.

(** A list of length k + 1 is not empty. *)
Lemma nonempty_of_length {A} (xs : list A) k : length xs = S k -> xs <> [].
Proof. intros H ->. discriminate H. Qed.

(** A block's byte and aux keys hold no life piece. *)
Lemma live_not_key b' b o xs cs : PLive b' ∉ (byte_ps b o xs ++ aux_ps b o cs).*1.
Proof.
  rewrite fmap_app byte_ps_keys aux_ps_keys. intros Hin.
  apply elem_of_app in Hin as [Hin|Hin]; apply list_elem_of_fmap in Hin as (? & E & _); discriminate E.
Qed.

(** A block's byte and aux keys are keys of the block after a call, of
    as many bytes and slots. *)
Lemma block_keys_after m' b reg o xs cs k l :
  length xs = k -> length cs = k -> l ∈ (byte_ps b o xs ++ aux_ps b o cs).*1 ->
  l ∈ (block_ps b reg o (mem_bytes m' (b + o) k) (mem_auxes m' (b + o) k)).*1.
Proof.
  intros Hx Hc Hin.
  rewrite (block_ps_keys b reg o xs cs); [| rewrite length_mem_bytes; auto | rewrite length_mem_auxes; auto].
  unfold block_ps. rewrite fmap_cons. apply elem_of_cons. right. exact Hin.
Qed.

(** ## libc's private state *)

(** libc's private state keeps apart from the program's objects: no
    piece of h is of an object libc may release, and of every live
    object owning a piece of h, every private root lies outside its
    extent and libc's private sources hand out none of its
    capabilities. *)
Definition libc_private (m : mem) (w : libc_world) (h : gmap piece pval) : Prop :=
  ids_apart (locale_owned (libc_locale (fst w))) h /\
  forall l v reg, h !! l = Some v -> mem_piece l -> live_at m (piece_id l) reg ->
    (forall root, In root (locale_roots (libc_locale (fst w))) ->
       spans_apart root (mkSpan (mkPtr (piece_id l) (Obj (piece_id l))) (r_end reg - piece_id l))) /\
    ~ available_cap (locale_sources [] m (libc_locale (fst w))) [] m (Obj (piece_id l)) /\
    ~ available_cap (locale_sources [] m (libc_locale (fst w))) [] m (Ro (piece_id l)).

(** What the program learns from mbrtowc(out, src, n, state)
    returning r, for 0 < n and the audited codec, read through the bytes
    it owns ([mbrtowc_result]): ss are the source bytes and xo the
    output's bytes before the call; xo', ys' and xe' the output's,
    state's and errno's bytes after it. A NUL converts to 0 and resets
    the state; a character of r bytes, none of them NUL, to a nonzero
    wide character; an invalid sequence sets errno to EILSEQ (84); an
    incomplete one, under the audited codec, is shorter than 16 bytes
    with no NUL. Under the audited C codec ([CodecC]) an invalid
    sequence keeps the state's bytes ys and starts with a byte of 128 or
    more ([mbrtowc_c_error]). *)
Definition conv_result (valid : term -> list Z -> Prop) (c_codec : Prop) (codec : term) (n : Z)
    (ss xo ys xo' ys' xe' : list Z) (r : Z) : Prop :=
  (r = 0 /\ valid codec ys' /\ (exists i, (i < Z.to_nat n)%nat /\ ss !! i = Some 0) /\
     le_value xo' = 0 /\ le_value (take 4 ys') = 0) \/
  (0 < r <= n /\ r < 2 ^ 64 - 2 /\ valid codec ys' /\ 0 < le_value xo' < 2 ^ 32 /\
     le_value (take 4 ys') = 0 /\ Forall (fun x => x <> 0) (take (Z.to_nat r) ss)) \/
  (r = 2 ^ 64 - 1 /\ le_value xe' = 84 /\ xo' = xo /\
     (c_codec -> ys' = ys /\ exists x, ss !! 0%nat = Some x /\ 128 <= x < 256) /\
     (valid codec ys -> le_value (take 4 ys) = 0 ->
        valid codec ys' /\ le_value (take 4 ys') = 0 /\ exists x, ss !! 0%nat = Some x /\ x <> 0)) \/
  (r = 2 ^ 64 - 2 /\ valid codec ys' /\ xo' = xo /\ n < 16 /\
     Forall (fun x => x <> 0) (take (Z.to_nat n) ss)).

(** ## gnulib's rpl_mbrtowc *)

(** `rpl_mbrtowc(pwc, s, n, ps)`: mbrtowc into pwc, or into a local
    if pwc is null; on an invalid or incomplete sequence, outside a
    hard locale, the first byte stands for itself. *)
Definition rpl_fn : func := Eval vm_compute in hello_fn "rpl_mbrtowc".
(** A block of rpl_mbrtowc. *)
Definition rpl_block (s : String.string) : block := hblk rpl_fn s.

(** rpl_mbrtowc's entry binds its four arguments. *)
Lemma rpl_entry pwc src n ps :
  invocation rpl_fn [WPtr pwc; WPtr src; WInt n; WPtr ps] =
  mkFrame rpl_fn [(TAtom "v6", WPtr ps); (TAtom "v4", WInt n); (TAtom "v2", WPtr src); (TAtom "v0", WPtr pwc)]
    [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** A signed byte load, then its low byte unsigned: the byte. *)
Lemma ub_of_sb x : 0 <= x < 256 -> extension Ub (extension Sb x mod 2 ^ 32) mod 2 ^ 32 = x.
Proof.
  intros Hx. cbn [extension]. unfold sign_extension.
  assert (E : x mod 256 = x) by (apply Z.mod_small; lia). rewrite E.
  destruct (Z.leb_spec 128 x) as [Hh | Hh].
  - assert (E2 : (x - 256) mod 2 ^ 32 = x - 256 + 2 ^ 32) by (symmetry; apply Z.mod_unique with (-1); lia).
    rewrite E2.
    assert (E3 : (x - 256 + 2 ^ 32) mod 256 = x) by (symmetry; apply Z.mod_unique with (2 ^ 24 - 1); lia).
    rewrite E3. apply Z.mod_small. lia.
  - assert (E2 : x mod 2 ^ 32 = x) by (apply Z.mod_small; lia). rewrite E2. rewrite E. apply Z.mod_small. lia.
Qed.

(** What rpl_mbrtowc's caller learns, in [conv_result]'s terms: mbrtowc's
    own answer r', or, after an invalid or incomplete sequence outside a
    hard locale, 1, with the first byte x stored as the wide character. *)
Definition rpl_result (valid : term -> list Z -> Prop) (c_codec : Prop) (codec : term) (n : Z)
    (ss xo ys xo' ys' xe' : list Z) (r' : Z) : Prop :=
  conv_result valid c_codec codec n ss xo ys xo' ys' xe' r' \/
  (r' = 1 /\ (exists r, 2 ^ 64 - 2 <= r /\ conv_result valid c_codec codec n ss xo ys xo ys' xe' r) /\
   exists x, ss !! 0%nat = Some x /\ xo' = le_bytes x 4).

(** mbrtowc's answers are 64-bit words, and the two at the top are the
    invalid and the incomplete sequence, which leave the output alone. *)
Lemma conv_result_range valid c_codec codec n ss xo ys xo' ys' xe' r :
  conv_result valid c_codec codec n ss xo ys xo' ys' xe' r ->
  0 <= r < 2 ^ 64 /\ (2 ^ 64 - 2 <= r -> xo' = xo).
Proof.
  intros [(-> & _) | [(Hr & Hr2 & _) | [(-> & _ & Hx & _) | (-> & _ & Hx & _)]]]; split; try lia; auto.
Qed.

(** ## gnulib's rpl_mbsrtowcs *)

(** `rpl_mbsrtowcs(dest, srcp, len, ps)`: converts the string at *srcp
    into at most len wide characters at dest, one rpl_mbrtowc call per
    character, each given a window of n bytes that reaches the NUL or
    is 16 bytes long. *)
Definition mbs_fn : func := Eval vm_compute in hello_fn "rpl_mbsrtowcs".
(** A block of rpl_mbsrtowcs. *)
Definition mbs_block (s : String.string) : block := hblk mbs_fn s.

(** A nonzero byte loaded signed is not zero. *)
Lemma sb_ne x : 0 < x < 256 -> ((if 128 <=? x then x - 256 else x) mod 2 ^ 32 =? 0) = false.
Proof.
  intros Hx. apply Z.eqb_neq. destruct (Z.leb_spec 128 x).
  - assert (E : (x - 256) mod 2 ^ 32 = x - 256 + 2 ^ 32) by (symmetry; apply Z.mod_unique with (-1); lia).
    rewrite E. lia.
  - rewrite Z.mod_small; lia.
Qed.

(** In a string's bytes and NUL, a zero byte is the NUL. *)
Lemma nul_index bs k x : Forall (fun x => 0 < x < 256) bs -> (bs ++ [0]) !! k = Some x ->
  0 <= x < 256 /\ (x = 0 -> k = length bs) /\ (x <> 0 -> (k < length bs)%nat).
Proof.
  intros Hbs Hk. pose proof (proj1 (Forall_lookup _ _) Hbs) as Hb.
  apply lookup_app_Some in Hk as [Hk|[Hl Hk]].
  - pose proof (Hb _ _ Hk) as Hx. cbv beta in Hx. apply lookup_lt_Some in Hk.
    split; [lia|]. split; [intros E; lia | auto].
  - apply list_lookup_singleton_Some in Hk as [Hk Ex]. subst x.
    split; [lia|]. split; [intros _; lia | intros E; lia].
Qed.

(** A window of four bytes and a count from the fifth: what strnlen1's
    answer plus 4 comes to. *)
Lemma window_min l : (4 <= l)%nat -> Z.min (Z.of_nat (l - 4) + 1) 12 + 4 = Z.min (Z.of_nat l + 1) 16.
Proof. intros Hl. lia. Qed.

(** A byte stored as a four-byte word reads back as itself. *)
Lemma le_value_byte x : 0 <= x < 256 -> le_value (le_bytes x 4) = x.
Proof.
  intros Hx. unfold le_bytes, le_value, byte_of. cbn.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
  change (8 * Z.of_nat 0) with 0.
  rewrite Z.pow_0_r. rewrite Z.div_1_r. rewrite (Z.mod_small x 256); [|lia].
  rewrite (Z.div_small x (2 ^ 8)); [|lia]. rewrite (Z.div_small x (2 ^ 16)); [|lia].
  rewrite (Z.div_small x (2 ^ 24)); [|lia]. rewrite Zmod_0_l. lia.
Qed.

(** A run of nonzero bytes at the start of a string and its NUL ends
    before the NUL. *)
Lemma before_nul bs r : 0 <= r -> Forall (fun x => x <> 0) (take (Z.to_nat r) (bs ++ [0])) ->
  r <= Z.of_nat (length bs).
Proof.
  intros Hr H. destruct (Z.le_gt_cases r (Z.of_nat (length bs))) as [Hle|Hgt]; [exact Hle|]. exfalso.
  rewrite Forall_lookup in H. apply (H (length bs) 0); [|reflexivity].
  rewrite lookup_take_lt; [|lia]. rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

(** One rpl_mbrtowc call of rpl_mbsrtowcs's converting loop, on the
    suffix bs of the string, with the window that reaches the NUL or is
    16 bytes long, from a valid state in its initial shift state: never
    the incomplete answer, which would abort; EILSEQ stores 84 in
    errno; the NUL stores a zero character; anything else consumes r
    bytes before the NUL and stores a nonzero character, leaving a
    valid initial state. *)
Lemma rpl_step valid c codec bs xo ys xo' ys' xe' r :
  Forall (fun x => 0 < x < 256) bs -> valid codec ys -> le_value (take 4 ys) = 0 ->
  rpl_result valid c codec (Z.min (Z.of_nat (length bs) + 1) 16) (bs ++ [0]) xo ys xo' ys' xe' r ->
  0 <= r < 2 ^ 64 /\ r <> 2 ^ 64 - 2 /\ (r = 2 ^ 64 - 1 -> le_value xe' = 84) /\
  (r = 0 -> le_value xo' = 0) /\
  (r <> 0 -> r <> 2 ^ 64 - 1 -> 0 < r <= Z.of_nat (length bs) /\ 0 < le_value xo' < 2 ^ 32 /\
     valid codec ys' /\ le_value (take 4 ys') = 0).
Proof.
  intros Hbs Hval Hinit Hres.
  assert (No2 : forall ys1 xo1 r1, ~ (r1 = 2 ^ 64 - 2 /\ valid codec ys1 /\ xo1 = xo /\
              Z.min (Z.of_nat (length bs) + 1) 16 < 16 /\
              Forall (fun x => x <> 0) (take (Z.to_nat (Z.min (Z.of_nat (length bs) + 1) 16)) (bs ++ [0])))).
  { intros ys1 xo1 r1 (_ & _ & _ & Hn16 & Hnz). apply before_nul in Hnz; lia. }
  destruct Hres as [Hc | (-> & (r0 & Hr0 & Hc0) & (x & Hx & ->))].
  - destruct Hc as [(-> & _ & _ & Ho & _) | [(Hr & Hr2 & Hv & Ho & Hs & Hnz) | [(-> & He & _) | H2]]].
    + repeat split; try lia; auto.
    + apply before_nul in Hnz; [|lia]. repeat split; try lia; auto.
    + repeat split; try lia; auto.
    + exfalso. exact (No2 _ _ _ H2).
  - destruct (nul_index _ _ _ Hbs Hx) as (Hxr & _ & Hn).
    destruct Hc0 as [(-> & _) | [(_ & Hr2 & _) | [(_ & _ & _ & _ & Hlaw) | H2]]]; try lia;
      [| exfalso; exact (No2 _ _ _ H2)].
    destruct (Hlaw Hval Hinit) as (Hv' & Hs' & x' & Hx' & Hx0). rewrite Hx in Hx'. injection Hx' as <-.
    pose proof (Hn Hx0) as Hlen. rewrite (le_value_byte x Hxr).
    repeat split; try lia; auto.
Qed.

(** The four-byte words of ws are wide characters, none of them zero. *)
Definition wide_ok (ws : list Z) : Prop :=
  forall k, (4 * k + 4 <= length ws)%nat -> 0 < le_value (take 4 (drop (4 * k) ws)) < 2 ^ 32.

(** No words, no wide characters. *)
Lemma wide_ok_nil : wide_ok [].
Proof. intros k Hk. cbn in Hk. lia. Qed.

(** A nonzero wide character after i of them. *)
Lemma wide_ok_app ws xo i :
  wide_ok ws -> length ws = (4 * i)%nat -> length xo = 4%nat -> 0 < le_value xo < 2 ^ 32 ->
  wide_ok (ws ++ xo).
Proof.
  intros Hw Lw Lx Hx k Hk. rewrite length_app in Hk.
  destruct (decide (4 * k + 4 <= length ws)%nat) as [Hlt|Hge].
  - rewrite drop_app_le; [|lia]. rewrite take_app_le; [|rewrite length_drop; lia]. apply Hw. exact Hlt.
  - assert (Ek : (4 * k = length ws)%nat) by lia. rewrite Ek drop_app_length. rewrite take_ge; [exact Hx | lia].
Qed.
