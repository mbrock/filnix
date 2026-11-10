(** GNU Hello's conversion of its greeting through the program logic
    of Logic.v (docs/logic.md): libc's `mbrtowc`, and gnulib's
    `rpl_mbrtowc` and `rpl_mbsrtowcs` around it, which main calls to
    turn the greeting into wide characters.

    mbrtowc(out, src, n, state) writes three cells the program owns:
    the wide character at out, the conversion state and errno. Its
    triple ([wp_mbrtowc]) takes the three as whole blocks, with their
    life, bytes and aux slots, and hands them back holding whatever the
    memory holds after the call, which [conv_result] describes:
    Campaign 4's [mbrtowc_result] read through the owned bytes, under
    the audited codec. ContractFrame.v's [prefix_agrees_out] keeps every
    other piece agreeing, though the call's roots now meet the
    program's objects.

    The world is Libc.v's [libc_world]. The triple is generic in the
    world interpretation wi, given that wi makes libc ready, fixes the
    codec and the errno cell, keeps libc's private roots, releases and
    capabilities apart from the program's objects ([libc_private]),
    and survives the call's writes into the three blocks. The audited
    codec premise ([Haudit]) stays explicit, as docs/logic.md records:
    it is not derived from the locale. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic MemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale.
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

Module HelloConvOn (R : Runtime) (LG0 : LogicSig R).
Module HLo := HelloLocaleOn R LG0.
Module HL := HLo.HL.
Module LL := HL.LL.
Module ML := HL.ML.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Module LB := LibcOn R L.M.
Import L LG SL ML LL HL HLo.

(** ## mbrtowc's triple *)

Section mbrtowc.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Local Instance conv_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation cexpr := (language.expr (nanofil_lang registry ge)).

(** mbrtowc has Campaign 4's contract, whose state predicate valid
    admits the zero state and holds only of bytes. *)
Context (valid : term -> list Z -> Prop) (audit : term -> option audited_codec)
  (rep : mem -> libc_world -> Prop) (requests : list word -> mem -> libc_world -> Z -> Z -> Prop)
  (Hmbrtowc : registry (TAtom "mbrtowc") = Some (mbrtowc_contract valid audit rep requests))
  (Hvalid0 : mbstate_zero_valid valid) (Hbytes : mbstate_valid_bytes valid).

(** The world interpretation makes libc ready, with the errno cell
    errno, keeps the codec piece current ([codec_current]) and libc's
    private state apart. A conversion learns the codec from the codec
    piece, which setlocale's setter set ([wp_setlocale_set]). *)
Context (errno : ptr)
  (Hlibc : forall m w h, wi m w h ->
     libc_ready rep m w /\ codec_current (libc_locale (fst w)) h /\
     libc_errno (fst w) = errno /\ libc_private m w h).

(** The audited codec premise: the world's codec is one of the audited
    profiles, C or C.UTF-8. *)
Context (Haudit : forall m w h, wi m w h -> hello_codec_profile audit w).

(** The world interpretation survives a return of mbrtowc into the
    output, state and errno blocks the program owns, holding whatever
    the memory holds there afterwards. *)
Context (Kmbrtowc : forall r args out src n state s m w h trace values s' m' w'
    bo ro oo xo co bs rs os ys cs be re oe xe ce,
  M.E.invoke (mbrtowc_contract valid audit rep requests) r args [WPtr out; WPtr src; WInt n; WPtr state]
    s m w trace (CallReturn values) s' m' w' ->
  (forall l v, (l, v) ∈ block_ps bo ro oo xo co ++ block_ps bs rs os ys cs ++ block_ps be re oe xe ce ->
     h !! l = Some v) ->
  wi m w h ->
  wi m' w' (overwrite (block_ps bo ro oo (mem_bytes m' (bo + oo) 4) (mem_auxes m' (bo + oo) 4) ++
                       block_ps bs rs os (mem_bytes m' (bs + os) 8) (mem_auxes m' (bs + os) 8) ++
                       block_ps be re oe (mem_bytes m' (be + oe) 4) (mem_auxes m' (be + oe) 4)) h)).

(** Owning two blocks, they are of different objects: each life is
    owned once. *)
Lemma block_ne b reg o xs cs b' reg' o' xs' cs' :
  pts (block_ps b reg o xs cs) -∗ pts (block_ps b' reg' o' xs' cs') -∗ ⌜b <> b'⌝.
Proof.
  rewrite /block_ps /pts !big_sepL_cons. iIntros "[Hl _] [Hl' _]".
  iDestruct (pointsto_ne with "Hl Hl'") as %Hne. iPureIntro. intros <-. apply Hne. reflexivity.
Qed.

(** The arguments are admitted ([mbrtowc_pre]) where the program owns
    the output, state and errno blocks and the source's life and bytes,
    of four different objects, the state's bytes valid. *)
Lemma mbrtowc_admitted codec m w h out src n state bo ro oo xo co bs rs os ys cs be re oe xe ce
    bsrc rsrc osrc ss :
  wi m w h -> agrees m h -> live_disjoint m -> objects_fit (m_regions m) ->
  h !! PName codec_key = Some (VCodec codec) ->
  (forall l v, (l, v) ∈ block_ps bo ro oo xo co -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ block_ps bs rs os ys cs -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ block_ps be re oe xe ce -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ block_ps bsrc rsrc osrc ss [] -> h !! l = Some v) ->
  bo <> bs -> bo <> be -> bo <> bsrc -> bs <> be -> bs <> bsrc -> be <> bsrc ->
  out = mkPtr (bo + oo) (Obj bo) -> state = mkPtr (bs + os) (Obj bs) -> errno = mkPtr (be + oe) (Obj be) ->
  (ptr_cap src = Obj bsrc \/ ptr_cap src = Ro bsrc) -> ptr_addr src = bsrc + osrc ->
  0 < bo -> 0 < bs -> 0 < bsrc -> (bo + oo) mod 4 = 0 -> (bs + os) mod 4 = 0 ->
  length xo = 4%nat -> length ys = 8%nat -> length xe = 4%nat ->
  0 < n <= Z.of_nat (length ss) -> Forall (fun x => 0 <= x < 256) ss ->
  valid codec ys ->
  mbrtowc_pre valid rep [WPtr out; WPtr src; WInt n; WPtr state] m w.
Proof.
  intros Hw Ha Hd Hfit Hcod Ho Hs He Hsr Nos Noe Nosr Nse Nssr Nesr -> -> Herr Hcap Haddr Hbo Hbs Hbsrc Hoal Hsal
    Lxo Lys Lxe Hn Hss Hval.
  pose proof (Hbytes _ _ Hval) as Hyb.
  destruct (Hlibc m w h Hw) as (Hready & Hcur & Herrno & Hown & Hpriv).
  pose proof (Hcur _ Hcod) as Hcodec.
  destruct (block_facts m h bo ro oo xo co Ha Ho (nonempty_of_length xo 3 Lxo)) as (Lo & Oo & Eo & _).
  destruct (block_facts m h bs rs os ys cs Ha Hs (nonempty_of_length ys 7 Lys)) as (Ls & Os & Es & Vs).
  destruct (block_facts m h be re oe xe ce Ha He (nonempty_of_length xe 3 Lxe)) as (Le & Oe & Ee & _).
  destruct (block_facts m h bsrc rsrc osrc ss [] Ha Hsr ltac:(intros E; rewrite E in Hn; cbn in Hn; lia))
    as (Lsr & Osr & Esr & Vsr).
  rewrite Lxo in Eo. rewrite Lys in Es. rewrite Lxe in Ee.
  assert (Hkey : forall b reg o zs ds, (forall l v, (l, v) ∈ block_ps b reg o zs ds -> h !! l = Some v) ->
            h !! PLive b = Some (VLive reg)).
  { intros b reg o zs ds H. apply H. apply elem_of_cons. left. reflexivity. }
  destruct (Hpriv _ _ _ (Hkey _ _ _ _ _ Ho) I Lo) as (Ro & Co1 & Co2).
  destruct (Hpriv _ _ _ (Hkey _ _ _ _ _ Hs) I Ls) as (Rs & Cs1 & Cs2).
  destruct (Hpriv _ _ _ (Hkey _ _ _ _ _ He) I Le) as (Re & Ce1 & Ce2).
  destruct (Hpriv _ _ _ (Hkey _ _ _ _ _ Hsr) I Lsr) as (Rsr & Csr1 & Csr2).
  cbn [piece_id] in Ro, Co1, Co2, Rs, Cs1, Cs2, Re, Ce1, Ce2, Rsr, Csr1, Csr2.
  pose proof (Hfit _ _ (proj1 Lsr)) as [Fsr0 Fsr1].
  assert (Hsrc_bytes : forall i, 0 <= i < n -> exists x, ss !! Z.to_nat i = Some x /\
            m_bytes m (ptr_addr src + i) = x /\ 0 <= x < 256).
  { intros i Hi. destruct (lookup_lt_is_Some_2 ss (Z.to_nat i) ltac:(lia)) as [x Hx]. exists x.
    split; [exact Hx|]. split; [|exact (proj1 (Forall_lookup _ _) Hss _ _ Hx)].
    rewrite Haddr. rewrite <- (Vsr _ _ Hx). f_equal. lia. }
  unfold mbrtowc_pre. rewrite Herrno Herr.
  split; [exact Hready|]. split; [exact Hvalid0|]. split; [exact Hbytes|].
  exists (mkPtr (bo + oo) (Obj bo)), src, n, (mkPtr (bs + os) (Obj bs)). split; [reflexivity|].
  cbn [ptr_addr ptr_cap].
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { split; [lia|]. split; [exists bsrc, rsrc; split; [exact Hcap | exact Lsr]|]. split.
    - destruct Hcap as [Hc|Hc]; rewrite Hc Haddr;
        [apply (access_obj _ _ rsrc _ _ Read) | apply (access_ro_read _ _ rsrc)];
        solve [exact (proj1 Lsr) | lia | apply Z.mod_1_r].
    - intros i Hi. destruct (Hsrc_bytes i Hi) as (x & _ & -> & Hx). exact Hx. }
  split.
  { unfold writable_span. cbn [span_size span_ptr ptr_addr ptr_cap].
    split; [lia|]. exists bo, ro. split; [reflexivity|]. split; [exact (proj1 Lo)|]. split; [exact (proj2 Lo)|].
    apply (access_obj _ _ ro _ _ Write); [exact (proj1 Lo) | lia | lia | apply Z.mod_1_r]. }
  split; [exact Hoal|].
  split.
  { unfold writable_span. cbn [span_size span_ptr ptr_addr ptr_cap].
    split; [lia|]. exists bs, rs. split; [reflexivity|]. split; [exact (proj1 Ls)|]. split; [exact (proj2 Ls)|].
    apply (access_obj _ _ rs _ _ Write); [exact (proj1 Ls) | lia | lia | apply Z.mod_1_r]. }
  split.
  { split; [lia|]. split; [exists bs, rs; split; [left; reflexivity | exact Ls]|]. split.
    - cbn [ptr_addr ptr_cap]. apply (access_obj _ _ rs _ _ Read); [exact (proj1 Ls) | lia | lia | apply Z.mod_1_r].
    - intros i Hi. cbn [ptr_addr]. destruct (lookup_lt_is_Some_2 ys (Z.to_nat i) ltac:(lia)) as [x Hx].
      replace (bs + os + i) with (bs + os + Z.of_nat (Z.to_nat i)) by lia. rewrite (Vs _ _ Hx).
      exact (proj1 (Forall_lookup _ _) Hyb _ _ Hx). }
  split; [exact Hsal|].
  split.
  { rewrite Hcodec mbstate_mem_bytes. cbn [ptr_addr]. rewrite <- Lys, mem_bytes_of; [exact Hval|].
    intros i x Hx. exact (Vs i x Hx). }
  split; [apply (spans_apart_objects m bsrc rsrc bo ro); cbn [ptr_addr]; auto; lia|].
  split; [apply (spans_apart_objects m bsrc rsrc bs rs); cbn [ptr_addr]; auto; lia|].
  split; [apply (spans_apart_objects m bo ro bs rs); cbn [ptr_addr]; auto; lia|].
  split.
  { intros p size Hin. cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; split.
    - apply (spans_apart_objects m be re bsrc rsrc); cbn [ptr_addr]; auto; lia.
    - intros root Hroot. apply (spans_apart_within root bsrc rsrc); [exact (Rsr root Hroot) | lia | lia].
    - apply (spans_apart_objects m be re bo ro); cbn [ptr_addr]; auto; lia.
    - intros root Hroot. apply (spans_apart_within root bo ro); [exact (Ro root Hroot) | cbn; lia | cbn; lia].
    - apply (spans_apart_objects m be re bs rs); cbn [ptr_addr]; auto; lia.
    - intros root Hroot. apply (spans_apart_within root bs rs); [exact (Rs root Hroot) | cbn; lia | cbn; lia]. }
  split.
  { intros base Hbase p Hp. cbn in Hp.
    pose proof (Hown base _ _ Hbase (Hkey _ _ _ _ _ Ho) I) as N1.
    pose proof (Hown base _ _ Hbase (Hkey _ _ _ _ _ Hs) I) as N2.
    pose proof (Hown base _ _ Hbase (Hkey _ _ _ _ _ He) I) as N3.
    pose proof (Hown base _ _ Hbase (Hkey _ _ _ _ _ Hsr) I) as N4.
    cbn [piece_id] in N1, N2, N3, N4.
    destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; cbn [ptr_cap];
      [| destruct Hcap as [Hc|Hc]; rewrite Hc | |]; split; congruence. }
  split.
  { intros root Hroot. apply (spans_apart_within root be re); [exact (Re root Hroot) | cbn; lia | cbn; lia]. }
  intros p Hp base Hc. cbn in Hp.
  destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; cbn [ptr_cap] in Hc.
  - destruct Hc as [E|E]; [injection E as <-; auto | discriminate E].
  - destruct Hcap as [Hc'|Hc']; rewrite Hc' in Hc; destruct Hc as [E|E];
      first [discriminate E | injection E as <-; auto].
  - destruct Hc as [E|E]; [injection E as <-; auto | discriminate E].
  - destruct Hc as [E|E]; [injection E as <-; auto | discriminate E].
Qed.

(** A return of the call keeps every piece but the three blocks'
    bytes and slots agreeing ([prefix_agrees_out]), so that, the blocks
    holding what the memory holds after it, the ghost heap agrees; the
    live objects stay apart and the runtime ready. *)
Lemma mbrtowc_frame r args s m w h trace values s' m' w' out src n state
    bo ro oo xo co bs rs os ys cs be re oe xe ce :
  M.E.invoke (mbrtowc_contract valid audit rep requests) r args [WPtr out; WPtr src; WInt n; WPtr state]
    s m w trace (CallReturn values) s' m' w' ->
  wi m w h -> agrees m h -> live_disjoint m -> R.ready s m ->
  (forall l v, (l, v) ∈ block_ps bo ro oo xo co -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ block_ps bs rs os ys cs -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ block_ps be re oe xe ce -> h !! l = Some v) ->
  out = mkPtr (bo + oo) (Obj bo) -> state = mkPtr (bs + os) (Obj bs) -> errno = mkPtr (be + oe) (Obj be) ->
  length xo = 4%nat -> length co = 4%nat -> length ys = 8%nat -> length cs = 8%nat ->
  length xe = 4%nat -> length ce = 4%nat -> n <> 0 ->
  agrees m' (overwrite (block_ps bo ro oo (mem_bytes m' (bo + oo) 4) (mem_auxes m' (bo + oo) 4) ++
                        block_ps bs rs os (mem_bytes m' (bs + os) 8) (mem_auxes m' (bs + os) 8) ++
                        block_ps be re oe (mem_bytes m' (be + oe) 4) (mem_auxes m' (be + oe) 4)) h) /\
  live_disjoint m' /\ R.ready s' m'.
Proof.
  intros Hi Hw Ha Hd Hr Ho Hs He -> -> Herr Lxo Lco Lys Lcs Lxe Lce Hn.
  destruct (Hlibc m w h Hw) as (_ & _ & Herrno & Hown & Hpriv).
  destruct (block_facts m h bo ro oo xo co Ha Ho (nonempty_of_length xo 3 Lxo)) as (Lo & Oo & Eo & _).
  destruct (block_facts m h bs rs os ys cs Ha Hs (nonempty_of_length ys 7 Lys)) as (Ls & Os & Es & _).
  destruct (block_facts m h be re oe xe ce Ha He (nonempty_of_length xe 3 Lxe)) as (Le & Oe & Ee & _).
  rewrite Lxo in Eo. rewrite Lys in Es. rewrite Lxe in Ee.
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  set (ks := (byte_ps bo oo xo ++ aux_ps bo oo co).*1 ++ (byte_ps bs os ys ++ aux_ps bs os cs).*1 ++
             (byte_ps be oe xe ++ aux_ps be oe ce).*1).
  set (outs := fun a => span_contains (mkSpan (mkPtr (bo + oo) (Obj bo)) 4) a \/
                        span_contains (mkSpan (mkPtr (bs + os) (Obj bs)) 8) a \/
                        span_contains (mkSpan (mkPtr (be + oe) (Obj be)) 4) a).
  assert (Hwr : contract_writes (mbrtowc_contract valid audit rep requests)
                  [WPtr (mkPtr (bo + oo) (Obj bo)); WPtr src; WInt n; WPtr (mkPtr (bs + os) (Obj bs))] m w =
                locale_roots (libc_locale (fst w)) ++
                  [mkSpan (mkPtr (bo + oo) (Obj bo)) 4; mkSpan (mkPtr (bs + os) (Obj bs)) 8;
                   mkSpan (mkPtr (be + oe) (Obj be)) 4]).
  { cbn [contract_writes mbrtowc_contract mbrtowc_writes]. rewrite (proj2 (Z.eqb_neq n 0) Hn) Herrno Herr.
    reflexivity. }
  assert (Hrel : contract_releases (mbrtowc_contract valid audit rep requests)
                   [WPtr (mkPtr (bo + oo) (Obj bo)); WPtr src; WInt n; WPtr (mkPtr (bs + os) (Obj bs))] m w =
                 locale_owned (libc_locale (fst w))).
  { cbn [contract_releases mbrtowc_contract mbrtowc_releases]. rewrite (proj2 (Z.eqb_neq n 0) Hn).
    reflexivity. }
  destruct (prefix_agrees_out _ _ _ _ _ _ _ _ _ _ _ h ks outs Hp Hr Hd) as (Ha' & _ & Hd' & _).
  - intros l v Hl _. exact (Ha l v Hl).
  - intros l v Hl Hm. exact (agree_piece_registered _ _ _ Hm (Ha l v Hl)).
  - rewrite Hwr. intros sp a Hin Hsp Hol. apply in_app_or in Hin as [Hin|Hin].
    + exfalso. destruct Hol as (l & v & reg & Hl & Hm & Hlv & Hb).
      destruct (Hpriv l v reg Hl Hm Hlv) as (Hroots & _).
      pose proof (Hroots sp Hin) as Hap. unfold spans_apart, span_contains in Hap, Hsp. cbn in Hap. lia.
    + unfold outs. destruct Hin as [<-|[<-|[<-|[]]]]; auto.
  - intros l v Hl Hk. destruct l as [b|b o|b o|k]; try exact I; intros reg Hlv Ho' He' Hout; apply Hk;
      unfold ks; rewrite !elem_of_app;
      (destruct Hout as [Hout|[Hout|Hout]]; unfold span_contains in Hout; cbn in Hout;
       [left | right; left | right; right]);
      solve [ eapply (block_key m bo ro oo xo co); eauto; lia
            | eapply (block_key m bs rs os ys cs); eauto; lia
            | eapply (block_key m be re oe xe ce); eauto; lia ].
  - rewrite Hrel. exact Hown.
  - assert (Hlive : forall b reg o zs ds, (forall l v, (l, v) ∈ block_ps b reg o zs ds -> h !! l = Some v) ->
              live_at m' b reg).
    { intros b reg o zs ds H. apply (Ha' (PLive b) (VLive reg)); [apply H; apply elem_of_cons; left; reflexivity|].
      unfold ks. rewrite !elem_of_app. intros [Hk|[Hk|Hk]]; exact (live_not_key _ _ _ _ _ Hk). }
    split; [|split; [exact Hd' | exact Hr']].
    intros l v Hl. apply lookup_overwrite in Hl as [Hin | [Hnk Hh]].
    + rewrite !elem_of_app in Hin. destruct Hin as [Hin|[Hin|Hin]].
      * exact (block_after m' bo ro oo 4 l v (Hlive _ _ _ _ _ Ho) Oo Eo Hin).
      * exact (block_after m' bs rs os 8 l v (Hlive _ _ _ _ _ Hs) Os Es Hin).
      * exact (block_after m' be re oe 4 l v (Hlive _ _ _ _ _ He) Oe Ee Hin).
    + apply (Ha' l v Hh). intros Hk. apply Hnk. unfold ks in Hk. rewrite !fmap_app !elem_of_app.
      rewrite !elem_of_app in Hk. destruct Hk as [Hk|[Hk|Hk]]; [left | right; left | right; right].
      * exact (block_keys_after m' bo ro oo xo co 4 l Lxo Lco Hk).
      * exact (block_keys_after m' bs rs os ys cs 8 l Lys Lcs Hk).
      * exact (block_keys_after m' be re oe xe ce 4 l Lxe Lce Hk).
Qed.

(** Campaign 4's [mbrtowc_result], for 0 < n and the audited codec,
    read through the owned bytes: [conv_result]. *)
Lemma conv_of_result codec m w out src n state res m' bo oo xo bs os ys be oe bsrc osrc ss :
  mbrtowc_result valid audit m w out src n state res m' ->
  hello_codec_profile audit w -> locale_codec (libc_locale (fst w)) = codec ->
  libc_errno (fst w) = mkPtr (be + oe) (Obj be) ->
  out = mkPtr (bo + oo) (Obj bo) -> state = mkPtr (bs + os) (Obj bs) -> ptr_addr src = bsrc + osrc ->
  length xo = 4%nat -> (forall i x, xo !! i = Some x -> m_bytes m (bo + oo + Z.of_nat i) = x) ->
  length ys = 8%nat -> (forall i x, ys !! i = Some x -> m_bytes m (bs + os + Z.of_nat i) = x) ->
  0 < n <= Z.of_nat (length ss) -> (forall i x, ss !! i = Some x -> m_bytes m (bsrc + osrc + Z.of_nat i) = x) ->
  conv_result valid (audit codec = Some CodecC) codec n ss xo ys (mem_bytes m' (bo + oo) 4) (mem_bytes m' (bs + os) 8)
    (mem_bytes m' (be + oe) 4) res.
Proof.
  intros Hfull Hprof Hcodec Herrno Eout Est Haddr Lxo Vo Lys Vs Hn Vss.
  pose proof Hfull as (_ & Hres). subst out state.
  assert (Hst4 : take 4 (mem_bytes m' (bs + os) 8) = mem_bytes m' (bs + os) 4) by reflexivity.
  assert (Hsrc : forall i, 0 <= i < n -> exists x, ss !! Z.to_nat i = Some x /\ m_bytes m (ptr_addr src + i) = x).
  { intros i Hi. destruct (lookup_lt_is_Some_2 ss (Z.to_nat i) ltac:(lia)) as [x Hx]. exists x.
    split; [exact Hx|]. rewrite Haddr. rewrite <- (Vss _ _ Hx). f_equal. lia. }
  assert (Hnz : forall k, k <= n -> (forall i, 0 <= i < k -> m_bytes m (ptr_addr src + i) <> 0) ->
            Forall (fun x => x <> 0) (take (Z.to_nat k) ss)).
  { intros k Hk H. apply Forall_lookup. intros i x Hx. apply lookup_take_Some in Hx as [Hx Hi].
    destruct (Hsrc (Z.of_nat i) ltac:(lia)) as (x' & Hx' & Hb). rewrite Nat2Z.id Hx in Hx'.
    injection Hx' as <-. rewrite <- Hb. apply H. lia. }
  assert (Hkept : (forall a, span_contains (mkSpan (mkPtr (bo + oo) (Obj bo)) 4) a -> m_bytes m' a = m_bytes m a) ->
            mem_bytes m' (bo + oo) 4 = xo).
  { intros H. rewrite <- Lxo. apply mem_bytes_of. intros i x Hx.
    pose proof (lookup_lt_Some _ _ _ Hx) as Hi. rewrite Lxo in Hi.
    rewrite H; [exact (Vo i x Hx)|]. unfold span_contains. cbn. lia. }
  destruct Hres as [(-> & Hv & Hp) | [(Hr & Hr2 & Hv & Hp) | [(-> & He & Hk & _) | (-> & Hv & Hk & Hp)]]].
  - left. destruct (Hp Hprof) as ((i & Hi & Hz) & Ho & Hs). split; [reflexivity|].
    split; [rewrite <- Hcodec; exact Hv|]. split.
    + destruct (Hsrc i Hi) as (x & Hx & Hb). exists (Z.to_nat i). split; [lia|]. rewrite Hx. congruence.
    + rewrite Hst4. rewrite <- !load_bytes_4. split; [exact Ho | exact Hs].
  - right; left. destruct (Hp Hprof) as (Ho & Hs & Hb). split; [exact Hr|]. split; [exact Hr2|].
    split; [rewrite <- Hcodec; exact Hv|].
    rewrite Hst4. rewrite <- !load_bytes_4. split; [exact Ho|]. split; [exact Hs|]. apply Hnz; [lia | exact Hb].
  - right; right; left. split; [reflexivity|]. split; [rewrite <- load_bytes_4; rewrite Herrno in He; exact He|].
    split; [exact (Hkept Hk)|]. split.
    { intros Hc. rewrite <- Hcodec in Hc.
      destruct (mbrtowc_c_error _ _ _ _ _ _ _ _ _ Hfull Hc) as [Hst Hsrc0]. split.
      + rewrite <- (mem_bytes_of m (bs + os) ys Vs). rewrite Lys. exact Hst.
      + destruct (Hsrc 0 ltac:(lia)) as (x & Hx & Hb). exists x. split; [exact Hx|].
        rewrite <- Hb, Z.add_0_r. exact Hsrc0. }
    { intros Hv0 Hz0. rewrite <- Hcodec in Hv0.
      assert (Ey : mem_bytes m (bs + os) 8 = ys).
      { rewrite <- (mem_bytes_of m (bs + os) ys Vs). rewrite Lys. reflexivity. }
      assert (Hl0 : load_bytes m (ptr_addr (mkPtr (bs + os) (Obj bs))) 4 = 0).
      { cbn [ptr_addr]. rewrite load_bytes_4. rewrite <- Ey in Hz0. exact Hz0. }
      rewrite <- Ey in Hv0.
      destruct (mbrtowc_initial_error _ _ _ _ _ _ _ _ _ Hfull Hprof Hl0 Hv0) as (Hv' & Hc' & Hs0).
      split; [rewrite <- Hcodec; exact Hv'|]. split.
      + rewrite Hst4. rewrite <- load_bytes_4. exact Hc'.
      + destruct (Hsrc 0 ltac:(lia)) as (x & Hx & Hb). exists x. split; [exact Hx|].
        rewrite <- Hb, Z.add_0_r. exact Hs0. }
  - right; right; right. destruct (Hp Hprof) as [Hn16 Hb]. split; [reflexivity|].
    split; [rewrite <- Hcodec; exact Hv|]. split; [exact (Hkept Hk)|].
    split; [exact Hn16|]. apply Hnz; [lia | exact Hb].
Qed.

(** mbrtowc(out, src, n, state)'s triple, from [mbrtowc_contract]:
    owning the output, state and errno blocks, of 4, 8 and 4 bytes with
    their slots, and the source's life and bytes ss, of four different
    objects, where vo, vs, vn and vt read as out, src, n and state, n is
    positive and within ss, and the state's bytes are valid, the call
    binds d to its result r and hands the blocks back holding new bytes
    and slots, which [conv_result] describes. *)
Lemma wp_mbrtowc f e ls lab d vo vs vn vt rest j out src n state
    bo ro oo xo co bs rs os ys cs be re oe xe ce bsrc rsrc osrc ss codec dq Φ :
  find_fn ge (TAtom "mbrtowc") = None -> lookup (TAtom "mbrtowc") (ge_globals ge) = None ->
  arg_x ge e (Arg P vo) = Some (WPtr out) -> arg_x ge e (Arg P vs) = Some (WPtr src) ->
  arg_x ge e (Arg L vn) = Some (WInt n) -> arg_x ge e (Arg P vt) = Some (WPtr state) ->
  out = mkPtr (bo + oo) (Obj bo) -> state = mkPtr (bs + os) (Obj bs) -> errno = mkPtr (be + oe) (Obj be) ->
  (ptr_cap src = Obj bsrc \/ ptr_cap src = Ro bsrc) -> ptr_addr src = bsrc + osrc ->
  0 < bo -> 0 < bs -> 0 < bsrc -> (bo + oo) mod 4 = 0 -> (bs + os) mod 4 = 0 ->
  length xo = 4%nat -> length co = 4%nat -> length ys = 8%nat -> length cs = 8%nat ->
  length xe = 4%nat -> length ce = 4%nat ->
  0 < n <= Z.of_nat (length ss) -> Forall (fun x => 0 <= x < 256) ss -> valid codec ys ->
  pointsto (PName codec_key) dq (VCodec codec) -∗
  pts (block_ps bo ro oo xo co) -∗ pts (block_ps bs rs os ys cs) -∗ pts (block_ps be re oe xe ce) -∗
  pts (block_ps bsrc rsrc osrc ss []) -∗
  ▷ (∀ r xo' ys' xe' co' cs' ce',
       ⌜conv_result valid (audit codec = Some CodecC) codec n ss xo ys xo' ys' xe' r /\ length xo' = 4%nat /\ length ys' = 8%nat /\
        length xe' = 4%nat /\ length co' = 4%nat /\ length cs' = 8%nat /\ length ce' = 4%nat⌝ -∗
       pointsto (PName codec_key) dq (VCodec codec) -∗ pts (block_ps bo ro oo xo' co') -∗ pts (block_ps bs rs os ys' cs') -∗ pts (block_ps be re oe xe' ce') -∗
       pts (block_ps bsrc rsrc osrc ss []) -∗
       WP (ERun (mkFrame f (put d (WInt r) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "mbrtowc")) [Arg P vo; Arg P vs; Arg L vn; Arg P vt]
                          :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hfn Hdata Hvo Hvs Hvn Hvt Eout Est Herr Hcap Haddr Hbo Hbs Hbsrc Hoal Hsal Lxo Lco Lys Lcs Lxe Lce
    Hn Hss Hval.
  iIntros "Hcod HBo HBs HBe HBsrc HK".
  iDestruct (block_ne with "HBo HBs") as %N1. iDestruct (block_ne with "HBo HBe") as %N2.
  iDestruct (block_ne with "HBo HBsrc") as %N3. iDestruct (block_ne with "HBs HBe") as %N4.
  iDestruct (block_ne with "HBs HBsrc") as %N5. iDestruct (block_ne with "HBe HBsrc") as %N6.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (mbrtowc_contract valid audit rep requests)
            [WPtr out; WPtr src; WInt n; WPtr state]
            (pointsto (PName codec_key) dq (VCodec codec) ∗
             pts (block_ps bo ro oo xo co) ∗ pts (block_ps bs rs os ys cs) ∗ pts (block_ps be re oe xe ce) ∗
             pts (block_ps bsrc rsrc osrc ss []))
            with "[$Hcod $HBo $HBs $HBe $HBsrc] [HK]");
    [exact Hfn | exact Hdata | reflexivity | exact Hmbrtowc | cbn [map_option]; rewrite Hvo Hvs Hvn Hvt; reflexivity
    | | |].
  - split; [right; eexists; reflexivity | do 4 eexists; reflexivity].
  - iIntros (σ) "Hσ (Hc & Ho & Hs & He & Hsr)". iDestruct "Hσ" as (h) "[Hh %Hf]".
    destruct Hf as (Ha & Hd & Hr & Hw). iDestruct (gen_heap_valid with "Hh Hc") as %Kc.
    iDestruct (pts_lookup with "Hh Ho") as %Ko. iDestruct (pts_lookup with "Hh Hs") as %Ks.
    iDestruct (pts_lookup with "Hh He") as %Ke. iDestruct (pts_lookup with "Hh Hsr") as %Ksr. iPureIntro.
    exact (mbrtowc_admitted _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hw Ha Hd
             (R.address_space _ _ Hr) Kc Ko Ks Ke Ksr N1 N2 N3 N4 N5 N6 Eout Est Herr Hcap Haddr Hbo Hbs Hbsrc Hoal Hsal
             Lxo Lys Lxe Hn Hss Hval).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) (Hc & Ho & Hs & He & Hsr)".
    destruct Hf as (Ha & Hd & Hr & Hw). iDestruct (gen_heap_valid with "Hh Hc") as %Kc.
    iDestruct (pts_lookup with "Hh Ho") as %Ko. iDestruct (pts_lookup with "Hh Hs") as %Ks.
    iDestruct (pts_lookup with "Hh He") as %Ke. iDestruct (pts_lookup with "Hh Hsr") as %Ksr.
    destruct (Hlibc _ _ _ Hw) as (_ & Hcur & Herrno & _). pose proof (Hcur _ Kc) as Hcodec.
    destruct (block_facts _ h bo ro oo xo co Ha Ko (nonempty_of_length xo 3 Lxo)) as (_ & _ & _ & Vo).
    destruct (block_facts _ h bs rs os ys cs Ha Ks (nonempty_of_length ys 7 Lys)) as (_ & _ & _ & Vs).
    destruct (block_facts _ h bsrc rsrc osrc ss [] Ha Ksr ltac:(intros E; rewrite E in Hn; cbn in Hn; lia))
      as (_ & _ & _ & Vsr).
    destruct (LB.mbrtowc_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (res & -> & Hres).
    rewrite (proj2 (Z.eqb_neq n 0) ltac:(lia)) in Hres.
    assert (Hnl : 0 < n <= Z.of_nat (length ss)) by lia.
    assert (Hn0 : n <> 0) by lia.
    pose proof (conv_of_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hres (Haudit _ _ _ Hw) Hcodec
                  (eq_trans Herrno Herr) Eout Est Haddr Lxo Vo Lys Vs Hnl Vsr) as Hconv.
    destruct (mbrtowc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv Hw Ha Hd Hr Ko Ks Ke
                Eout Est Herr Lxo Lco Lys Lcs Lxe Lce Hn0) as (Ha' & Hd' & Hr').
    assert (Hlk : forall l v, (l, v) ∈ block_ps bo ro oo xo co ++ block_ps bs rs os ys cs ++ block_ps be re oe xe ce ->
                    h !! l = Some v).
    { intros l v Hin. rewrite !elem_of_app in Hin. destruct Hin as [Hin|[Hin|Hin]]; auto. }
    pose proof (Kmbrtowc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv Hlk Hw) as Hw'.
    iMod (pts_update _ (block_ps bo ro oo xo co ++ block_ps bs rs os ys cs ++ block_ps be re oe xe ce)
            (block_ps bo ro oo (mem_bytes m' (bo + oo) 4) (mem_auxes m' (bo + oo) 4) ++
             block_ps bs rs os (mem_bytes m' (bs + os) 8) (mem_auxes m' (bs + os) 8) ++
             block_ps be re oe (mem_bytes m' (be + oe) 4) (mem_auxes m' (be + oe) 4))
            with "Hh [Ho Hs He]") as "[Hh Hn]".
    { rewrite !fmap_app. rewrite (block_ps_keys bo ro oo xo co); [| rewrite length_mem_bytes; auto | rewrite length_mem_auxes; auto].
      rewrite (block_ps_keys bs rs os ys cs); [| rewrite length_mem_bytes; auto | rewrite length_mem_auxes; auto].
      rewrite (block_ps_keys be re oe xe ce); [| rewrite length_mem_bytes; auto | rewrite length_mem_auxes; auto].
      reflexivity. }
    { rewrite !pts_app. iFrame. }
    iModIntro. iExists _. iSplit.
    { iPureIntro. unfold external_env. cbn. rewrite Z.mod_small; [reflexivity | exact (proj1 Hres)]. }
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. auto.
    + rewrite !pts_app. iDestruct "Hn" as "(Ho & Hs & He)".
      iApply ("HK" $! res with "[%] Hc Ho Hs He Hsr").
      rewrite !length_mem_bytes !length_mem_auxes. split; [exact Hconv|]. repeat split.
Qed.

(** ## rpl_mbrtowc's triple *)

(** The genv links Hello, whose world interpretation keeps every lent
    string where [lent_at] says: hard_locale's premises (HelloLocale.v). *)
Context (Hlinked : hello_linked ge)
  (wi_lent : forall m w h k p t, wi m w h -> live_disjoint m -> objects_fit (m_regions m) ->
     freed_empty (m_regions m) -> h !! PName k = Some (VName p t) -> lent_at m h p t).

(** setlocale's query, as hard_locale needs it. *)
Context (set_spec : contract libc_world) (Hset : registry (TAtom "setlocale") = Some set_spec)
  (Hset_ret : contract_returns set_spec = RClass P)
  (Hset_abi : forall d c v, contract_abi set_spec (CResult d P) [Arg W c; Arg P v])
  (Hset_pre : forall m w h k p t z, wi m w h -> h !! PName k = Some (VName p t) -> ptr_addr z = 0 ->
     contract_pre set_spec [WInt k; WPtr z] m w)
  (Hset_query : forall r args s m w h k p t z trace ending s' m' w',
     wi m w h -> h !! PName k = Some (VName p t) -> ptr_addr z = 0 ->
     M.E.invoke set_spec r args [WInt k; WPtr z] s m w trace ending s' m' w' ->
     s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr p]).

(** strlen, memcpy and strcmp have their contracts. *)
Context (Hstrlen : registry (TAtom "strlen") = Some (strlen_contract libc_world))
  (Hmemcpy : registry (TAtom "memcpy") = Some (memcpy_contract libc_world))
  (Hstrcmp : registry (TAtom "strcmp") = Some (strcmp_contract libc_world)).

(** The world interpretation survives a copy, a byte store and a
    four-byte store into a block the program owns, and an allocation. *)
Context (Kcopy : forall b reg o xs cs s n m m' wd h ys,
     copy_result m (mkPtr (b + o) (Obj b)) s n m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     length ys = length xs ->
     wi m' wd (overwrite (block_ps b reg o ys (slots_after m' b o (length xs))) h))
  (Kbyte : forall b reg o x y m wd h,
     (forall l v, (l, v) ∈ [(PLive b, VLive reg); (PByte b o, VByte x)] -> h !! l = Some v) ->
     wi m wd h ->
     wi (store_bytes m (b + o) 1 y) wd (overwrite [(PLive b, VLive reg); (PByte b o, VByte (y mod 256))] h))
  (Kstore : forall b reg o xs y m wd h,
     (forall l v, (l, v) ∈ (PLive b, VLive reg) :: byte_ps b o xs -> h !! l = Some v) -> wi m wd h ->
     wi (store_bytes m (b + o) 4 y) wd (overwrite ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 4)) h))
  (Kalloc : forall q m wd h base, fresh m q base -> wi m wd h ->
     wi (allocated m q base) wd (overwrite (obj_ps base q) h)).

(** Enter a block of rpl_mbrtowc. *)
Ltac rm_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (rpl_block s));
  [vm_compute; reflexivity | word_premise |]; iNext;
  cbn [b_insts b_jump rpl_block hblk].

(** A pure instruction. *)
Ltac rm_let :=
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]; iNext.

(** rpl_mbrtowc from its block L11, where pr.1 is the output pointer
    out, whichever entry chose it: the call to mbrtowc, then the
    fallback outside a hard locale. *)
Lemma rpl_tail pwc b8 b13 b15 out src n state bo ro oo xo co bs rs os ys cs be re oe xe ce
    bsrc rsrc osrc ss codec dq p t rc rp Φ :
  out = mkPtr (bo + oo) (Obj bo) -> state = mkPtr (bs + os) (Obj bs) -> errno = mkPtr (be + oe) (Obj be) ->
  (ptr_cap src = Obj bsrc \/ ptr_cap src = Ro bsrc) -> ptr_addr src = bsrc + osrc ->
  0 < bo -> 0 < bs -> 0 < bsrc -> 0 <= oo -> 0 <= osrc ->
  bo + oo + 4 <= r_end ro -> bsrc + osrc + Z.of_nat (length ss) <= r_end rsrc ->
  r_end ro <= 2 ^ 48 -> r_end rsrc <= 2 ^ 48 ->
  (bo + oo) mod 4 = 0 -> (bs + os) mod 4 = 0 ->
  length xo = 4%nat -> length co = 4%nat -> length ys = 8%nat -> length cs = 8%nat ->
  length xe = 4%nat -> length ce = 4%nat ->
  0 < n <= Z.of_nat (length ss) -> Forall (fun x => 0 <= x < 256) ss -> valid codec ys ->
  LL.lent 0 p t -∗ SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
  pointsto (PName codec_key) dq (VCodec codec) -∗
  pts (block_ps bo ro oo xo co) -∗ pts (block_ps bs rs os ys cs) -∗ pts (block_ps be re oe xe ce) -∗
  pts (block_ps bsrc rsrc osrc ss []) -∗
  ▷ (∀ r xo' ys' xe' co' cs' ce',
       ⌜rpl_result valid (audit codec = Some CodecC) codec n ss xo ys xo' ys' xe' r /\
        length xo' = 4%nat /\ length ys' = 8%nat /\ length xe' = 4%nat /\
        length co' = 4%nat /\ length cs' = 8%nat /\ length ce' = 4%nat⌝ -∗
       SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
       pointsto (PName codec_key) dq (VCodec codec) -∗ pts (block_ps bo ro oo xo' co') -∗
       pts (block_ps bs rs os ys' cs') -∗ pts (block_ps be re oe xe' ce') -∗
       pts (block_ps bsrc rsrc osrc ss []) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame rpl_fn
        (put (TAtom "pr.1") (WPtr out) (put (TAtom "v15") b15 (put (TAtom "v13") b13 (put (TAtom "v8") b8
          [(TAtom "v6", WPtr state); (TAtom "v4", WInt n); (TAtom "v2", WPtr src); (TAtom "v0", pwc)]))))
        [] None (Exec (TAtom "L11") (b_insts (rpl_block "L11")) (b_jump (rpl_block "L11")))) : cexpr) {{ Φ }}.
Proof.
  intros Eout Est Herr Hcap Haddr Hbo Hbs Hbsrc Hoo Hosrc Heo Hesrc Ho48 Hs48 Hoal Hsal
    Lxo Lco Lys Lcs Lxe Lce Hn Hss Hval.
  iIntros "#Hk Hc Hposix Hcod HBo HBs HBe HBsrc HΦ".
  assert (Hn64 : n mod 2 ^ 64 = n) by (apply Z.mod_small; lia).
  pose proof Hlinked as (Hm & _ & Hext).
  cbn [b_insts b_jump rpl_block hblk].
  iApply (wp_mbrtowc with "Hcod HBo HBs HBe HBsrc");
    [apply hello_outside; [exact Hm | reflexivity] | apply Hext; reflexivity |
     word_premise | word_premise | word_premise | word_premise |
     exact Eout | exact Est | exact Herr | exact Hcap | exact Haddr | exact Hbo | exact Hbs | exact Hbsrc |
     exact Hoal | exact Hsal | exact Lxo | exact Lco | exact Lys | exact Lcs | exact Lxe | exact Lce |
     rewrite Hn64; exact Hn | exact Hss | exact Hval |].
  iNext. iIntros (res xo1 ys1 xe1 co1 cs1 ce1 (Hconv & Lxo1 & Lys1 & Lxe1 & Lco1 & Lcs1 & Lce1))
    "Hcod HBo HBs HBe HBsrc".
  rewrite Hn64 in Hconv.
  destruct (conv_result_range _ _ _ _ _ _ _ _ _ _ _ Hconv) as [Hres Hkeep].
  destruct (Z.le_gt_cases (2 ^ 64 - 2) res) as [Hge | Hlt].
  - (* An invalid or incomplete sequence. *)
    rm_let. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    rm_enter "L29". rm_let. iApply wp_goto. iNext. rm_enter "L30".
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    rm_enter "L35".
    iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ hard_locale_fn
              (invocation hard_locale_fn [WInt 0]));
      [word_premise | unfold find_fn; rewrite Hm; vm_compute; reflexivity | reflexivity |].
    iNext.
    iApply (HLo.hard_locale_spec registry wi ge Hlinked wi_lent set_spec Hset Hset_ret Hset_abi
              Hset_pre Hset_query Hstrlen Hmemcpy Kcopy Kbyte Kalloc Hstrcmp with "Hk Hc Hposix");
      [lia|].
    iNext. iIntros (hr) "Hc Hposix". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
    rm_let. rm_let. iApply wp_goto. iNext. rm_enter "L36".
    iApply wp_branch; [word_premise|]. iNext.
    lazymatch goal with |- context[if ?t then 1 else 0] => destruct t end.
    all: change (1 mod 2 ^ 32) with 1; change (0 mod 2 ^ 32) with 0; cbn [Z.eqb edge_label].
    + (* Not a hard locale: the first byte stands for itself. *)
      rm_enter "L22".
      destruct ss as [|x0 ss']; [cbn in Hn; lia|].
      pose proof (Forall_inv Hss) as Hx0. cbv beta in Hx0.
      iEval (rewrite /block_ps; rewrite /pts big_sepL_cons big_sepL_app byte_ps_cons big_sepL_cons) in "HBsrc".
      iEval (rewrite /block_ps; rewrite /pts big_sepL_cons big_sepL_app) in "HBo".
      iDestruct "HBsrc" as "(Hls & (Hb0 & Hbs) & Has)". iDestruct "HBo" as "(Hlo & Hbo & Hao)".
      iAssert (live bsrc rsrc) with "[Hls]" as "Hls"; [rewrite /live /pts big_sepL_singleton; iExact "Hls"|].
      iAssert (ibyte bsrc osrc x0) with "[Hb0]" as "Hb0"; [rewrite /ibyte /pts big_sepL_singleton; iExact "Hb0"|].
      iAssert (live bo ro) with "[Hlo]" as "Hlo"; [rewrite /live /pts big_sepL_singleton; iExact "Hlo"|].
      iAssert (bytes bo oo xo1) with "[Hbo]" as "Hbo"; [rewrite /bytes /pts; iExact "Hbo"|].
      iApply (wp_check_read with "Hls");
        [reflexivity | word_premise | exact Hcap | rewrite Haddr; addr_premise |
         rewrite Haddr; cbn [length] in Hesrc; addr_premise | apply Z.mod_1_r |].
      iNext. iIntros "Hls". gen_env.
      iApply (wp_raw_load_byte with "Hls Hb0");
        [reflexivity | word_premise | reflexivity | reflexivity | exact Hcap | rewrite Haddr; addr_premise |].
      iNext. iIntros "Hls Hb0". gen_env.
      iApply (wp_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (WInt x0));
        [reflexivity | reflexivity | word_premise | intros m'; cbn; rewrite (Zmod_mod (sign_extension 256 128 x0) (2 ^ 32));
         exact (f_equal (fun z => Some (OpRes (RVal (WInt z)) m')) (ub_of_sb x0 Hx0)) |].
      iNext. gen_env.
      iApply (wp_check with "Hlo");
        [reflexivity | word_premise | rewrite Eout; reflexivity | rewrite Eout; addr_premise |
         rewrite Eout; addr_premise | apply Z.mod_1_r |].
      iNext. iIntros "Hlo". gen_env.
      iApply (wp_raw_store_w with "Hlo Hbo");
        [word_premise | word_premise | rewrite Eout; reflexivity | rewrite Eout; addr_premise | exact Lxo1 |
         intros m' wd h Hl Hw; exact (Kstore _ _ _ _ _ _ _ _ Hl Hw) |].
      iNext. iIntros "Hlo Hbo".
      assert (Hx32 : x0 mod 2 ^ 32 = x0) by (apply Z.mod_small; lia).
      iEval (rewrite Hx32) in "Hbo".
      iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      iApply ("HΦ" $! 1 (le_bytes x0 4) ys1 xe1 co1 cs1 ce1 with "[%] Hc Hposix Hcod [Hlo Hbo Hao] HBs HBe [Hls Hb0 Hbs Has]").
      * split; [| rewrite length_le_bytes; repeat split; first [assumption | reflexivity]].
        right. split; [reflexivity|]. split.
        { exists res. split; [exact Hge|]. rewrite (Hkeep Hge) in Hconv. exact Hconv. }
        exists x0. split; reflexivity.
      * rewrite /block_ps /pts big_sepL_cons big_sepL_app.
        rewrite /live /bytes /pts big_sepL_singleton. iFrame.
      * rewrite /block_ps /pts big_sepL_cons big_sepL_app byte_ps_cons big_sepL_cons.
        rewrite /live /ibyte /pts !big_sepL_singleton. iFrame.
    + (* A hard locale: mbrtowc's answer. *)
      rm_enter "L24". iApply wp_ret; [reflexivity | word_premise |]. iNext.
    rewrite (Z.mod_small res (2 ^ 64)); [|lia].
      iApply ("HΦ" $! res xo1 ys1 xe1 co1 cs1 ce1 with "[%] Hc Hposix Hcod HBo HBs HBe HBsrc").
      split; [left; exact Hconv|]. repeat split; assumption.
  - (* A character, a NUL or nothing to stand for: mbrtowc's answer. *)
    rm_let. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    rm_enter "L30". iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    rm_enter "L36". iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    rm_enter "L24". iApply wp_ret; [reflexivity | word_premise |]. iNext.
    rewrite (Z.mod_small res (2 ^ 64)); [|lia].
    iApply ("HΦ" $! res xo1 ys1 xe1 co1 cs1 ce1 with "[%] Hc Hposix Hcod HBo HBs HBe HBsrc").
    split; [left; exact Hconv|]. repeat split; assumption.
Qed.

(** rpl_mbrtowc(out, src, n, state) for a non-null out, from
    [wp_mbrtowc] and HelloLocale.v's [hard_locale_spec]: owning the
    output, state and errno blocks, the source's n bytes or more, the
    codec piece, the literals "C" and "POSIX", and the name of LC_CTYPE
    (category 0) lent, the call returns what [rpl_result] says, and
    hands every block back. *)
Lemma rpl_mbrtowc_spec out src n state bo ro oo xo co bs rs os ys cs be re oe xe ce
    bsrc rsrc osrc ss codec dq p t rc rp Φ :
  out = mkPtr (bo + oo) (Obj bo) -> state = mkPtr (bs + os) (Obj bs) -> errno = mkPtr (be + oe) (Obj be) ->
  (ptr_cap src = Obj bsrc \/ ptr_cap src = Ro bsrc) -> ptr_addr src = bsrc + osrc ->
  0 < bo -> 0 < bs -> 0 < bsrc -> 0 <= oo -> 0 <= osrc ->
  bo + oo + 4 <= r_end ro -> bsrc + osrc + Z.of_nat (length ss) <= r_end rsrc ->
  r_end ro <= 2 ^ 48 -> r_end rsrc <= 2 ^ 48 ->
  (bo + oo) mod 4 = 0 -> (bs + os) mod 4 = 0 ->
  length xo = 4%nat -> length co = 4%nat -> length ys = 8%nat -> length cs = 8%nat ->
  length xe = 4%nat -> length ce = 4%nat ->
  0 < n <= Z.of_nat (length ss) -> Forall (fun x => 0 <= x < 256) ss -> valid codec ys ->
  LL.lent 0 p t -∗ SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
  pointsto (PName codec_key) dq (VCodec codec) -∗
  pts (block_ps bo ro oo xo co) -∗ pts (block_ps bs rs os ys cs) -∗ pts (block_ps be re oe xe ce) -∗
  pts (block_ps bsrc rsrc osrc ss []) -∗
  ▷ (∀ r xo' ys' xe' co' cs' ce',
       ⌜rpl_result valid (audit codec = Some CodecC) codec n ss xo ys xo' ys' xe' r /\
        length xo' = 4%nat /\ length ys' = 8%nat /\ length xe' = 4%nat /\
        length co' = 4%nat /\ length cs' = 8%nat /\ length ce' = 4%nat⌝ -∗
       SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
       pointsto (PName codec_key) dq (VCodec codec) -∗ pts (block_ps bo ro oo xo' co') -∗
       pts (block_ps bs rs os ys' cs') -∗ pts (block_ps be re oe xe' ce') -∗
       pts (block_ps bsrc rsrc osrc ss []) -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (invocation rpl_fn [WPtr out; WPtr src; WInt n; WPtr state]) : cexpr) {{ Φ }}.
Proof.
  intros Eout Est Herr Hcap Haddr Hbo Hbs Hbsrc Hoo Hosrc Heo Hesrc Ho48 Hs48 Hoal Hsal
    Lxo Lco Lys Lcs Lxe Lce Hn Hss Hval.
  iIntros "#Hk Hc Hposix Hcod HBo HBs HBe HBsrc HΦ".
  rewrite rpl_entry. rm_enter "start".
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 4);
    [reflexivity | lia | unfold max_allocation_size; lia | intros m wd h base Hf Hw; exact (Kalloc _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (base _) "_".
  rm_let. rm_let.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [subst out; word_premise|]. iNext. cbn [Z.eqb edge_label].
  rm_enter "L10". iApply wp_goto. iNext. rm_enter "L11".
  iApply (rpl_tail with "Hk Hc Hposix Hcod HBo HBs HBe HBsrc HΦ"); assumption.
Qed.

(** ## rpl_mbsrtowcs's window *)

(** The memchr contract, for `strnlen1`. *)
Context (Hmemchr : registry (TAtom "memchr") = Some (memchr_contract libc_world)).

(** Enter a block of rpl_mbsrtowcs. *)
Ltac ms_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (mbs_block s));
  [vm_compute; reflexivity | word_premise |]; iNext;
  cbn [b_insts b_jump mbs_block hblk].

(** Read byte k of the window in block blk, after the first: a flight
    to q + k, a half check against the first check, a load and its
    test. Leaves the branch on the test, with the byte named x. *)
Ltac mid_read blk q bs k Hc x Hx Hxr Hz Hn Hbs :=
  ms_enter blk;
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr q + Z.of_nat k));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]; iNext; gen_env;
  destruct (lookup_lt_is_Some_2 (bs ++ [0]) k) as [x Hx]; [rewrite length_app; cbn; lia|];
  destruct (nul_index _ _ _ Hbs Hx) as (Hxr & Hz & Hn);
  iDestruct (string_byte _ _ _ _ k x with "Hs") as "(_ & Hl & Hb & Hk)"; [exact Hx|];
  iApply (wp_half_check_read with "Hl");
    [reflexivity | word_premise | reflexivity | exact Hc | addr_premise | addr_premise | lia | lia |
     apply Z.mod_1_r |];
  iNext; iIntros "Hl"; gen_env;
  iApply (wp_raw_load_byte with "Hl Hb");
    [reflexivity | word_premise | reflexivity | reflexivity | exact Hc | addr_premise |];
  iNext; iIntros "Hl Hb"; iDestruct ("Hk" with "Hl Hb") as "Hs"; gen_env;
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]; iNext; gen_env.

(** The temporaries the converting loop keeps, and their values: the
    destination cursor, the source cursor, the count left, the state,
    srcp, its check, and the destination's address. *)
Definition mbs_vars (e : env) (q : ptr) (dst len st sp c0 d0 : word) : Prop :=
  lookup (TAtom "pr.5") e = Some (WPtr q) /\ lookup (TAtom "pr.7") e = Some dst /\
  lookup (TAtom "pr.1") e = Some len /\ lookup (TAtom "pr.2") e = Some st /\
  lookup (TAtom "v2") e = Some sp /\ lookup (TAtom "chk0") e = Some c0 /\
  lookup (TAtom "v23") e = Some d0.

(** End the window at L37, with the window's length n in pr.8. *)
Ltac close_window L :=
  ms_enter "L37"; gen_env;
  iApply ("HK" with "[%] Hs"); split; [repeat split; assumption|];
  match goal with H : lookup (TAtom "pr.8") _ = Some _ |- _ => rewrite H end;
  rewrite <- L; reflexivity.

(** rpl_mbsrtowcs's window, blocks L29 to L57: with the source cursor q
    at a string bs, the loop reads up to four bytes, stopping at the
    NUL, and then asks strnlen1 for at most 12 more; pr.8 is then
    min(len + 1, 16), and the loop's other temporaries are as they
    were. *)
Lemma mbs_window e q dst len st sp c0 d0 b reg bs Φ :
  mbs_vars e q dst len st sp c0 d0 ->
  SL.string q b reg bs -∗
  ▷ (∀ e', ⌜mbs_vars e' q dst len st sp c0 d0 /\
             lookup (TAtom "pr.8") e' = Some (WInt (Z.min (Z.of_nat (length bs) + 1) 16))⌝ -∗
        SL.string q b reg bs -∗
        WP (ERun (mkFrame mbs_fn e' [] None
              (Exec (TAtom "L37") (b_insts (mbs_block "L37")) (b_jump (mbs_block "L37")))) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame mbs_fn e [] None
        (Exec (TAtom "L29") (b_insts (mbs_block "L29")) (b_jump (mbs_block "L29")))) : cexpr) {{ Φ }}.
Proof.
  intros (Hq & H7 & H1 & H2 & Hv2 & Hc0 & H23). iIntros "Hs HK".
  iDestruct "Hs" as "[%Hok Hps]". iAssert (SL.string q b reg bs) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hc & Hb0 & Hbq & Hend & H48 & Hbs).
  pose proof (Hm := proj1 Hlinked).
  cbn [b_insts b_jump mbs_block hblk].
  (* The first byte, through a check. *)
  destruct (lookup_lt_is_Some_2 (bs ++ [0]) 0) as [x0 Hx0]; [rewrite length_app; cbn; lia|].
  destruct (nul_index _ _ _ Hbs Hx0) as (Hx0r & Hz0 & Hn0).
  iDestruct (string_byte _ _ _ _ 0 x0 with "Hs") as "(_ & Hl & Hb & Hk)"; [exact Hx0|].
  iApply (wp_check_read with "Hl");
    [reflexivity | word_premise | exact Hc | addr_premise | addr_premise | apply Z.mod_1_r |].
  iNext. iIntros "Hl". gen_env.
  iApply (wp_raw_load_byte with "Hl Hb");
    [reflexivity | word_premise | reflexivity | reflexivity | exact Hc | addr_premise |].
  iNext. iIntros "Hl Hb". iDestruct ("Hk" with "Hl Hb") as "Hs". gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  destruct (Z.eqb_spec x0 0) as [E0|E0].
  { subst x0. (* The NUL first: a window of one byte. *)
    pose proof (Hz0 eq_refl) as L0. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|].
    iNext. cbn [Z.eqb edge_label]. close_window L0. }
  pose proof (Hn0 E0) as L0.
  match goal with H : lookup (TAtom "v41") _ = _ |- _ => rewrite (sb_ne x0) in H; [|lia] end.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  (* The second byte. *)
  ms_enter "L36".
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr q + Z.of_nat 1));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]. iNext. gen_env.
  destruct (lookup_lt_is_Some_2 (bs ++ [0]) 1) as [x1 Hx1]; [rewrite length_app; cbn; lia|].
  destruct (nul_index _ _ _ Hbs Hx1) as (Hx1r & Hz1 & Hn1).
  iDestruct (string_byte _ _ _ _ 1 x1 with "Hs") as "(_ & Hl & Hb & Hk)"; [exact Hx1|].
  iApply (wp_half_check_read with "Hl");
    [reflexivity | word_premise | reflexivity | exact Hc | addr_premise | addr_premise | lia | lia |
     apply Z.mod_1_r |].
  iNext. iIntros "Hl". gen_env.
  iApply (wp_raw_load_byte with "Hl Hb");
    [reflexivity | word_premise | reflexivity | reflexivity | exact Hc | addr_premise |].
  iNext. iIntros "Hl Hb". iDestruct ("Hk" with "Hl Hb") as "Hs". gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eqb_spec x1 0) as [E1|E1].
  { subst x1. pose proof (Hz1 eq_refl) as L1. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|].
    iNext. cbn [Z.eqb edge_label]. close_window L1. }
  pose proof (Hn1 E1) as L1.
  match goal with H : lookup (TAtom "v48") _ = _ |- _ => rewrite (sb_ne x1) in H; [|lia] end.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  (* The third byte. *)
  mid_read "L43" q bs 2%nat Hc x2 Hx2 Hx2r Hz2 Hn2 Hbs.
  destruct (Z.eqb_spec x2 0) as [E2|E2].
  { subst x2. pose proof (Hz2 eq_refl) as L2. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|].
    iNext. cbn [Z.eqb edge_label]. close_window L2. }
  pose proof (Hn2 E2) as L2.
  match goal with H : lookup (TAtom "v55") _ = _ |- _ => rewrite (sb_ne x2) in H; [|lia] end.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  (* The fourth byte. *)
  mid_read "L60" q bs 3%nat Hc x3 Hx3 Hx3r Hz3 Hn3 Hbs.
  destruct (Z.eqb_spec x3 0) as [E3|E3].
  { subst x3. pose proof (Hz3 eq_refl) as L3. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|].
    iNext. cbn [Z.eqb edge_label]. close_window L3. }
  pose proof (Hn3 E3) as L3.
  match goal with H : lookup (TAtom "v65") _ = _ |- _ => rewrite (sb_ne x3) in H; [|lia] end.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  (* Four bytes before the NUL: strnlen1 counts the rest, up to 12. *)
  ms_enter "L57".
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr q + Z.of_nat 4));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]. iNext. gen_env.
  iDestruct (string_suffix _ _ _ _ 4 with "Hs") as "[Hs4 Hback]"; [lia|].
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ strnlen1_fn
            (invocation strnlen1_fn [WPtr (mkPtr (ptr_addr q + Z.of_nat 4) (ptr_cap q)); WInt 12]));
    [word_premise | unfold find_fn; rewrite Hm; vm_compute; reflexivity | reflexivity |].
  iNext. iApply (HL.strnlen1_spec registry wi ge Hlinked with "Hs4"); [exact Hmemchr | lia |].
  iNext. iIntros "Hs4". iDestruct ("Hback" with "Hs4") as "Hs".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply wp_goto. iNext. ms_enter "L37". gen_env.
  iApply ("HK" with "[%] Hs"). split; [repeat split; assumption|].
  match goal with H : lookup (TAtom "pr.8") _ = Some _ |- _ => rewrite H end.
  rewrite length_drop. rewrite window_min; [reflexivity | lia].
Qed.

(** A string's pieces are a block from its offset: its life and its
    bytes with the NUL, and no aux slots. *)
Lemma string_block q b reg bs :
  SL.string q b reg bs ⊣⊢ ⌜string_ok q b reg bs⌝ ∗ pts (block_ps b reg (ptr_addr q - b) (bs ++ [0]) []).
Proof. rewrite /SL.string /string_ps /block_ps. cbn [aux_ps]. rewrite app_nil_r. done. Qed.

(** An object's life, bytes and aux slots from offset o are its block
    from o. *)
Lemma dest_block b reg o xs cs : live b reg ∗ bytes b o xs ∗ auxes b o cs ⊣⊢ pts (block_ps b reg o xs cs).
Proof. rewrite /block_ps /pts big_sepL_cons big_sepL_app /live /bytes /auxes /pts big_sepL_singleton. done. Qed.

(** errno's lookup has Campaign 4's contract. *)
Context (Herrno_reg : registry (TAtom "__errno_location") = Some (LB.errno_contract rep)).

(** The world interpretation survives a pointer store into a cell the
    program owns. *)
Context (Kpstore : forall b reg o x xp m wd h,
  (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
     h !! l = Some v) ->
  wi m wd h ->
  wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
    (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)).

(** `__errno_location()` returns the errno cell and changes nothing:
    HelloClose.v's [wp_close_errno] over [libc_world]. A local rule, for
    promotion to a libc logic module. *)
Lemma wp_conv_errno f e ls lab d rest j Φ :
  ▷ WP (ERun (mkFrame f (put d (WPtr errno) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Call (CResult d P) (Global (TAtom "__errno_location")) [] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  iIntros "HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (LB.errno_contract rep) [] True%I with "[] [HK]").
  - apply linked_outside; [exact Hlinked | reflexivity].
  - apply linked_unbound; [exact Hlinked | reflexivity].
  - reflexivity.
  - exact Herrno_reg.
  - reflexivity.
  - split; [right; eexists; reflexivity | reflexivity].
  - iIntros (σ) "Hσ _". iDestruct "Hσ" as (h) "[_ %Hσ]".
    destruct (Hlibc _ _ _ (proj2 (proj2 (proj2 Hσ)))) as (Hr & _).
    iPureIntro. split; [reflexivity|]. split; [exact Hr | exact (proj1 (proj2 (proj2 (proj2 Hr))))].
  - done.
  - iNext. iIntros (σ tr vs s' m' w' Hi) "Hσ _".
    destruct (LB.errno_exact _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (-> & -> & -> & -> & He).
    injection He as ->.
    iDestruct "Hσ" as (h) "[Hh %Hσ]".
    destruct (Hlibc _ _ _ (proj2 (proj2 (proj2 Hσ)))) as (_ & _ & Ec & _).
    iModIntro. iExists _. iSplit.
    + iPureIntro. cbn [external_env external_outcome contract_returns site_result returned_env].
      rewrite Ec. reflexivity.
    + iSplitL "Hh"; [iExists h; iFrame; done|]. iExact "HK".
Qed.

(** What rpl_mbsrtowcs's caller learns when it returns r, with dest's
    final bytes ws, errno's bytes xe and the length l of the source:
    EILSEQ, -1 with 84 in errno; or r wide characters, none zero,
    then a zero one. *)
Definition mbs_post (l : nat) (r : Z) (ws xe : list Z) : Prop :=
  (r = 2 ^ 64 - 1 /\ le_value xe = 84) \/
  (exists k : nat, r = Z.of_nat k /\ (k <= l)%nat /\ wide_ok (take (4 * k) ws) /\
     le_value (take 4 (drop (4 * k) ws)) = 0).

(** Owning the bytes xs from o is owning their first n and the rest. *)
Lemma bytes_split b o xs n : (n <= length xs)%nat ->
  bytes b o xs ⊣⊢ bytes b o (take n xs) ∗ bytes b (o + Z.of_nat n) (drop n xs).
Proof.
  intros Hn. assert (E : Z.of_nat n = Z.of_nat (length (take n xs))) by (rewrite length_take; lia).
  rewrite E -bytes_app take_drop. done.
Qed.

(** Owning the slots cs from o is owning their first n and the rest. *)
Lemma auxes_split b o cs n : (n <= length cs)%nat ->
  auxes b o cs ⊣⊢ auxes b o (take n cs) ∗ auxes b (o + Z.of_nat n) (drop n cs).
Proof.
  intros Hn. assert (E : Z.of_nat n = Z.of_nat (length (take n cs))) by (rewrite length_take; lia).
  rewrite E -auxes_app take_drop. done.
Qed.

(** rpl_mbsrtowcs's converting loop, from block L28, by Löb induction:
    after i wide characters from the first j bytes of the string at p,
    with the state valid and in its initial shift state, every path
    returns what [mbs_post] says; the abort after an incomplete
    sequence is never reached. *)
Lemma mbs_loop p b reg bs bd rd sb sr so be re oe spb spr spo codec dq p0 t0 rc rp Φ :
  errno = mkPtr (be + oe) (Obj be) ->
  0 < bd -> bd mod 4 = 0 -> bd + 4 * (Z.of_nat (length bs) + 1) <= r_end rd -> r_end rd <= 2 ^ 48 ->
  0 < sb -> (sb + so) mod 4 = 0 ->
  0 < spb -> 0 <= spo -> (spb + spo) mod 8 = 0 -> spb + spo + 8 <= r_end spr -> r_end spr <= 2 ^ 48 ->
  0 < be -> 0 <= oe -> be + oe + 4 <= r_end re -> r_end re <= 2 ^ 48 ->
  ⊢ ∀ e (i j : nat) wpre cpre wrest crest ys cs xe ce x,
    ⌜mbs_vars e (mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p)) (WPtr (mkPtr (bd + Z.of_nat (4 * i)) (Obj bd)))
        (WInt (Z.of_nat (length bs) + 1 - Z.of_nat i)) (WPtr (mkPtr (sb + so) (Obj sb)))
        (WPtr (mkPtr (spb + spo) (Obj spb))) (WPtr (mkPtr (spb + spo) (Obj spb))) (WInt bd) /\
      (i <= j <= length bs)%nat /\ length wpre = (4 * i)%nat /\ length cpre = (4 * i)%nat /\
      length wrest = (4 * (length bs + 1 - i))%nat /\ length crest = (4 * (length bs + 1 - i))%nat /\
      wide_ok wpre /\ valid codec ys /\ le_value (take 4 ys) = 0 /\ length ys = 8%nat /\ length cs = 8%nat /\
      length xe = 4%nat /\ length ce = 4%nat⌝ -∗
    LL.lent 0 p0 t0 -∗ SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
    pointsto (PName codec_key) dq (VCodec codec) -∗ SL.string p b reg bs -∗
    live bd rd -∗ bytes bd 0 wpre -∗ auxes bd 0 cpre -∗
    bytes bd (Z.of_nat (4 * i)) wrest -∗ auxes bd (Z.of_nat (4 * i)) crest -∗
    pts (block_ps sb sr so ys cs) -∗ pts (block_ps be re oe xe ce) -∗ live spb spr -∗ pcell spb spo x -∗
    (∀ r ws cws ys' cs' xe' ce' x',
       ⌜mbs_post (length bs) r ws xe' /\ length ws = (4 * (length bs + 1))%nat⌝ -∗
       SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
       pointsto (PName codec_key) dq (VCodec codec) -∗ SL.string p b reg bs -∗
       live bd rd -∗ bytes bd 0 ws -∗ auxes bd 0 cws -∗
       pts (block_ps sb sr so ys' cs') -∗ pts (block_ps be re oe xe' ce') -∗ live spb spr -∗ pcell spb spo x' -∗
       Φ (Ret (WInt r))) -∗
    WP (ERun (mkFrame mbs_fn e [] None
          (Exec (TAtom "L28") (b_insts (mbs_block "L28")) (b_jump (mbs_block "L28")))) : cexpr) {{ Φ }}.
Proof.
  intros Herr Hbd Hbd4 Hdend Hd48 Hsb Hsal Hspb Hspo Hspal Hspend Hsp48 Hbe Hoe Heend He48.
  pose proof Hlinked as (Hm & _ & Hext).
  iLöb as "IH".
  iIntros (e i j wpre cpre wrest crest ys cs xe ce x
    ((Hq & H7 & H1 & H2 & Hv2 & Hc0 & H23) & Hij & Lwp & Lcp & Lwr & Lcr & Hwide & Hval & Hinit & Lys & Lcs & Lxe & Lce))
    "#Hk Hc Hposix Hcod Hs Hdl Hdw Hda Hrw Hra HBs HBe Hspl Hsp HΦ".
  iDestruct "Hs" as "[%Hok Hps]". iAssert (SL.string p b reg bs) with "[$Hps]" as "Hs"; [done|].
  pose proof Hok as (Hc & Hb0 & Hbp & Hsend & H48 & Hbs).
  cbn [b_insts b_jump mbs_block hblk].
  (* Characters are left to write. *)
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  ms_enter "L29".
  (* The window over the suffix from byte j. *)
  iDestruct (string_suffix _ _ _ _ j with "Hs") as "[Hsuf Hback]"; [lia|].
  iApply (mbs_window with "Hsuf"); [repeat split; eassumption|].
  iNext. iIntros (e' ((Hq' & H7' & H1' & H2' & Hv2' & Hc0' & H23') & Hn8)) "Hsuf".
  (* The next output word, and the source as a block. *)
  assert (Lr4 : (4 <= length wrest)%nat) by lia. assert (Lc4 : (4 <= length crest)%nat) by lia.
  iEval (rewrite (bytes_split _ _ _ 4 Lr4)) in "Hrw". iDestruct "Hrw" as "[Hw0 Hw1]".
  iEval (rewrite (auxes_split _ _ _ 4 Lc4)) in "Hra". iDestruct "Hra" as "[Ha0 Ha1]".
  iAssert (pts (block_ps bd rd (Z.of_nat (4 * i)) (take 4 wrest) (take 4 crest))) with "[Hdl Hw0 Ha0]" as "HBo";
    [rewrite -dest_block; iFrame|].
  iEval (rewrite string_block) in "Hsuf". iDestruct "Hsuf" as "[%Hok' HBsrc]".
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ rpl_fn
            (invocation rpl_fn [WPtr (mkPtr (bd + Z.of_nat (4 * i)) (Obj bd));
                                WPtr (mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p));
                                WInt (Z.min (Z.of_nat (length (drop j bs)) + 1) 16);
                                WPtr (mkPtr (sb + so) (Obj sb))]));
    [word_premise | unfold find_fn; rewrite Hm; vm_compute; reflexivity | reflexivity |].
  iNext.
  pose proof Hok' as (Hc' & _ & Hbq' & Hsend' & _ & Hbs').
  assert (Hal : (bd + Z.of_nat (4 * i)) mod 4 = 0).
  { replace (bd + Z.of_nat (4 * i)) with (bd + Z.of_nat i * 4) by lia. rewrite Z.mod_add; [exact Hbd4 | lia]. }
  assert (Hss : Forall (fun x => 0 <= x < 256) (drop j bs ++ [0])).
  { apply Forall_app. split; [| repeat constructor; lia].
    apply Forall_drop. eapply Forall_impl; [exact Hbs | intros y Hy; cbv beta in Hy |- *; lia]. }
  iApply (rpl_mbrtowc_spec _ _ _ _ bd rd (Z.of_nat (4 * i)) (take 4 wrest) (take 4 crest) sb sr so ys cs
            be re oe xe ce b reg (ptr_addr p + Z.of_nat j - b) (drop j bs ++ [0])
            with "Hk Hc Hposix Hcod HBo HBs HBe [HBsrc]").
  all: try first [reflexivity | assumption | exact Herr | lia | (cbn [ptr_addr ptr_cap]; lia) |
                  (rewrite length_take; lia) | (rewrite length_app length_drop; cbn [length]; lia)].
  { iEval (cbn [ptr_addr]) in "HBsrc". iExact "HBsrc". }
  iNext. iIntros (r xo' ys' xe' co' cs' ce' (Hres & Lxo' & Lys' & Lxe' & Lco' & Lcs' & Lce'))
    "Hc Hposix Hcod HBo HBs HBe HBsrc".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  iDestruct ("Hback" with "[HBsrc]") as "Hs".
  { iApply string_block. iSplit; [done|]. iEval (cbn [ptr_addr]) in "HBsrc". iExact "HBsrc". }
  destruct (rpl_step _ _ _ (drop j bs) _ _ _ _ _ _ (Forall_drop _ _ _ Hbs) Hval Hinit Hres)
    as (Hr64 & Hn2 & Hm1 & Hz & Hpos).
  iEval (rewrite -dest_block) in "HBo". iDestruct "HBo" as "(Hdl & Hw0 & Ha0)".
  (* Never incomplete: the abort is not reached. *)
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  ms_enter "L82".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eqb_spec r (2 ^ 64 - 1)) as [Er|Er].
  { (* EILSEQ: the cursor goes back through srcp, errno gets 84, and -1 returns. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    ms_enter "L94".
    iApply (wp_renew with "Hspl");
      [reflexivity | word_premise | reflexivity | reflexivity | addr_premise | addr_premise |
       cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; rewrite Z.add_0_r; exact Hspal |].
    iNext. iIntros "Hspl". gen_env.
    iApply (wp_raw_store_pointer with "Hspl Hsp");
      [word_premise | word_premise | reflexivity | addr_premise | exact Hspal |
       intros ?m ?wd ?h Hl Hw; exact (Kpstore _ _ _ _ _ _ _ _ Hl Hw) |].
    iNext. iIntros "Hspl Hsp".
    iApply wp_goto. iNext. ms_enter "L196".
    iApply wp_conv_errno. iNext. gen_env.
    iEval (rewrite -dest_block) in "HBe". iDestruct "HBe" as "(Hel & Hew & Hea)".
    iApply (wp_check with "Hel");
      [reflexivity | word_premise | rewrite Herr; reflexivity | rewrite Herr; addr_premise |
       rewrite Herr; addr_premise | apply Z.mod_1_r |].
    iNext. iIntros "Hel". gen_env.
    iApply (wp_raw_store_w with "Hel Hew");
      [word_premise | word_premise | rewrite Herr; reflexivity | rewrite Herr; addr_premise | exact Lxe' |
       intros ?m ?wd ?h Hl Hw; exact (Kstore _ _ _ _ _ _ _ _ Hl Hw) |].
    iNext. iIntros "Hel Hew".
    iApply wp_ret; [reflexivity | word_premise |]. iNext.
    change (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1).
    iApply ("HΦ" $! _ (wpre ++ xo' ++ drop 4 wrest) (cpre ++ co' ++ drop 4 crest) ys' cs' (le_bytes 84 4) ce'
              with "[%] Hc Hposix Hcod Hs Hdl [Hdw Hw0 Hw1] [Hda Ha0 Ha1] HBs [Hel Hew Hea] Hspl Hsp").
    - split; [left; split; [reflexivity | apply le_value_byte; lia]|].
      rewrite !length_app length_drop. lia.
    - rewrite bytes_app bytes_app Lwp Lxo' Z.add_0_l. iFrame.
    - rewrite auxes_app auxes_app Lcp Lco' Z.add_0_l. iFrame.
    - rewrite -dest_block. iFrame. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  ms_enter "L89".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eqb_spec r 0) as [Ez|Ez].
  { (* The NUL: null goes back through srcp, and the count of characters returns. *)
    subst r. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    ms_enter "L31". gen_env.
    iApply (wp_renew with "Hspl");
      [reflexivity | word_premise | reflexivity | reflexivity | addr_premise | addr_premise |
       cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; rewrite Z.add_0_r; exact Hspal |].
    iNext. iIntros "Hspl". gen_env.
    iApply (wp_raw_store_pointer with "Hspl Hsp");
      [word_premise | word_premise | reflexivity | addr_premise | exact Hspal |
       intros ?m ?wd ?h Hl Hw; exact (Kpstore _ _ _ _ _ _ _ _ Hl Hw) |].
    iNext. iIntros "Hspl Hsp".
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
    iApply wp_ret; [reflexivity | word_premise |]. iNext.
    assert (E4 : bd + Z.of_nat (i + (i + (i + (i + 0)))) - bd = Z.of_nat i * 4) by lia. rewrite E4.
    rewrite Z.div_mul; [|lia]. rewrite Z.mod_small; [|lia].
    iApply ("HΦ" $! _ (wpre ++ xo' ++ drop 4 wrest) (cpre ++ co' ++ drop 4 crest) ys' cs' xe' ce'
              with "[%] Hc Hposix Hcod Hs Hdl [Hdw Hw0 Hw1] [Hda Ha0 Ha1] HBs HBe Hspl Hsp").
    - split; [right; exists i; split; [reflexivity|]; split; [lia|]; split|].
      + rewrite <- Lwp. rewrite take_app_length. exact Hwide.
      + rewrite <- Lwp. rewrite drop_app_length. rewrite take_app_le; [|lia]. rewrite take_ge; [|lia].
        exact (Hz eq_refl).
      + rewrite !length_app length_drop. lia.
    - rewrite bytes_app bytes_app Lwp Lxo' Z.add_0_l. iFrame.
    - rewrite auxes_app auxes_app Lcp Lco' Z.add_0_l. iFrame. }
  (* A character: both cursors move on, and the loop goes round. *)
  destruct (Hpos Ez Er) as (Hr0 & Hxo & Hv' & Hi').
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  ms_enter "L102".
  rewrite length_drop in Hr0.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat (j + Z.to_nat r)));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]. iNext. gen_env.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bd + Z.of_nat (4 * S i)));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply wp_goto. iNext. ms_enter "L28". gen_env.
  iAssert (bytes bd 0 (wpre ++ xo')) with "[Hdw Hw0]" as "Hdw"; [rewrite bytes_app Lwp Z.add_0_l; iFrame|].
  iAssert (auxes bd 0 (cpre ++ co')) with "[Hda Ha0]" as "Hda"; [rewrite auxes_app Lcp Z.add_0_l; iFrame|].
  assert (Eo : Z.of_nat (4 * i) + Z.of_nat 4 = Z.of_nat (4 * S i)) by lia.
  iEval (rewrite Eo) in "Hw1". iEval (rewrite Eo) in "Ha1".
  iApply ("IH" $! _ (S i) (j + Z.to_nat r)%nat (wpre ++ xo') (cpre ++ co') (drop 4 wrest) (drop 4 crest)
            ys' cs' xe' ce' x with "[%] Hk Hc Hposix Hcod Hs Hdl Hdw Hda Hw1 Ha1 HBs HBe Hspl Hsp HΦ").
  pose proof (wide_ok_app _ _ i Hwide Lwp Lxo' Hxo) as Hw'.
  unfold mbs_vars. repeat match goal with |- _ /\ _ => split end.
  all: try assumption; try lia; try (rewrite length_app; lia); try (rewrite length_drop; lia).
  match goal with H : lookup (TAtom "pr.1") _ = Some _ |- _ => rewrite H; f_equal; f_equal; lia end.
Qed.

(** ## rpl_mbsrtowcs *)

(** rpl_mbsrtowcs's entry binds its four arguments. *)
Lemma mbs_entry dst src len ps :
  invocation mbs_fn [WPtr dst; WPtr src; WInt len; WPtr ps] =
  mkFrame mbs_fn [(TAtom "v6", WPtr ps); (TAtom "v4", WInt len); (TAtom "v2", WPtr src); (TAtom "v0", WPtr dst)]
    [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** rpl_mbsrtowcs(dest, srcp, len, ps) as main calls it: dest a fresh
    buffer of len wide characters, srcp a cell holding the string p,
    len the string's length and its NUL, and ps a non-null state, valid
    and in its initial shift state. The entry allocates a local it never
    uses, keeps ps, loads the string through srcp, a read-only literal
    or not, and goes to the converting loop ([mbs_loop]) with nothing
    written yet; the counting loop, for a null dest, is not reached.
    The call returns what [mbs_post] says. *)
Lemma rpl_mbsrtowcs_spec p b reg bs bd rd ws cws sb sr so ys cs be re oe xe ce spb spr spo
    codec dq p0 t0 rc rp Φ :
  errno = mkPtr (be + oe) (Obj be) ->
  0 < bd -> bd mod 4 = 0 -> bd + 4 * (Z.of_nat (length bs) + 1) <= r_end rd -> r_end rd <= 2 ^ 48 ->
  0 < sb -> 0 <= so -> (sb + so) mod 4 = 0 -> sb + so + 8 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 < spb -> 0 <= spo -> (spb + spo) mod 8 = 0 -> spb + spo + 8 <= r_end spr -> r_end spr <= 2 ^ 48 ->
  0 < be -> 0 <= oe -> be + oe + 4 <= r_end re -> r_end re <= 2 ^ 48 ->
  length ws = (4 * (length bs + 1))%nat -> length cws = (4 * (length bs + 1))%nat ->
  valid codec ys -> le_value (take 4 ys) = 0 -> length ys = 8%nat -> length cs = 8%nat ->
  length xe = 4%nat -> length ce = 4%nat ->
  LL.lent 0 p0 t0 -∗ SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
  pointsto (PName codec_key) dq (VCodec codec) -∗ SL.string p b reg bs -∗
  live bd rd -∗ bytes bd 0 ws -∗ auxes bd 0 cws -∗
  pts (block_ps sb sr so ys cs) -∗ pts (block_ps be re oe xe ce) -∗ live spb spr -∗ pcell spb spo p -∗
  (∀ r ws' cws' ys' cs' xe' ce' x',
     ⌜mbs_post (length bs) r ws' xe' /\ length ws' = (4 * (length bs + 1))%nat⌝ -∗
     SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
     pointsto (PName codec_key) dq (VCodec codec) -∗ SL.string p b reg bs -∗
     live bd rd -∗ bytes bd 0 ws' -∗ auxes bd 0 cws' -∗
     pts (block_ps sb sr so ys' cs') -∗ pts (block_ps be re oe xe' ce') -∗ live spb spr -∗ pcell spb spo x' -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun (invocation mbs_fn [WPtr (mkPtr bd (Obj bd)); WPtr (mkPtr (spb + spo) (Obj spb));
                                WInt (Z.of_nat (length bs) + 1); WPtr (mkPtr (sb + so) (Obj sb))]) : cexpr)
    {{ Φ }}.
Proof.
  intros Herr Hbd Hbd4 Hdend Hd48 Hsb Hso Hsal Hsend' Hs48 Hspb Hspo Hspal Hspend Hsp48 Hbe Hoe Heend He48
    Lws Lcws Hval Hinit Lys Lcs Lxe Lce.
  iIntros "#Hk Hc Hposix Hcod Hs Hdl Hdw Hda HBs HBe Hspl Hsp HΦ".
  iDestruct "Hs" as "[%Hok Hps]".
  pose proof Hok as (Hcp & Hb0 & Hbp & Hsend & H48 & Hbs).
  rewrite mbs_entry.
  iApply (wp_enter _ _ _ _ _ _ _ _ (mbs_block "start")); [vm_compute; reflexivity | word_premise |]; iNext.
  cbn [b_insts b_jump mbs_block hblk].
  (* The local for the counting loop, never used here. *)
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 8);
    [reflexivity | lia | unfold max_allocation_size; lia | intros m wd h base Hf Hw; exact (Kalloc _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (base _) "_".
  rm_let. rm_let. rm_let.
  (* ps is not null. *)
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0);
    [cbn; rewrite (Z.mod_small (sb + so)); [|lia]; rewrite (proj2 (Z.eqb_neq (sb + so) _));
     [reflexivity | change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0; lia]|]. iNext. cbn [Z.eqb edge_label].
  ms_enter "L10". gen_env.
  (* The string through srcp. *)
  iApply (wp_check_read with "Hspl");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise | addr_premise |].
  iNext. iIntros "Hspl". gen_env.
  iApply (wp_raw_load_pointer_in
           with "Hspl Hsp Hps");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise | lia |
     intros xb Hxb; exists reg; destruct Hcp as [Hcp | Hcp]; rewrite Hcp in Hxb;
     destruct Hxb as [Hxb | Hxb]; try discriminate Hxb; injection Hxb as <-;
     apply elem_of_cons; left; reflexivity |].
  iNext. iIntros "Hspl Hsp Hps". gen_env.
  iAssert (SL.string p b reg bs) with "[$Hps]" as "Hs"; [done|].
  (* dest is not null: the converting loop. *)
  rm_let. gen_env. rm_let. gen_env.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1);
    [cbn; rewrite (Z.mod_small bd); [|lia]; rewrite (proj2 (Z.eqb_neq bd _));
     [reflexivity | change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0; lia]|]. iNext. cbn [Z.eqb edge_label].
  iApply (wp_enter _ _ _ _ _ _ _ _ (mbs_block "L28")); [vm_compute; reflexivity | word_premise |]; iNext.
  gen_env.
  iPoseProof (mbs_loop p b reg bs bd rd sb sr so be re oe spb spr spo codec dq p0 t0 rc rp Φ
    Herr Hbd Hbd4 Hdend Hd48 Hsb Hsal Hspb Hspo Hspal Hspend Hsp48 Hbe Hoe Heend He48) as "L".
  iApply ("L" $! _ 0%nat 0%nat [] [] ws cws ys cs xe ce p
           with "[%] Hk Hc Hposix Hcod Hs Hdl [] [] Hdw Hda HBs HBe Hspl Hsp HΦ").
  - assert (Ep : mkPtr (ptr_addr p + Z.of_nat 0) (ptr_cap p) = p) by (destruct p; cbn; f_equal; lia).
    rewrite Ep. replace (bd + Z.of_nat (4 * 0)) with bd by lia.
    replace (Z.of_nat (length bs) + 1 - Z.of_nat 0) with (Z.of_nat (length bs) + 1) by lia.
    split; [unfold mbs_vars; repeat split; cbn; first [reflexivity | rewrite Z.mod_small; [reflexivity | lia]]|].
    split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite Lws; lia|]. split; [rewrite Lcws; lia|].
    split; [exact wide_ok_nil|]. repeat split; assumption.
  - rewrite /bytes /byte_ps /pts /=. done.
  - rewrite /auxes /aux_ps /pts /=. done.
Qed.

End mbrtowc.

End HelloConvOn.

(** [HelloConvOn] over a Logic instance of its own. *)
Module HelloConv (R : Runtime).
Module LG0 := Logic R.
Include HelloConvOn R LG0.
End HelloConv.
