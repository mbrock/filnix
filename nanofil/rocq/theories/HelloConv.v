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
  LentLogic Locale Libc HelloModule HelloLeaf HelloLocale.
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
     (c_codec -> ys' = ys /\ exists x, ss !! 0%nat = Some x /\ 128 <= x < 256)) \/
  (r = 2 ^ 64 - 2 /\ valid codec ys' /\ xo' = xo /\ n < 16 /\
     Forall (fun x => x <> 0) (take (Z.to_nat n) ss)).

Module HelloConv (R : Runtime).
Module HLo := HelloLocale R.
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

(** The world interpretation makes libc ready, with the codec codec
    and the errno cell errno, and keeps libc's private state apart. *)
Context (codec : term) (errno : ptr)
  (Hlibc : forall m w h, wi m w h ->
     libc_ready rep m w /\ locale_codec (libc_locale (fst w)) = codec /\
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
Lemma mbrtowc_admitted m w h out src n state bo ro oo xo co bs rs os ys cs be re oe xe ce
    bsrc rsrc osrc ss :
  wi m w h -> agrees m h -> live_disjoint m -> objects_fit (m_regions m) ->
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
  intros Hw Ha Hd Hfit Ho Hs He Hsr Nos Noe Nosr Nse Nssr Nesr -> -> Herr Hcap Haddr Hbo Hbs Hbsrc Hoal Hsal
    Lxo Lys Lxe Hn Hss Hval.
  pose proof (Hbytes _ _ Hval) as Hyb.
  destruct (Hlibc m w h Hw) as (Hready & Hcodec & Herrno & Hown & Hpriv).
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
Lemma conv_of_result m w out src n state res m' bo oo xo bs os ys be oe bsrc osrc ss :
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
    split; [exact (Hkept Hk)|]. intros Hc. rewrite <- Hcodec in Hc.
    destruct (mbrtowc_c_error _ _ _ _ _ _ _ _ _ Hfull Hc) as [Hst Hsrc0]. split.
    + rewrite <- (mem_bytes_of m (bs + os) ys Vs). rewrite Lys. exact Hst.
    + destruct (Hsrc 0 ltac:(lia)) as (x & Hx & Hb). exists x. split; [exact Hx|].
      rewrite <- Hb, Z.add_0_r. exact Hsrc0.
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
    bo ro oo xo co bs rs os ys cs be re oe xe ce bsrc rsrc osrc ss Φ :
  find_fn ge (TAtom "mbrtowc") = None -> lookup (TAtom "mbrtowc") (ge_globals ge) = None ->
  arg_x ge e (Arg P vo) = Some (WPtr out) -> arg_x ge e (Arg P vs) = Some (WPtr src) ->
  arg_x ge e (Arg L vn) = Some (WInt n) -> arg_x ge e (Arg P vt) = Some (WPtr state) ->
  out = mkPtr (bo + oo) (Obj bo) -> state = mkPtr (bs + os) (Obj bs) -> errno = mkPtr (be + oe) (Obj be) ->
  (ptr_cap src = Obj bsrc \/ ptr_cap src = Ro bsrc) -> ptr_addr src = bsrc + osrc ->
  0 < bo -> 0 < bs -> 0 < bsrc -> (bo + oo) mod 4 = 0 -> (bs + os) mod 4 = 0 ->
  length xo = 4%nat -> length co = 4%nat -> length ys = 8%nat -> length cs = 8%nat ->
  length xe = 4%nat -> length ce = 4%nat ->
  0 < n <= Z.of_nat (length ss) -> Forall (fun x => 0 <= x < 256) ss -> valid codec ys ->
  pts (block_ps bo ro oo xo co) -∗ pts (block_ps bs rs os ys cs) -∗ pts (block_ps be re oe xe ce) -∗
  pts (block_ps bsrc rsrc osrc ss []) -∗
  ▷ (∀ r xo' ys' xe' co' cs' ce',
       ⌜conv_result valid (audit codec = Some CodecC) codec n ss xo ys xo' ys' xe' r /\ length xo' = 4%nat /\ length ys' = 8%nat /\
        length xe' = 4%nat /\ length co' = 4%nat /\ length cs' = 8%nat /\ length ce' = 4%nat⌝ -∗
       pts (block_ps bo ro oo xo' co') -∗ pts (block_ps bs rs os ys' cs') -∗ pts (block_ps be re oe xe' ce') -∗
       pts (block_ps bsrc rsrc osrc ss []) -∗
       WP (ERun (mkFrame f (put d (WInt r) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "mbrtowc")) [Arg P vo; Arg P vs; Arg L vn; Arg P vt]
                          :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hfn Hdata Hvo Hvs Hvn Hvt Eout Est Herr Hcap Haddr Hbo Hbs Hbsrc Hoal Hsal Lxo Lco Lys Lcs Lxe Lce
    Hn Hss Hval.
  iIntros "HBo HBs HBe HBsrc HK".
  iDestruct (block_ne with "HBo HBs") as %N1. iDestruct (block_ne with "HBo HBe") as %N2.
  iDestruct (block_ne with "HBo HBsrc") as %N3. iDestruct (block_ne with "HBs HBe") as %N4.
  iDestruct (block_ne with "HBs HBsrc") as %N5. iDestruct (block_ne with "HBe HBsrc") as %N6.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (mbrtowc_contract valid audit rep requests)
            [WPtr out; WPtr src; WInt n; WPtr state]
            (pts (block_ps bo ro oo xo co) ∗ pts (block_ps bs rs os ys cs) ∗ pts (block_ps be re oe xe ce) ∗
             pts (block_ps bsrc rsrc osrc ss []))
            with "[$HBo $HBs $HBe $HBsrc] [HK]");
    [exact Hfn | exact Hdata | reflexivity | exact Hmbrtowc | cbn [map_option]; rewrite Hvo Hvs Hvn Hvt; reflexivity
    | | |].
  - split; [right; eexists; reflexivity | do 4 eexists; reflexivity].
  - iIntros (σ) "Hσ (Ho & Hs & He & Hsr)". iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Ho") as %Ko. iDestruct (pts_lookup with "Hh Hs") as %Ks.
    iDestruct (pts_lookup with "Hh He") as %Ke. iDestruct (pts_lookup with "Hh Hsr") as %Ksr. iPureIntro.
    exact (mbrtowc_admitted _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hw Ha Hd
             (R.address_space _ _ Hr) Ko Ks Ke Ksr N1 N2 N3 N4 N5 N6 Eout Est Herr Hcap Haddr Hbo Hbs Hbsrc Hoal Hsal
             Lxo Lys Lxe Hn Hss Hval).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) (Ho & Hs & He & Hsr)".
    destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Ho") as %Ko. iDestruct (pts_lookup with "Hh Hs") as %Ks.
    iDestruct (pts_lookup with "Hh He") as %Ke. iDestruct (pts_lookup with "Hh Hsr") as %Ksr.
    destruct (Hlibc _ _ _ Hw) as (_ & Hcodec & Herrno & _).
    destruct (block_facts _ h bo ro oo xo co Ha Ko (nonempty_of_length xo 3 Lxo)) as (_ & _ & _ & Vo).
    destruct (block_facts _ h bs rs os ys cs Ha Ks (nonempty_of_length ys 7 Lys)) as (_ & _ & _ & Vs).
    destruct (block_facts _ h bsrc rsrc osrc ss [] Ha Ksr ltac:(intros E; rewrite E in Hn; cbn in Hn; lia))
      as (_ & _ & _ & Vsr).
    destruct (LB.mbrtowc_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (res & -> & Hres).
    rewrite (proj2 (Z.eqb_neq n 0) ltac:(lia)) in Hres.
    assert (Hnl : 0 < n <= Z.of_nat (length ss)) by lia.
    assert (Hn0 : n <> 0) by lia.
    pose proof (conv_of_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hres (Haudit _ _ _ Hw) Hcodec
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
      iApply ("HK" $! res with "[%] Ho Hs He Hsr").
      rewrite !length_mem_bytes !length_mem_auxes. split; [exact Hconv|]. repeat split.
Qed.

End mbrtowc.

End HelloConv.
