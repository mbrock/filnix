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
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs.
Open Scope Z_scope.
Open Scope list_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

From Nanofil Require Import HelloConvLoop.
Module HelloConvOn (R : Runtime) (LG0 : LogicSig R).
Include HelloConvLoopOn R LG0.
Import HLo HL ML LG.
Import L LG SL ML LL HL HLo.
Local Hint Opaque pts live bytes auxes pcell rpl_fn mbs_fn : typeclass_instances.

Ltac rm_let :=
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]; iNext.

(** ## mbrtowc's triple *)

Section mbrtowc.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Let conv_irisGS_local := conv_irisGS registry wi ge.
Local Existing Instance conv_irisGS_local.

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
(** The memchr contract, for `strnlen1`. *)
Context (Hmemchr : registry (TAtom "memchr") = Some (memchr_contract libc_world)).
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
     ⌜mbs_post (length bs) r ws' xe' /\ length ws' = (4 * (length bs + 1))%nat /\ length xe' = 4%nat⌝ -∗
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
  iPoseProof (mbs_loop registry wi ge valid audit rep requests Hmbrtowc Hvalid0 Hbytes
    errno Hlibc Haudit Kmbrtowc Hlinked wi_lent set_spec Hset Hset_ret Hset_abi Hset_pre Hset_query
    Hstrlen Hmemcpy Hstrcmp Kcopy Kbyte Kstore Kalloc Hmemchr Herrno_reg Kpstore
    p b reg bs bd rd sb sr so be re oe spb spr spo codec dq p0 t0 rc rp Φ
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
