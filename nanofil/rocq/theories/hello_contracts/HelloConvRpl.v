(** GNU Hello wraps mbrtowc with a fallback for locales that treat each
    byte as a character. This module proves that wrapper's [[hoare-triple|triple]],
    using the libc call proof and the existing locale helper proof.

    The caller recovers its source, output, state, and errno blocks on
    both paths. The conversion loop uses this result for each character. *)

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

From Nanofil Require Import HelloConvCall.
Module HelloConvRplOn (R : Runtime) (LG0 : LogicSig R).
Include HelloConvCallOn R LG0.
Import HLo HL ML LG.
Import L LG SL ML LL HL HLo.
Local Hint Opaque pts live bytes auxes pcell rpl_fn mbs_fn : typeclass_instances.

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
  iApply (wp_mbrtowc registry wi ge valid audit rep requests Hmbrtowc Hvalid0 Hbytes
    errno Hlibc Haudit Kmbrtowc with "Hcod HBo HBs HBe HBsrc");
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

End mbrtowc.
End HelloConvRplOn.
