(** GNU Hello calls libc's mbrtowc to convert source bytes into a wide
    character. The call writes the output, conversion state, and errno
    blocks while preserving the caller's other [[separation-logic|ownership]].

    This module proves the call's [[hoare-triple|triple]] from its libc contract.
    The proof keeps the audited codec assumption explicit and returns
    all three blocks with the bytes produced by the conversion. *)

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

Module HelloConvCallOn (R : Runtime) (LG0 : LogicSig R).
Module HLo.
Include HelloLocaleOn R LG0.
End HLo.
Import HLo HL ML LG.
Module LB := LibcOn R L.M.
Import L LG SL ML LL HL HLo.

Local Hint Opaque pts live bytes auxes pcell rpl_fn mbs_fn : typeclass_instances.

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
Proof using Type.
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
Proof using Hbytes Hlibc Hvalid0.
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
Proof using Hlibc.
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
Proof using Type.
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
Proof using Haudit Hbytes Hlibc Hmbrtowc Hvalid0 Kmbrtowc SafepointStable0.
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

End mbrtowc.
End HelloConvCallOn.
