(** GNU Hello converts its greeting one character at a time while
    advancing the source and destination cursors. This module proves
    the converting loop by [[later-modality|Löb induction]].

    Each iteration obtains a bounded source window and applies the
    single-character conversion rule. The loop either records an error,
    returns at the NUL, or preserves its invariant for the next character. *)

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

From Nanofil Require Import HelloConvWindow.
Module HelloConvLoopOn (R : Runtime) (LG0 : LogicSig R).
Include HelloConvWindowOn R LG0.
Import HLo HL ML LG.
Import L LG SL ML LL HL HLo.
Local Hint Opaque pts live bytes auxes pcell rpl_fn mbs_fn : typeclass_instances.

(** Advancing one instruction does not require examining every hypothesis.
    We introduce the [[later-modality]] directly and use [iNext] only
    before reusing the induction hypothesis. *)
Local Ltac loop_next := iApply bi.later_intro.

Ltac ms_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (mbs_block s));
  [apply mbs_loop_block; repeat first [left; reflexivity | right]; reflexivity | word_premise |]; iApply bi.later_intro;
  cbn [b_insts b_jump mbs_block hblk].

(** The loop repeatedly evaluates pure instructions. Supplying the rule's
    frame arguments first avoids repeating their introduction in Iris. *)
Local Ltac loop_let :=
  iApply (wp_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
  [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]; iApply bi.later_intro; gen_env.

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
       ⌜mbs_post (length bs) r ws xe' /\ length ws = (4 * (length bs + 1))%nat /\ length xe' = 4%nat⌝ -∗
       SL.string c_ptr 65824 rc c_bytes -∗ SL.string posix_ptr 65856 rp posix_bytes -∗
       pointsto (PName codec_key) dq (VCodec codec) -∗ SL.string p b reg bs -∗
       live bd rd -∗ bytes bd 0 ws -∗ auxes bd 0 cws -∗
       pts (block_ps sb sr so ys' cs') -∗ pts (block_ps be re oe xe' ce') -∗ live spb spr -∗ pcell spb spo x' -∗
       Φ (Ret (WInt r))) -∗
    WP (ERun (mkFrame mbs_fn e [] None
          (Exec (TAtom "L28") (b_insts (mbs_block "L28")) (b_jump (mbs_block "L28")))) : cexpr) {{ Φ }}.
Proof using Haudit Hbytes Herrno_reg Hlibc Hlinked Hmbrtowc Hmemchr Hmemcpy Hset Hset_abi Hset_pre
  Hset_query Hset_ret Hstrcmp Hstrlen Hvalid0 Kalloc Kbyte Kcopy Kmbrtowc Kpstore Kstore
  SafepointStable0 invGS_gen0 wi_lent.
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
  loop_let.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. loop_next. cbn [Z.eqb edge_label].
  ms_enter "L29".
  (* The window over the suffix from byte j. *)
  iDestruct (string_suffix _ _ _ _ j with "Hs") as "[Hsuf Hback]"; [lia|].
  iApply (mbs_window registry wi ge Hlinked Hmemchr with "Hsuf"); [repeat split; eassumption|].
  loop_next. iIntros (e' ((Hq' & H7' & H1' & H2' & Hv2' & Hc0' & H23') & Hn8)) "Hsuf".
  (* The next output word, and the source as a block. *)
  assert (Lr4 : (4 <= length wrest)%nat) by lia. assert (Lc4 : (4 <= length crest)%nat) by lia.
  iEval (rewrite (bytes_take_drop _ _ _ 4 Lr4)) in "Hrw". iDestruct "Hrw" as "[Hw0 Hw1]".
  iEval (rewrite (auxes_take_drop _ _ _ 4 Lc4)) in "Hra". iDestruct "Hra" as "[Ha0 Ha1]".
  iAssert (pts (block_ps bd rd (Z.of_nat (4 * i)) (take 4 wrest) (take 4 crest))) with "[Hdl Hw0 Ha0]" as "HBo";
    [rewrite -dest_block; iFrame|].
  iEval (rewrite string_block) in "Hsuf". iDestruct "Hsuf" as "[%Hok' HBsrc]".
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ rpl_fn
            (invocation rpl_fn [WPtr (mkPtr (bd + Z.of_nat (4 * i)) (Obj bd));
                                WPtr (mkPtr (ptr_addr p + Z.of_nat j) (ptr_cap p));
                                WInt (Z.min (Z.of_nat (length (drop j bs)) + 1) 16);
                                WPtr (mkPtr (sb + so) (Obj sb))]));
    [word_premise | unfold find_fn; rewrite Hm; vm_compute; reflexivity | reflexivity |].
  loop_next.
  pose proof Hok' as (Hc' & _ & Hbq' & Hsend' & _ & Hbs').
  assert (Hal : (bd + Z.of_nat (4 * i)) mod 4 = 0).
  { replace (bd + Z.of_nat (4 * i)) with (bd + Z.of_nat i * 4) by lia. rewrite Z.mod_add; [exact Hbd4 | lia]. }
  assert (Hss : Forall (fun x => 0 <= x < 256) (drop j bs ++ [0])).
  { apply Forall_app. split; [| repeat constructor; lia].
    apply Forall_drop. eapply Forall_impl; [exact Hbs | intros y Hy; cbv beta in Hy |- *; lia]. }
  iApply (rpl_mbrtowc_spec registry wi ge valid audit rep requests Hmbrtowc Hvalid0 Hbytes
            errno Hlibc Haudit Kmbrtowc Hlinked wi_lent set_spec Hset Hset_ret Hset_abi Hset_pre Hset_query
            Hstrlen Hmemcpy Hstrcmp Kcopy Kbyte Kstore Kalloc
            _ _ _ _ bd rd (Z.of_nat (4 * i)) (take 4 wrest) (take 4 crest) sb sr so ys cs
            be re oe xe ce b reg (ptr_addr p + Z.of_nat j - b) (drop j bs ++ [0])
            with "Hk Hc Hposix Hcod HBo HBs HBe [HBsrc]").
  all: try first [reflexivity | assumption | exact Herr | lia | (cbn [ptr_addr ptr_cap]; lia) |
                  (rewrite length_take; lia) | (rewrite length_app length_drop; cbn [length]; lia)].
  { iEval (cbn [ptr_addr]) in "HBsrc". iExact "HBsrc". }
  loop_next. iIntros (r xo' ys' xe' co' cs' ce' (Hres & Lxo' & Lys' & Lxe' & Lco' & Lcs' & Lce'))
    "Hc Hposix Hcod HBo HBs HBe HBsrc".
  iExists _. iSplit; [iPureIntro; reflexivity|]. loop_next. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  iDestruct ("Hback" with "[HBsrc]") as "Hs".
  { iApply string_block. iSplit; [done|]. iEval (cbn [ptr_addr]) in "HBsrc". iExact "HBsrc". }
  destruct (rpl_step _ _ _ (drop j bs) _ _ _ _ _ _ (Forall_drop _ _ _ Hbs) Hval Hinit Hres)
    as (Hr64 & Hn2 & Hm1 & Hz & Hpos).
  iEval (rewrite -dest_block) in "HBo". iDestruct "HBo" as "(Hdl & Hw0 & Ha0)".
  (* Never incomplete: the abort is not reached. *)
  loop_let.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. loop_next. cbn [Z.eqb edge_label].
  ms_enter "L82".
  loop_let.
  destruct (Z.eqb_spec r (2 ^ 64 - 1)) as [Er|Er].
  { (* EILSEQ: the cursor goes back through srcp, errno gets 84, and -1 returns. *)
    iClear "IH".
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. loop_next. cbn [Z.eqb edge_label].
    ms_enter "L94".
    iApply (wp_mbs_cursor_store registry wi ge Kpstore _ _ _ _ _ _ _ _ _ _ _ _ with "Hspl Hsp");
      [exact Hspb | exact Hspo | exact Hspal | exact Hspend | exact Hsp48 |
       assumption | assumption | cbn [value_x]; rewrite lookup_after_put_other; [word_premise | reflexivity] |].
    iIntros "Hspl Hsp". gen_env.
    iApply wp_goto. loop_next. ms_enter "L196".
    iApply (wp_mbs_error_return registry wi ge rep errno Hlibc Hlinked Kstore Herrno_reg
      _ _ _ _ _ _ _ with "HBe"); [exact Herr | exact Hbe | exact Hoe | exact Heend | exact He48 | exact Lxe' |].
    iIntros "HBe".
    iDestruct (mbs_finish_output _ _ _ _ _ _ _ _ Lwp Lcp Lxo' Lco'
      with "Hdw Hda Hw0 Ha0 Hw1 Ha1") as "[Hdw Hda]".
    iApply ("HΦ" $! _ (wpre ++ xo' ++ drop 4 wrest) (cpre ++ co' ++ drop 4 crest) ys' cs' (le_bytes 84 4) ce'
              with "[%] Hc Hposix Hcod Hs Hdl Hdw Hda HBs HBe Hspl Hsp").
    split; [left; split; [reflexivity | apply le_value_byte; lia]|].
    split; [eapply mbs_output_length; [exact Lwp | exact Lxo' | exact Lwr | lia] | apply length_le_bytes]. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. loop_next. cbn [Z.eqb edge_label].
  ms_enter "L89".
  loop_let.
  destruct (Z.eqb_spec r 0) as [Ez|Ez].
  { (* The NUL: null goes back through srcp, and the count of characters returns. *)
    iClear "IH".
    subst r. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. loop_next. cbn [Z.eqb edge_label].
    ms_enter "L31". gen_env.
    iApply (wp_mbs_cursor_store registry wi ge Kpstore _ _ _ _ _ _ _ _ _ _ _ _ with "Hspl Hsp");
      [exact Hspb | exact Hspo | exact Hspal | exact Hspend | exact Hsp48 |
       assumption | assumption | cbn [value_x]; rewrite lookup_after_put_other; [word_premise | reflexivity] |].
    iIntros "Hspl Hsp". gen_env.
    iApply (wp_mbs_count_return registry wi ge _ bd i); [exact Hbd | lia | assumption | assumption |].
    iDestruct (mbs_finish_output _ _ _ _ _ _ _ _ Lwp Lcp Lxo' Lco'
      with "Hdw Hda Hw0 Ha0 Hw1 Ha1") as "[Hdw Hda]".
    iApply ("HΦ" $! _ (wpre ++ xo' ++ drop 4 wrest) (cpre ++ co' ++ drop 4 crest) ys' cs' xe' ce'
              with "[%] Hc Hposix Hcod Hs Hdl Hdw Hda HBs HBe Hspl Hsp").
    split; [right; exists i; split; [reflexivity|]; split; [lia|]; split|].
    - rewrite <- Lwp. rewrite take_app_length. exact Hwide.
    - rewrite <- Lwp. rewrite drop_app_length. rewrite take_app_le; [|lia]. rewrite take_ge; [|lia].
      exact (Hz eq_refl).
    - split; [eapply mbs_output_length; [exact Lwp | exact Lxo' | exact Lwr | lia] | exact Lxe']. }
  (* A character: both cursors move on, and the loop goes round. *)
  destruct (Hpos Ez Er) as (Hr0 & Hxo & Hv' & Hi').
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. loop_next. cbn [Z.eqb edge_label].
  ms_enter "L102".
  rewrite length_drop in Hr0.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat (j + Z.to_nat r)));
    [word_premise | cbn; f_equal; f_equal;
     clear - Hr0 Hij Hbp Hb0 Hsend H48; addr_premise | word_premise |]. loop_next. gen_env.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bd + Z.of_nat (4 * S i)));
    [word_premise | cbn; f_equal; f_equal;
     clear - Hbd Hdend Hd48 Hij; addr_premise | word_premise |]. loop_next. gen_env.
  loop_let.
  iApply wp_goto. iNext. ms_enter "L28". gen_env.
  iAssert (bytes bd 0 (wpre ++ xo')) with "[Hdw Hw0]" as "Hdw"; [rewrite bytes_app Lwp Z.add_0_l; iFrame|].
  iAssert (auxes bd 0 (cpre ++ co')) with "[Hda Ha0]" as "Hda"; [rewrite auxes_app Lcp Z.add_0_l; iFrame|].
  assert (Eo : Z.of_nat (4 * i) + Z.of_nat 4 = Z.of_nat (4 * S i)) by lia.
  iEval (rewrite Eo) in "Hw1". iEval (rewrite Eo) in "Ha1".
  iApply ("IH" $! _ (S i) (j + Z.to_nat r)%nat (wpre ++ xo') (cpre ++ co') (drop 4 wrest) (drop 4 crest)
            ys' cs' xe' ce' x with "[%] Hk Hc Hposix Hcod Hs Hdl Hdw Hda Hw1 Ha1 HBs HBe Hspl Hsp HΦ").
  pose proof (wide_ok_app _ _ i Hwide Lwp Lxo' Hxo) as Hw'.
  unfold mbs_vars. repeat match goal with |- _ /\ _ => split end.
  all: try assumption.
  all: try match goal with
    | H : lookup (TAtom "pr.1") ?e = Some _ |- lookup (TAtom "pr.1") ?e = Some _ =>
        rewrite H; f_equal; f_equal; lia
    end.
  all: rewrite ?length_app ?length_drop;
    clear - Hij Lwp Lcp Lwr Lcr Lxo' Lco' Hr0; lia.
Qed.

End mbrtowc.
End HelloConvLoopOn.
