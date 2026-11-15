(** GNU Hello bounds each conversion by a window of source bytes that
    stops at the string's NUL or at sixteen bytes. This module proves
    that the window scan preserves the string's [[separation-logic|ownership]].

    If conversion fails, the program must locate errno and store the
    error code there. This module also proves the loop's terminal steps:
    storing the source cursor, returning the character count, and
    recording a conversion error in errno. *)

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

From Nanofil Require Import HelloConvRpl.
Module HelloConvWindowOn (R : Runtime) (LG0 : LogicSig R).
Include HelloConvRplOn R LG0.
Import HLo HL ML LG.
Import L LG SL ML LL HL HLo.
Local Hint Opaque pts live bytes auxes pcell rpl_fn mbs_fn : typeclass_instances.

(** Branches in rpl_mbsrtowcs jump to the blocks listed below. Checking
    their destinations once avoids searching the function's block list
    again at every jump. *)
Lemma mbs_loop_block s :
  s = "L28"%string \/ s = "L29"%string \/ s = "L82"%string \/ s = "L94"%string \/
  s = "L196"%string \/ s = "L89"%string \/ s = "L31"%string \/ s = "L102"%string \/ s = "L10"%string ->
  find_block (TAtom s) (fn_blocks mbs_fn) = Some (mbs_block s).
Proof.
  intros Hs. repeat destruct Hs as [Hs|Hs]; subst s; vm_compute; reflexivity.
Qed.

(** The conversion function returns a machine integer. *)
Lemma mbs_return_class : fn_ret mbs_fn = RClass L.
Proof. reflexivity. Qed.

Lemma mbs_output_length (n i : nat) (pre word rest : list Z) :
  length pre = (4 * i)%nat -> length word = 4%nat ->
  length rest = (4 * (n + 1 - i))%nat -> (i <= n)%nat ->
  length (pre ++ word ++ drop 4 rest) = (4 * (n + 1))%nat.
Proof. intros. rewrite !length_app length_drop. lia. Qed.

(** The bounded cursor cell's address does not wrap. *)
Lemma mbs_cursor_address b o reg :
  0 < b -> 0 <= o -> b + o + 8 <= r_end reg -> r_end reg <= 2 ^ 48 ->
  raw_address (b + o) 0 = b + o.
Proof. intros. unfold raw_address. drop_wraps_goal. lia. Qed.

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

(** A terminal branch rejoins the output prefix, current word, and unused tail. *)
Lemma mbs_finish_output bd (i : nat) wpre cpre word cword tail ctail :
  length wpre = (4 * i)%nat -> length cpre = (4 * i)%nat ->
  length word = 4%nat -> length cword = 4%nat ->
  bytes bd 0 wpre -∗ auxes bd 0 cpre -∗
  bytes bd (Z.of_nat (4 * i)) word -∗ auxes bd (Z.of_nat (4 * i)) cword -∗
  bytes bd (Z.of_nat (4 * i) + Z.of_nat 4) tail -∗
  auxes bd (Z.of_nat (4 * i) + Z.of_nat 4) ctail -∗
  bytes bd 0 (wpre ++ word ++ tail) ∗ auxes bd 0 (cpre ++ cword ++ ctail).
Proof.
  intros Hwp Hcp Hw Hc. iIntros "Hwp Hcp Hw Hc Ht Hct".
  rewrite !bytes_app !auxes_app Hwp Hcp Hw Hc !Z.add_0_l. iFrame.
Qed.

(** The final pointer difference counts four-byte output characters. *)
Lemma wp_mbs_count_return e bd (i : nat) Φ :
  0 < bd -> bd + Z.of_nat (4 * i) <= 2 ^ 48 ->
  lookup (TAtom "pr.7") e = Some (WPtr (mkPtr (bd + Z.of_nat (4 * i)) (Obj bd))) ->
  lookup (TAtom "v23") e = Some (WInt bd) ->
  Φ (Ret (WInt (Z.of_nat i))) -∗
  WP (ERun (mkFrame mbs_fn e [] None
    (Exec (TAtom "L31") (drop 2 (b_insts (mbs_block "L31")))
      (b_jump (mbs_block "L31")))) : cexpr) {{ Φ }}.
Proof.
  intros Hb Hend Hp Hbase. iIntros "HΦ".
  cbn [mbs_block hblk b_insts b_jump drop].
  do 3 (iApply (wp_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [reflexivity | reflexivity | word_premise | intros ?m; word_premise |];
    iApply bi.later_intro; gen_env).
  iApply (wp_ret _ _ _ _ _ _ _ _ _ _); [exact mbs_return_class | word_premise |].
  iApply bi.later_intro.
  assert (E4 : bd + Z.of_nat (i + (i + (i + (i + 0)))) - bd = Z.of_nat i * 4) by lia.
  rewrite E4 Z.div_mul; [|lia]. rewrite Z.mod_small; [|lia]. iExact "HΦ".
Qed.

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

(** Both terminal branches renew the source cursor cell and store a pointer. *)
Lemma wp_mbs_cursor_store e lab d src rest j b reg o x xp Φ :
  0 < b -> 0 <= o -> (b + o) mod 8 = 0 -> b + o + 8 <= r_end reg -> r_end reg <= 2 ^ 48 ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  value_x ge (put d (WPtr (mkPtr (b + o) (Obj b))) e) P src = Some (WPtr xp) ->
  live b reg -∗ pcell b o x -∗
  (live b reg -∗ pcell b o xp -∗
    WP (ERun (mkFrame mbs_fn (put d (WPtr (mkPtr (b + o) (Obj b))) e) [] None
      (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame mbs_fn e [] None (Exec lab
    (Let d A (Renew 0 8 Write 8) [Tmp (TAtom "chk0"); Tmp (TAtom "v2")] ::
     RawStorePointer 0 src (Tmp d)
       [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hb Ho Hal Hend H48 Hchk Hv Hsrc. iIntros "Hl Hcell HK".
  pose proof (mbs_cursor_address _ _ _ Hb Ho Hend H48) as Ha.
  iApply (wp_renew _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ with "Hl");
    [reflexivity | word_premise | reflexivity | reflexivity |
     cbn [ptr_addr]; rewrite Ha; lia | cbn [ptr_addr]; rewrite Ha; exact Hend |
     cbn [ptr_addr]; rewrite Ha; exact Hal |].
  iApply bi.later_intro. iIntros "Hl".
  iApply (wp_raw_store_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ with "Hl Hcell");
    [exact Hsrc | cbn [value_x]; rewrite lookup_after_put_same; reflexivity | reflexivity | exact Ha | exact Hal |
     intros ?m ?wd ?h Hl Hw; exact (Kpstore _ _ _ _ _ _ _ _ Hl Hw) |].
  iApply bi.later_intro. iExact "HK".
Qed.

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

(** The error branch writes EILSEQ to errno and returns minus one. *)
Lemma wp_mbs_error_return e be re oe xe ce Φ :
  errno = mkPtr (be + oe) (Obj be) ->
  0 < be -> 0 <= oe -> be + oe + 4 <= r_end re -> r_end re <= 2 ^ 48 -> length xe = 4%nat ->
  pts (block_ps be re oe xe ce) -∗
  (pts (block_ps be re oe (le_bytes 84 4) ce) -∗ Φ (Ret (WInt (2 ^ 64 - 1)))) -∗
  WP (ERun (mkFrame mbs_fn e [] None
    (Exec (TAtom "L196") (b_insts (mbs_block "L196"))
      (b_jump (mbs_block "L196")))) : cexpr) {{ Φ }}.
Proof.
  intros Herr Hb Ho Hend H48 Lxe. iIntros "HBe HK".
  cbn [mbs_block hblk b_insts b_jump].
  iApply wp_conv_errno. iApply bi.later_intro. gen_env.
  iEval (rewrite -dest_block) in "HBe". iDestruct "HBe" as "(Hel & Hew & Hea)".
  iApply (wp_check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ with "Hel");
    [reflexivity | word_premise | rewrite Herr; reflexivity | rewrite Herr; addr_premise |
     rewrite Herr; addr_premise | apply Z.mod_1_r |].
  iApply bi.later_intro. iIntros "Hel". gen_env.
  iApply (wp_raw_store_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ with "Hel Hew");
    [word_premise | word_premise | rewrite Herr; reflexivity | rewrite Herr; addr_premise | exact Lxe |
     intros ?m ?wd ?h Hl Hw; exact (Kstore _ _ _ _ _ _ _ _ Hl Hw) |].
  iApply bi.later_intro. iIntros "Hel Hew".
  iApply (wp_ret _ _ _ _ _ _ _ _ _ _); [exact mbs_return_class | word_premise |].
  iApply bi.later_intro.
  change (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1).
  iApply "HK". rewrite -dest_block. iFrame.
Qed.

(** What rpl_mbsrtowcs's caller learns when it returns r, with dest's
    final bytes ws, errno's bytes xe and the length l of the source:
    EILSEQ, -1 with 84 in errno; or r wide characters, none zero,
    then a zero one. *)
Definition mbs_post (l : nat) (r : Z) (ws xe : list Z) : Prop :=
  (r = 2 ^ 64 - 1 /\ le_value xe = 84) \/
  (exists k : nat, r = Z.of_nat k /\ (k <= l)%nat /\ wide_ok (take (4 * k) ws) /\
     le_value (take 4 (drop (4 * k) ws)) = 0).


End mbrtowc.
End HelloConvWindowOn.
