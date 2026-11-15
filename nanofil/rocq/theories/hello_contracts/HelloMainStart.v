(** GNU Hello initializes its program name, locale, greeting cell, and
    conversion state before parsing options. This file proves that
    initialization using the call rules from [HelloMainBase]. [HelloMain]
    includes the proofs without changing the names callers use. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia Permutation.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs HelloName
  HelloProgName Startup Getopt GetoptLogic HelloVersion HelloMainBase HelloMainFacts.
Open Scope Z_scope.
Open Scope list_scope.
Import MainDefinitions.

Module HelloMainStart (R : Runtime).
Include HelloMainBase R.
Include MainFacts.
Import HLo HL ML LG.
Import L LG SL ML LL HL.

Local Hint Opaque main_fn pts bytes auxes live pcell main_irisGS
  HP.HN.literals HP.HN.name_cells : typeclass_instances.

Section main.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

Let section_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  main_irisGS registry wi ge.
Local Existing Instance section_irisGS.
Local Hint Opaque section_irisGS : typeclass_instances.
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

Local Ltac mn_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (main_block s));
  [abstract (vm_cast_no_check (eq_refl (Some (main_block s)))) | word_premise |]; iNext;
  cbn [b_insts b_jump main_block hblk].

Context (Hlinked : hello_linked ge).

Context (Kalloc : forall q m wd h base, fresh m q base -> wi m wd h ->
     wi (allocated m q base) wd (overwrite (obj_ps base q) h)).

Context (Hmemset : registry (TAtom "memset") = Some (memset_contract libc_world))
  (Kmemset : forall b reg o xs cs m m' wd h, memset_result m (mkPtr (b + o) (Obj b)) 0 8 m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (replicate 8 0) (clear_slots o cs)) h)).

Context (Hstrrchr : registry (TAtom "strrchr") = Some (strrchr_contract libc_world))
  (Hmemcmp : registry (TAtom "memcmp") = Some (memcmp_contract libc_world))
  (Hstrncmp : registry (TAtom "strncmp") = Some (strncmp_contract libc_world)).

Context (pn nreg sreg : region) (nb sb : Z)
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hpn_end : program_name_b + 8 <= r_end pn)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48)
  (Kpn : HP.HN.store_keeps wi program_name_b pn) (Knb : HP.HN.store_keeps wi nb nreg)
  (Ksb : HP.HN.store_keeps wi sb sreg).

Context (rep : mem -> libc_world -> Prop) (requests : list word -> mem -> libc_world -> Z -> Z -> Prop)
  (Hsetlocale : registry (TAtom "setlocale") = Some (libc_setlocale_contract rep requests))
  (Hlent : forall m w h k p t,
     wi m w h -> live_disjoint m -> objects_fit (m_regions m) -> freed_empty (m_regions m) ->
     h !! PName k = Some (VName p t) -> lent_at m h p t)
  (Hset_pre : forall m w h c p b reg bytes, wi m w h -> In c locale_categories ->
     string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
     libc_setlocale_pre rep [WInt c; WPtr p] m w)
  (Kset : forall r args c p s m w h trace values s' m' w', wi m w h -> agrees m h -> live_disjoint m -> R.ready s m ->
     M.E.invoke (libc_setlocale_contract rep requests) r args [WInt c; WPtr p] s m w trace (CallReturn values) s' m' w' ->
     exists q (new : Z -> ptr * list Z) c', values = [WPtr q] /\ (q = mkPtr 0 CNone \/ q = (new c).1) /\
       agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\
       wi m' w' (overwrite (codec_ps c') (rename h locale_categories new))).

Context (Kpstore : forall b reg o x xp m wd h,
  (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
     h !! l = Some v) ->
  wi m wd h ->
  wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
    (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)).

Context (atexit_spec : contract libc_world)
  (Hatexit : registry (TAtom "atexit") = Some atexit_spec)
  (Hatexit_ret : contract_returns atexit_spec = RClass W)
  (Hatexit_abi : contract_abi atexit_spec (CResult (TAtom "v15") W) [Arg P (Tmp (TAtom "v14"))])
  (Hatexit_pre : forall m w h, wi m w h -> contract_pre atexit_spec [WPtr close_stdout_ptr] m w)
  (Katexit : forall r args s m w h trace values s' m' w', wi m w h -> agrees m h -> live_disjoint m ->
     R.ready s m ->
     M.E.invoke atexit_spec r args [WPtr close_stdout_ptr] s m w trace (CallReturn values) s' m' w' ->
     exists x, values = [WInt x] /\ 0 <= x < 2 ^ 32 /\ agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\
       wi m' w' h).

Local Notation mbszero_at := (mbszero_at registry wi ge Hlinked Hmemset Kmemset).
(** Main allocates cells for the greeting and conversion state, then
    initializes the program name from its first argument. It next
    prepares the empty string for the locale call. *)
Lemma main_to_setlocale argc av ar a0 b0 r0 ys0 r3 r4 x0 x1 y0 Φ :
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live av ar -∗ pcell av 0 a0 -∗ string a0 b0 r0 ys0 -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  ▷ (∀ e b4 b6 (i k : nat),
       ⌜start_vars e argc av b4 b6 /\ fresh_ok b4 /\ fresh_ok b6 /\
        (i <= length ys0)%nat /\ (k <= length ys0)%nat⌝ -∗
       live av ar -∗ pcell av 0 a0 -∗ string a0 b0 r0 ys0 -∗ HP.HN.literals r3 r4 -∗
       HP.HN.name_cells pn nreg sreg nb sb
         (mkPtr (ptr_addr a0 + Z.of_nat i) (ptr_cap a0)) (mkPtr (ptr_addr a0 + Z.of_nat i) (ptr_cap a0))
         (mkPtr (ptr_addr a0 + Z.of_nat k) (ptr_cap a0)) -∗
       live b4 (mkRegion b4 (b4 + 16) Heap Live) -∗ bytes b4 0 (replicate 16 0) -∗
       auxes b4 0 (replicate 16 CNone) -∗
       live b6 (mkRegion b6 (b6 + 16) Heap Live) -∗ bytes b6 0 (replicate 8 0) -∗
       bytes b6 8 (replicate 8 0) -∗ auxes b6 0 (clear_slots 0 (replicate 8 CNone)) -∗
       auxes b6 8 (replicate 8 CNone) -∗
       WP (ERun (mkFrame main_fn e [] None (Exec (TAtom "start") start_rest (b_jump (main_block "start"))))
             : mexpr) {{ Φ }}) -∗
  WP (ERun (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))]) : mexpr) {{ Φ }}.
Proof.
  clear - SafepointStable0 Hlinked Kalloc Hmemset Kmemset Hstrrchr Hmemcmp Hstrncmp
    Hnb Hsb Hpn_end Hnb_cell Hsb_cell Kpn Knb Ksb.
  intros Hav Hav8 Haend Har48. iIntros "Hal Ha0 Hs0 Hlit Hcells HK".
  pose proof Hlinked as (Hm & _ & Hext).
  rewrite main_entry. mn_enter "start".
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 8);
    [reflexivity | lia | unfold max_allocation_size; lia | intros m wd h base Hf Hw; exact (Kalloc _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b4 Hb4) "Hb4". gen_env.
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 8);
    [reflexivity | lia | unfold max_allocation_size; lia | intros m wd h base Hf Hw; exact (Kalloc _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b6 Hb6) "Hb6". gen_env.
  (* The state is zeroed. *)
  iEval (rewrite (obj_zero_block b6 _); [|compute; congruence]) in "Hb6".
  iDestruct "Hb6" as "(Hl6 & Hy6 & Hc6)". cbn [req_extent heap_req Z.to_nat Pos.to_nat] in *.
  iEval (rewrite (bytes_take_drop _ _ _ 8); [|rewrite length_replicate; vm_compute; lia]) in "Hy6".
  iEval (rewrite (auxes_take_drop _ _ _ 8); [|rewrite length_replicate; vm_compute; lia]) in "Hc6".
  iDestruct "Hy6" as "[Hy6 Hy6']". iDestruct "Hc6" as "[Hc6 Hc6']".
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ mbszero_fn (invocation mbszero_fn [WPtr (mkPtr b6 (Obj b6))]));
    [word_premise | unfold find_fn; rewrite Hm;
     abstract (vm_cast_no_check (eq_refl (Some (Defined mbszero_fn)))) | reflexivity |].
  iNext. iApply (mbszero_at with "Hl6 Hy6 Hc6");
    [rewrite length_take length_replicate; vm_compute; lia | rewrite length_take length_replicate; vm_compute; lia |
     destruct Hb6 as (_ & H16 & _); apply mod16_mod8; exact H16 | change (b6 + 8 <= b6 + 16); lia |].
  iNext. iIntros "Hl6 Hy6 Hc6".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  (* argv[0], the program's name. *)
  iApply (wp_check_read with "Hal");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise |
     cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; rewrite Z.add_0_r; exact Hav8 |].
  iNext. iIntros "Hal". gen_env.
  iDestruct "Hs0" as "[%Hok0 Hps0]". pose proof Hok0 as (Hc0 & Hb0 & Hbp0 & Hsend0 & H480 & Hbs0).
  iApply (wp_raw_load_pointer_in with "Hal Ha0 Hps0");
    [reflexivity | word_premise | left; reflexivity | addr_premise |
     rewrite Z.add_0_r; exact Hav8 | lia |
     intros xb Hxb; exists r0; destruct Hc0 as [Hc0 | Hc0]; rewrite Hc0 in Hxb;
     destruct Hxb as [Hxb | Hxb]; try discriminate Hxb; injection Hxb as <-;
     apply elem_of_cons; left; reflexivity |].
  iNext. iIntros "Hal Ha0 Hps0". gen_env.
  iAssert (string a0 b0 r0 ys0) with "[$Hps0]" as "Hs0"; [done|].
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ set_program_name_fn
            (invocation set_program_name_fn [WPtr a0]));
    [word_premise | unfold find_fn; rewrite Hm;
     abstract (vm_cast_no_check (eq_refl (Some (Defined set_program_name_fn)))) | reflexivity |].
  iNext.
  iApply (HP.set_program_name_string_spec registry wi ge Hlinked Hstrrchr Hmemcmp Hstrncmp
            pn nreg sreg nb sb Hnb Hsb Hpn_end Hnb_cell Hsb_cell Kpn Knb Ksb with "Hs0 Hlit Hcells").
  iNext. iIntros (i k [Hi Hk]) "Hsuf Hback Hlit Hcells".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  iDestruct ("Hback" with "Hsuf") as "Hs0".
  (* setlocale(LC_ALL, ""). *)
  destruct main_globals as (G80 & G81 & Gcs). destruct Hlinked as (_ & Hg & _).
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hg _ _ G80); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iEval (rewrite (obj_zero_block b4 _); [|compute; congruence]) in "Hb4".
  iDestruct "Hb4" as "(Hl4 & Hy4 & Hc4)".
  destruct Hb4 as (Hb40 & Hb416 & Hb448). destruct Hb6 as (Hb60 & Hb616 & Hb648).
  iApply ("HK" $! _ b4 b6 i k with "[%] Hal Ha0 Hs0 Hlit Hcells Hl4 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'").
  split; [repeat split; assumption|]. split; [split; [exact Hb40 | split; [exact Hb416 | exact Hb448]]|].
  split; [split; [exact Hb60 | split; [exact Hb616 | exact Hb648]]|]. auto.
Qed.
Local Notation wp_main_setlocale := (wp_main_setlocale registry wi ge Hlinked
  nreg sreg nb sb Hnb_cell Hsb_cell rep requests Hsetlocale Hlent Hset_pre Kset).
(** Main sets the locale, stores its default greeting, and registers
    close_stdout with atexit. Initialization then enters the option loop. *)
Lemma main_start_rest e argc av b4 b6 old c0 r80 Φ :
  start_vars e argc av b4 b6 -> fresh_ok b4 ->
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗
  live b4 (mkRegion b4 (b4 + 16) Heap Live) -∗ bytes b4 0 (replicate 16 0) -∗
  auxes b4 0 (replicate 16 CNone) -∗
  ▷ (∀ e' q (new : Z -> ptr * list Z) c',
       ⌜start_vars e' argc av b4 b6 /\ lookup (TAtom "chk1") e' = Some (WPtr (mkPtr b4 (Obj b4))) /\
        (q = mkPtr 0 CNone \/ q = (new 6).1)⌝ -∗
       ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗ pts (codec_ps c') -∗
       string empty_ptr 69968 r80 [] -∗
       live b4 (mkRegion b4 (b4 + 16) Heap Live) -∗ pcell b4 0 greeting_ptr -∗
       bytes b4 8 (replicate 8 0) -∗ auxes b4 1 (replicate 15 CNone) -∗
       WP (ERun (mkFrame main_fn e' [] None (Enter (TAtom "iw_1.L8") (Some (TAtom "start")))) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame main_fn e [] None (Exec (TAtom "start") start_rest (b_jump (main_block "start"))))
        : mexpr) {{ Φ }}.
Proof.
  intros (H0 & H2 & H4 & H6 & H11) (Hb40 & Hb416 & Hb448).
  iIntros "Hks Hcod Hs80 Hl4 Hy4 Hc4 HK".
  destruct main_globals as (G80 & G81 & Gcs). pose proof Hlinked as (Hm & Hg & _).
  rewrite /start_rest. cbn [b_jump main_block hblk].
  (* setlocale(LC_ALL, ""). *)
  iApply (wp_main_setlocale with "Hks Hcod Hs80"); [word_premise | word_premise | cbn; tauto |].
  iNext. iIntros (q new c' Hq) "Hs80 Hcod Hlent". gen_env.
  (* The default greeting, stored in b4's cell. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hg _ _ G81); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_check with "Hl4");
    [reflexivity | word_premise | reflexivity | addr_premise | cbn [ptr_addr r_end]; unfold raw_address; drop_wraps_goal; lia |
     cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; rewrite Z.add_0_r; apply mod16_mod8; exact Hb416 |].
  iNext. iIntros "Hl4". gen_env.
  iEval (rewrite (bytes_take_drop _ _ _ 8); [|rewrite length_replicate; lia]) in "Hy4".
  iEval (rewrite (auxes_take_drop _ _ _ 1); [|rewrite length_replicate; lia]) in "Hc4".
  iDestruct "Hy4" as "[Hy4 Hy4']". iDestruct "Hc4" as "[Hc4 Hc4']".
  iAssert (pcell b4 0 (mkPtr 0 CNone)) with "[Hy4 Hc4]" as "Hp4"; [iApply zero_pcell; iFrame|].
  iApply (wp_raw_store_pointer with "Hl4 Hp4");
    [word_premise | word_premise | reflexivity | addr_premise |
     rewrite Z.add_0_r; apply mod16_mod8; exact Hb416 |
     intros m wd h Hin Hw; exact (Kpstore _ _ _ _ _ _ _ _ Hin Hw) |].
  iNext. iIntros "Hl4 Hp4".
  (* atexit(close_stdout). *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hg _ _ Gcs); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ atexit_spec [WPtr close_stdout_ptr] emp%I with "[//] [-]");
    [apply linked_outside; first [exact Hlinked | reflexivity] |
     apply linked_unbound; first [exact Hlinked | reflexivity] | reflexivity | exact Hatexit |
     cbn [map_option]; word_premise | exact Hatexit_abi | |].
  - iIntros (σ) "Hσ _". iDestruct "Hσ" as (h) "[_ %Hf]". destruct Hf as (_ & _ & _ & Hw).
    iPureIntro. exact (Hatexit_pre _ _ _ Hw).
  - iNext. iIntros (σ trace values s' m' w' Hi) "Hσ _".
    iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (Katexit _ _ _ _ _ _ _ _ _ _ _ Hw Ha Hd Hr Hi) as (x & -> & Hx & Ha' & Hd' & Hr' & Hw').
    iModIntro. iExists _. iSplit.
    + iPureIntro. unfold external_env. rewrite Hatexit_ret. cbn. reflexivity.
    + iSplitL "Hh"; [iExists h; iFrame; iPureIntro; auto|].
      iApply wp_goto. iNext. cbn [edge_label]. gen_env.
      iApply ("HK" $! _ q new c' with "[%] Hlent Hcod Hs80 Hl4 Hp4 Hy4' Hc4'").
      split; [repeat split; assumption|]. split; [assumption | exact Hq].
Qed.

(** The two initialization phases connect main's entry to the option loop. *)
Lemma main_start argc av ar a0 b0 r0 ys0 r3 r4 x0 x1 y0 old c0 r80 Φ :
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live av ar -∗ pcell av 0 a0 -∗ string a0 b0 r0 ys0 -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗
  ▷ (∀ e b4 b6 (i k : nat) q (new : Z -> ptr * list Z) c',
       ⌜start_vars e argc av b4 b6 /\ lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
        fresh_ok b4 /\ fresh_ok b6 /\ (i <= length ys0)%nat /\ (k <= length ys0)%nat /\
        (q = mkPtr 0 CNone \/ q = (new 6).1)⌝ -∗
       live av ar -∗ pcell av 0 a0 -∗ string a0 b0 r0 ys0 -∗ HP.HN.literals r3 r4 -∗
       HP.HN.name_cells pn nreg sreg nb sb
         (mkPtr (ptr_addr a0 + Z.of_nat i) (ptr_cap a0)) (mkPtr (ptr_addr a0 + Z.of_nat i) (ptr_cap a0))
         (mkPtr (ptr_addr a0 + Z.of_nat k) (ptr_cap a0)) -∗
       ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗ pts (codec_ps c') -∗
       string empty_ptr 69968 r80 [] -∗
       live b4 (mkRegion b4 (b4 + 16) Heap Live) -∗ pcell b4 0 greeting_ptr -∗
       bytes b4 8 (replicate 8 0) -∗ auxes b4 1 (replicate 15 CNone) -∗
       live b6 (mkRegion b6 (b6 + 16) Heap Live) -∗ bytes b6 0 (replicate 8 0) -∗
       bytes b6 8 (replicate 8 0) -∗ auxes b6 0 (clear_slots 0 (replicate 8 CNone)) -∗
       auxes b6 8 (replicate 8 CNone) -∗
       WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom "start")))) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))]) : mexpr) {{ Φ }}.
Proof.
  intros Hav Hav8 Haend Har48. iIntros "Hal Ha0 Hs0 Hlit Hcells Hks Hcod Hs80 HK".
  iApply (main_to_setlocale with "Hal Ha0 Hs0 Hlit Hcells"); [exact Hav | exact Hav8 | exact Haend | exact Har48 |].
  iNext. iIntros (e b4 b6 i k (Hv & Hf4 & Hf6 & Hi & Hk))
    "Hal Ha0 Hs0 Hlit Hcells Hl4 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'".
  iApply (main_start_rest with "Hks Hcod Hs80 Hl4 Hy4 Hc4"); [exact Hv | exact Hf4 |].
  iNext. iIntros (e' q new c' (Hv' & Hc1 & Hq)) "Hlent Hcod Hs80 Hl4 Hp4 Hy4 Hc4".
  iApply ("HK" $! e' b4 b6 i k q new c' with
           "[%] Hal Ha0 Hs0 Hlit Hcells Hlent Hcod Hs80 Hl4 Hp4 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'").
  auto 10.
Qed.

End main.
End HelloMainStart.
