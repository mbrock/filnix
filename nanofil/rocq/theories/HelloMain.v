(** * GNU Hello's main through the program logic

    Main's proof calls the triples of every Hello layer, so it applies
    each layer's functor to one Logic instance: two applications of
    [Logic] have distinct expressions, and their triples could not be
    combined. The world is libc's, and its interpretation wi stays
    abstract: each premise below is what one call needs of it, so a
    concrete interpretation discharges them once. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic MemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConv HelloName
  HelloProgName.
Open Scope Z_scope.
Open Scope list_scope.

(** Main's function, read from the linked module. *)
Definition main_fn : func := Eval vm_compute in hello_fn "main".

(** A block of main. *)
Definition main_block (s : String.string) : block := hblk main_fn s.

(** A 16-aligned base is 8-aligned. *)
Lemma mod16_mod8 b : b mod 16 = 0 -> b mod 8 = 0.
Proof.
  intros H. apply Z.mod_divide in H; [|lia]. destruct H as [k ->].
  replace (k * 16) with ((2 * k) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(** The literals main copies: "" for setlocale, the default greeting,
    read-only, and close_stdout's function pointer. *)
Definition empty_ptr : ptr := mkPtr 69968 (Ro 69968).
(** "Hello, world!". *)
Definition greeting_ptr : ptr := mkPtr 70000 (Ro 70000).
(** Its bytes. *)
Definition greeting_bytes : list Z := [72; 101; 108; 108; 111; 44; 32; 119; 111; 114; 108; 100; 33].
(** close_stdout, as a function pointer. *)
Definition close_stdout_ptr : ptr := mkPtr 65568 (Fn (TAtom "close_stdout")).

(** Hello's symbols put them there. *)
Lemma main_globals :
  lookup (TAtom "hello#str.80") hello_globals = Some empty_ptr /\
  lookup (TAtom "hello#str.81") hello_globals = Some greeting_ptr /\
  lookup (TAtom "close_stdout") hello_globals = Some close_stdout_ptr.
Proof. vm_compute. auto. Qed.

(** Main's entry binds argc and argv. *)
Lemma main_entry argc argv :
  invocation main_fn [WInt argc; WPtr argv] =
  mkFrame main_fn [(TAtom "v2", WPtr argv); (TAtom "v0", WInt argc)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** Main's proof over one Logic instance shared by every layer. *)
Module HelloMain (R : Runtime).
Module LG0 := Logic R.
Module HC := HelloConvOn R LG0.
Module HP := HelloProgNameOn R LG0.
Module HLo := HC.HLo.
Module HL := HC.HL.
Module LL := HC.LL.
Module ML := HC.ML.
Module SL := HC.SL.
Module LG := LG0.
Module L := LG.L.
Import L LG SL ML LL HL.

Section main.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Local Instance main_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

(** The genv links Hello. *)
Context (Hlinked : hello_linked ge).

(** An allocation of a fresh object, with its pieces added, keeps wi. *)
Context (Kalloc : forall q m wd h base, fresh m q base -> wi m wd h ->
     wi (allocated m q base) wd (overwrite (obj_ps base q) h)).

(** memset has its contract, and zeroing eight bytes of a block the
    program owns keeps wi. *)
Context (Hmemset : registry (TAtom "memset") = Some (memset_contract libc_world))
  (Kmemset : forall b reg o xs cs m m' wd h, memset_result m (mkPtr (b + o) (Obj b)) 0 8 m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (replicate 8 0) (clear_slots o cs)) h)).

(** set_program_name's contracts, and the layout and store premises of
    its three cells, as HelloName states them. *)
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

(** setlocale has libc's contract. The world interpretation keeps every
    lent name where [lent_at] says, admits setlocale's precondition for
    a category and a string the program owns, and survives its return,
    which lends every category's new name and sets the codec piece. *)
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

(** setlocale(c, p) over libc's world, from [wp_lend]: owning every
    category's name, the codec piece and the string at p, the call lends
    every category's new name for good, gives the codec piece a new
    codec and binds d to null or c's new name. *)
Lemma wp_main_setlocale f e ls lab d vc vp rest j c p b reg bytes old c0 Φ :
  arg_x ge e (Arg W vc) = Some (WInt c) -> arg_x ge e (Arg P vp) = Some (WPtr p) ->
  In c locale_categories ->
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string p b reg bytes -∗
  ▷ (∀ q (new : Z -> ptr * list Z) c', ⌜q = mkPtr 0 CNone \/ q = (new c).1⌝ -∗
     string p b reg bytes -∗ pts (codec_ps c') -∗
     ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "setlocale")) [Arg W vc; Arg P vp] :: rest) j))
        : mexpr) {{ Φ }}.
Proof.
  intros Hc Hp Hcat. iIntros "Hks Hcodec Hs HK".
  pose proof Hlinked as (_ & _ & Hext).
  iApply (LL.wp_lend registry wi ge Hlent f e ls lab d (TAtom "setlocale")
            [Arg W vc; Arg P vp] rest j (libc_setlocale_contract rep requests) [WInt c; WPtr p]
            locale_categories old (codec_ps c0)
            (fun q new gs' => (q = mkPtr 0 CNone \/ q = (new c).1) /\ exists c', gs' = codec_ps c')
            with "Hks Hcodec Hs [HK]");
    [exact Hsetlocale | reflexivity | apply linked_outside; first [exact Hlinked | reflexivity] |
     apply linked_unbound; first [exact Hlinked | reflexivity] | reflexivity |
     cbn [map_option]; rewrite Hc Hp; reflexivity | | | | | ].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - apply List.Forall_forall. intros k Hk. cbn. rewrite list_elem_of_singleton. intros E.
    injection E as ->. unfold codec_key, locale_categories in Hk. cbn in Hk. intuition lia.
  - iIntros (σ) "Hσ Hs". iDestruct "Hs" as "[%Hok Hps]".
    iDestruct (pts_facts with "Hσ Hps") as %(Hag & _).
    iDestruct "Hσ" as (h) "[_ %Hf]". destruct Hf as (_ & _ & _ & Hw).
    iPureIntro. exact (Hset_pre _ _ _ _ _ _ _ _ Hw Hcat Hok Hag).
  - intros s m w h trace values s' m' w' Hw Ha Hd Hr Hi.
    destruct (Kset _ _ _ _ _ _ _ _ _ _ _ _ _ Hw Ha Hd Hr Hi)
      as (q & new & c' & Hv & Hq & Ha' & Hd' & Hr' & Hw').
    exists q, new, (codec_ps c'). split; [exact Hv|]. split; [split; [exact Hq | eauto]|].
    split; [reflexivity|]. split; [cbn; repeat constructor|]. auto.
  - iNext. iIntros (q new gs' [Hq [c' ->]]) "Hs Hcodec Hl". iApply ("HK" with "[%] Hs Hcodec Hl"). exact Hq.
Qed.

(** Eight zero bytes and an empty slot at offset 0 are a null pointer
    cell. *)
Lemma zero_pcell b : bytes b 0 (replicate 8 0) ∗ auxes b 0 [CNone] ⊣⊢ pcell b 0 (mkPtr 0 CNone).
Proof.
  rewrite /bytes /auxes /pcell -pts_app.
  assert (E : byte_ps b 0 (replicate 8 0) ++ aux_ps b 0 [CNone] = cell b 0 0 ++ [(PAux b 0, VAux CNone)]).
  { vm_compute. reflexivity. }
  rewrite E pts_app. cbn [ptr_addr ptr_cap]. rewrite /pts !big_sepL_cons big_sepL_nil.
  iSplit; [iIntros "[H [A _]]"; iFrame | iIntros "[A H]"; iFrame].
Qed.

(** Enter a block of main. *)
Ltac mn_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (main_block s));
  [vm_compute; reflexivity | word_premise |]; iNext;
  cbn [b_insts b_jump main_block hblk].

(** mbszero at the start of an object: [mbszero_spec] at offset 0. *)
Lemma mbszero_at b reg xs cs Φ :
  length xs = 8%nat -> length cs = 8%nat -> b mod 8 = 0 -> b + 8 <= r_end reg ->
  live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗
  ▷ (live b reg -∗ bytes b 0 (replicate 8 0) -∗ auxes b 0 (clear_slots 0 cs) -∗ Φ RetVoid) -∗
  WP (ERun (invocation mbszero_fn [WPtr (mkPtr b (Obj b))]) : mexpr) {{ Φ }}.
Proof.
  intros Lx Lc Hb8 Hend.
  pose proof (mbszero_spec registry wi ge Hlinked b reg 0 xs cs Φ) as H. rewrite !Z.add_0_r in H.
  iApply H; [exact Hmemset | exact Lx | exact Lc | exact Hb8 | reflexivity | lia | exact Hend |].
  intros m m' wd h Hr Hin Hw. pose proof (Kmemset b reg 0 xs cs m m' wd h) as K.
  rewrite !Z.add_0_r in K. exact (K Hr Hin Hw).
Qed.

(** The instructions of main's start block from setlocale's call on. *)
Definition start_rest : list inst := Eval vm_compute in drop 7 (b_insts (main_block "start")).

(** The temporaries main has bound before setlocale: argc, argv, the
    greeting's cell b4, the state b6, and the literal "". *)
Definition start_vars (e : env) (argc : Z) (av b4 b6 : Z) : Prop :=
  lookup (TAtom "v0") e = Some (WInt argc) /\ lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) /\
  lookup (TAtom "v4") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
  lookup (TAtom "v6") e = Some (WPtr (mkPtr b6 (Obj b6))) /\
  lookup (TAtom "v11") e = Some (WPtr empty_ptr).

(** A fresh heap object of main: positive, 16-aligned, in the address
    space. *)
Definition fresh_ok (b : Z) : Prop := 0 < b /\ b mod 16 = 0 /\ b + 16 <= 2 ^ 48.

(** Main's start block up to setlocale: two fresh objects, b4 for the
    greeting's cell and b6 for the conversion state, which mbszero
    zeroes; argv[0] loaded and handed to set_program_name, which leaves
    the name cells at a suffix of it; the literal "" copied. *)
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
  iEval (rewrite (HC.bytes_split _ _ _ 8); [|rewrite length_replicate; vm_compute; lia]) in "Hy6".
  iEval (rewrite (HC.auxes_split _ _ _ 8); [|rewrite length_replicate; vm_compute; lia]) in "Hc6".
  iDestruct "Hy6" as "[Hy6 Hy6']". iDestruct "Hc6" as "[Hc6 Hc6']".
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ mbszero_fn (invocation mbszero_fn [WPtr (mkPtr b6 (Obj b6))]));
    [word_premise | unfold find_fn; rewrite Hm; vm_compute; reflexivity | reflexivity |].
  iNext. iApply (mbszero_at with "Hl6 Hy6 Hc6");
    [rewrite length_take length_replicate; vm_compute; lia | rewrite length_take length_replicate; vm_compute; lia |
     destruct Hb6 as (_ & H16 & _); apply mod16_mod8; exact H16 | change (b6 + 8 <= b6 + 16); lia |].
  iNext. iIntros "Hl6 Hy6 Hc6".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  (* argv[0], the program's name. *)
  iApply (wp_check_read with "Hal");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise | addr_premise |].
  iNext. iIntros "Hal". gen_env.
  iDestruct "Hs0" as "[%Hok0 Hps0]". pose proof Hok0 as (Hc0 & Hb0 & Hbp0 & Hsend0 & H480 & Hbs0).
  iApply (wp_raw_load_pointer_in with "Hal Ha0 Hps0");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise | lia |
     intros xb Hxb; exists r0; destruct Hc0 as [Hc0 | Hc0]; rewrite Hc0 in Hxb;
     destruct Hxb as [Hxb | Hxb]; try discriminate Hxb; injection Hxb as <-;
     apply elem_of_cons; left; reflexivity |].
  iNext. iIntros "Hal Ha0 Hps0". gen_env.
  iAssert (string a0 b0 r0 ys0) with "[$Hps0]" as "Hs0"; [done|].
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ set_program_name_fn
            (invocation set_program_name_fn [WPtr a0]));
    [word_premise | unfold find_fn; rewrite Hm; vm_compute; reflexivity | reflexivity |].
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

End main.
End HelloMain.
