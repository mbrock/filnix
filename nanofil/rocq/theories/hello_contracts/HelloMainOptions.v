(** GNU Hello's greeting options update the pointer stored in its greeting
    cell. This file proves the two update blocks separately, returning
    their resources to a continuation at the next loop iteration. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia Permutation.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs HelloName
  HelloProgName Startup Getopt GetoptLogic HelloVersion HelloMainInterface HelloMainFacts.
Open Scope Z_scope.
Open Scope list_scope.
Import HelloMainBase.MainDefinitions MainFacts.

Module HelloMainOptions (R : Runtime) (B : HelloMainInterface.HelloMainBase R).
Import B B.LG0 B.LG0.L B.HLo.HL B.HLo.HL.ML B.HLo.HL.ML.CSL.

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

Context (av : Z) (ar : region) (sargs : list argument)
  (Hav : 0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length sargs) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48)
  (Hargc : 1 <= Z.of_nat (length sargs) < 2 ^ 31)
  (Hargs : Forall (fun s => string_ok (arg_ptr s) (arg_base s) (arg_region s) (arg_text s)) sargs).

(** Each argument pointer and the null sentinel occupy eight byte and auxiliary slots. *)
Local Notation argv_len := (8 * (length sargs + 1))%nat.

(** The parser contract records its initial state, allocations, and
    state changes when a call returns. *)
Context (initialized running : mem -> libc_world -> Prop)
  (grequests : list word -> mem -> libc_world -> Z -> Z -> Prop)
  (transition : list word -> mem -> libc_world -> list Z -> list event -> list word -> mem -> libc_world -> Prop)
  (Hgetopt : registry (TAtom "getopt_long") =
     Some (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition)).

(** The contract. *)
Local Notation getopt_spec :=
  (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition).

(** wi ties libc's optarg and optind cells to the parser's state and
    the getopt token, as GetoptLogic.v's reads need. *)
Context (optarg_cell optind_cell : ptr)
  (Hgetopt_wi : forall m w h, wi m w h ->
     getopt_state_at m (libc_getopt_view w) /\ getopt_optarg_cell (libc_getopt_view w) = optarg_cell /\
     getopt_optind_cell (libc_getopt_view w) = optind_cell /\ getopt_current (libc_getopt_view w) h).

(** wi keeps Hello's option literals in memory. *)
Context (Htable : forall m w h, wi m w h -> hello_table_at m).

(** The parser's private memory remains separate from the caller's
    argument vector and strings. Its input buffers remain readable. *)
Context (Hgetopt_env : forall m w h xs cs, wi m w h -> agrees m h -> live_disjoint m ->
   (forall l v, (l, v) ∈ block_ps av ar 0 xs cs ++ flat_map arg_ps sargs -> h !! l = Some v) ->
   getopt_input_at m (hello_input av sargs) ->
   libc_getopt_rep initialized m w /\
   Forall (writable_span m) (getopt_roots (libc_getopt_view w)) /\
   Forall (fun s => readable_bytes m (span_ptr s) (span_size s)) (getopt_reads (libc_getopt_view w)) /\
   getopt_separated (hello_input av sargs) (libc_getopt_view w) /\
   getopt_disjoint (getopt_public_writes (hello_input av sargs) (libc_getopt_view w)) /\
   getopt_private_owned m (hello_input av sargs) (libc_getopt_view w)).

(** getopt_long's private roots and libc's cells are apart from the
    program's objects, and it releases none of them. *)
Context (Hgetopt_apart : forall m w h, wi m w h ->
   (forall s a, In s (getopt_roots (libc_getopt_view w) ++ getopt_cells (libc_getopt_view w)) ->
      span_contains s a -> ~ owned_live h m a) /\
   ids_apart (getopt_owned (libc_getopt_view w)) h).

(** A parser call preserves the world interpretation after updating
    the argument vector and the current option's value and position. *)
Context (Kgetopt : forall r args xs s m w h trace values s' m' w' bs cs,
   M.E.invoke getopt_spec r args xs s m w trace (CallReturn values) s' m' w' ->
   (forall l v, (l, v) ∈ block_ps av ar 0 bs cs -> h !! l = Some v) -> wi m w h ->
   agrees m h -> live_disjoint m -> R.ready s m ->
   wi m' w' (overwrite (block_ps av ar 0 (mem_bytes m' av argv_len) (mem_auxes m' av argv_len) ++
     getopt_ps (getopt_optarg (libc_getopt_view w')) (getopt_optind (libc_getopt_view w'))) h)).
Context (Hoptarg_g : lookup (TAtom "optarg") (ge_globals ge) = Some optarg_cell)
  (Hcells : 0 <= ptr_addr optarg_cell < 2 ^ 64 /\ 0 <= ptr_addr optind_cell < 2 ^ 64).

Local Notation order_length := (order_length sargs).
Local Notation getopt_step := (getopt_step wi transition).
Local Notation loop_res := (loop_res av ar sargs).
Local Notation loop_facts := (loop_facts av sargs).
Local Notation loop_exit := (loop_exit registry wi ge av ar sargs).
Local Notation wp_main_getopt := (wp_main_getopt registry wi ge Hlinked
  av ar sargs Hav Hargc Hargs initialized running grequests transition Hgetopt
  optarg_cell optind_cell Hgetopt_wi Htable Hgetopt_env Hgetopt_apart Kgetopt).
Local Notation main_to_L8 := (main_to_L8 registry wi ge Hlinked Kalloc Hmemset Kmemset
  Hstrrchr Hmemcmp Hstrncmp pn nreg sreg nb sb Hnb Hsb Hpn_end Hnb_cell Hsb_cell
  Kpn Knb Ksb rep requests Hsetlocale Hlent Hset_pre Kset Kpstore
  atexit_spec Hatexit Hatexit_ret Hatexit_abi Hatexit_pre Katexit av ar sargs Hav Hargc Hargs).

(** The greeting option borrows optarg and stores it in the greeting cell.
    The continuation receives the loop resources with this new greeting. *)
Lemma loop_greeting b4 b6 e ps cs a i g lose Φ :
  loop_facts e b4 b6 ps cs i g ->
  lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) ->
  (lose = 0 \/ lose = 1) -> getopt_borrow (hello_input av sargs) a -> ptr_addr a <> 0 ->
  loop_res b4 ps cs a i g -∗
  loop_exit b4 b6 "iw_1.L8"%string "iw_1.L35"%string Φ -∗
  WP (ERun (mkFrame main_fn e [] None
    (Enter (TAtom "iw_1.L35") (Some (TAtom "iw_1.L48")))) : mexpr) {{ Φ }}.
Proof using Hcells Hgetopt_wi Hoptarg_g Kpstore SafepointStable0.
  intros ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg)
    Hpr Hlose Hborrow Hnz.
  pose proof Hfr as (Hb40 & Hb416 & Hb448).
  iIntros "(Hb & Hs & Ht & Hl4 & Hp4) HK".
  mn_enter "iw_1.L35".
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hoptarg_g; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (GL.wp_optarg_check registry wi ge libc_getopt_view optarg_cell optind_cell Hcells Hgetopt_wi);
    [reflexivity | word_premise |].
  iNext. gen_env.
  iApply (GL.wp_optarg_load registry wi ge libc_getopt_view optarg_cell optind_cell Hcells Hgetopt_wi
    with "Ht"); [reflexivity | word_premise |].
  iNext. iIntros "Ht". gen_env.
  iApply (wp_renew with "Hl4");
    [reflexivity | word_premise | reflexivity | reflexivity | addr_premise |
     cbn [ptr_addr r_end]; unfold raw_address; drop_wraps_goal; lia |
     cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; rewrite Z.add_0_r; apply mod16_mod8; exact Hb416 |].
  iNext. iIntros "Hl4". gen_env.
  iApply (wp_raw_store_pointer with "Hl4 Hp4");
    [word_premise | word_premise | reflexivity | addr_premise |
     rewrite Z.add_0_r; apply mod16_mod8; exact Hb416 |
     intros m wd h Hin Hw; exact (Kpstore _ _ _ _ _ _ _ _ Hin Hw) |].
  iNext. iIntros "Hl4 Hp4".
  iApply wp_goto. iNext. cbn [edge_label].
  iApply ("HK" $! _ ps cs a i a lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
  split; [|split; assumption].
  split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|].
  split; [exact Ho|]. split; [exact Hc|]. split; [exact Hi|]. right; right; split; assumption.
Qed.

(** The traditional option stores the linked traditional greeting.
    It preserves the option token and all other loop resources. *)
Lemma loop_traditional b4 b6 e ps cs a i g lose Φ :
  loop_facts e b4 b6 ps cs i g ->
  lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) -> (lose = 0 \/ lose = 1) ->
  loop_res b4 ps cs a i g -∗
  loop_exit b4 b6 "iw_1.L8"%string "iw_1.L42"%string Φ -∗
  WP (ERun (mkFrame main_fn e [] None
    (Enter (TAtom "iw_1.L42") (Some (TAtom "iw_1.L52")))) : mexpr) {{ Φ }}.
Proof using Hlinked Kpstore SafepointStable0.
  intros ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg) Hpr Hlose.
  pose proof Hfr as (Hb40 & Hb416 & Hb448).
  destruct getopt_globals as (_ & _ & G76 & _). pose proof Hlinked as (_ & Hglob & _).
  iIntros "(Hb & Hs & Ht & Hl4 & Hp4) HK".
  mn_enter "iw_1.L42".
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hglob _ _ G76); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_renew with "Hl4");
    [reflexivity | word_premise | reflexivity | reflexivity | addr_premise |
     cbn [ptr_addr r_end]; unfold raw_address; drop_wraps_goal; lia |
     cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; rewrite Z.add_0_r; apply mod16_mod8; exact Hb416 |].
  iNext. iIntros "Hl4". gen_env.
  iApply (wp_raw_store_pointer with "Hl4 Hp4");
    [word_premise | word_premise | reflexivity | addr_premise |
     rewrite Z.add_0_r; apply mod16_mod8; exact Hb416 |
     intros m wd h Hin Hw; exact (Kpstore _ _ _ _ _ _ _ _ Hin Hw) |].
  iNext. iIntros "Hl4 Hp4".
  iApply wp_goto. iNext. cbn [edge_label].
  iApply ("HK" $! _ ps cs a i traditional_ptr lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
  split; [|split; assumption].
  split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|].
  split; [exact Ho|]. split; [exact Hc|]. split; [exact Hi|]. right; left; reflexivity.
Qed.

(** Each option either exits the loop or returns its resources for another iteration. *)
Lemma loop_dispatch b4 b6 e ps' cs' a' i' g lose c Φ :
  loop_facts e b4 b6 ps' cs' i' g ->
  lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) -> (lose = 0 \/ lose = 1) ->
  lookup (TAtom "iw_1.v15") e = Some (WInt c) -> 0 <= c < 2 ^ 32 ->
  (c = 103 -> getopt_borrow (hello_input av sargs) a' /\ ptr_addr a' <> 0) ->
  loop_res b4 ps' cs' a' i' g -∗
  (loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ ∧
   loop_exit b4 b6 "iw_1.L39"%string "iw_1.L50"%string Φ ∧
   loop_exit b4 b6 "iw_1.L10"%string "iw_1.L8"%string Φ) -∗
  (∀ from e lose ps cs a i g,
    ⌜loop_entry from e lose /\ loop_facts e b4 b6 ps cs i g⌝ -∗ loop_res b4 ps cs a i g -∗
    (loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ ∧
     loop_exit b4 b6 "iw_1.L39"%string "iw_1.L50"%string Φ ∧
     loop_exit b4 b6 "iw_1.L10"%string "iw_1.L8"%string Φ) -∗
    WP (ERun (mkFrame main_fn e [] None
      (Enter (TAtom "iw_1.L8") (Some (TAtom from)))) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame main_fn e [] None
    (Enter (TAtom "iw_1.L19") (Some (TAtom "iw_1.L8")))) : mexpr) {{ Φ }}.
Proof using Hcells Hgetopt_wi Hlinked Hoptarg_g Kpstore SafepointStable0.
  clear - Hlinked Kpstore optarg_cell optind_cell Hgetopt_wi Hoptarg_g Hcells SafepointStable0.
  intros ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho' & Hc' & Hi' & Hg)
    Hpr Hlose Hcode Hcr Hgc.
  iIntros "(Hb & Hs & Ht & Hl4 & Hp4) HK IH".
  mn_enter "iw_1.L19".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 129) as [-> | H129].
  { iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iDestruct "HK" as "[HK _]".
    iApply ("HK" $! _ ps' cs' a' i' g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
    split; [|split; [assumption | exact Hlose]].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  mn_enter "iw_1.L48".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 103) as [-> | H103].
  { destruct (Hgc eq_refl) as [Hborrow Hnz].
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply (loop_greeting b4 b6 _ ps' cs' a' i' g lose Φ with "[$Hb $Hs $Ht $Hl4 $Hp4] [IH HK]").
    - split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
    - assumption.
    - exact Hlose.
    - exact Hborrow.
    - exact Hnz.
    - iIntros (e'' ps'' cs'' a'' i'' g'' lose'' [Hf' [Hpr Hlose']]) "Hres".
      iApply ("IH" $! "iw_1.L35"%string e'' lose'' ps'' cs'' a'' i'' g'' with "[%] Hres HK").
      split; [right; right; split; [left; reflexivity|split; assumption]|exact Hf']. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  mn_enter "iw_1.L50".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 128) as [-> | H128].
  { iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iDestruct "HK" as "[_ [HK _]]".
    iApply ("HK" $! _ ps' cs' a' i' g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
    split; [|split; [assumption | exact Hlose]].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  mn_enter "iw_1.L52".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 116) as [-> | H116].
  { iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply (loop_traditional b4 b6 _ ps' cs' a' i' g lose Φ with "[$Hb $Hs $Ht $Hl4 $Hp4] [IH HK]").
    - split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
    - assumption.
    - exact Hlose.
    - iIntros (e'' ps'' cs'' a'' i'' g'' lose'' [Hf' [Hpr Hlose']]) "Hres".
      iApply ("IH" $! "iw_1.L42"%string e'' lose'' ps'' cs'' a'' i'' g'' with "[%] Hres HK").
      split; [right; right; split; [right; reflexivity|split; assumption]|exact Hf']. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  iApply ("IH" $! "iw_1.L52"%string _ 1 ps' cs' a' i' g with "[%] [$Hb $Hs $Ht $Hl4 $Hp4] HK").
  split; [right; left; split; reflexivity|].
  split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
Qed.

(** The option loop preserves its resources until it selects one of its three exits. *)
Lemma main_loop b4 b6 Φ :
  ⊢ ∀ from e lose ps cs a i g,
  ⌜loop_entry from e lose /\ loop_facts e b4 b6 ps cs i g⌝ -∗ loop_res b4 ps cs a i g -∗
  (loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ ∧ loop_exit b4 b6 "iw_1.L39"%string "iw_1.L50"%string Φ ∧
   loop_exit b4 b6 "iw_1.L10"%string "iw_1.L8"%string Φ) -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom from)))) : mexpr) {{ Φ }}.
Proof using Hargc Hargs Hav Hcells Hgetopt Hgetopt_apart Hgetopt_env Hgetopt_wi Hlinked Hoptarg_g
  Htable Kgetopt Kpstore SafepointStable0.
  clear - SafepointStable0 Hlinked Hav Hargc Hargs Hgetopt Hgetopt_wi Htable Hgetopt_env
    Hgetopt_apart Kgetopt Hoptarg_g Hcells Kpstore.
  unfold loop_res, loop_exit.
  iLöb as "IH". iIntros (from e lose ps cs a i g [Hent Hf]) "(Hb & Hs & Ht & Hl4 & Hp4) HK".
  destruct Hf as ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg).
  assert (Hlose : lose = 0 \/ lose = 1).
  { destruct Hent as [[_ ->] | [[_ ->] | [_ [_ Hl]]]]; auto. }
  destruct getopt_globals as (G69 & G64 & _). pose proof Hlinked as (_ & Hglob & _).
  pose proof Hargc as Hargc'.
  iApply (wp_enter _ _ _ _ _ _ _ _ (main_block "iw_1.L8") (put (TAtom "iw_1.pr.2") (WInt lose) e)).
  { abstract (vm_cast_no_check (eq_refl (Some (main_block "iw_1.L8")))). }
  { destruct Hent as [[-> ->] | [[-> ->] | [[-> | ->] [Hpr _]]]]; word_premise. }
  iNext. cbn [b_insts b_jump main_block hblk]. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hglob _ _ G69); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hglob _ _ G64); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_getopt with "Hb Hs Ht"); [word_premise | exact Ho | exact Hc | exact Hi |].
  iNext. iIntros (code ps' cs' a' i' (Ho' & Hc' & Hi' & Hint & Hgc & _)) "Hb Hs Ht".
  pose proof (fun k => int32_eq code k Hint) as Hceq.
  pose proof (Z.mod_pos_bound code (2 ^ 32) ltac:(lia)) as Hcr.
  set (c := code mod 2 ^ 32) in *. clearbody c. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 4294967295) as [-> | Hn1].
  { iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iDestruct "HK" as "[_ [_ HK]]".
    iApply ("HK" $! _ ps' cs' a' i' g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
    split; [|split; [assumption | exact Hlose]].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  iApply (loop_dispatch b4 b6 _ ps' cs' a' i' g lose c Φ with "[$Hb $Hs $Ht $Hl4 $Hp4] HK IH").
  - split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
  - assumption.
  - exact Hlose.
  - assumption.
  - exact Hcr.
  - intros Ec. apply Hgc. apply (proj1 (Hceq 103 ltac:(lia))). exact Ec.
Qed.

(** Initialization supplies the resources that the option loop carries to its exits. *)
Lemma main_to_loop s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix Φ :
  sargs = s0 :: srest -> argv_caps cs0 (map arg_ptr sargs) -> 0 <= ix <= Z.of_nat (length sargs) ->
  pts (block_ps av ar 0 (argv_bytes (map arg_ptr sargs)) cs0) -∗ pts (flat_map arg_ps sargs) -∗
  pts (getopt_ps a ix) -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗
  ▷ (∀ e b4 b6 (i k : nat) q (new : Z -> ptr * list Z) c',
       ⌜start_vars e (Z.of_nat (length sargs)) av b4 b6 /\
        lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
        fresh_ok b4 /\ fresh_ok b6 /\ (i <= length (arg_text s0))%nat /\ (k <= length (arg_text s0))%nat /\
        (q = mkPtr 0 CNone \/ q = (new 6).1)⌝ -∗
       HP.HN.literals r3 r4 -∗
       HP.HN.name_cells pn nreg sreg nb sb
         (mkPtr (ptr_addr (arg_ptr s0) + Z.of_nat i) (ptr_cap (arg_ptr s0)))
         (mkPtr (ptr_addr (arg_ptr s0) + Z.of_nat i) (ptr_cap (arg_ptr s0)))
         (mkPtr (ptr_addr (arg_ptr s0) + Z.of_nat k) (ptr_cap (arg_ptr s0))) -∗
       ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗ pts (codec_ps c') -∗
       string empty_ptr 69968 r80 [] -∗
       bytes b4 8 (replicate 8 0) -∗ auxes b4 1 (replicate 15 CNone) -∗
       live b6 (mkRegion b6 (b6 + 16) Heap Live) -∗ bytes b6 0 (replicate 8 0) -∗
       bytes b6 8 (replicate 8 0) -∗ auxes b6 0 (clear_slots 0 (replicate 8 CNone)) -∗
       auxes b6 8 (replicate 8 CNone) -∗
       (loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ ∧
        loop_exit b4 b6 "iw_1.L39"%string "iw_1.L50"%string Φ ∧
        loop_exit b4 b6 "iw_1.L10"%string "iw_1.L8"%string Φ)) -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length sargs)); WPtr (mkPtr av (Obj av))]) : mexpr) {{ Φ }}.
Proof using Hargc Hargs Hatexit Hatexit_abi Hatexit_pre Hatexit_ret Hav Hcells Hgetopt Hgetopt_apart
  Hgetopt_env Hgetopt_wi Hlent Hlinked Hmemcmp Hmemset Hnb Hnb_cell Hoptarg_g Hpn_end Hsb Hsb_cell
  Hset_pre Hsetlocale Hstrncmp Hstrrchr Htable Kalloc Katexit Kgetopt Kmemset Knb Kpn Kpstore Ksb Kset
  SafepointStable0.
  intros Hhd Hcs Hix. iIntros "Hb Hs Ht Hlit Hcells Hks Hcod Hs80 HK".
  iApply (main_to_L8 with "Hb Hs Ht Hlit Hcells Hks Hcod Hs80"); [exact Hhd | exact Hcs | exact Hix |].
  iNext. iIntros (e b4 b6 i k q new c' Hst Hf) "Hres Hlit Hcells Hlent Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'".
  iApply (main_loop b4 b6 Φ $! "start"%string e 0 (map arg_ptr sargs) cs0 a ix greeting_ptr
            with "[%] Hres [-]").
  - split; [left; split; reflexivity | exact Hf].
  - iApply ("HK" $! e b4 b6 i k q new c' with "[%] Hlit Hcells Hlent Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'").
    exact Hst.
Qed.

End main.
End HelloMainOptions.
