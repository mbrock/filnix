(** GNU Hello rejects extra operands after parsing its options. These
    proofs load the remaining argument pointer and select either the
    greeting, an extra-operand diagnostic, or a hint to try --help. *)

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

Module HelloMainOperands (R : Runtime) (B : HelloMainInterface.HelloMainBase R).
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
(** ## The operand check

    Main checks for remaining operands after parsing the options.
    The parser position stays within the vector, so main can safely
    load the next argument or the null sentinel. *)

(** libc's optind cell is the global optind. *)
Context (Hoptind_g : lookup (TAtom "optind") (ge_globals ge) = Some optind_cell).

(** A pointer cell is its bytes and its first aux slot. *)
Lemma pcell_split b o q : pcell b o q ⊣⊢ bytes b o (slot_bytes (ptr_addr q)) ∗ auxes b o [ptr_cap q].
Proof.
  rewrite /pcell /bytes /auxes slot_cell.
  change ((PAux b o, VAux (ptr_cap q)) :: cell b o (ptr_addr q)) with
    ([(PAux b o, VAux (ptr_cap q))] ++ cell b o (ptr_addr q)).
  rewrite pts_app. change (aux_ps b o [ptr_cap q]) with [(PAux b o, VAux (ptr_cap q))].
  iSplit; iIntros "[A B]"; iFrame.
Qed.

(** Splitting the argument vector exposes one pointer cell and preserves
    the slots on either side of it. *)
Lemma argv_block_slot b reg ps cs k q :
  argv_caps cs ps -> (ps ++ [null]) !! k = Some q ->
  pts (block_ps b reg 0 (argv_bytes ps) cs) ⊣⊢
  live b reg ∗ bytes b 0 (slots_bytes (take k (ps ++ [null]))) ∗ auxes b 0 (take (8 * k) cs) ∗
  pcell b (8 * Z.of_nat k) q ∗
  bytes b (8 * Z.of_nat k + 8) (slots_bytes (drop (S k) (ps ++ [null]))) ∗
  auxes b (8 * Z.of_nat k + 1) (drop (S (8 * k)) cs).
Proof.
  intros [Lc Hc] Hq. pose proof (lookup_lt_Some _ _ _ Hq) as Hk. pose proof (Hc k q Hq) as Hcq.
  assert (Ex : argv_bytes ps = slots_bytes (take k (ps ++ [null])) ++ slot_bytes (ptr_addr q) ++
                               slots_bytes (drop (S k) (ps ++ [null]))).
  { unfold argv_bytes. transitivity (slots_bytes (take k (ps ++ [null]) ++ q :: drop (S k) (ps ++ [null]))).
    - rewrite (take_drop_middle _ _ _ Hq). reflexivity.
    - unfold slots_bytes. rewrite flat_map_app. reflexivity. }
  assert (Ec : take (8 * k) cs ++ ptr_cap q :: drop (S (8 * k)) cs = cs) by exact (take_drop_middle _ _ _ Hcq).
  assert (Lt : length (slots_bytes (take k (ps ++ [null]))) = (8 * k)%nat).
  { rewrite length_slots_bytes length_take. lia. }
  assert (Lt' : length (take (8 * k) cs) = (8 * k)%nat).
  { rewrite length_take Lc. lia. }
  assert (A : auxes b 0 cs ⊣⊢ auxes b 0 (take (8 * k) cs) ∗ auxes b (8 * Z.of_nat k) [ptr_cap q] ∗
                              auxes b (8 * Z.of_nat k + 1) (drop (S (8 * k)) cs)).
  { transitivity (auxes b 0 (take (8 * k) cs ++ ptr_cap q :: drop (S (8 * k)) cs)); [rewrite Ec; reflexivity|].
    rewrite auxes_app Lt'.
    change (ptr_cap q :: drop (S (8 * k)) cs) with ([ptr_cap q] ++ drop (S (8 * k)) cs).
    rewrite auxes_app. cbn [length]. replace (0 + Z.of_nat (8 * k)) with (8 * Z.of_nat k) by lia.
    change (Z.of_nat 1) with 1. reflexivity. }
  rewrite block_pts Ex !bytes_app Lt. change (length (slot_bytes (ptr_addr q))) with 8%nat.
  replace (0 + Z.of_nat (8 * k)) with (8 * Z.of_nat k) by lia. change (Z.of_nat 8) with 8.
  rewrite A pcell_split.
  iSplit; [iIntros "(Hl & (Hy0 & Hy1 & Hy2) & (Hx0 & Hx1 & Hx2))" |
           iIntros "(Hl & Hy0 & Hx0 & (Hy1 & Hx1) & Hy2 & Hx2)"]; iFrame.
Qed.

(** Each exit receives the loop's memory and facts about the error flag
    and parser position. The continuation supplies the condition for that exit. *)
Definition operand_exit (b4 b6 : Z) (lab from : String.string) (P : Z -> Z -> Prop)
    (Φ : language.val (nanofil_lang registry ge) → iProp Σ) : iProp Σ :=
  ∀ e ps cs a i g lose,
    ⌜loop_facts e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ P lose i⌝ -∗
    loop_res b4 ps cs a i g -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom lab) (Some (TAtom from)))) : mexpr) {{ Φ }}.

(** Main loads the next argument pointer and tests whether it is null.
    A remaining argument selects the extra-operand diagnostic; the
    sentinel selects the help hint after an option error. *)
Lemma operand_L55 b4 b6 e ps cs a i g lose Φ :
  ⌜loop_facts e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\
   (lose = 0 \/ lose = 1) /\ (lose = 0 -> i < Z.of_nat (length sargs))⌝ -∗
  loop_res b4 ps cs a i g -∗
  (operand_exit b4 b6 "iw_1.L79"%string "iw_1.L55"%string (fun _ i => i < Z.of_nat (length sargs)) Φ ∧
   operand_exit b4 b6 "iw_1.L113"%string "iw_1.L55"%string
     (fun lose i => lose = 1 /\ i = Z.of_nat (length sargs)) Φ) -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L55") (Some (TAtom "iw_1.L60")))) : mexpr) {{ Φ }}.
Proof using Type SafepointStable0 Hav Hargc Hargs Hcells Hgetopt_wi Hoptind_g nb sb.
  clear - SafepointStable0 Hav Hargc Hargs Hcells Hgetopt_wi Hoptind_g nb sb.
  unfold loop_res, operand_exit. iIntros ((Hf & Hpr & Hlose & Hlt)) "(Hb & Hs & Ht & Hl4 & Hp4) HK".
  pose proof Hf as ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg).
  pose proof Hav as (Hav0 & Hav8 & Haend & Har48). pose proof Hargc as Hargc'.
  pose proof (order_length ps Ho) as Lp.
  destruct (lookup_lt_is_Some_2 (ps ++ [null]) (Z.to_nat i)) as [q Hq].
  { rewrite length_app Lp. cbn [length]. lia. }
  pose proof (slot_kinds sargs ps (Z.to_nat i) q Ho Hq) as Hkind.
  assert (Hqf : 0 <= ptr_addr q < 2 ^ 64 /\ (forall xb, ptr_cap q = Obj xb \/ ptr_cap q = Ro xb ->
                  exists xr, (PLive xb, VLive xr) ∈ flat_map arg_ps sargs)).
  { destruct Hkind as [[_ ->] | [_ (s & Hs & ->)]].
    - split; [cbn; lia|]. intros xb [E|E]; discriminate E.
    - pose proof (proj1 (List.Forall_forall _ _) Hargs s Hs) as (Hcap & Hb0 & Hbp & Hend & H48 & _).
      split; [lia|]. intros xb Hxb. exists (arg_region s).
      assert (xb = arg_base s) as ->.
      { destruct Hcap as [E1|E1]; rewrite E1 in Hxb; destruct Hxb as [E2|E2]; congruence. }
      apply list_elem_of_In, in_flat_map. exists s. split; [exact Hs|]. unfold arg_ps, string_ps. left. reflexivity. }
  destruct Hqf as [Hqr Hlife].
  mn_enter "iw_1.L55".
  (* optind, sign-extended, times 8, past argv. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hoptind_g; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (GL.wp_optind_check registry wi ge libc_getopt_view optarg_cell optind_cell Hcells Hgetopt_wi);
    [reflexivity | word_premise |].
  iNext. gen_env.
  iApply (GL.wp_optind_load registry wi ge libc_getopt_view optarg_cell optind_cell Hcells Hgetopt_wi
            with "Ht"); [reflexivity | word_premise |].
  iNext. iIntros "Ht". gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply wp_flight; [word_premise | word_premise | word_premise |]. iNext. gen_env.
  (* argv[optind]. *)
  iEval (rewrite (argv_block_slot av ar ps cs (Z.to_nat i) q Hc Hq)) in "Hb".
  iDestruct "Hb" as "(Hal & Hy0 & Hx0 & Hq & Hy1 & Hx1)".
  iApply (wp_check_read with "Hal");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise | addr_premise |].
  iNext. iIntros "Hal". gen_env.
  iApply (wp_raw_load_pointer_in with "Hal Hq Hs");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise | exact Hqr | exact Hlife |].
  iNext. iIntros "Hal Hq Hs". gen_env.
  iAssert (pts (block_ps av ar 0 (argv_bytes ps) cs)) with "[Hal Hy0 Hx0 Hq Hy1 Hx1]" as "Hb".
  { rewrite (argv_block_slot av ar ps cs (Z.to_nat i) q Hc Hq). iFrame. }
  destruct Hkind as [[Ek ->] | [Ek (s & Hs & ->)]].
  - (* Null: optind is argc, which only pr.2 set lets through. *)
    assert (Ei : i = Z.of_nat (length sargs)) by lia.
    assert (Hl1 : lose = 1).
    { destruct Hlose as [El | El]; [|exact El]. specialize (Hlt El). lia. }
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iDestruct "HK" as "[_ HK]".
    iApply ("HK" $! _ ps cs a i g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
    split; [|split; [assumption | split; [exact Hl1 | exact Ei]]].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
  - (* An argument: an extra operand. *)
    pose proof (proj1 (List.Forall_forall _ _) Hargs s Hs) as (_ & Hb0 & Hbp & _).
    assert (Ei : i < Z.of_nat (length sargs)) by lia.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iDestruct "HK" as "[HK _]".
    iApply ("HK" $! _ ps cs a i g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
    split; [|split; [assumption | exact Ei]].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
Qed.

(** Main checks whether option parsing left an operand or reported an error.
    The result selects the greeting, extra-operand diagnostic, or help hint. *)
Lemma main_operands b4 b6 e ps cs a i g lose Φ :
  ⌜loop_facts e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ (lose = 0 \/ lose = 1)⌝ -∗
  loop_res b4 ps cs a i g -∗
  (operand_exit b4 b6 "iw_1.L79"%string "iw_1.L55"%string (fun _ i => i < Z.of_nat (length sargs)) Φ ∧
   operand_exit b4 b6 "iw_1.L113"%string "iw_1.L55"%string
     (fun lose i => lose = 1 /\ i = Z.of_nat (length sargs)) Φ ∧
   operand_exit b4 b6 "iw_1.join"%string "iw_1.L60"%string
     (fun lose i => lose = 0 /\ i = Z.of_nat (length sargs)) Φ) -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L10") (Some (TAtom "iw_1.L8")))) : mexpr) {{ Φ }}.
Proof.
  clear - SafepointStable0 Hav Hargc Hargs Hcells Hgetopt_wi Hoptind_g nb sb.
  iIntros ((Hf & Hpr & Hlose)) "Hr HK".
  pose proof Hf as ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg).
  pose proof Hargc as Hargc'.
  mn_enter "iw_1.L10".
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ lose); [word_premise|]. iNext.
  destruct Hlose as [El | El]; subst lose; cbn [Z.eqb edge_label].
  - mn_enter "iw_1.L59". unfold loop_res. iDestruct "Hr" as "(Hb & Hs & Ht & Hl4 & Hp4)".
    iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hoptind_g; reflexivity | intros ?m; word_premise |].
    iNext. gen_env.
    iApply (GL.wp_optind_check registry wi ge libc_getopt_view optarg_cell optind_cell Hcells Hgetopt_wi);
      [reflexivity | word_premise |].
    iNext. gen_env.
    iApply (GL.wp_optind_load registry wi ge libc_getopt_view optarg_cell optind_cell Hcells Hgetopt_wi
              with "Ht"); [reflexivity | word_premise |].
    iNext. iIntros "Ht". gen_env.
    destruct (Z.lt_ge_cases i (Z.of_nat (length sargs))) as [Hlt | Hge].
    + iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
      iApply wp_goto. iNext. cbn [edge_label]. mn_enter "iw_1.L60". gen_env.
      iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      iApply (operand_L55 b4 b6 _ ps cs a i g 0 with "[%] [$Hb $Hs $Ht $Hl4 $Hp4] [HK]").
      * split; [|split; [assumption | split; [left; reflexivity | intros _; exact Hlt]]].
        split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
      * iSplit; [iDestruct "HK" as "[H _]" | iDestruct "HK" as "[_ [H _]]"]; iExact "H".
    + iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
      iApply wp_goto. iNext. cbn [edge_label]. mn_enter "iw_1.L60". gen_env.
      iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      iDestruct "HK" as "[_ [_ HK]]".
      iApply ("HK" $! _ ps cs a i g 0 with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
      split; [|split; [assumption | split; [reflexivity | lia]]].
      split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
  - mn_enter "iw_1.L60". gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply (operand_L55 b4 b6 _ ps cs a i g 1 with "[%] Hr [HK]").
    + split; [|split; [assumption | split; [right; reflexivity | intros E; discriminate E]]].
      split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
    + iSplit; [iDestruct "HK" as "[H _]" | iDestruct "HK" as "[_ [H _]]"]; iExact "H".
Qed.

(** The operand check supplies the loop's end-of-options exit. *)
Lemma operands_exit b4 b6 Φ :
  (operand_exit b4 b6 "iw_1.L79"%string "iw_1.L55"%string (fun _ i => i < Z.of_nat (length sargs)) Φ ∧
   operand_exit b4 b6 "iw_1.L113"%string "iw_1.L55"%string
     (fun lose i => lose = 1 /\ i = Z.of_nat (length sargs)) Φ ∧
   operand_exit b4 b6 "iw_1.join"%string "iw_1.L60"%string
     (fun lose i => lose = 0 /\ i = Z.of_nat (length sargs)) Φ) -∗
  loop_exit b4 b6 "iw_1.L10"%string "iw_1.L8"%string Φ.
Proof.
  iIntros "HK". rewrite /loop_exit. iIntros (e ps cs a i g lose Hf) "Hr".
  iApply (main_operands with "[%] Hr HK"). exact Hf.
Qed.

End main.
End HelloMainOperands.
