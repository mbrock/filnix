(** The version and help paths borrow strings for their output calls.
    These proofs preserve those strings and handle the locale-dependent
    translation instructions and the final exit status. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics StepRules Symbolic
  ExternalCalls ExternalMachine LibcCalls Pieces Heap ContractFrame Logic HelloLeaf HelloVersion HelloModule HelloConvDefs
  MemLogic StringLogic Getopt GetoptLogic Libc VariadicLogic HelloMainBase HelloMainFacts HelloMainInterface
  HelloName LentLogic Locale LocaleLogic Startup.
Open Scope Z_scope.
Open Scope list_scope.
Import HelloMainBase.MainDefinitions MainFacts.

Module HelloMainHelpOutput (R : Runtime) (B : HelloMainInterface.HelloMainBase R).
Import B B.LG0 B.LG0.L.
Import B.HLo.HL B.HLo.HL.ML.CSL.
Local Hint Opaque main_fn pts live pcell main_irisGS : typeclass_instances.
Section main.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Let section_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := main_irisGS registry wi ge.
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
Local Notation main_to_L8 := (main_to_L8 registry wi ge Hlinked Kalloc Hmemset Kmemset
  Hstrrchr Hmemcmp Hstrncmp pn nreg sreg nb sb Hnb Hsb Hpn_end Hnb_cell Hsb_cell
  Kpn Knb Ksb rep requests Hsetlocale Hlent Hset_pre Kset Kpstore
  atexit_spec Hatexit Hatexit_ret Hatexit_abi Hatexit_pre Katexit av ar sargs Hav Hargc Hargs).
Local Notation argv_len := (8 * (length sargs + 1))%nat.
Context (initialized running : mem -> libc_world -> Prop)
  (grequests : list word -> mem -> libc_world -> Z -> Z -> Prop)
  (transition : list word -> mem -> libc_world -> list Z -> list event -> list word -> mem -> libc_world -> Prop)
  (Hgetopt : registry (TAtom "getopt_long") =
     Some (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition)).
Local Notation getopt_spec :=
  (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition).
Context (optarg_cell optind_cell : ptr)
  (Hgetopt_wi : forall m w h, wi m w h ->
     getopt_state_at m (libc_getopt_view w) /\ getopt_optarg_cell (libc_getopt_view w) = optarg_cell /\
     getopt_optind_cell (libc_getopt_view w) = optind_cell /\ getopt_current (libc_getopt_view w) h).
Context (Htable : forall m w h, wi m w h -> hello_table_at m).
Context (Hgetopt_env : forall m w h xs cs, wi m w h -> agrees m h -> live_disjoint m ->
   (forall l v, (l, v) ∈ block_ps av ar 0 xs cs ++ flat_map arg_ps sargs -> h !! l = Some v) ->
   getopt_input_at m (hello_input av sargs) ->
   libc_getopt_rep initialized m w /\
   Forall (writable_span m) (getopt_roots (libc_getopt_view w)) /\
   Forall (fun s => readable_bytes m (span_ptr s) (span_size s)) (getopt_reads (libc_getopt_view w)) /\
   getopt_separated (hello_input av sargs) (libc_getopt_view w) /\
   getopt_disjoint (getopt_public_writes (hello_input av sargs) (libc_getopt_view w)) /\
   getopt_private_owned m (hello_input av sargs) (libc_getopt_view w)).
Context (Hgetopt_apart : forall m w h, wi m w h ->
   (forall s a, In s (getopt_roots (libc_getopt_view w) ++ getopt_cells (libc_getopt_view w)) ->
      span_contains s a -> ~ owned_live h m a) /\
   ids_apart (getopt_owned (libc_getopt_view w)) h).
Context (Kgetopt : forall r args xs s m w h trace values s' m' w' bs cs,
   M.E.invoke getopt_spec r args xs s m w trace (CallReturn values) s' m' w' ->
   (forall l v, (l, v) ∈ block_ps av ar 0 bs cs -> h !! l = Some v) -> wi m w h ->
   agrees m h -> live_disjoint m -> R.ready s m ->
   wi m' w' (overwrite (block_ps av ar 0 (mem_bytes m' av argv_len) (mem_auxes m' av argv_len) ++
     getopt_ps (getopt_optarg (libc_getopt_view w')) (getopt_optind (libc_getopt_view w'))) h)).
Context (Hcells : 0 <= ptr_addr optarg_cell < 2 ^ 64 /\ 0 <= ptr_addr optind_cell < 2 ^ 64).
Local Notation getopt_step := (getopt_step wi transition).
Local Notation loop_res := (loop_res av ar sargs).
Local Notation loop_facts := (loop_facts av sargs).
Local Notation loop_exit := (loop_exit registry wi ge av ar sargs).
Local Notation wp_main_getopt := (wp_main_getopt registry wi ge Hlinked
  av ar sargs Hav Hargc Hargs initialized running grequests transition Hgetopt
  optarg_cell optind_cell Hgetopt_wi Htable Hgetopt_env Hgetopt_apart Kgetopt).
Context (exit_spec : contract libc_world)
  (Hexit : registry (TAtom "exit") = Some exit_spec)
  (Hexit_abi : forall v, contract_abi exit_spec CVoid [Arg W v])
  (Hexit_pre : forall n m w h, 0 <= n < 2 ^ 32 -> wi m w h -> contract_pre exit_spec [WInt n] m w)
  (Hexit_post : forall args n s m w tr vs s' m' w',
    M.E.invoke exit_spec CVoid args [WInt n] s m w tr (CallReturn vs) s' m' w' -> False).
Local Notation wp_main_exit := (wp_main_exit registry wi ge Hlinked exit_spec Hexit Hexit_abi Hexit_pre Hexit_post).
Context (stdout_cell stream : ptr)
  (Hstdout_g : lookup (TAtom "stdout") (ge_globals ge) = Some stdout_cell)
  (wi_stdout : forall m w h, wi m w h ->
    access_res m (raw_address (ptr_addr stdout_cell) 0) (ptr_cap stdout_cell) 8 Read 8 = Some ok /\
    pointer_load_effects m (raw_address (ptr_addr stdout_cell) 0)
      [AuxRead; LowerResolve; AddressRead] = Some stream).
Context (version_ps : list (piece * pval)) (author_reg : String.string -> region)
  (Hauthor_live : forall s, In s ["hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75"] ->
    (PLive (ptr_addr (version_literal s)), VLive (author_reg s)) ∈ version_ps)
  (version_spec : name -> contract libc_world)
  (Hversion_reg : forall g xs, In (g, xs) (version_output_args stream) -> registry g = Some (version_spec g))
  (Hversion_ret : forall g xs, In (g, xs) (version_output_args stream) ->
    contract_returns (version_spec g) = RClass W)
  (Hversion_abi : forall g xs d args, In (g, xs) (version_output_args stream) ->
    map (fun a => match a with Arg k _ => k end) args = version_output_classes xs ->
    contract_abi (version_spec g) (CResult d W) args)
  (Hversion_pre : forall g xs m w h, In (g, xs) (version_output_args stream) ->
    (forall l v, (l, v) ∈ version_ps -> h !! l = Some v) ->
    agrees m h -> wi m w h -> contract_pre (version_spec g) xs m w)
  (Hversion_frame : forall g xs r args s m w h trace values s' m' w',
    In (g, xs) (version_output_args stream) ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    M.E.invoke (version_spec g) r args xs s m w trace (CallReturn values) s' m' w' ->
    agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
      exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32)
  (Kversion_alloc : forall size m wd h base,
    In size [24; 80] -> fresh m (heap_req 8 size) base -> wi m wd h ->
    wi (allocated m (heap_req 8 size) base) wd (overwrite (obj_ps base (heap_req 8 size)) h))
  (Kversion_store : forall b reg o x xp m wd h,
    (forall k v, (k, v) ∈ [(PLive b, VLive reg)] ++
      (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) -> h !! k = Some v) ->
    wi m wd h ->
    wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
      (overwrite ([(PLive b, VLive reg)] ++
        (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h))
  (Kversion_cursor : forall cb cr sb off m wd h,
    (forall k v, (k, v) ∈ va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb)) -> h !! k = Some v) ->
    wi m wd h -> wi (store_bytes m cb 8 (sb + off + 8)) wd
      (overwrite (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) h))
  (Kversion_snapshot : forall m wd h sb,
    fresh m (heap_req 16 72) sb -> wi m wd h ->
    wi (snapshot_values (HV.version_main_args stream) sb (allocated m (heap_req 16 72) sb)) wd
      (overwrite (snapshot_ps (HV.version_main_args stream) sb (heap_req 16 72)) h)).
Local Notation main_version_lookup := (MainFacts.main_version_lookup ge Hlinked).

Lemma wp_main_proper_name e ls lab d v rest j p Φ :
  arg_x ge e (Arg P v) = Some (WPtr p) ->
  ▷ WP (ERun (mkFrame main_fn (put d (WPtr p) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }} -∗
  WP (ERun (mkFrame main_fn e ls None (Exec lab
    (Call (CResult d P) (Global (TAtom "proper_name")) [Arg P v] :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hv. iIntros "HK".
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ proper_name_fn (invocation proper_name_fn [WPtr p])).
  1: cbn [map_option]; rewrite Hv; reflexivity.
  1: unfold find_fn; rewrite (proj1 Hlinked); vm_compute; reflexivity.
  1: reflexivity.
  iNext. iApply (HV.proper_name_spec registry wi ge).
  iNext. iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. iExact "HK".
Qed.

Lemma main_version b4 b6 Φ :
  pts version_ps -∗ loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ.
Proof using Type SafepointStable0 section_irisGS Hlinked Hnb_cell Hsb_cell Hav Hargc Hcells
  Hexit Hexit_abi Hexit_pre Hexit_post Hstdout_g wi_stdout Hauthor_live
  Hversion_reg Hversion_ret Hversion_abi Hversion_pre Hversion_frame
  Kversion_alloc Kversion_store Kversion_cursor Kversion_snapshot.
  pose proof (main_version_lookup "hello#str.70" ltac:(simpl; tauto)) as H70.
  pose proof (main_version_lookup "hello#str.63" ltac:(simpl; tauto)) as H63.
  pose proof (main_version_lookup "hello#str.71" ltac:(simpl; tauto)) as H71.
  pose proof (main_version_lookup "hello#str.72" ltac:(simpl; tauto)) as H72.
  pose proof (main_version_lookup "hello#str.73" ltac:(simpl; tauto)) as H73.
  pose proof (main_version_lookup "hello#str.74" ltac:(simpl; tauto)) as H74.
  pose proof (main_version_lookup "hello#str.75" ltac:(simpl; tauto)) as H75.
  iIntros "Hps". rewrite /loop_exit. iIntros (e ps cs a i g lose _) "_".
  mn_enter "iw_1.L21".
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hstdout_g; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_check. exact (proj1 (wi_stdout _ _ _ Hw)). }
  iNext. iIntros "_". gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_raw_load_pointer; apply (wi_stdout _ _ _ Hw). }
  iNext. iIntros "_". gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H70; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H63; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H71; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H72; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_main_proper_name; [word_premise|]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H73; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_main_proper_name; [word_premise|]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H74; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_main_proper_name; [word_premise|]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H75; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_main_proper_name; [word_premise|]. iNext. gen_env.
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ HV.version_etc_fn
            (invocation HV.version_etc_fn (HV.version_main_args stream)));
    [word_premise | unfold find_fn; rewrite (proj1 Hlinked); vm_compute; reflexivity | reflexivity |].
  iNext.
  iApply (HV.version_etc_spec registry wi ge Hlinked stream version_ps author_reg Hauthor_live
            version_spec Hversion_reg Hversion_ret Hversion_abi Hversion_pre Hversion_frame
            Kversion_alloc Kversion_store Kversion_cursor Kversion_snapshot with "Hps").
  iNext. iIntros "_". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. gen_env.
  iApply (wp_main_exit _ _ _ _ _ _ _ 0); [reflexivity | lia].
Qed.

(** The first option selects version output when its contract permits only code 129.
    The loop preserves its resources until it reaches the version block. *)
Lemma loop_version b4 b6 from e lose ps cs a i g Φ :
  loop_entry from e lose -> loop_facts e b4 b6 ps cs i g ->
  (forall c, 0 <= c < 2 ^ 32 -> getopt_step a i [WInt c] -> c = 129) ->
  loop_res b4 ps cs a i g -∗ loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom from)))) : mexpr) {{ Φ }}.
Proof.
  intros Hent Hf Hlaw. unfold loop_res, loop_exit.
  iIntros "(Hb & Hs & Ht & Hl4 & Hp4) HK".
  destruct Hf as ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg).
  assert (Hlose : lose = 0 \/ lose = 1).
  { destruct Hent as [[_ ->] | [[_ ->] | [_ [_ Hl]]]]; auto. }
  destruct getopt_globals as (G69 & G64 & _). pose proof Hlinked as (Hm & Hglob & _).
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
  iNext. iIntros (code ps' cs' a' i' (Ho' & Hc' & Hi' & Hint & _ & Hstep)) "Hb Hs Ht".
  pose proof (Z.mod_pos_bound code (2 ^ 32) ltac:(lia)) as Hcr.
  pose proof (Hlaw _ Hcr Hstep) as E129. rewrite E129. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  mn_enter "iw_1.L19".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  iApply ("HK" $! _ ps' cs' a' i' g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
  split; [|split; [assumption | exact Hlose]].
  split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
Qed.

(** Initialization supplies the loop resources and the first option selects version output.
    Main then prints the version information and calls exit. *)
Lemma main_to_version s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix Φ :
  sargs = s0 :: srest -> argv_caps cs0 (map arg_ptr sargs) -> 0 <= ix <= Z.of_nat (length sargs) ->
  (forall c, 0 <= c < 2 ^ 32 -> getopt_step a ix [WInt c] -> c = 129) ->
  pts (block_ps av ar 0 (argv_bytes (map arg_ptr sargs)) cs0) -∗ pts (flat_map arg_ps sargs) -∗
  pts (getopt_ps a ix) -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗ pts version_ps -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length sargs)); WPtr (mkPtr av (Obj av))]) : mexpr) {{ Φ }}.
Proof.
  intros Hhd Hcs Hix Hlaw. iIntros "Hb Hs Ht Hlit Hcells Hks Hcod Hs80 Hv".
  iApply (main_to_L8 with "Hb Hs Ht Hlit Hcells Hks Hcod Hs80"); [exact Hhd | exact Hcs | exact Hix |].
  iNext. iIntros (e b4 b6 i k q new c' _ Hf) "Hres _ _ _ _ _ _ _ _ _ _ _ _".
  iApply (loop_version b4 b6 "start"%string e 0 with "Hres [Hv]").
  - left. split; reflexivity.
  - exact Hf.
  - exact Hlaw.
  - iApply (main_version with "Hv").
Qed.

(** Querying the messages locale returns its borrowed name without
    changing memory or libc's state. *)
Context (Hquery_pre : forall m w h p t, wi m w h -> h !! PName 5 = Some (VName p t) ->
    contract_pre (libc_setlocale_contract rep requests) [WInt 5; WPtr null] m w)
  (Hquery : forall r args s m w h p t trace ending s' m' w',
    wi m w h -> h !! PName 5 = Some (VName p t) ->
    M.E.invoke (libc_setlocale_contract rep requests) r args [WInt 5; WPtr null] s m w trace ending s' m' w' ->
    s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr p]).

(** The stderr cell remains readable and contains the expected stream pointer. *)
Context (stderr_cell errstream : ptr)
  (Hstderr_g : lookup (TAtom "stderr") (ge_globals ge) = Some stderr_cell)
  (wi_stderr : forall m w h, wi m w h ->
    access_res m (raw_address (ptr_addr stderr_cell) 0) (ptr_cap stderr_cell) 8 Read 8 = Some ok /\
    pointer_load_effects m (raw_address (ptr_addr stderr_cell) 0)
      [AuxRead; LowerResolve; AddressRead] = Some errstream).

(** Output calls borrow their format strings and any argument strings
    they print. They return a C integer and preserve the caller's
    memory even when writing to the stream fails. *)
Context (help_ps : list (piece * pval)) (output_spec : name -> contract libc_world)
  (Hhelp_reg : forall pname g xs, In (g, xs) (main_output_args stream errstream pname) ->
    registry g = Some (output_spec g))
  (Hhelp_ret : forall pname g xs, In (g, xs) (main_output_args stream errstream pname) ->
    contract_returns (output_spec g) = RClass W)
  (Hhelp_abi : forall pname g xs d args, In (g, xs) (main_output_args stream errstream pname) ->
    map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
    contract_abi (output_spec g) (CResult d W) args)
  (Hhelp_pre : forall pname g xs m w h, name_ok sargs pname -> In (g, xs) (main_output_args stream errstream pname) ->
    (forall l v, (l, v) ∈ help_ps ++ flat_map arg_ps sargs -> h !! l = Some v) ->
    agrees m h -> wi m w h -> contract_pre (output_spec g) xs m w)
  (Hhelp_frame : forall pname g xs r args s m w h trace values s' m' w',
    In (g, xs) (main_output_args stream errstream pname) ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    M.E.invoke (output_spec g) r args xs s m w trace (CallReturn values) s' m' w' ->
    agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
      exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32)
  (Houtput_reg : forall g xs, In (g, xs) (emit_output_args stream) -> registry g = Some (output_spec g))
  (Houtput_ret : forall g xs, In (g, xs) (emit_output_args stream) ->
    contract_returns (output_spec g) = RClass W)
  (Houtput_abi : forall g xs d args, In (g, xs) (emit_output_args stream) ->
    map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
    contract_abi (output_spec g) (CResult d W) args)
  (Houtput_pre : forall g xs m w h, In (g, xs) (emit_output_args stream) ->
    (forall l v, (l, v) ∈ help_ps -> h !! l = Some v) ->
    agrees m h -> wi m w h -> contract_pre (output_spec g) xs m w)
  (Houtput_frame : forall g xs r args s m w h trace values s' m' w',
    In (g, xs) (emit_output_args stream) ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    M.E.invoke (output_spec g) r args xs s m w trace (CallReturn values) s' m' w' ->
    agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
      exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32).

(** The help block's literals and program_name's cell are linked where
    main reads them. *)
Lemma main_help_lookup s :
  In s ["hello#str.54"; "hello#str.55"; "hello#str.56"; "hello#str.57"; "hello#str.58";
        "hello#str.59"; "hello#str.60"; "hello#str.61"; "hello#str.62"; "hello#str.63";
        "hello#str.79"] ->
  lookup (TAtom s) (ge_globals ge) = Some (version_literal s).
Proof.
  intros Hin. apply (proj1 (proj2 Hlinked)).
  repeat destruct Hin as [<- | Hin]; try contradiction; vm_compute; reflexivity.
Qed.

(** Each output call returns an integer and preserves the literal
    strings and argument strings it borrows. *)
Lemma wp_main_output f e ls lab d g args rest j pname xs Φ :
  name_ok sargs pname -> In (g, xs) (main_output_args stream errstream pname) ->
  map_option (arg_x ge e) args = Some xs ->
  map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
  pts help_ps -∗ pts (flat_map arg_ps sargs) -∗
  ▷ (∀ n, pts help_ps -∗ pts (flat_map arg_ps sargs) -∗
     WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d W) (Global g) args :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hname Hin Hargs' Hclasses. iIntros "Hps Has HK".
  assert (Hg : g = TAtom "fputs" \/ g = TAtom "fprintf").
  { unfold main_output_args in Hin. repeat destruct Hin as [H | Hin];
      try contradiction; inversion H; auto. }
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (output_spec g) xs
            (pts help_ps ∗ pts (flat_map arg_ps sargs)) with "[$Hps $Has] [HK]").
  - destruct Hg as [-> | ->]; apply linked_outside; first [exact Hlinked | reflexivity].
  - destruct Hg as [-> | ->]; apply linked_unbound; first [exact Hlinked | reflexivity].
  - destruct Hg as [-> | ->]; reflexivity.
  - exact (Hhelp_reg _ _ _ Hin).
  - exact Hargs'.
  - exact (Hhelp_abi _ _ _ _ _ Hin Hclasses).
  - iIntros (σ) "(%h & Hh & %Hf) [Hps Has]". destruct Hf as (Ha & _ & _ & Hw).
    iDestruct (pts_lookup with "Hh Hps") as %Hps. iDestruct (pts_lookup with "Hh Has") as %Has.
    iPureIntro. apply (Hhelp_pre _ _ _ _ _ h Hname Hin); [|exact Ha|exact Hw].
    intros l v Hl. apply elem_of_app in Hl as [Hl|Hl]; [exact (Hps _ _ Hl) | exact (Has _ _ Hl)].
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) [Hps Has]".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (Hhelp_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hin Ha Hd Hr Hw Hinv)
      as (Ha' & Hd' & Hr' & Hw' & n & -> & Hn).
    iModIntro. iExists (put d (WInt n) e). iSplit.
    + iPureIntro. unfold external_env. cbn [site_result]. rewrite (Hhelp_ret _ _ _ Hin).
      cbn. rewrite Z.mod_small; [reflexivity | exact Hn].
    + iSplitL "Hh"; [iExists h; iFrame; iPureIntro; auto |]. iApply ("HK" with "Hps Has").
Qed.

(** The program's name is a pointer whose capability's life, if any,
    is among the arguments' pieces: [wp_raw_load_pointer_in] can load
    it out of its cell. *)
Lemma name_life x0 : name_ok sargs x0 ->
  0 <= ptr_addr x0 < 2 ^ 64 /\
  (forall xb, ptr_cap x0 = Obj xb \/ ptr_cap x0 = Ro xb ->
     exists xr, (PLive xb, VLive xr) ∈ flat_map arg_ps sargs).
Proof.
  intros (s0 & srest & i & Hs0 & Hi & Ex0).
  assert (Hin0 : In s0 sargs) by (rewrite Hs0; left; reflexivity).
  pose proof (proj1 (List.Forall_forall _ _) Hargs s0 Hin0) as (Hcap & Hb0 & Hbp & Hend & H48 & _).
  split; [rewrite Ex0; cbn [ptr_addr]; lia|].
  intros xb Hxb. exists (arg_region s0). rewrite Ex0 in Hxb. cbn [ptr_cap] in Hxb.
  assert (xb = arg_base s0) as ->.
  { destruct Hcap as [E1|E1]; rewrite E1 in Hxb; destruct Hxb as [E2|E2]; congruence. }
  apply list_elem_of_In, in_flat_map. exists s0. split; [exact Hin0|]. unfold arg_ps, string_ps. left. reflexivity.
Qed.

(** iw_1.iw_1.L32, the help text's end: main loads stderr, compares it
    with stdout and exits with 0 or 1. *)
Lemma help_L32 e from Φ :
  lookup (TAtom "iw_1.v41") e = Some (WPtr stream) ->
  ⊢ WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.iw_1.L32") (Some (TAtom from)))) : mexpr)
      {{ Φ }}.
Proof.
  intros H41. mn_enter "iw_1.iw_1.L32".
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hstderr_g; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_check. exact (proj1 (wi_stderr _ _ _ Hw)). }
  iNext. iIntros "_". gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_raw_load_pointer; apply (wi_stderr _ _ _ Hw). }
  iNext. iIntros "_". gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (ptr_addr stream mod 2 ^ 64 =? ptr_addr errstream mod 2 ^ 64).
  - (* Help went to stderr: exit(1). *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    mn_enter "iw_1.iw_1.L50".
    iApply (wp_main_exit _ _ _ _ _ _ _ 1); [word_premise | lia].
  - (* To stdout: exit(0). *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    mn_enter "iw_1.iw_1.L49".
    iApply wp_goto. iNext. cbn [edge_label].
    mn_enter "iw_1.iw_1.L50".
    iApply (wp_main_exit _ _ _ _ _ _ _ 0); [word_premise | lia].
Qed.

(** Pick the output call's entry in a list of calls. *)
Local Ltac pick_output := repeat (first [left; reflexivity | right]).

(** Main checks the locale after printing the footer. Both branches
    finish by comparing the output stream with stderr and exiting. *)
Lemma help_locale e p t b61 r61 pname Φ :
  lookup (TAtom "iw_1.v41") e = Some (WPtr stream) ->
  lookup (TAtom "iw_1.iw_1.v3") e = Some (WPtr p) ->
  name_ok sargs pname ->
  LL.lent 5 p t -∗ pts help_ps -∗ pts (flat_map arg_ps sargs) -∗
  string (version_literal "hello#str.61") b61 r61 [101; 110; 95] -∗
  WP (ERun (mkFrame main_fn e [] None
    (Enter (TAtom "iw_1.iw_1.L36") (Some (TAtom "iw_1.L39")))) : mexpr) {{ Φ }}.
Proof.
  clear - section_irisGS SafepointStable0 Hlinked Hstrncmp Hlent
    Hexit Hexit_abi Hexit_pre Hexit_post Hstderr_g wi_stderr
    Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame.
  intros Hstream Hp Hname. iIntros "#Hk Hps Has H61".
  pose proof (main_help_lookup "hello#str.61" ltac:(simpl; tauto)) as H61.
  pose proof (main_help_lookup "hello#str.62" ltac:(simpl; tauto)) as H62.
  pose proof (main_help_lookup "hello#str.63" ltac:(simpl; tauto)) as H63.
  mn_enter "iw_1.iw_1.L36".
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H61; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (LL.wp_strncmp_lent registry wi ge Hlent _ _ _ _ _ _ _ _ _ _ 5 p t _ _ _ _ 3 with "Hk H61");
    [exact Hstrncmp | apply linked_outside; first [exact Hlinked | reflexivity] |
     apply linked_unbound; first [exact Hlinked | reflexivity] | word_premise | word_premise | word_premise | lia |].
  iNext. iIntros (bits) "H61". gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply wp_goto. iNext. cbn [edge_label].
  mn_enter "iw_1.iw_1.L37". gen_env.
  match goal with H : lookup (TAtom "iw_1.iw_1.v43") _ = Some (WInt ((if ?c then _ else _) mod _)) |- _ =>
    destruct c end.
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    mn_enter "iw_1.iw_1.L30".
    iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H62; reflexivity | intros ?m; word_premise |].
    iNext. gen_env.
    iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H63; reflexivity | intros ?m; word_premise |].
    iNext. gen_env.
    iApply (wp_main_output with "Hps Has");
      [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
    iNext. iIntros (?n) "Hps Has". gen_env.
    iApply wp_goto. iNext. cbn [edge_label].
    iApply help_L32. assumption.
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply help_L32. assumption.
Qed.

End main.
End HelloMainHelpOutput.
