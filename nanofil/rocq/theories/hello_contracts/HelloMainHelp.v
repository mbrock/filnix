(** Main prints its usage text and footer when an option requests help.
    The proof reuses initialization without copying its module body. *)
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

From Nanofil Require Import HelloMainHelpOutput.
Module HelloMainHelp (R : Runtime) (B : HelloMainInterface.HelloMainBase R).
Import B B.LG0 B.LG0.L.
Import B.HLo.HL B.HLo.HL.ML.CSL.
Local Hint Opaque main_fn pts live pcell main_irisGS : typeclass_instances.
Include HelloMainHelpOutput R B.
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

Local Notation main_help_lookup := (main_help_lookup ge Hlinked).
Local Notation name_life := (name_life sargs Hargs).
Local Notation wp_main_output := (wp_main_output registry wi ge Hlinked sargs stream errstream
  help_ps output_spec Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame).
Local Ltac pick_output := repeat (first [left; reflexivity | right]).
(** The help path prints the usage line, options, and footer.
    A locale whose name does not start with "en_" also receives
    translation-reporting instructions before the program exits. *)
Lemma main_help b4 b6 x0 x1 y0 p t b61 r61 Φ :
  name_ok sargs x0 ->
  LL.lent 5 p t -∗ pts help_ps -∗ string (version_literal "hello#str.61") b61 r61 [101; 110; 95] -∗
  HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  loop_exit b4 b6 "iw_1.L39"%string "iw_1.L50"%string Φ.
Proof using Type section_irisGS SafepointStable0 Hlinked Hstrncmp Hpn_end Hnb_cell Hsb_cell
  Hsetlocale Hlent Hav Hargc Hargs Hcells Hexit Hexit_abi Hexit_pre Hexit_post
  Hstdout_g wi_stdout Hquery_pre Hquery Hstderr_g wi_stderr
  Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame
  Houtput_reg Houtput_ret Houtput_abi Houtput_pre Houtput_frame.
  clear - section_irisGS SafepointStable0 Hlinked Hstrncmp Hpn_end Hsetlocale Hlent Hargs
    Hexit Hexit_abi Hexit_pre Hexit_post Hstdout_g wi_stdout Hquery_pre Hquery Hstderr_g wi_stderr
    Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame
    Houtput_reg Houtput_ret Houtput_abi Houtput_pre Houtput_frame.
  intros Hname.
  pose proof (main_help_lookup "hello#str.54" ltac:(simpl; tauto)) as H54.
  pose proof (main_help_lookup "hello#str.55" ltac:(simpl; tauto)) as H55.
  pose proof (main_help_lookup "hello#str.56" ltac:(simpl; tauto)) as H56.
  pose proof (main_help_lookup "hello#str.57" ltac:(simpl; tauto)) as H57.
  pose proof (main_help_lookup "hello#str.58" ltac:(simpl; tauto)) as H58.
  pose proof (main_help_lookup "hello#str.59" ltac:(simpl; tauto)) as H59.
  pose proof (main_help_lookup "hello#str.60" ltac:(simpl; tauto)) as H60.
  pose proof (main_help_lookup "hello#str.61" ltac:(simpl; tauto)) as H61.
  pose proof (main_help_lookup "hello#str.62" ltac:(simpl; tauto)) as H62.
  pose proof (main_help_lookup "hello#str.63" ltac:(simpl; tauto)) as H63.
  assert (Hpn : lookup (TAtom "program_name") (ge_globals ge) =
                Some (mkPtr program_name_b (Obj program_name_b))).
  { apply (proj1 (proj2 Hlinked)). vm_compute. reflexivity. }
  destruct (name_life x0 Hname) as [Hxr Hxlife].
  pose proof Hpn_end as Hpn_end'.
  rewrite /HP.HN.name_cells.
  iIntros "#Hk Hps H61 (Hpl & Hpc & _)".
  rewrite /loop_exit. iIntros (e ps cs a ix g lose _) "(_ & Has & _)".
  iPoseProof "Hk" as "[%Hpk _]". destruct Hpk as (Hp0 & Hpt & _).
  mn_enter "iw_1.L39".
  (* stdout's stream. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hstdout_g; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_check. exact (proj1 (wi_stdout _ _ _ Hw)). }
  iNext. iIntros "_". gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_raw_load_pointer; apply (wi_stdout _ _ _ Hw). }
  iNext. iIntros "_". gen_env.
  (* setlocale(LC_MESSAGES, NULL). *)
  iApply (LL.wp_lent_query registry wi ge _ _ _ _ _ (TAtom "setlocale") _ _ _
            (libc_setlocale_contract rep requests) [WInt 5; WPtr null] 5 p t with "Hk");
    [exact Hsetlocale | reflexivity | apply linked_outside; first [exact Hlinked | reflexivity] |
     apply linked_unbound; first [exact Hlinked | reflexivity] | reflexivity | word_premise |
     split; [right; eexists; reflexivity | do 2 eexists; reflexivity] |
     intros m w h Hw Hl; exact (Hquery_pre _ _ _ _ _ Hw Hl) |
     intros s m w h trace ending s' m' w' Hw Hl Hq; exact (Hquery _ _ _ _ _ _ _ _ _ _ _ _ _ Hw Hl Hq) |].
  iNext. gen_env.
  (* The usage line. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H54; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hpn; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_check_read with "Hpl");
    [reflexivity | word_premise | left; reflexivity |
     unfold raw_address; cbn [ptr_addr]; unfold program_name_b; rewrite Z.add_0_r Z.mod_small; lia |
     unfold raw_address; cbn [ptr_addr]; rewrite Z.add_0_r Z.mod_small; [lia | unfold program_name_b; lia] |
     unfold raw_address; cbn [ptr_addr]; unfold program_name_b; reflexivity |].
  iNext. iIntros "Hpl". gen_env.
  iApply (wp_raw_load_pointer_in with "Hpl Hpc Has");
    [reflexivity | word_premise | left; reflexivity |
     unfold raw_address; cbn [ptr_addr]; unfold program_name_b; reflexivity |
     unfold program_name_b; reflexivity | exact Hxr | exact Hxlife |].
  iNext. iIntros "_ _ Has". gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (n0) "Hps Has". gen_env.
  (* The option lines. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H55; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (?n) "Hps Has". gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H56; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (?n) "Hps Has". gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H57; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (?n) "Hps Has". gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H58; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (?n) "Hps Has". gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H56; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (?n) "Hps Has". gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H59; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (?n) "Hps Has". gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H60; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (?n) "Hps Has". gen_env.
  (* The footer. *)
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ emit_bug_reporting_address_fn
            (invocation emit_bug_reporting_address_fn []));
    [reflexivity | unfold find_fn; rewrite (proj1 Hlinked); vm_compute; reflexivity | reflexivity |].
  iNext.
  iApply (HV.emit_bug_reporting_address_spec registry wi ge Hlinked stdout_cell stream Hstdout_g wi_stdout
            help_ps output_spec Houtput_reg Houtput_ret Houtput_abi Houtput_pre Houtput_frame with "Hps").
  iNext. iIntros "Hps". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  (* The locale's name is never null: it is lent. *)
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  assert (Ep : (ptr_addr p =? 0) = false) by (apply Z.eqb_neq; lia).
  match goal with H : lookup (TAtom "iw_1.iw_1.v35") _ = _ |- _ => rewrite Ep in H; cbn [negb] in H end.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  (* strncmp(name, "en_", 3). *)
  iApply (help_locale with "Hk Hps Has H61"); eassumption.
Qed.
End main.
End HelloMainHelp.
