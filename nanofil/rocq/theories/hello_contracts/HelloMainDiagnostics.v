(** Main reports invalid options and extra operands before exiting.
    These proofs combine the output phases and connect initialization
    to the greeting continuation under their shared interface. *)
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

From Nanofil Require Import HelloMainOptions HelloMainOperands HelloMainHelp.
Module HelloMainDiagnostics (R : Runtime) (B : HelloMainInterface.HelloMainBase R).
Import B B.LG0 B.LG0.L B.HLo.HL B.HLo.HL.ML B.HLo.HL.ML.CSL.
Include HelloMainOptions.HelloMainOptions R B.
Include HelloMainOperands.HelloMainOperands R B.
Include HelloMainHelp.HelloMainHelp R B.
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
Context (Hoptarg_g : lookup (TAtom "optarg") (ge_globals ge) = Some optarg_cell).
Context (Hcells : 0 <= ptr_addr optarg_cell < 2 ^ 64 /\ 0 <= ptr_addr optind_cell < 2 ^ 64).
Context (Hoptind_g : lookup (TAtom "optind") (ge_globals ge) = Some optind_cell).
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


Local Ltac pick_output := repeat (first [left; reflexivity | right]).
Local Notation order_length := (order_length sargs).
Local Notation main_help_lookup := (main_help_lookup ge Hlinked).
Local Notation name_life := (name_life sargs Hargs).
Local Notation wp_main_output := (wp_main_output registry wi ge Hlinked sargs stream errstream
  help_ps output_spec Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame).
Local Notation operand_exit := (operand_exit registry wi ge av ar sargs).
Local Notation argv_block_slot := (argv_block_slot sargs).
Local Notation operands_exit := (operands_exit registry wi ge nb sb av ar sargs Hav Hargc Hargs
  optarg_cell optind_cell Hgetopt_wi Hcells Hoptind_g).
Local Notation main_help := (main_help registry wi ge Hlinked Hstrncmp pn nreg sreg nb sb Hpn_end
  Hnb_cell Hsb_cell rep requests Hsetlocale Hlent av ar sargs Hav Hargc Hargs
  optarg_cell optind_cell Hcells exit_spec Hexit Hexit_abi Hexit_pre Hexit_post
  stdout_cell stream Hstdout_g wi_stdout Hquery_pre Hquery stderr_cell errstream Hstderr_g wi_stderr
  help_ps output_spec Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame
  Houtput_reg Houtput_ret Houtput_abi Houtput_pre Houtput_frame).
Local Notation main_version := (main_version registry wi ge Hlinked nreg sreg nb sb Hnb_cell Hsb_cell
  av ar sargs Hav Hargc optarg_cell optind_cell Hcells exit_spec Hexit Hexit_abi Hexit_pre Hexit_post
  stdout_cell stream Hstdout_g wi_stdout version_ps author_reg Hauthor_live version_spec Hversion_reg
  Hversion_ret Hversion_abi Hversion_pre Hversion_frame Kversion_alloc Kversion_store Kversion_cursor Kversion_snapshot).
Local Notation main_to_loop := (main_to_loop registry wi ge Hlinked Kalloc Hmemset Kmemset
  Hstrrchr Hmemcmp Hstrncmp pn nreg sreg nb sb Hnb Hsb Hpn_end Hnb_cell Hsb_cell Kpn Knb Ksb
  rep requests Hsetlocale Hlent Hset_pre Kset Kpstore atexit_spec Hatexit Hatexit_ret Hatexit_abi
  Hatexit_pre Katexit av ar sargs Hav Hargc Hargs initialized running grequests transition Hgetopt
  optarg_cell optind_cell Hgetopt_wi Htable Hgetopt_env Hgetopt_apart Kgetopt Hoptarg_g Hcells).
(** iw_1.L113, after a bad option or an extra operand: main prints to
    stderr that --help says more, naming the program, and exits with 1. *)
Lemma main_hint e from x0 x1 y0 Φ :
  name_ok sargs x0 ->
  pts help_ps -∗ pts (flat_map arg_ps sargs) -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L113") (Some (TAtom from)))) : mexpr) {{ Φ }}.
Proof.
  intros Hname.
  pose proof (main_help_lookup "hello#str.79" ltac:(simpl; tauto)) as H79.
  assert (Hpn : lookup (TAtom "program_name") (ge_globals ge) =
                Some (mkPtr program_name_b (Obj program_name_b))).
  { apply (proj1 (proj2 Hlinked)). vm_compute. reflexivity. }
  destruct (name_life x0 Hname) as [Hxr Hxlife].
  pose proof Hpn_end as Hpn_end'.
  rewrite /HP.HN.name_cells.
  iIntros "Hps Has (Hpl & Hpc & Hnl & Hnc & Hsl & Hsc)".
  mn_enter "iw_1.L113".
  (* stderr's stream. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hstderr_g; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_check. exact (proj1 (wi_stderr _ _ _ Hw)). }
  iNext. iIntros "_". gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_raw_load_pointer; apply (wi_stderr _ _ _ Hw). }
  iNext. iIntros "_". gen_env.
  (* The hint, naming the program. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H79; reflexivity | intros ?m; word_premise |].
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
  iNext. iIntros "Hpl Hpc Has". gen_env.
  iApply (wp_main_output with "Hps Has");
    [exact Hname | | word_premise | reflexivity |]; [unfold main_output_args; pick_output |].
  iNext. iIntros (?n) "Hps Has". gen_env.
  iApply (wp_main_exit _ _ _ _ _ _ _ 1); [word_premise | lia].
Qed.

(** The help hint borrows argument strings from the loop and literal
    strings and program-name cells from its caller. *)
Lemma hint_exit b4 b6 from P x0 x1 y0 Φ :
  name_ok sargs x0 ->
  pts help_ps -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  operand_exit b4 b6 "iw_1.L113"%string from P Φ.
Proof.
  intros Hname. iIntros "Hps Hcells". rewrite /operand_exit.
  iIntros (e ps cs a i g lose _) "(_ & Has & _)".
  iApply (main_hint with "Hps Has Hcells"). exact Hname.
Qed.

(** The extra-operand diagnostic prints the offending argument and returns.
    It preserves the world interpretation and all memory owned by main. *)
Context (diag_spec : contract libc_world)
  (Hdiag_reg : registry (TAtom "error") = Some diag_spec)
  (Hdiag_ret : contract_returns diag_spec = RVoid)
  (Hdiag_abi : forall args, map (fun a => match a with Arg k _ => k end) args = [W; W; P; P; P] ->
    contract_abi diag_spec CVoid args)
  (Hdiag_pre : forall q m w h, In q (map arg_ptr sargs) ->
    (forall l v, (l, v) ∈ help_ps ++ flat_map arg_ps sargs -> h !! l = Some v) ->
    agrees m h -> wi m w h ->
    contract_pre diag_spec [WInt 0; WInt 0; WPtr (version_literal "hello#str.77");
                            WPtr (version_literal "hello#str.78"); WPtr q] m w)
  (Hdiag_post : forall q args s m w h tr vs s' m' w', In q (map arg_ptr sargs) ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    M.E.invoke diag_spec CVoid args [WInt 0; WInt 0; WPtr (version_literal "hello#str.77");
                                     WPtr (version_literal "hello#str.78"); WPtr q]
      s m w tr (CallReturn vs) s' m' w' ->
    vs = [] /\ agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h).

(** The literals of the extra-operand diagnostic are linked. *)
Lemma main_extra_lookup s :
  In s ["hello#str.77"; "hello#str.78"] -> lookup (TAtom s) (ge_globals ge) = Some (version_literal s).
Proof.
  intros Hin. apply (proj1 (proj2 Hlinked)).
  repeat destruct Hin as [<- | Hin]; try contradiction; vm_compute; reflexivity.
Qed.

(** Main reloads the extra argument, reports it with error, and prints
    the help hint. The parser position is below the argument count,
    so this load cannot select the null sentinel. *)
Lemma main_extra b4 b6 x0 x1 y0 Φ :
  name_ok sargs x0 ->
  pts help_ps -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  operand_exit b4 b6 "iw_1.L79"%string "iw_1.L55"%string (fun _ i => i < Z.of_nat (length sargs)) Φ.
Proof.
  intros Hname.
  pose proof (main_extra_lookup "hello#str.77" ltac:(simpl; tauto)) as H77.
  pose proof (main_extra_lookup "hello#str.78" ltac:(simpl; tauto)) as H78.
  iIntros "Hps Hcells". rewrite /operand_exit.
  iIntros (e ps cs a i g lose (Hf & Hpr & Hlt)) "(Hb & Hs & Ht & Hl4 & Hp4)".
  pose proof Hf as ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg).
  pose proof Hav as (Hav0 & Hav8 & Haend & Har48). pose proof Hargc as Hargc'.
  pose proof (order_length ps Ho) as Lp.
  destruct (lookup_lt_is_Some_2 (ps ++ [null]) (Z.to_nat i)) as [q Hq].
  { rewrite length_app Lp. cbn [length]. lia. }
  pose proof (slot_kinds sargs ps (Z.to_nat i) q Ho Hq) as Hkind.
  destruct Hkind as [[Ek _] | [_ (s & Hs & ->)]]; [lia|].
  pose proof (proj1 (List.Forall_forall _ _) Hargs s Hs) as (Hcap & Hb0 & Hbp & Hend & H48 & _).
  assert (Hqr : 0 <= ptr_addr (arg_ptr s) < 2 ^ 64) by lia.
  assert (Hlife : forall xb, ptr_cap (arg_ptr s) = Obj xb \/ ptr_cap (arg_ptr s) = Ro xb ->
                    exists xr, (PLive xb, VLive xr) ∈ flat_map arg_ps sargs).
  { intros xb Hxb. exists (arg_region s).
    assert (xb = arg_base s) as ->.
    { destruct Hcap as [E1|E1]; rewrite E1 in Hxb; destruct Hxb as [E2|E2]; congruence. }
    apply list_elem_of_In, in_flat_map. exists s. split; [exact Hs|]. unfold arg_ps, string_ps. left. reflexivity. }
  assert (Hqin : In (arg_ptr s) (map arg_ptr sargs)) by (apply in_map; exact Hs).
  mn_enter "iw_1.L79".
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H77; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite H78; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  (* argv[optind] again. *)
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
  iEval (rewrite (argv_block_slot av ar ps cs (Z.to_nat i) (arg_ptr s) Hc Hq)) in "Hb".
  iDestruct "Hb" as "(Hal & Hy0 & Hx0 & Hq & Hy1 & Hx1)".
  iApply (wp_check_read with "Hal");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise | addr_premise |].
  iNext. iIntros "Hal". gen_env.
  iApply (wp_raw_load_pointer_in with "Hal Hq Hs");
    [reflexivity | word_premise | left; reflexivity | addr_premise | addr_premise | exact Hqr | exact Hlife |].
  iNext. iIntros "Hal Hq Hs". gen_env.
  (* error(0, 0, "extra operand %s", ..., argv[optind]). *)
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ diag_spec
            [WInt 0; WInt 0; WPtr (version_literal "hello#str.77");
             WPtr (version_literal "hello#str.78"); WPtr (arg_ptr s)]
            (pts help_ps ∗ pts (flat_map arg_ps sargs)) with "[$Hps $Hs] [Hcells]");
    [apply linked_outside; first [exact Hlinked | reflexivity] |
     apply linked_unbound; first [exact Hlinked | reflexivity] | reflexivity | exact Hdiag_reg |
     word_premise | apply Hdiag_abi; reflexivity | |].
  - iIntros (σ) "(%h & Hh & %Hσ) [Hps Has]". destruct Hσ as (Ha & _ & _ & Hw).
    iDestruct (pts_lookup with "Hh Hps") as %Hps. iDestruct (pts_lookup with "Hh Has") as %Has.
    iPureIntro. apply (Hdiag_pre _ _ _ h Hqin); [|exact Ha|exact Hw].
    intros l v Hl. apply elem_of_app in Hl as [Hl|Hl]; [exact (Hps _ _ Hl) | exact (Has _ _ Hl)].
  - iNext. iIntros (σ tr vs s' m' w' Hinv) "(%h & Hh & %Hσ) [Hps Has]".
    destruct Hσ as (Ha & Hd & Hr & Hw).
    destruct (Hdiag_post _ _ _ _ _ _ _ _ _ _ _ Hqin Ha Hd Hr Hw Hinv) as (-> & Ha' & Hd' & Hr' & Hw').
    iModIntro. iExists _. iSplit.
    + iPureIntro. unfold external_env. rewrite Hdiag_ret. reflexivity.
    + iSplitL "Hh"; [iExists h; iFrame; iPureIntro; auto|].
      iApply wp_goto. iNext. cbn [edge_label].
      iApply (main_hint with "Hps Has Hcells"). exact Hname.
Qed.

(** The option loop can exit through version output, help, or operand checks.
    Each alternative receives the available resources because only one branch runs. *)
Lemma loop_exits b4 b6 x0 x1 y0 p t b61 r61 Φ :
  name_ok sargs x0 ->
  pts version_ps -∗ pts help_ps -∗ LL.lent 5 p t -∗
  string (version_literal "hello#str.61") b61 r61 [101; 110; 95] -∗
  HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  operand_exit b4 b6 "iw_1.join"%string "iw_1.L60"%string
    (fun lose i => lose = 0 /\ i = Z.of_nat (length sargs)) Φ -∗
  (loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ ∧
   loop_exit b4 b6 "iw_1.L39"%string "iw_1.L50"%string Φ ∧
   loop_exit b4 b6 "iw_1.L10"%string "iw_1.L8"%string Φ).
Proof.
  intros Hname. iIntros "Hv Hh #Hk H61 Hc Hj".
  iSplit; [iApply (main_version with "Hv")|].
  iSplit; [iApply (main_help with "Hk Hh H61 Hc"); exact Hname|].
  iApply operands_exit.
  iSplit; [iApply (main_extra with "Hh Hc"); exact Hname|].
  iSplit; [iApply (hint_exit with "Hh Hc"); exact Hname | iExact "Hj"].
Qed.

(** Initialization and option parsing lead either to an exit or to the greeting.
    The greeting continuation receives a clear error flag and a parser
    position at the end of the arguments. *)
Lemma main_to_join s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix b61 r61 Φ :
  sargs = s0 :: srest -> argv_caps cs0 (map arg_ptr sargs) -> 0 <= ix <= Z.of_nat (length sargs) ->
  pts (block_ps av ar 0 (argv_bytes (map arg_ptr sargs)) cs0) -∗ pts (flat_map arg_ps sargs) -∗
  pts (getopt_ps a ix) -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗
  pts version_ps -∗ pts help_ps -∗ string (version_literal "hello#str.61") b61 r61 [101; 110; 95] -∗
  ▷ (∀ e b4 b6 (i k : nat) q (new : Z -> ptr * list Z) c',
       ⌜start_vars e (Z.of_nat (length sargs)) av b4 b6 /\
        lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
        fresh_ok b4 /\ fresh_ok b6 /\ (i <= length (arg_text s0))%nat /\ (k <= length (arg_text s0))%nat /\
        (q = mkPtr 0 CNone \/ q = (new 6).1)⌝ -∗
       HP.HN.literals r3 r4 -∗
       ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗ pts (codec_ps c') -∗
       string empty_ptr 69968 r80 [] -∗
       bytes b4 8 (replicate 8 0) -∗ auxes b4 1 (replicate 15 CNone) -∗
       live b6 (mkRegion b6 (b6 + 16) Heap Live) -∗ bytes b6 0 (replicate 8 0) -∗
       bytes b6 8 (replicate 8 0) -∗ auxes b6 0 (clear_slots 0 (replicate 8 CNone)) -∗
       auxes b6 8 (replicate 8 CNone) -∗
       operand_exit b4 b6 "iw_1.join"%string "iw_1.L60"%string
         (fun lose i => lose = 0 /\ i = Z.of_nat (length sargs)) Φ) -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length sargs)); WPtr (mkPtr av (Obj av))]) : mexpr) {{ Φ }}.
Proof.
  intros Hhd Hcs Hix.
  iIntros "Hb Hs Ht Hlit Hcells Hks Hcod Hs80 Hv Hh H61 HK".
  iApply (main_to_loop with "Hb Hs Ht Hlit Hcells Hks Hcod Hs80"); [exact Hhd | exact Hcs | exact Hix |].
  iNext. iIntros (e b4 b6 i k q new c' Hf) "Hlit Hcells #Hl Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'".
  pose proof Hf as (_ & _ & _ & _ & Hi & _).
  iDestruct (big_sepL_elem_of _ _ 5 with "Hl") as "Hk5";
    [apply list_elem_of_In; unfold locale_categories; cbn; repeat (first [left; reflexivity | right]) |].
  iApply (loop_exits with "Hv Hh Hk5 H61 Hcells [-]").
  { exists s0, srest, i. auto. }
  iApply ("HK" $! e b4 b6 i k q new c' Hf with "Hlit Hl Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'").
Qed.

End main.
End HelloMainDiagnostics.
