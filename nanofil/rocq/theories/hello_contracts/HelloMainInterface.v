(** Main's option, version, and help proofs use a small part of its program logic.
    This interface lets those phases reuse it without copying initialization proofs. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics StepRules
  ExternalCalls LibcCalls Pieces Heap ContractFrame Logic HelloLeaf HelloVersion HelloModule HelloConvDefs
  MemLogic StringLogic Getopt GetoptLogic Libc VariadicLogic HelloMainBase HelloMainFacts
  HelloName LentLogic Locale LocaleLogic Startup.
Open Scope Z_scope.
Open Scope list_scope.
Import HelloMainBase.MainDefinitions MainFacts.

Module Type HelloMainBase (R : Runtime).
Declare Module LG0 : LogicSig R.
Import LG0 LG0.L.

Module HP.
Module HN.
Parameter store_keeps : forall {world : Type},
  (mem -> world -> gmap piece pval -> Prop) -> Z -> region -> Prop.
Parameter literals : forall {Σ} `{!gen_heapGS piece pval Σ}, region -> region -> iProp Σ.
Definition name_cells {Σ} `{!gen_heapGS piece pval Σ}
    (pn nreg sreg : region) (nb sb : Z) (x0 x1 y : ptr) : iProp Σ :=
  live program_name_b pn ∗ pcell program_name_b 0 x0 ∗ live nb nreg ∗ pcell nb 0 x1 ∗
  live sb sreg ∗ pcell sb 0 y.
End HN.
End HP.
Module HLo.
Module HL.
Parameter linked_outside : forall ge, hello_linked ge -> forall s,
  existsb (String.eqb s) hello_externals = true -> find_fn ge (TAtom s) = None.
Parameter linked_unbound : forall ge, hello_linked ge -> forall s,
  existsb (String.eqb s) hello_externals = true -> lookup (TAtom s) (ge_globals ge) = None.
Module ML.
Section ownership.
Context `{!gen_heapGS piece pval Σ}.
Definition bytes (b o : Z) (xs : list Z) : iProp Σ := pts (byte_ps b o xs).
Definition auxes (b o : Z) (cs : list cap) : iProp Σ := pts (aux_ps b o cs).
Parameter block_pts : forall b reg o xs cs,
  pts (block_ps b reg o xs cs) ⊣⊢ live b reg ∗ bytes b o xs ∗ auxes b o cs.
Parameter bytes_app : forall b o xs ys,
  bytes b o (xs ++ ys) ⊣⊢ bytes b o xs ∗ bytes b (o + Z.of_nat (length xs)) ys.
Parameter auxes_app : forall b o cs ds,
  auxes b o (cs ++ ds) ⊣⊢ auxes b o cs ∗ auxes b (o + Z.of_nat (length cs)) ds.
End ownership.
Module CSL.
Parameter string : forall {Σ} `{!gen_heapGS piece pval Σ}, ptr -> Z -> region -> list Z -> iProp Σ.
End CSL.
End ML.
Module LL.
Parameter named : forall {Σ} `{!gen_heapGS piece pval Σ}, Z -> ptr -> list Z -> iProp Σ.
Definition lent {Σ} `{!gen_heapGS piece pval Σ} (k : Z) (p : ptr) (t : list Z) : iProp Σ :=
  ⌜0 < ptr_addr p /\ ptr_addr p + Z.of_nat (length t) < 2 ^ 64 /\ Forall (fun x => 0 < x < 256) t⌝ ∗
  pointsto (PName k) DfracDiscarded (VName p t).
Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance lent_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Parameter wp_lent_query : let _ := SafepointStable0 in
  forall f e ls lab d g args rest j spec xs k p t Φ,
  registry g = Some spec -> contract_returns spec = RClass P ->
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
  map_option (arg_x ge e) args = Some xs -> contract_abi spec (CResult d P) args ->
  (forall m w h, wi m w h -> h !! PName k = Some (VName p t) -> contract_pre spec xs m w) ->
  (forall s m w h trace ending s' m' w', wi m w h -> h !! PName k = Some (VName p t) ->
     M.E.invoke spec (CResult d P) args xs s m w trace ending s' m' w' ->
     s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr p]) ->
  lent k p t -∗
  ▷ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec lab rest j))) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d P) (Global g) args :: rest) j))) {{ Φ }}.
Parameter wp_strncmp_lent : let _ := SafepointStable0 in
  (forall m w h k p t,
    wi m w h -> live_disjoint m -> objects_fit (m_regions m) -> freed_empty (m_regions m) ->
    h !! PName k = Some (VName p t) -> lent_at m h p t) ->
  forall f e ls lab d v w u rest j k p t q b' reg' ys n Φ,
  registry (TAtom "strncmp") = Some (strncmp_contract world) ->
  find_fn ge (TAtom "strncmp") = None -> lookup (TAtom "strncmp") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg P w) = Some (WPtr q) ->
  arg_x ge e (Arg L u) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  lent k p t -∗ ML.CSL.string q b' reg' ys -∗
  ▷ (∀ bits, ML.CSL.string q b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WInt bits) e) ls None (Exec lab rest j))) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec lab (Call (CResult d W) (Global (TAtom "strncmp")) [Arg P v; Arg P w; Arg L u] :: rest) j))) {{ Φ }}.
End rules.
End LL.
End HL.
End HLo.

Module GL.
Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance getopt_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Context (view : world -> getopt_world) (optarg_cell optind_cell : ptr)
  (Hcells : 0 <= ptr_addr optarg_cell < 2 ^ 64 /\ 0 <= ptr_addr optind_cell < 2 ^ 64)
  (Hgetopt_wi : forall m w h, wi m w h ->
     getopt_state_at m (view w) /\ getopt_optarg_cell (view w) = optarg_cell /\
     getopt_optind_cell (view w) = optind_cell /\ getopt_current (view w) h).
Parameter wp_optarg_check : let _ := (SafepointStable0, Hcells, Hgetopt_wi) in
  forall f e ls l d args rest j classes Φ,
  op_arg_classes (Check 0 8 Read 8) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr optarg_cell] ->
  ▷ WP (ERun (mkFrame f (put d (WPtr optarg_cell) e) ls None (Exec l rest j))) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check 0 8 Read 8) args :: rest) j))) {{ Φ }}.
Parameter wp_optarg_load : let _ := (SafepointStable0, Hcells, Hgetopt_wi) in
  forall f e ls l d args rest j classes a i Φ,
  op_arg_classes (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr optarg_cell] ->
  pts (getopt_ps a i) -∗
  ▷ (pts (getopt_ps a i) -∗ WP (ERun (mkFrame f (put d (WPtr a) e) ls None (Exec l rest j))) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) args :: rest) j))) {{ Φ }}.
Parameter wp_optind_check : let _ := (SafepointStable0, Hcells, Hgetopt_wi) in
  forall f e ls l d args rest j classes Φ,
  op_arg_classes (Check 0 4 Read 1) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr optind_cell] ->
  ▷ WP (ERun (mkFrame f (put d (WPtr optind_cell) e) ls None (Exec l rest j))) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check 0 4 Read 1) args :: rest) j))) {{ Φ }}.
Parameter wp_optind_load : let _ := (SafepointStable0, Hcells, Hgetopt_wi) in
  forall f e ls l d args rest j classes a i Φ,
  op_arg_classes (RawLoad (LdNarrow Sw) 0) W = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr optind_cell] ->
  pts (getopt_ps a i) -∗
  ▷ (pts (getopt_ps a i) -∗
     WP (ERun (mkFrame f (put d (WInt (i mod 2 ^ 32)) e) ls None (Exec l rest j))) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d W (RawLoad (LdNarrow Sw) 0) args :: rest) j))) {{ Φ }}.
End rules.
End GL.

Module HV.
Definition version_main_args (stream : ptr) : list word :=
  [WPtr stream; WPtr (version_literal "hello#str.70");
   WPtr (version_literal "hello#str.63"); WPtr (version_literal "hello#str.71");
   WPtr (version_literal "hello#str.72"); WPtr (version_literal "hello#str.73");
   WPtr (version_literal "hello#str.74"); WPtr (version_literal "hello#str.75"); WPtr null].
Definition version_etc_fn : func := Eval vm_compute in hello_fn "version_etc".
Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance version_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Parameter proper_name_spec : let _ := SafepointStable0 in forall p Φ,
  ▷ Φ (Ret (WPtr p)) -∗
  WP (ERun (invocation proper_name_fn [WPtr p])) {{ Φ }}.
Parameter version_etc_spec : let _ := SafepointStable0 in hello_linked ge ->
  forall (stream : ptr) (literal_ps : list (piece * pval)) (author_reg : String.string -> region),
  (forall s, In s ["hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75"] ->
    (PLive (ptr_addr (version_literal s)), VLive (author_reg s)) ∈ literal_ps) ->
  forall version_spec : name -> contract world,
  (forall g xs, In (g, xs) (version_output_args stream) -> registry g = Some (version_spec g)) ->
  (forall g xs, In (g, xs) (version_output_args stream) -> contract_returns (version_spec g) = RClass W) ->
  (forall g xs d args, In (g, xs) (version_output_args stream) ->
    map (fun a => match a with Arg k _ => k end) args = version_output_classes xs ->
    contract_abi (version_spec g) (CResult d W) args) ->
  (forall g xs m w h, In (g, xs) (version_output_args stream) ->
    (forall l v, (l, v) ∈ literal_ps -> h !! l = Some v) ->
    agrees m h -> wi m w h -> contract_pre (version_spec g) xs m w) ->
  (forall g xs r args s m w h trace values s' m' w',
    In (g, xs) (version_output_args stream) ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    M.E.invoke (version_spec g) r args xs s m w trace (CallReturn values) s' m' w' ->
    agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
      exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32) ->
  (forall size m wd h base,
    In size [24; 80] -> fresh m (heap_req 8 size) base -> wi m wd h ->
    wi (allocated m (heap_req 8 size) base) wd (overwrite (obj_ps base (heap_req 8 size)) h)) ->
  (forall b reg o x xp m wd h,
    (forall k v, (k, v) ∈ [(PLive b, VLive reg)] ++
      (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) -> h !! k = Some v) ->
    wi m wd h ->
    wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
      (overwrite ([(PLive b, VLive reg)] ++
        (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)) ->
  (forall cb cr sb off m wd h,
    (forall k v, (k, v) ∈ va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb)) -> h !! k = Some v) ->
    wi m wd h -> wi (store_bytes m cb 8 (sb + off + 8)) wd
      (overwrite (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) h)) ->
  (forall m wd h sb,
    fresh m (heap_req 16 72) sb -> wi m wd h ->
    wi (snapshot_values (version_main_args stream) sb (allocated m (heap_req 16 72) sb)) wd
      (overwrite (snapshot_ps (version_main_args stream) sb (heap_req 16 72)) h)) ->
  forall Φ, pts literal_ps -∗ ▷ (pts literal_ps -∗ Φ RetVoid) -∗
  WP (ERun (invocation version_etc_fn (version_main_args stream))) {{ Φ }}.
Parameter emit_bug_reporting_address_spec : let _ := SafepointStable0 in
  hello_linked ge -> forall stdout_cell stdout : ptr,
  lookup (TAtom "stdout") (ge_globals ge) = Some stdout_cell ->
  (forall m w h, wi m w h ->
    access_res m (raw_address (ptr_addr stdout_cell) 0) (ptr_cap stdout_cell) 8 Read 8 = Some ok /\
    pointer_load_effects m (raw_address (ptr_addr stdout_cell) 0)
      [AuxRead; LowerResolve; AddressRead] = Some stdout) ->
  forall (literal_ps : list (piece * pval)) (output_spec : name -> contract world),
  (forall g xs, In (g, xs) (emit_output_args stdout) -> registry g = Some (output_spec g)) ->
  (forall g xs, In (g, xs) (emit_output_args stdout) -> contract_returns (output_spec g) = RClass W) ->
  (forall g xs d args, In (g, xs) (emit_output_args stdout) ->
    map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
    contract_abi (output_spec g) (CResult d W) args) ->
  (forall g xs m w h, In (g, xs) (emit_output_args stdout) ->
    (forall l v, (l, v) ∈ literal_ps -> h !! l = Some v) ->
    agrees m h -> wi m w h -> contract_pre (output_spec g) xs m w) ->
  (forall g xs r args s m w h trace values s' m' w',
    In (g, xs) (emit_output_args stdout) ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    M.E.invoke (output_spec g) r args xs s m w trace (CallReturn values) s' m' w' ->
    agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
      exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32) ->
  forall Φ, pts literal_ps -∗ ▷ (pts literal_ps -∗ Φ RetVoid) -∗
  WP (ERun (invocation emit_bug_reporting_address_fn [])) {{ Φ }}.
End rules.
End HV.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance main_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Definition loop_res (av : Z) (ar : region) (sargs : list argument)
    (b4 : Z) (ps : list ptr) (cs : list cap) (a : ptr) (i : Z) (g : ptr) : iProp Σ :=
  pts (block_ps av ar 0 (argv_bytes ps) cs) ∗ pts (flat_map arg_ps sargs) ∗ pts (getopt_ps a i) ∗
  live b4 (mkRegion b4 (b4 + 16) Heap Live) ∗ pcell b4 0 g.
Definition loop_exit (av : Z) (ar : region) (sargs : list argument)
    (b4 b6 : Z) (lab from : String.string)
    (Φ : language.val (nanofil_lang registry ge) → iProp Σ) : iProp Σ :=
  ∀ e ps cs a i g lose,
    ⌜loop_facts av sargs e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ (lose = 0 \/ lose = 1)⌝ -∗
    loop_res av ar sargs b4 ps cs a i g -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom lab) (Some (TAtom from))))) {{ Φ }}.
Parameter wp_main_exit : let _ := SafepointStable0 in hello_linked ge -> forall exit_spec : contract libc_world,
  registry (TAtom "exit") = Some exit_spec ->
  (forall v, contract_abi exit_spec CVoid [Arg W v]) ->
  (forall n m w h, 0 <= n < 2 ^ 32 -> wi m w h -> contract_pre exit_spec [WInt n] m w) ->
  (forall args n s m w tr vs s' m' w',
    M.E.invoke exit_spec CVoid args [WInt n] s m w tr (CallReturn vs) s' m' w' -> False) ->
  forall f e ls lab v rest j n Φ,
  arg_x ge e (Arg W v) = Some (WInt n) -> 0 <= n < 2 ^ 32 ->
  ⊢ WP (ERun (mkFrame f e ls None (Exec lab
    (Call CVoid (Global (TAtom "exit")) [Arg W v] :: rest) j))) {{ Φ }}.
End rules.

Section getopt.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Let section_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  main_irisGS registry wi ge.
Local Existing Instance section_irisGS.
Context (Hlinked : hello_linked ge).
Context (av : Z) (ar : region) (sargs : list argument)
  (Hav : 0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length sargs) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48)
  (Hargc : 1 <= Z.of_nat (length sargs) < 2 ^ 31)
  (Hargs : Forall (fun s => string_ok (arg_ptr s) (arg_base s) (arg_region s) (arg_text s)) sargs).
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
Parameter wp_main_getopt :
  let _ := (SafepointStable0, Hlinked, Hav, Hargc, Hargs, Hgetopt, Hgetopt_wi,
    Htable, Hgetopt_env, Hgetopt_apart, Kgetopt) in
  forall f e ls lab d va vv vs vl vi rest j ps cs a i Φ,
  map_option (arg_x ge e) [Arg W va; Arg P vv; Arg P vs; Arg P vl; Arg P vi] =
    Some (getopt_words (hello_input av sargs)) ->
  getopt_order (map arg_ptr sargs) ps -> argv_caps cs ps -> 0 <= i <= Z.of_nat (length sargs) ->
  pts (block_ps av ar 0 (argv_bytes ps) cs) -∗ pts (flat_map arg_ps sargs) -∗ pts (getopt_ps a i) -∗
  ▷ (∀ code ps' cs' a' i',
       ⌜getopt_order (map arg_ptr sargs) ps' /\ argv_caps cs' ps' /\ 0 <= i' <= Z.of_nat (length sargs) /\
        getopt_int code /\ (code = 103 -> getopt_borrow (hello_input av sargs) a' /\ ptr_addr a' <> 0) /\
        getopt_step wi transition a i [WInt (code mod 2 ^ 32)]⌝ -∗
       pts (block_ps av ar 0 (argv_bytes ps') cs') -∗ pts (flat_map arg_ps sargs) -∗ pts (getopt_ps a' i') -∗
       WP (ERun (mkFrame f (put d (WInt (code mod 2 ^ 32)) e) ls None (Exec lab rest j))) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
     (Exec lab (Call (CResult d W) (Global (TAtom "getopt_long"))
                  [Arg W va; Arg P vv; Arg P vs; Arg P vl; Arg P vi] :: rest) j))) {{ Φ }}.
End getopt.

Section startup.
Import HLo.HL HLo.HL.ML HLo.HL.ML.CSL.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Let section_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := main_irisGS registry wi ge.
Local Existing Instance section_irisGS.
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
Parameter main_to_L8 :
  let _ := (SafepointStable0, Hlinked, Kalloc, Hmemset, Kmemset, Hstrrchr, Hmemcmp, Hstrncmp,
    Hnb, Hsb, Hpn_end, Hnb_cell, Hsb_cell, Kpn, Knb, Ksb,
    Hsetlocale, Hlent, Hset_pre, Kset, Kpstore, Hatexit, Hatexit_ret, Hatexit_abi, Hatexit_pre,
    Katexit, Hav, Hargc, Hargs) in
  forall s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix Φ,
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
       ⌜loop_facts av sargs e b4 b6 (map arg_ptr sargs) cs0 ix greeting_ptr⌝ -∗
       loop_res av ar sargs b4 (map arg_ptr sargs) cs0 a ix greeting_ptr -∗
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
       WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom "start")))))
         {{ Φ }}) -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length sargs)); WPtr (mkPtr av (Obj av))])) {{ Φ }}.
End startup.
End HelloMainBase.
