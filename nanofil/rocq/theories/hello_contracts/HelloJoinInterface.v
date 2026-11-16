(** Printing the greeting requires initialized memory and character conversion.
    This interface lets separate proofs use those operations without repeatedly checking their implementations. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs
  HelloName HelloProgName HelloClose HelloVersion Startup Getopt GetoptLogic.
Open Scope Z_scope.
Open Scope list_scope.

From Nanofil Require Import HelloMainBase HelloMainFacts.
Import MainDefinitions MainFacts.
Module Type HelloJoinBase (R : Runtime).
Module HM.
Declare Module LG0 : LogicSig R.
Import LG0 LG0.L.
Module HLo.
Module HL.
Parameter linked_outside :
  ∀ ge : genv, hello_linked ge → ∀ s : String.string, existsb (String.eqb s) hello_externals = true → find_fn
  ge (TAtom s) = None.
Arguments linked_outside ge Hlinked s%_string_scope _.
Parameter linked_unbound :
  ∀ ge : genv, hello_linked ge → ∀ s : String.string, existsb (String.eqb s) hello_externals = true → lookup
  (TAtom s) (ge_globals ge) = None.
Arguments linked_unbound ge Hlinked s%_string_scope _.
Module ML.
Definition bytes {Σ} `{!gen_heapGS piece pval Σ} (b o : Z) (xs : list Z) : iProp Σ := pts (byte_ps b o xs).
Definition auxes {Σ} `{!gen_heapGS piece pval Σ} (b o : Z) (cs : list cap) : iProp Σ := pts (aux_ps b o cs).
Module CSL.
Definition string {Σ} `{!gen_heapGS piece pval Σ} (p : ptr) (b : Z) (reg : region) (bs : list Z) : iProp Σ :=
  ⌜string_ok p b reg bs⌝ ∗ pts (string_ps p b reg bs).
Parameter string_suffix :
  ∀ {Σ : gFunctors} {gen_heapGS0 : gen_heapGS piece pval Σ} (p : ptr) (b : Z) (reg : region) (bytes : list Z)
  (i : nat), (i <= length bytes)%nat → string p b reg bytes -∗ string {| ptr_addr := ptr_addr p + i; ptr_cap
  := ptr_cap p |} b reg (drop i bytes) ∗ (string {| ptr_addr := ptr_addr p + i; ptr_cap := ptr_cap p |} b reg
  (drop i bytes) -∗ string p b reg bytes).
Arguments string_suffix {Σ gen_heapGS0} p b%_Z_scope reg bytes%_list_scope i%_nat_scope _.
Parameter wp_strlen :
  ∀ {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : gen_heapGS piece pval Σ}
  {world : Type} (registry : name → option (contract world)) (wi : mem → world → gmap piece pval → Prop),
  LG0.SafepointStable wi → ∀ (ge : genv), let _ := @nanofil_irisGS hlc Σ invGS_gen0 gen_heapGS0 world registry
  wi ge in ∀ (f : func) (e : env) (ls : list (name * option Z)) (lab d : name) (v : value) (rest : list inst)
  (j : jump) (p : ptr) (b : Z) (reg : region) (bytes : list Z) (Φ : val (L.nanofil_lang registry ge) → iPropI
  Σ), registry (TAtom "strlen") = Some (strlen_contract world) → find_fn ge (TAtom "strlen") = None → lookup
  (TAtom "strlen") (ge_globals ge) = None → arg_x ge e (Arg P v) = Some (WPtr p) → string p b reg bytes -∗ ▷
  (string p b reg bytes -∗ WP L.ERun {| fr_fn := f; fr_env := put d (WInt (length bytes)) e; fr_locals := ls;
  fr_doomed := None; fr_at := Exec lab rest j |} : language.expr (L.nanofil_lang registry ge) {{ v, Φ v }}) -∗
  WP L.ERun {| fr_fn := f; fr_env := e; fr_locals := ls; fr_doomed := None; fr_at := Exec lab (Call (CResult d
  L) (Global (TAtom "strlen")) [Arg P v] :: rest) j |} : language.expr (L.nanofil_lang registry ge) {{ v, Φ v
  }}.
Arguments wp_strlen {hlc Σ invGS_gen0 gen_heapGS0} {world}%_type_scope (registry wi)%_function_scope
  {SafepointStable0} ge f e ls%_list_scope lab d v rest%_list_scope j p b%_Z_scope reg bytes%_list_scope
  Φ%_function_scope _ _ _ _.
End CSL.
Parameter block_pts :
  ∀ {Σ : gFunctors} {gen_heapGS0 : gen_heapGS piece pval Σ} (b : Z) (reg : region) (o : Z) (xs : list Z) (cs :
  list cap), pts (block_ps b reg o xs cs) ⊣⊢ LG0.live b reg ∗ bytes b o xs ∗ auxes b o cs.
Arguments block_pts {Σ gen_heapGS0} b%_Z_scope reg o%_Z_scope (xs cs)%_list_scope.
Parameter bytes_take_drop :
  ∀ {Σ : gFunctors} {gen_heapGS0 : gen_heapGS piece pval Σ} (b o : Z) (xs : list Z) (n : nat), (n <= length
  xs)%nat → bytes b o xs ⊣⊢ bytes b o (take n xs) ∗ bytes b (o + n) (drop n xs).
Arguments bytes_take_drop {Σ gen_heapGS0} (b o)%_Z_scope xs%_list_scope n%_nat_scope _.
Parameter auxes_take_drop :
  ∀ {Σ : gFunctors} {gen_heapGS0 : gen_heapGS piece pval Σ} (b o : Z) (cs : list cap) (n : nat), (n <= length
  cs)%nat → auxes b o cs ⊣⊢ auxes b o (take n cs) ∗ auxes b (o + n) (drop n cs).
Arguments auxes_take_drop {Σ gen_heapGS0} (b o)%_Z_scope cs%_list_scope n%_nat_scope _.
Parameter obj_zero_block :
  ∀ {Σ : gFunctors} {gen_heapGS0 : gen_heapGS piece pval Σ} (b : Z) (q : alloc_req), 0 <= req_extent q →
  LG0.obj b q ⊣⊢ LG0.live b {| r_base := b; r_end := b + req_extent q; r_kind := req_kind q; r_life := Live |}
  ∗ bytes b 0 (replicate (Z.to_nat (req_extent q)) 0) ∗ auxes b 0 (replicate (Z.to_nat (req_extent q)) CNone).
Arguments obj_zero_block {Σ gen_heapGS0} b%_Z_scope q _.
Parameter wp_malloc :
  ∀ {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : gen_heapGS piece pval Σ}
  {world : Type} (registry : name → option (contract world)) (wi : mem → world → gmap piece pval → Prop),
  LG0.SafepointStable wi → ∀ (ge : genv), let _ := @nanofil_irisGS hlc Σ invGS_gen0 gen_heapGS0 world
  registry wi ge in ∀ (f : func) (e : env) (ls : list (name * option Z)) (lab d : name) (v : value) (rest :
  list inst) (j : jump) (n : Z) (Φ : val (L.nanofil_lang registry ge) → iPropI Σ), registry (TAtom "malloc") =
  Some (malloc_contract world) → find_fn ge (TAtom "malloc") = None → lookup (TAtom "malloc") (ge_globals ge)
  = None → arg_x ge e (Arg L v) = Some (WInt n) → 0 <= n < 2 ^ 64 → (∀ (m : mem) (wd : world) (h : gmap piece
  pval) (base : Z), fresh m (heap_req 16 n) base → wi m wd h → wi (allocated m (heap_req 16 n) base) wd
  (overwrite (obj_ps base (heap_req 16 n)) h)) → ▷ (∀ base : Z, ⌜0 < base ∧ base mod 16 = 0 ∧ base +
  req_extent (heap_req 16 n) <= 2 ^ 48 ∧ n <= max_allocation_size⌝ -∗ LG0.obj base (heap_req 16 n) -∗ WP
  L.ERun {| fr_fn := f; fr_env := put d (WPtr {| ptr_addr := base; ptr_cap := Obj base |}) e; fr_locals := ls;
  fr_doomed := None; fr_at := Exec lab rest j |} : language.expr (L.nanofil_lang registry ge) {{ v, Φ v }}) -∗
  WP L.ERun {| fr_fn := f; fr_env := e; fr_locals := ls; fr_doomed := None; fr_at := Exec lab (Call (CResult d
  P) (Global (TAtom "malloc")) [Arg L v] :: rest) j |} : language.expr (L.nanofil_lang registry ge) {{ v, Φ v
  }}.
Arguments wp_malloc {hlc Σ invGS_gen0 gen_heapGS0} {world}%_type_scope (registry wi)%_function_scope
  {SafepointStable0} ge f e ls%_list_scope lab d v rest%_list_scope j n%_Z_scope Φ%_function_scope
  _ _ _ _ _ _%_function_scope.
End ML.
Module LL.
Definition lent {Σ} `{!gen_heapGS piece pval Σ} (k : Z) (p : ptr) (t : list Z) : iProp Σ :=
  ⌜0 < ptr_addr p /\ ptr_addr p + Z.of_nat (length t) < 2 ^ 64 /\ Forall (fun x => 0 < x < 256) t⌝ ∗
  pointsto (PName k) DfracDiscarded (VName p t).
Definition named {Σ} `{!gen_heapGS piece pval Σ} (k : Z) (p : ptr) (t : list Z) : iProp Σ :=
  pointsto (PName k) (DfracOwn 1) (VName p t).
End LL.
End HL.
End HLo.
Import HLo.HL HLo.HL.ML HLo.HL.ML.CSL HLo.HL.LL.
Module HP.
Module HN.
Parameter store_keeps :
  ∀ {world : Type}, (mem → world → gmap piece pval → Prop) → Z → region → Prop.
Arguments store_keeps {world}%_type_scope wi%_function_scope b%_Z_scope reg.
Parameter literals :
  ∀ {Σ : gFunctors}, gen_heapGS piece pval Σ → region → region → iProp Σ.
Arguments literals {Σ gen_heapGS0} r3 r4.
Parameter name_cells :
  ∀ {Σ : gFunctors}, gen_heapGS piece pval Σ → region → region → region → Z → Z → ptr → ptr → ptr → iProp Σ.
Arguments name_cells {Σ gen_heapGS0} pn nreg sreg (nb sb)%_Z_scope x0 x1 y.
End HN.
End HP.
Module HV.
Parameter version_main_args :
  ptr → list word.
Arguments version_main_args stream.
End HV.
Definition fresh_ok := MainFacts.fresh_ok.
Definition greeting_ok := MainFacts.greeting_ok.
Definition operand_exit {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (registry : name -> option (contract libc_world)) (wi : mem -> libc_world -> gmap piece pval -> Prop)
  (ge : genv) (av : Z) (ar : region) (sargs : list argument) (b4 b6 : Z)
  (lab from : String.string) (P : Z -> Z -> Prop)
  (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  let _ := @nanofil_irisGS hlc Σ invGS_gen0 gen_heapGS0 libc_world registry wi ge in
  ∀ e ps cs a i g lose,
    ⌜loop_facts av sargs e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ P lose i⌝ -∗
    (pts (block_ps av ar 0 (argv_bytes ps) cs) ∗ pts (flat_map arg_ps sargs) ∗ pts (getopt_ps a i) ∗
     live b4 (mkRegion b4 (b4 + 16) Heap Live) ∗ pcell b4 0 g) -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom lab) (Some (TAtom from)))) :
      language.expr (nanofil_lang registry ge)) {{ Φ }}.
Arguments operand_exit {hlc Σ invGS_gen0 gen_heapGS0} registry wi ge av ar sargs b4 b6 lab from P Φ.
Parameter main_to_join :
  ∀ {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : gen_heapGS piece pval Σ}
  (registry : name → option (contract libc_world)) (wi : mem → libc_world → gmap piece pval → Prop),
  LG0.SafepointStable wi → ∀ ge : genv, let _ := @nanofil_irisGS hlc Σ invGS_gen0 gen_heapGS0 libc_world registry wi ge in
  hello_linked ge → (∀ (q : alloc_req) (m : mem) (wd : libc_world) (h : gmap piece pval) (base : Z), fresh m q
  base → wi m wd h → wi (allocated m q base) wd (overwrite (obj_ps base q) h)) → registry (TAtom "memset") =
  Some (memset_contract libc_world) → (∀ (b : Z) (reg : region) (o : Z) (xs : list Z) (cs : list cap) (m m' :
  mem) (wd : libc_world) (h : gmap piece pval), memset_result m {| ptr_addr := b + o; ptr_cap := Obj b |} 0 8
  m' → (∀ (l : piece) (v : pval), (l, v) ∈ block_ps b reg o xs cs → h !! l = Some v) → wi m wd h → wi m' wd
  (overwrite (block_ps b reg o (replicate 8 0) (clear_slots o cs)) h)) → registry (TAtom "strrchr") = Some
  (strrchr_contract libc_world) → registry (TAtom "memcmp") = Some (memcmp_contract libc_world) → registry
  (TAtom "strncmp") = Some (strncmp_contract libc_world) → ∀ (pn nreg sreg : region) (nb sb : Z), lookup
  (TAtom "program_invocation_name") (ge_globals ge) = Some {| ptr_addr := nb; ptr_cap := Obj nb |} → lookup
  (TAtom "program_invocation_short_name") (ge_globals ge) = Some {| ptr_addr := sb; ptr_cap := Obj sb |} →
  program_name_b + 8 <= r_end pn → 0 <= nb ∧ nb mod 8 = 0 ∧ nb + 8 <= r_end nreg <= 2 ^ 48 → 0 <= sb ∧ sb mod
  8 = 0 ∧ sb + 8 <= r_end sreg <= 2 ^ 48 → HP.HN.store_keeps wi program_name_b pn → HP.HN.store_keeps wi nb
  nreg → HP.HN.store_keeps wi sb sreg → ∀ (rep : mem → libc_world → Prop) (requests : list word → mem →
  libc_world → Z → Z → Prop), registry (TAtom "setlocale") = Some (libc_setlocale_contract rep requests) → (∀
  (m : mem) (w : libc_world) (h : gmap piece pval) (k : Z) (p : ptr) (t : list Z), wi m w h → live_disjoint m
  → objects_fit (m_regions m) → freed_empty (m_regions m) → h !! PName k = Some (VName p t) → lent_at m h p t)
  → (∀ (m : mem) (w : libc_world) (h : gmap piece pval) (c : Z) (p : ptr) (b : Z) (reg : region) (bytes : list
  Z), wi m w h → In c locale_categories → string_ok p b reg bytes → all_agree m (string_ps p b reg bytes) →
  libc_setlocale_pre rep [WInt c; WPtr p] m w) → (∀ (r : call_result) (args : list arg) (c : Z) (p : ptr) (s :
  R.state) (m : mem) (w : libc_world) (h : gmap piece pval) (trace : list event) (values : list word) (s' :
  R.state) (m' : mem) (w' : libc_world), wi m w h → agrees m h → live_disjoint m → R.ready s m → M.E.invoke
  (libc_setlocale_contract rep requests) r args [WInt c; WPtr p] s m w trace (CallReturn values) s' m' w' → ∃
  (q : ptr) (new : Z → ptr * list Z) (c' : term), values = [WPtr q] ∧ (q = {| ptr_addr := 0; ptr_cap := CNone
  |} ∨ q = (new c).1) ∧ agrees m' h ∧ live_disjoint m' ∧ R.ready s' m' ∧ wi m' w' (overwrite (codec_ps c')
  (rename h locale_categories new))) → (∀ (b : Z) (reg : region) (o : Z) (x xp : ptr) (m : mem) (wd :
  libc_world) (h : gmap piece pval), (∀ (l : piece) (v : pval), (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o,
  VAux (ptr_cap x)) :: cell b o (ptr_addr x) → h !! l = Some v) → wi m wd h → wi (store_bytes (store_aux m (b
  + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux
  (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)) → ∀ atexit_spec : contract libc_world, registry (TAtom
  "atexit") = Some atexit_spec → contract_returns atexit_spec = RClass W → contract_abi atexit_spec (CResult
  (TAtom "v15") W) [Arg P (Tmp (TAtom "v14"))] → (∀ (m : mem) (w : libc_world) (h : gmap piece pval), wi m w h
  → contract_pre atexit_spec [WPtr close_stdout_ptr] m w) → (∀ (r : call_result) (args : list arg) (s :
  R.state) (m : mem) (w : libc_world) (h : gmap piece pval) (trace : list event) (values : list word) (s' :
  R.state) (m' : mem) (w' : libc_world), wi m w h → agrees m h → live_disjoint m → R.ready s m → M.E.invoke
  atexit_spec r args [WPtr close_stdout_ptr] s m w trace (CallReturn values) s' m' w' → ∃ x : Z, values =
  [WInt x] ∧ 0 <= x < 2 ^ 32 ∧ agrees m' h ∧ live_disjoint m' ∧ R.ready s' m' ∧ wi m' w' h) → ∀ (av : Z) (ar :
  region) (sargs : list argument), 0 < av ∧ av mod 8 = 0 ∧ av + 8 * (length sargs + 1) <= r_end ar <= 2 ^ 48 →
  1 <= length sargs < 2 ^ 31 → Forall (λ s : argument, string_ok (arg_ptr s) (arg_base s) (arg_region s)
  (arg_text s)) sargs → ∀ (initialized running : mem → libc_world → Prop) (grequests : list word → mem →
  libc_world → Z → Z → Prop) (transition : list word → mem → libc_world → list Z → list event → list word →
  mem → libc_world → Prop), registry (TAtom "getopt_long") = Some (libc_getopt_refined_contract (hello_input
  av sargs) initialized running grequests transition) → ∀ optarg_cell optind_cell : ptr, (∀ (m : mem) (w :
  libc_world) (h : gmap piece pval), wi m w h → getopt_state_at m (libc_getopt_view w) ∧ getopt_optarg_cell
  (libc_getopt_view w) = optarg_cell ∧ getopt_optind_cell (libc_getopt_view w) = optind_cell ∧ getopt_current
  (libc_getopt_view w) h) → (∀ (m : mem) (w : libc_world) (h : gmap piece pval), wi m w h → hello_table_at m)
  → (∀ (m : mem) (w : libc_world) (h : gmap piece pval) (xs : list Z) (cs : list cap), wi m w h → agrees m h →
  live_disjoint m → (∀ (l : piece) (v : pval), ( l, v) ∈ block_ps av ar 0 xs cs ++ flat_map arg_ps sargs → h
  !! l = Some v) → getopt_input_at m (hello_input av sargs) → libc_getopt_rep initialized m w ∧ Forall
  (writable_span m) (getopt_roots (libc_getopt_view w)) ∧ Forall (λ s : span, readable_bytes m (span_ptr s)
  (span_size s)) (getopt_reads (libc_getopt_view w)) ∧ getopt_separated (hello_input av sargs)
  (libc_getopt_view w) ∧ getopt_disjoint (getopt_public_writes (hello_input av sargs) (libc_getopt_view w)) ∧
  getopt_private_owned m (hello_input av sargs) (libc_getopt_view w)) → (∀ (m : mem) (w : libc_world) (h :
  gmap piece pval), wi m w h → (∀ (s : span) (a : Z), In s (getopt_roots (libc_getopt_view w) ++ getopt_cells
  (libc_getopt_view w)) → span_contains s a → ¬ owned_live h m a) ∧ ids_apart (getopt_owned (libc_getopt_view
  w)) h) → (∀ (r : call_result) (args : list arg) (xs : list word) (s : R.state) (m : mem) (w : libc_world) (h
  : gmap piece pval) (trace : list event) (values : list word) (s' : R.state) (m' : mem) (w' : libc_world) (bs
  : list Z) (cs : list cap), M.E.invoke (libc_getopt_refined_contract (hello_input av sargs) initialized
  running grequests transition) r args xs s m w trace (CallReturn values) s' m' w' → (∀ (l : piece) (v :
  pval), ( l, v) ∈ block_ps av ar 0 bs cs → h !! l = Some v) → wi m w h → agrees m h → live_disjoint m →
  R.ready s m → wi m' w' (overwrite (block_ps av ar 0 (mem_bytes m' av (8 * (length sargs + 1))) (mem_auxes m'
  av (8 * (length sargs + 1))) ++ getopt_ps (getopt_optarg (libc_getopt_view w')) (getopt_optind
  (libc_getopt_view w'))) h)) → lookup (TAtom "optarg") (ge_globals ge) = Some optarg_cell → 0 <= ptr_addr
  optarg_cell < 2 ^ 64 ∧ 0 <= ptr_addr optind_cell < 2 ^ 64 → lookup (TAtom "optind") (ge_globals ge) = Some
  optind_cell → ∀ exit_spec : contract libc_world, registry (TAtom "exit") = Some exit_spec → (∀ v : value,
  contract_abi exit_spec CVoid [Arg W v]) → (∀ (n : Z) (m : mem) (w : libc_world) (h : gmap piece pval), 0 <=
  n < 2 ^ 32 → wi m w h → contract_pre exit_spec [WInt n] m w) → (∀ (args : list arg) (n : Z) (s : R.state) (m
  : mem) (w : libc_world) (tr : list event) (vs : list word) (s' : R.state) (m' : mem) (w' : libc_world),
  M.E.invoke exit_spec CVoid args [ WInt n] s m w tr (CallReturn vs) s' m' w' → False) → ∀ stdout_cell stream
  : ptr, lookup (TAtom "stdout") (ge_globals ge) = Some stdout_cell → (∀ (m : mem) (w : libc_world) (h : gmap
  piece pval), wi m w h → access_res m (raw_address (ptr_addr stdout_cell) 0) (ptr_cap stdout_cell) 8 Read 8 =
  Some ok ∧ pointer_load_effects m (raw_address (ptr_addr stdout_cell) 0) [AuxRead; LowerResolve; AddressRead]
  = Some stream) → ∀ (version_ps : list (piece * pval)) (author_reg : String.string → region), (∀ s :
  String.string, In s ["hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75"] → ( PLive (ptr_addr
  (version_literal s)), VLive (author_reg s)) ∈ version_ps) → ∀ version_spec : name → contract libc_world, (∀
  (g : name) (xs : list word), In ( g, xs) (version_output_args stream) → registry g = Some (version_spec g))
  → (∀ (g : name) (xs : list word), In ( g, xs) (version_output_args stream) → contract_returns (version_spec
  g) = RClass W) → (∀ (g : name) (xs : list word) (d : name) (args : list arg), In ( g, xs)
  (version_output_args stream) → map (λ a : arg, match a with | Arg k _ => k end) args =
  version_output_classes xs → contract_abi (version_spec g) (CResult d W) args) → (∀ (g : name) (xs : list
  word) (m : mem) (w : libc_world) (h : gmap piece pval), In ( g, xs) (version_output_args stream) → (∀ (l :
  piece) (v : pval), (l, v) ∈ version_ps → h !! l = Some v) → agrees m h → wi m w h → contract_pre
  (version_spec g) xs m w) → (∀ (g : name) (xs : list word) (r : call_result) (args : list arg) (s : R.state)
  (m : mem) (w : libc_world) (h : gmap piece pval) (trace : list event) (values : list word) (s' : R.state)
  (m' : mem) (w' : libc_world), In ( g, xs) (version_output_args stream) → agrees m h → live_disjoint m →
  R.ready s m → wi m w h → M.E.invoke (version_spec g) r args xs s m w trace (CallReturn values) s' m' w' →
  agrees m' h ∧ live_disjoint m' ∧ R.ready s' m' ∧ wi m' w' h ∧ ∃ n : Z, values = [WInt n] ∧ 0 <= n < 2 ^ 32)
  → (∀ (size : Z) (m : mem) (wd : libc_world) (h : gmap piece pval) (base : Z), In size [24; 80] → fresh m
  (heap_req 8 size) base → wi m wd h → wi (allocated m (heap_req 8 size) base) wd (overwrite (obj_ps base
  (heap_req 8 size)) h)) → (∀ (b : Z) (reg : region) (o : Z) (x xp : ptr) (m : mem) (wd : libc_world) (h :
  gmap piece pval), (∀ (k : piece) (v : pval), ( k, v) ∈ [( PLive b, VLive reg)] ++ ( PAux b o, VAux (ptr_cap
  x)) :: cell b o (ptr_addr x) → h !! k = Some v) → wi m wd h → wi (store_bytes (store_aux m (b + o) (ptr_cap
  xp)) (b + o) 8 (ptr_addr xp)) wd (overwrite ([( PLive b, VLive reg)] ++ ( PAux b o, VAux (ptr_cap xp)) ::
  cell b o (ptr_addr xp)) h)) → (∀ (cb : Z) (cr : region) (sb0 off : Z) (m : mem) (wd : libc_world) (h : gmap
  piece pval), (∀ (k : piece) (v : pval), ( k, v) ∈ va_cursor_ps cb cr {| ptr_addr := sb0 + off; ptr_cap := Ro
  sb0 |} → h !! k = Some v) → wi m wd h → wi (store_bytes m cb 8 (sb0 + off + 8)) wd (overwrite (va_cursor_ps
  cb cr {| ptr_addr := sb0 + off + 8; ptr_cap := Ro sb0 |}) h)) → (∀ (m : mem) (wd : libc_world) (h : gmap
  piece pval) (sb0 : Z), fresh m (heap_req 16 72) sb0 → wi m wd h → wi (snapshot_values (HV.version_main_args
  stream) sb0 (allocated m (heap_req 16 72) sb0)) wd (overwrite (snapshot_ps (HV.version_main_args stream) sb0
  (heap_req 16 72)) h)) → (∀ (m : mem) (w : libc_world) (h : gmap piece pval) (p : ptr) (t : list Z), wi m w h
  → h !! PName 5 = Some (VName p t) → contract_pre (libc_setlocale_contract rep requests) [ WInt 5; WPtr null]
  m w) → (∀ (r : call_result) (args : list arg) (s : R.state) (m : mem) (w : libc_world) (h : gmap piece pval)
  (p : ptr) (t : list Z) (trace : list event) (ending : call_end) (s' : R.state) (m' : mem) (w' : libc_world),
  wi m w h → h !! PName 5 = Some (VName p t) → M.E.invoke (libc_setlocale_contract rep requests) r args [WInt
  5; WPtr null] s m w trace ending s' m' w' → s' = s ∧ m' = m ∧ w' = w ∧ ending = CallReturn [WPtr p]) → ∀
  stderr_cell errstream : ptr, lookup (TAtom "stderr") (ge_globals ge) = Some stderr_cell → (∀ (m : mem) (w :
  libc_world) (h : gmap piece pval), wi m w h → access_res m (raw_address (ptr_addr stderr_cell) 0) (ptr_cap
  stderr_cell) 8 Read 8 = Some ok ∧ pointer_load_effects m (raw_address (ptr_addr stderr_cell) 0) [AuxRead;
  LowerResolve; AddressRead] = Some errstream) → ∀ (help_ps : list (piece * pval)) (output_spec : name →
  contract libc_world), (∀ (pname : ptr) (g : name) (xs : list word), In ( g, xs) (main_output_args stream
  errstream pname) → registry g = Some (output_spec g)) → (∀ (pname : ptr) (g : name) (xs : list word), In (
  g, xs) (main_output_args stream errstream pname) → contract_returns (output_spec g) = RClass W) → (∀ (pname
  : ptr) (g : name) (xs : list word) (d : name) (args : list arg), In ( g, xs) (main_output_args stream
  errstream pname) → map (λ a : arg, match a with | Arg k _ => k end) args = replicate (length xs) P →
  contract_abi (output_spec g) (CResult d W) args) → (∀ (pname : ptr) (g : name) (xs : list word) (m : mem) (w
  : libc_world) (h : gmap piece pval), name_ok sargs pname → In ( g, xs) (main_output_args stream errstream
  pname) → (∀ (l : piece) (v : pval), ( l, v) ∈ help_ps ++ flat_map arg_ps sargs → h !! l = Some v) → agrees m
  h → wi m w h → contract_pre (output_spec g) xs m w) → (∀ (pname : ptr) (g : name) (xs : list word) (r :
  call_result) (args : list arg) (s : R.state) (m : mem) (w : libc_world) (h : gmap piece pval) (trace : list
  event) (values : list word) (s' : R.state) (m' : mem) (w' : libc_world), In ( g, xs) (main_output_args
  stream errstream pname) → agrees m h → live_disjoint m → R.ready s m → wi m w h → M.E.invoke (output_spec g)
  r args xs s m w trace (CallReturn values) s' m' w' → agrees m' h ∧ live_disjoint m' ∧ R.ready s' m' ∧ wi m'
  w' h ∧ ∃ n : Z, values = [WInt n] ∧ 0 <= n < 2 ^ 32) → (∀ (g : name) (xs : list word), In ( g, xs)
  (emit_output_args stream) → registry g = Some (output_spec g)) → (∀ (g : name) (xs : list word), In ( g, xs)
  (emit_output_args stream) → contract_returns (output_spec g) = RClass W) → (∀ (g : name) (xs : list word) (d
  : name) (args : list arg), In ( g, xs) (emit_output_args stream) → map (λ a : arg, match a with | Arg k _ =>
  k end) args = replicate (length xs) P → contract_abi (output_spec g) (CResult d W) args) → (∀ (g : name) (xs
  : list word) (m : mem) (w : libc_world) (h : gmap piece pval), In ( g, xs) (emit_output_args stream) → (∀ (l
  : piece) (v : pval), (l, v) ∈ help_ps → h !! l = Some v) → agrees m h → wi m w h → contract_pre (output_spec
  g) xs m w) → (∀ (g : name) (xs : list word) (r : call_result) (args : list arg) (s : R.state) (m : mem) (w :
  libc_world) (h : gmap piece pval) (trace : list event) (values : list word) (s' : R.state) (m' : mem) (w' :
  libc_world), In ( g, xs) (emit_output_args stream) → agrees m h → live_disjoint m → R.ready s m → wi m w h →
  M.E.invoke (output_spec g) r args xs s m w trace (CallReturn values) s' m' w' → agrees m' h ∧ live_disjoint
  m' ∧ R.ready s' m' ∧ wi m' w' h ∧ ∃ n : Z, values = [WInt n] ∧ 0 <= n < 2 ^ 32) → ∀ diag_spec : contract
  libc_world, registry (TAtom "error") = Some diag_spec → contract_returns diag_spec = RVoid → (∀ args : list
  arg, map (λ a : arg, match a with | Arg k _ => k end) args = [ W; W; P; P; P] → contract_abi diag_spec CVoid
  args) → (∀ (q : ptr) (m : mem) (w : libc_world) (h : gmap piece pval), In q (map arg_ptr sargs) → (∀ (l :
  piece) (v : pval), ( l, v) ∈ help_ps ++ flat_map arg_ps sargs → h !! l = Some v) → agrees m h → wi m w h →
  contract_pre diag_spec [WInt 0; WInt 0; WPtr (version_literal "hello#str.77"); WPtr (version_literal
  "hello#str.78"); WPtr q] m w) → (∀ (q : ptr) (args : list arg) (s : R.state) (m : mem) (w : libc_world) (h :
  gmap piece pval) (tr : list event) (vs : list word) (s' : R.state) (m' : mem) (w' : libc_world), In q (map
  arg_ptr sargs) → agrees m h → live_disjoint m → R.ready s m → wi m w h → M.E.invoke diag_spec CVoid args
  [WInt 0; WInt 0; WPtr (version_literal "hello#str.77"); WPtr (version_literal "hello#str.78"); WPtr q] s m w
  tr (CallReturn vs) s' m' w' → vs = [] ∧ agrees m' h ∧ live_disjoint m' ∧ R.ready s' m' ∧ wi m' w' h) → ∀ (s0
  : argument) (srest : list argument) (r3 r4 : region) (x0 x1 y0 : ptr) (old : Z → ptr * list Z) (c0 : term)
  (r80 : region) (cs0 : list cap) (a : ptr) (ix b61 : Z) (r61 : region) (Φ : val (nanofil_lang registry ge) →
  iProp Σ), sargs = s0 :: srest → argv_caps cs0 (map arg_ptr sargs) → 0 <= ix <= length sargs → pts (block_ps
  av ar 0 (argv_bytes (map arg_ptr sargs)) cs0) -∗ pts (flat_map arg_ps sargs) -∗ pts (getopt_ps a ix) -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗ ([∗ list] k ∈ locale_categories,
  named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗ string empty_ptr 69968 r80 [] -∗ pts version_ps -∗ pts
  help_ps -∗ string (version_literal "hello#str.61") b61 r61 [101; 110; 95] -∗ ▷ (∀ (e : env) (b4 b6 : Z) (i k
  : nat) (q : ptr) (new : Z → ptr * list Z) (c' : term), ⌜ start_vars e (length sargs) av b4 b6 ∧ lookup
  (TAtom "chk1") e = Some (WPtr {| ptr_addr := b4; ptr_cap := Obj b4 |}) ∧ fresh_ok b4 ∧ fresh_ok b6 ∧ (i <=
  length (arg_text s0))%nat ∧ (k <= length (arg_text s0))%nat ∧ (q = {| ptr_addr := 0; ptr_cap := CNone |} ∨ q
  = (new 6).1)⌝ -∗ HP.HN.literals r3 r4 -∗ ([∗ list] k0 ∈ locale_categories, lent k0 (new k0).1 (new k0).2) -∗
  pts (codec_ps c') -∗ string empty_ptr 69968 r80 [] -∗ bytes b4 8 (replicate 8 0) -∗ auxes b4 1 (replicate 15
  CNone) -∗ LG0.live b6 {| r_base := b6; r_end := b6 + 16; r_kind := Heap; r_life := Live |} -∗ bytes b6 0
  (replicate 8 0) -∗ bytes b6 8 (replicate 8 0) -∗ auxes b6 0 (clear_slots 0 (replicate 8 CNone)) -∗ auxes b6
  8 (replicate 8 CNone) -∗ operand_exit registry wi ge av ar sargs b4 b6 "iw_1.join" "iw_1.L60" (λ lose i0 :
  Z, (lose = 0 ∧ i0 = length sargs)%type) Φ) -∗ WP ERun (invocation main_fn [WInt (length sargs); WPtr {|
  ptr_addr := av; ptr_cap := Obj av |}]) : language.expr (nanofil_lang registry ge) {{ v, Φ v }}.
Arguments main_to_join {hlc Σ invGS_gen0 gen_heapGS0} (registry wi)%_function_scope {SafepointStable0}
  ge Hlinked Kalloc%_function_scope Hmemset Kmemset%_function_scope Hstrrchr Hmemcmp Hstrncmp
  pn nreg sreg (nb sb)%_Z_scope Hnb Hsb Hpn_end Hnb_cell Hsb_cell Kpn Knb Ksb (rep requests)%_function_scope
  Hsetlocale (Hlent Hset_pre Kset Kpstore)%_function_scope atexit_spec Hatexit Hatexit_ret
  Hatexit_abi (Hatexit_pre Katexit)%_function_scope av%_Z_scope ar sargs%_list_scope Hav Hargc
  Hargs (initialized running grequests transition)%_function_scope Hgetopt optarg_cell optind_cell
  (Hgetopt_wi Htable Hgetopt_env Hgetopt_apart Kgetopt)%_function_scope Hoptarg_g Hcells Hoptind_g
  exit_spec Hexit (Hexit_abi Hexit_pre Hexit_post)%_function_scope stdout_cell stream Hstdout_g
  wi_stdout%_function_scope version_ps%_list_scope
  (author_reg Hauthor_live version_spec Hversion_reg Hversion_ret Hversion_abi Hversion_pre Hversion_frame
   Kversion_alloc Kversion_store Kversion_cursor Kversion_snapshot Hquery_pre Hquery)%_function_scope
  stderr_cell errstream Hstderr_g wi_stderr%_function_scope help_ps%_list_scope
  (output_spec Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame Houtput_reg Houtput_ret Houtput_abi Houtput_pre
   Houtput_frame)%_function_scope
  diag_spec Hdiag_reg Hdiag_ret (Hdiag_abi Hdiag_pre Hdiag_post)%_function_scope s0 srest%_list_scope
  r3 r4 x0 x1 y0 old%_function_scope c0 r80 cs0%_list_scope a (ix b61)%_Z_scope r61 Φ%_function_scope
  _ _ _.
End HM.
Import HM HM.LG0 HM.LG0.L HM.HLo.HL HM.HLo.HL.ML HM.HLo.HL.ML.CSL.
Module HC.
Module LB.
Definition errno_contract (rep : mem -> libc_world -> Prop) : contract libc_world :=
  errno_location_contract libc_world (fun w => libc_errno (fst w)) (libc_ready rep).
End LB.
Parameter rpl_mbsrtowcs_spec :
  ∀ {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : gen_heapGS piece pval Σ}
  (registry : name → option (contract libc_world)) (wi : mem → libc_world → gmap piece pval → Prop),
  LG0.SafepointStable wi → ∀ (ge : genv), let _ := @nanofil_irisGS hlc Σ invGS_gen0 gen_heapGS0 libc_world registry wi ge in
  ∀ (valid : term → list Z → Prop) (audit : term → option audited_codec) (rep : mem → libc_world → Prop)
  (requests : list word → mem → libc_world → Z → Z → Prop), registry (TAtom "mbrtowc") = Some
  (mbrtowc_contract valid audit rep requests) → mbstate_zero_valid valid → mbstate_valid_bytes valid → ∀ errno
  : ptr, (∀ (m : mem) (w : libc_world) (h : gmap piece pval), wi m w h → libc_ready rep m w ∧ codec_current
  (libc_locale w.1) h ∧ libc_errno w.1 = errno ∧ libc_private m w h) → (∀ (m : mem) (w : libc_world) (h : gmap
  piece pval), wi m w h → hello_codec_profile audit w) → (∀ (r : call_result) (args : list arg) (out src :
  ptr) (n : Z) (state : ptr) (s : R.state) (m : mem) (w : libc_world) (h : gmap piece pval) (trace : list
  event) (values : list word) (s' : R.state) (m' : mem) (w' : libc_world) (bo : Z) (ro : region) (oo : Z) (xo
  : list Z) (co : list cap) (bs : Z) (rs : region) (os : Z) (ys : list Z) (cs : list cap) (be : Z) (re :
  region) (oe : Z) (xe : list Z) (ce : list cap), L.M.E.invoke (mbrtowc_contract valid audit rep requests) r
  args [WPtr out; WPtr src; WInt n; WPtr state] s m w trace (CallReturn values) s' m' w' → (∀ (l : piece) (v :
  pval), (l, v) ∈ block_ps bo ro oo xo co ++ block_ps bs rs os ys cs ++ block_ps be re oe xe ce → h !! l =
  Some v) → wi m w h → wi m' w' (overwrite (block_ps bo ro oo (mem_bytes m' (bo + oo) 4) (mem_auxes m' (bo +
  oo) 4) ++ block_ps bs rs os (mem_bytes m' (bs + os) 8) (mem_auxes m' (bs + os) 8) ++ block_ps be re oe
  (mem_bytes m' (be + oe) 4) (mem_auxes m' (be + oe) 4)) h)) → hello_linked ge → (∀ (m : mem) (w : libc_world)
  (h : gmap piece pval) (k : Z) (p : ptr) (t : list Z), wi m w h → live_disjoint m → objects_fit (m_regions m)
  → freed_empty (m_regions m) → h !! PName k = Some (VName p t) → lent_at m h p t) → ∀ set_spec : contract
  libc_world, registry (TAtom "setlocale") = Some set_spec → contract_returns set_spec = RClass P → (∀ (d :
  name) (c v : value), contract_abi set_spec (CResult d P) [Arg W c; Arg P v]) → (∀ (m : mem) (w : libc_world)
  (h : gmap piece pval) (k : Z) (p : ptr) (t : list Z) (z : ptr), wi m w h → h !! PName k = Some (VName p t) →
  ptr_addr z = 0 → contract_pre set_spec [WInt k; WPtr z] m w) → (∀ (r : call_result) (args : list arg) (s :
  R.state) (m : mem) (w : libc_world) (h : gmap piece pval) (k : Z) (p : ptr) (t : list Z) (z : ptr) (trace :
  list event) (ending : call_end) (s' : R.state) (m' : mem) (w' : libc_world), wi m w h → h !! PName k = Some
  (VName p t) → ptr_addr z = 0 → L.M.E.invoke set_spec r args [ WInt k; WPtr z] s m w trace ending s' m' w' →
  s' = s ∧ m' = m ∧ w' = w ∧ ending = CallReturn [WPtr p]) → registry (TAtom "strlen") = Some (strlen_contract
  libc_world) → registry (TAtom "memcpy") = Some (memcpy_contract libc_world) → registry (TAtom "strcmp") =
  Some (strcmp_contract libc_world) → (∀ (b : Z) (reg : region) (o : Z) (xs : list Z) (cs : list cap) (s :
  ptr) (n : Z) (m m' : mem) (wd : libc_world) (h : gmap piece pval) (ys : list Z), copy_result m {| ptr_addr
  := b + o; ptr_cap := Obj b |} s n m' → (∀ (l : piece) (v : pval), (l, v) ∈ block_ps b reg o xs cs → h !! l =
  Some v) → wi m wd h → length ys = length xs → wi m' wd (overwrite (block_ps b reg o ys (slots_after m' b o
  (length xs))) h)) → (∀ (b : Z) (reg : region) (o x y : Z) (m : mem) (wd : libc_world) (h : gmap piece pval),
  (∀ (l : piece) (v : pval), (l, v) ∈ [(PLive b, VLive reg); (PByte b o, VByte x)] → h !! l = Some v) → wi m
  wd h → wi (store_bytes m (b + o) 1 y) wd (overwrite [(PLive b, VLive reg); (PByte b o, VByte (y mod 256))]
  h)) → (∀ (b : Z) (reg : region) (o : Z) (xs : list Z) (y : Z) (m : mem) (wd : libc_world) (h : gmap piece
  pval), (∀ (l : piece) (v : pval), (l, v) ∈ (PLive b, VLive reg) :: byte_ps b o xs → h !! l = Some v) → wi m
  wd h → wi (store_bytes m (b + o) 4 y) wd (overwrite ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 4)) h))
  → (∀ (q : alloc_req) (m : mem) (wd : libc_world) (h : gmap piece pval) (base : Z), fresh m q base → wi m wd
  h → wi (allocated m q base) wd (overwrite (obj_ps base q) h)) → registry (TAtom "memchr") = Some
  (memchr_contract libc_world) → registry (TAtom "__errno_location") = Some (LB.errno_contract rep) → (∀ (b :
  Z) (reg : region) (o : Z) (x xp : ptr) (m : mem) (wd : libc_world) (h : gmap piece pval), (∀ (l : piece) (v
  : pval), (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) → h !! l =
  Some v) → wi m wd h → wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
  (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)) → ∀ (p :
  ptr) (b : Z) (reg : region) (bs : list Z) (bd : Z) (rd : region) (ws : list Z) (cws : list cap) (sb : Z) (sr
  : region) (so : Z) (ys : list Z) (cs : list cap) (be : Z) (re : region) (oe : Z) (xe : list Z) (ce : list
  cap) (spb : Z) (spr : region) (spo : Z) (codec : term) (dq : dfrac) (p0 : ptr) (t0 : list Z) (rc rp :
  region) (Φ : outcome → iPropI Σ), errno = {| ptr_addr := be + oe; ptr_cap := Obj be |} → 0 < bd → bd mod 4 =
  0 → bd + 4 * (length bs + 1) <= r_end rd → r_end rd <= 2 ^ 48 → 0 < sb → 0 <= so → (sb + so) mod 4 = 0 → sb
  + so + 8 <= r_end sr → r_end sr <= 2 ^ 48 → 0 < spb → 0 <= spo → (spb + spo) mod 8 = 0 → spb + spo + 8 <=
  r_end spr → r_end spr <= 2 ^ 48 → 0 < be → 0 <= oe → be + oe + 4 <= r_end re → r_end re <= 2 ^ 48 → length
  ws = (4 * (length bs + 1))%nat → length cws = (4 * (length bs + 1))%nat → valid codec ys → le_value (take 4
  ys) = 0 → length ys = 8%nat → length cs = 8%nat → length xe = 4%nat → length ce = 4%nat → LL.lent 0 p0 t0 -∗
  CSL.string c_ptr 65824 rc c_bytes -∗ CSL.string posix_ptr 65856 rp posix_bytes -∗ pointsto (PName codec_key)
  dq (VCodec codec) -∗ CSL.string p b reg bs -∗ LG0.live bd rd -∗ ML.bytes bd 0 ws -∗ ML.auxes bd 0 cws -∗ pts
  (block_ps sb sr so ys cs) -∗ pts (block_ps be re oe xe ce) -∗ LG0.live spb spr -∗ LG0.pcell spb spo p -∗ (∀
  (r : Z) (ws' : list Z) (cws' : list cap) (ys' : list Z) (cs' : list cap) (xe' : list Z) (ce' : list cap) (x'
  : ptr), ⌜ ((r = 2 ^ 64 - 1 ∧ le_value xe' = 84) ∨
    (exists k : nat, r = Z.of_nat k ∧ (k <= length bs)%nat ∧ wide_ok (take (4 * k) ws') ∧
     le_value (take 4 (drop (4 * k) ws')) = 0)) ∧ length ws' = (4 * (length bs + 1))%nat ∧ length xe' = 4%nat⌝ -∗
  CSL.string c_ptr 65824 rc c_bytes -∗ CSL.string posix_ptr 65856 rp posix_bytes -∗ pointsto (PName codec_key)
  dq (VCodec codec) -∗ CSL.string p b reg bs -∗ LG0.live bd rd -∗ ML.bytes bd 0 ws' -∗ ML.auxes bd 0 cws' -∗
  pts (block_ps sb sr so ys' cs') -∗ pts (block_ps be re oe xe' ce') -∗ LG0.live spb spr -∗ LG0.pcell spb spo
  x' -∗ Φ (Ret (WInt r))) -∗ WP L.ERun (invocation mbs_fn [WPtr {| ptr_addr := bd; ptr_cap := Obj bd |}; WPtr
  {| ptr_addr := spb + spo; ptr_cap := Obj spb |}; WInt (length bs + 1); WPtr {| ptr_addr := sb + so; ptr_cap
  := Obj sb |}]) : language.expr (L.nanofil_lang registry ge) {{ v, Φ v }}.
Arguments rpl_mbsrtowcs_spec {hlc Σ invGS_gen0 gen_heapGS0} (registry wi)%_function_scope
  {SafepointStable0} ge (valid audit rep requests)%_function_scope Hmbrtowc Hvalid0 Hbytes
  errno (Hlibc Haudit Kmbrtowc)%_function_scope Hlinked wi_lent%_function_scope set_spec Hset
  Hset_ret (Hset_abi Hset_pre Hset_query)%_function_scope Hstrlen Hmemcpy Hstrcmp
  (Kcopy Kbyte Kstore Kalloc)%_function_scope Hmemchr Herrno_reg Kpstore%_function_scope p
  b%_Z_scope reg bs%_list_scope bd%_Z_scope rd (ws cws)%_list_scope sb%_Z_scope sr so%_Z_scope
  (ys cs)%_list_scope be%_Z_scope re oe%_Z_scope (xe ce)%_list_scope spb%_Z_scope spr spo%_Z_scope
  codec dq p0 t0%_list_scope rc rp Φ%_function_scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  _ _ _ _ _ _ _ _.
End HC.
Module HCl.
Parameter wp_close_errno :
  ∀ {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : gen_heapGS piece pval Σ}
  {world : Type} (registry : name → option (contract world)) (wi : mem → world → gmap piece pval → Prop),
  LG0.SafepointStable wi → ∀ (ge : genv), let _ := @nanofil_irisGS hlc Σ invGS_gen0 gen_heapGS0 world registry
  wi ge in ∀ (eb eo : Z) (cell : world → ptr) (rep : mem → world → Prop), registry (TAtom "__errno_location")
  = Some (errno_location_contract world cell rep) → hello_linked ge → (∀ (m : mem) (w : world) (h : gmap piece
  pval), wi m w h → cell w = {| ptr_addr := eb + eo; ptr_cap := Obj eb |}) → (∀ (m : mem) (w : world) (h :
  gmap piece pval), wi m w h → rep m w ∧ errno_cell m (cell w)) → ∀ (f : func) (e : list (name * word)) (ls :
  list (name * option Z)) (lab d : name) (rest : list inst) (j : jump) (Φ : val (L.nanofil_lang registry ge) →
  iPropI Σ), ▷ WP L.ERun {| fr_fn := f; fr_env := put d (WPtr {| ptr_addr := eb + eo; ptr_cap := Obj eb |}) e;
  fr_locals := ls; fr_doomed := None; fr_at := Exec lab rest j |} : language.expr (L.nanofil_lang registry ge)
  {{ v, Φ v }} -∗ WP L.ERun {| fr_fn := f; fr_env := e; fr_locals := ls; fr_doomed := None; fr_at := Exec lab
  (Call (CResult d P) (Global (TAtom "__errno_location")) [] :: rest) j |} : language.expr (L.nanofil_lang
  registry ge) {{ v, Φ v }}.
Arguments wp_close_errno {hlc Σ invGS_gen0 gen_heapGS0} {world}%_type_scope (registry wi)%_function_scope
  {SafepointStable0} ge (eb eo)%_Z_scope (cell rep)%_function_scope Herrno Hlinked (Hcell Hrep)%_function_scope
  f (e ls)%_list_scope lab d rest%_list_scope j Φ%_function_scope.
Parameter wp_close_load_w :
  ∀ {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {gen_heapGS0 : gen_heapGS piece pval Σ}
  {world : Type} (registry : name → option (contract world)) (wi : mem → world → gmap piece pval → Prop),
  LG0.SafepointStable wi → ∀ (ge : genv), let _ := @nanofil_irisGS hlc Σ invGS_gen0 gen_heapGS0 world registry
  wi ge in ∀ (f : func) (e : env) (ls : list (name * option Z)) (lab d : name) (v : value) (rest : list inst)
  (j : jump) (b : Z) (reg : region) (o : Z) (xs : list Z) (Φ : val (L.nanofil_lang registry ge) → iPropI Σ),
  value_x ge e A v = Some (WPtr {| ptr_addr := b + o; ptr_cap := Obj b |}) → 0 <= b + o < 2 ^ 64 → length xs =
  4%nat → LG0.live b reg -∗ ML.bytes b o xs -∗ ▷ (LG0.live b reg -∗ ML.bytes b o xs -∗ WP L.ERun {| fr_fn :=
  f; fr_env := put d (WInt (close_w xs)) e; fr_locals := ls; fr_doomed := None; fr_at := Exec lab rest j |} :
  language.expr (L.nanofil_lang registry ge) {{ v, Φ v }}) -∗ WP L.ERun {| fr_fn := f; fr_env := e; fr_locals
  := ls; fr_doomed := None; fr_at := Exec lab (Let d W (RawLoad (LdNarrow Sw) 0) [v] :: rest) j |} :
  language.expr (L.nanofil_lang registry ge) {{ v, Φ v }}.
Arguments wp_close_load_w {hlc Σ invGS_gen0 gen_heapGS0} {world}%_type_scope (registry wi)%_function_scope
  {SafepointStable0} ge f e ls%_list_scope lab d v rest%_list_scope j b%_Z_scope reg o%_Z_scope
  xs%_list_scope Φ%_function_scope _ _ _.
End HCl.
Definition join_irisGS (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) (ge : genv)
  {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} := nanofil_irisGS registry wi ge.
End HelloJoinBase.
