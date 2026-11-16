(** GNU Hello initializes its memory before converting and printing the greeting.
    These proofs connect initialization to output and establish safety for every execution length. *)

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

From Nanofil Require Import HelloJoinInterface HelloJoinFacts HelloMainBase HelloMainFacts.
Import MainDefinitions MainFacts JoinDefinitions.
From Nanofil Require Import HelloJoinFinish.
Module HelloJoinComplete (R : Runtime) (B : HelloJoinBase R).
Import B B.HM B.HM.LG0 B.HM.LG0.L B.HM.HLo.HL B.HM.HLo.HL.ML B.HM.HLo.HL.ML.CSL.
Local Hint Opaque pts bytes auxes live pcell main_fn xmalloc_fn
  HP.HN.literals HP.HN.name_cells : typeclass_instances.
Include HelloJoinFinish R B.
Section join.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The genv links Hello. *)
Context (Hlinked : hello_linked ge).

(** Allocating fresh storage preserves the relation between memory and the external world. *)
Context (Kalloc : forall q m wd h base, fresh m q base -> wi m wd h ->
     wi (allocated m q base) wd (overwrite (obj_ps base q) h)).

(** memset has its contract, and zeroing eight bytes of a block the
    program owns keeps wi. *)
Context (Hmemset : registry (TAtom "memset") = Some (memset_contract libc_world))
  (Kmemset : forall b reg o xs cs m m' wd h, memset_result m (mkPtr (b + o) (Obj b)) 0 8 m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (replicate 8 0) (clear_slots o cs)) h)).

(** Setting the program name uses three string operations with known contracts. *)
Context (Hstrrchr : registry (TAtom "strrchr") = Some (strrchr_contract libc_world))
  (Hmemcmp : registry (TAtom "memcmp") = Some (memcmp_contract libc_world))
  (Hstrncmp : registry (TAtom "strncmp") = Some (strncmp_contract libc_world)).

(** The program-name cells have enough aligned storage for pointer writes. *)
Context (pn nreg sreg : region) (nb sb : Z)
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hpn_end : program_name_b + 8 <= r_end pn)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48)
  (Kpn : HP.HN.store_keeps wi program_name_b pn) (Knb : HP.HN.store_keeps wi nb nreg)
  (Ksb : HP.HN.store_keeps wi sb sreg).

(** Setting the locale borrows the requested name and updates the selected codec.
    The returned category names remain readable at their recorded addresses. *)
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

(** Writing a pointer into owned storage preserves the relation between memory and the external world. *)
Context (Kpstore : forall b reg o x xp m wd h,
  (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
     h !! l = Some v) ->
  wi m wd h ->
  wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
    (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)).

(** Registering the output cleanup handler returns an integer and preserves the program's memory.
    Libc records the handler in its private state. *)
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

(** The argument vector is aligned and fits in its allocation, including its null terminator.
    Its length is a positive C integer, and each argument is a C string. *)
Context (av : Z) (ar : region) (sargs : list argument)
  (Hav : 0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length sargs) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48)
  (Hargc : 1 <= Z.of_nat (length sargs) < 2 ^ 31)
  (Hargs : Forall (fun s => string_ok (arg_ptr s) (arg_base s) (arg_region s) (arg_text s)) sargs).

(** Option parsing uses the supplied input and parser state.
    The safety proof permits any transition allowed by the parser's contract. *)
Context (initialized running : mem -> libc_world -> Prop)
  (grequests : list word -> mem -> libc_world -> Z -> Z -> Prop)
  (transition : list word -> mem -> libc_world -> list Z -> list event -> list word -> mem -> libc_world -> Prop)
  (Hgetopt : registry (TAtom "getopt_long") =
     Some (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition)).

(** wi ties libc's optarg and optind cells to the parser's state and
    the getopt token, as GetoptLogic.v's reads need. *)
Context (optarg_cell optind_cell : ptr)
  (Hgetopt_wi : forall m w h, wi m w h ->
     getopt_state_at m (libc_getopt_view w) /\ getopt_optarg_cell (libc_getopt_view w) = optarg_cell /\
     getopt_optind_cell (libc_getopt_view w) = optind_cell /\ getopt_current (libc_getopt_view w) h).

(** wi keeps Hello's option literals in memory. *)
Context (Htable : forall m w h, wi m w h -> hello_table_at m).

(** The parser can read its inputs and write its private state.
    Those writes stay separate from the argument strings that main owns. *)
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

(** Returning from option parsing updates the argument vector and records the new option argument and index.
    The updated ownership records agree with memory. *)
Context (Kgetopt : forall r args xs s m w h trace values s' m' w' bs cs,
   M.E.invoke (libc_getopt_refined_contract (hello_input av sargs) initialized running grequests transition)
     r args xs s m w trace (CallReturn values) s' m' w' ->
   (forall l v, (l, v) ∈ block_ps av ar 0 bs cs -> h !! l = Some v) -> wi m w h ->
   agrees m h -> live_disjoint m -> R.ready s m ->
   wi m' w' (overwrite (block_ps av ar 0 (mem_bytes m' av (8 * (length sargs + 1))) (mem_auxes m' av (8 * (length sargs + 1))) ++
     getopt_ps (getopt_optarg (libc_getopt_view w')) (getopt_optind (libc_getopt_view w'))) h)).

(** libc's optarg cell is the global optarg, and both cells are at
    word addresses. *)
Context (Hoptarg_g : lookup (TAtom "optarg") (ge_globals ge) = Some optarg_cell)
  (Hcells : 0 <= ptr_addr optarg_cell < 2 ^ 64 /\ 0 <= ptr_addr optind_cell < 2 ^ 64).

(** libc's optind cell is the global optind. *)
Context (Hoptind_g : lookup (TAtom "optind") (ge_globals ge) = Some optind_cell).

(** exit has a contract that admits any canonical status and never
    returns to main. The handlers it runs, close_stdout among them, are
    the ending's, not main's: in this language the call stalls. *)
Context (exit_spec : contract libc_world)
  (Hexit : registry (TAtom "exit") = Some exit_spec)
  (Hexit_abi : forall v, contract_abi exit_spec CVoid [Arg W v])
  (Hexit_pre : forall n m w h, 0 <= n < 2 ^ 32 -> wi m w h -> contract_pre exit_spec [WInt n] m w)
  (Hexit_post : forall args n s m w tr vs s' m' w',
    M.E.invoke exit_spec CVoid args [WInt n] s m w tr (CallReturn vs) s' m' w' -> False).

(** The standard-output cell remains readable and contains the expected stream pointer. *)
Context (stdout_cell stream : ptr)
  (Hstdout_g : lookup (TAtom "stdout") (ge_globals ge) = Some stdout_cell)
  (wi_stdout : forall m w h, wi m w h ->
    access_res m (raw_address (ptr_addr stdout_cell) 0) (ptr_cap stdout_cell) 8 Read 8 = Some ok /\
    pointer_load_effects m (raw_address (ptr_addr stdout_cell) 0)
      [AuxRead; LowerResolve; AddressRead] = Some stream).

(** Printing the version borrows the program's literal strings and author names.
    Its output calls preserve those strings and the caller's other memory. *)
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
    wi m wd h ->
    wi (store_bytes m cb 8 (sb + off + 8)) wd
      (overwrite (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) h))
  (Kversion_snapshot : forall m wd h sb,
    fresh m (heap_req 16 72) sb -> wi m wd h ->
    wi (snapshot_values (HV.version_main_args stream) sb (allocated m (heap_req 16 72) sb)) wd
      (overwrite (snapshot_ps (HV.version_main_args stream) sb (heap_req 16 72)) h)).

(** The standard-error cell remains readable and contains the expected stream pointer. *)
Context (stderr_cell errstream : ptr)
  (Hstderr_g : lookup (TAtom "stderr") (ge_globals ge) = Some stderr_cell)
  (wi_stderr : forall m w h, wi m w h ->
    access_res m (raw_address (ptr_addr stderr_cell) 0) (ptr_cap stderr_cell) 8 Read 8 = Some ok /\
    pointer_load_effects m (raw_address (ptr_addr stderr_cell) 0)
      [AuxRead; LowerResolve; AddressRead] = Some errstream).

(** Output calls borrow literal strings and any argument strings they print.
    Each call returns a C integer and preserves the caller's memory, even when writing fails. *)
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

(** The extra-operand diagnostic borrows its format and argument strings.
    It returns to main without changing the caller's memory. *)
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

(** Character conversion accepts a zero-initialized conversion state.
    Every valid state consists of bytes. *)
Context (valid : term -> list Z -> Prop) (audit : term -> option audited_codec)
  (Hmbrtowc : registry (TAtom "mbrtowc") = Some (mbrtowc_contract valid audit rep requests))
  (Hvalid0 : mbstate_zero_valid valid) (Hbytes : mbstate_valid_bytes valid).

(** Libc's private state stays separate from the program's memory.
    Character conversion uses the codec selected by the preceding locale update. *)
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

(** Querying a locale category returns its borrowed name without changing memory or libc's state. *)
Context (Hset_query_pre : forall m w h k p t z, wi m w h -> h !! PName k = Some (VName p t) -> ptr_addr z = 0 ->
     contract_pre (libc_setlocale_contract rep requests) [WInt k; WPtr z] m w)
  (Hset_query : forall r args s m w h k p t z trace ending s' m' w',
     wi m w h -> h !! PName k = Some (VName p t) -> ptr_addr z = 0 ->
     M.E.invoke (libc_setlocale_contract rep requests) r args [WInt k; WPtr z] s m w trace ending s' m' w' ->
     s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr p]).

(** strlen, memcpy and strcmp have their contracts. *)
Context (Hstrlen : registry (TAtom "strlen") = Some (strlen_contract libc_world))
  (Hmemcpy : registry (TAtom "memcpy") = Some (memcpy_contract libc_world))
  (Hstrcmp : registry (TAtom "strcmp") = Some (strcmp_contract libc_world)).

(** The world interpretation survives a copy, a byte store and a
    four-byte store into a block the program owns. *)
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
     wi (store_bytes m (b + o) 4 y) wd (overwrite ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 4)) h)).

(** The bounded string scan uses the standard byte-search contract. *)
Context (Hmemchr : registry (TAtom "memchr") = Some (memchr_contract libc_world)).

(** Looking up errno uses the contract for libc's private state. *)
Context (Herrno_reg : registry (TAtom "__errno_location") = Some (HC.LB.errno_contract rep)).

(** malloc has its contract. *)
Context (Hmalloc : registry (TAtom "malloc") = Some (malloc_contract libc_world)).

(** Main owns the allocation containing the errno cell, whose four bytes fit within the address space. *)
Context (eb eo : Z) (er : region) (Herrno_at : errno = mkPtr (eb + eo) (Obj eb))
  (Herrno_range : 0 < eb /\ 0 <= eo /\ eb + eo + 4 <= r_end er /\ r_end er <= 2 ^ 48).

(** Main owns the format strings for the conversion diagnostic and the printed greeting. *)
Context (join_ps : list (piece * pval))
  (Hjoin_lookup : forall s, In s ["hello#str.82"; "hello#str.83"] ->
     lookup (TAtom s) (ge_globals ge) = Some (version_literal s)).

(** A failed conversion prints a diagnostic and terminates the program.
    This call shares the extra-operand diagnostic's contract but passes a nonzero exit status. *)
Context (Herror_abi : forall args, map (fun a => match a with Arg k _ => k end) args = [W; W; P] ->
     contract_abi diag_spec CVoid args)
  (Herror_pre : forall n m w h, wi m w h -> (forall l v, (l, v) ∈ join_ps -> h !! l = Some v) ->
     agrees m h -> contract_pre diag_spec [WInt 1; WInt n; WPtr (version_literal "hello#str.82")] m w)
  (Herror_fatal : forall n args s m w tr vs s' m' w',
     M.E.invoke diag_spec CVoid args [WInt 1; WInt n; WPtr (version_literal "hello#str.82")]
       s m w tr (CallReturn vs) s' m' w' -> False).

(** errno's lookup returns the errno cell, whose bytes main owns. *)
Context (Herrno_cell : forall m w h, wi m w h -> errno_cell m errno).

(** Printing the greeting borrows its format and terminated wide string.
    The call returns a C integer and preserves the caller's memory even when output fails. *)
Context (wprintf_spec : contract libc_world) (Hwprintf_reg : registry (TAtom "wprintf") = Some wprintf_spec)
  (Hwprintf_ret : contract_returns wprintf_spec = RClass W)
  (Hwprintf_abi : forall d args, map (fun a => match a with Arg k _ => k end) args = [P; P] ->
     contract_abi wprintf_spec (CResult d W) args)
  (Hwprintf_pre : forall bd rd ws k m w h,
     wide_ok (take (4 * k) ws) -> le_value (take 4 (drop (4 * k) ws)) = 0 -> (4 * k + 4 <= length ws)%nat ->
     (forall l v, (l, v) ∈ join_ps ++ (PLive bd, VLive rd) :: byte_ps bd 0 ws -> h !! l = Some v) ->
     agrees m h -> wi m w h ->
     contract_pre wprintf_spec [WPtr (version_literal "hello#str.83"); WPtr (mkPtr bd (Obj bd))] m w)
  (Hwprintf_frame : forall bd r args s m w h tr values s' m' w',
     agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
     M.E.invoke wprintf_spec r args [WPtr (version_literal "hello#str.83"); WPtr (mkPtr bd (Obj bd))]
       s m w tr (CallReturn values) s' m' w' ->
     agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
       exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32).

(** free releases a heap object main owns, keeping the world
    interpretation. *)
Context (Hfree : frees_heap (ge_free ge))
  (Kfree : forall b reg m wd h rs, h !! PLive b = Some (VLive reg) ->
     replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs -> wi m wd h ->
     wi (mkMem (m_bytes m) rs (m_aux m)) wd (overwrite [(PLive b, VFreed)] h)).

(** These proofs track ownership of the greeting and its newly allocated buffer. *)
Section iris.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The logic interprets calls using the supplied contracts and memory relation. *)
Let section_join_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := join_irisGS registry wi ge.
Local Existing Instance section_join_irisGS.

Local Hint Opaque join_irisGS : typeclass_instances.

(** The expression type records the supplied contracts and linked program. *)
Local Notation jexpr := (language.expr (nanofil_lang registry ge)).

(** The entry tactic reads the requested block from the linked function. *)
Local Ltac jn_enter blk :=
  iApply (wp_enter _ _ _ _ _ _ _ _ blk);
  [abstract (vm_cast_no_check (eq_refl (Some blk))) | word_premise |]; iNext;
  cbn [b_insts b_jump main_block xmalloc_block hblk].

(** Main initializes its memory, parses options, and prints the selected greeting.
    Every path either loops indefinitely or terminates through exit or a fatal diagnostic; none reaches abort. *)
Lemma main_full s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix b61 r61 rg rt rc rp xe ce Φ :
  sargs = s0 :: srest -> argv_caps cs0 (map arg_ptr sargs) -> 0 <= ix <= Z.of_nat (length sargs) ->
  length xe = 4%nat -> length ce = 4%nat ->
  pts (block_ps av ar 0 (argv_bytes (map arg_ptr sargs)) cs0) -∗ pts (flat_map arg_ps sargs) -∗
  pts (getopt_ps a ix) -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗
  pts version_ps -∗ pts help_ps -∗ string (version_literal "hello#str.61") b61 r61 [101; 110; 95] -∗
  string c_ptr 65824 rc c_bytes -∗ string posix_ptr 65856 rp posix_bytes -∗
  pts (block_ps eb er eo xe ce) -∗ pts join_ps -∗
  string greeting_ptr 70000 rg greeting_bytes -∗ string traditional_ptr 69808 rt traditional_bytes -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length sargs)); WPtr (mkPtr av (Obj av))]) : jexpr) {{ Φ }}.
Proof using registry wi SafepointStable0 ge Hlinked Kalloc Hmemset Kmemset Hstrrchr Hmemcmp Hstrncmp pn nreg sreg nb sb Hnb Hsb Hpn_end Hnb_cell Hsb_cell Kpn Knb Ksb rep requests Hsetlocale Hlent Hset_pre Kset Kpstore atexit_spec Hatexit Hatexit_ret Hatexit_abi Hatexit_pre Katexit av ar sargs Hav Hargc Hargs initialized running grequests transition Hgetopt optarg_cell optind_cell Hgetopt_wi Htable Hgetopt_env Hgetopt_apart Kgetopt Hoptarg_g Hcells Hoptind_g exit_spec Hexit Hexit_abi Hexit_pre Hexit_post stdout_cell stream Hstdout_g wi_stdout version_ps author_reg Hauthor_live version_spec Hversion_reg Hversion_ret Hversion_abi Hversion_pre Hversion_frame Kversion_alloc Kversion_store Kversion_cursor Kversion_snapshot stderr_cell errstream Hstderr_g wi_stderr help_ps output_spec Hhelp_reg Hhelp_ret Hhelp_abi Hhelp_pre Hhelp_frame Houtput_reg Houtput_ret Houtput_abi Houtput_pre Houtput_frame diag_spec Hdiag_reg Hdiag_ret Hdiag_abi Hdiag_pre Hdiag_post valid audit Hmbrtowc Hvalid0 Hbytes errno Hlibc Haudit Kmbrtowc Hset_query_pre Hset_query Hstrlen Hmemcpy Hstrcmp Kcopy Kbyte Kstore Hmemchr Herrno_reg Hmalloc eb eo er Herrno_at Herrno_range join_ps Hjoin_lookup Herror_abi Herror_pre Herror_fatal Herrno_cell wprintf_spec Hwprintf_reg Hwprintf_ret Hwprintf_abi Hwprintf_pre Hwprintf_frame Hfree Kfree hlc Σ invGS_gen0 gen_heapGS0.
  intros Hhd Hcs Hix Lxe Lce.
  iIntros "Hb Has Ht Hlit Hcells Hks Hcod Hs80 Hv Hh H61 Hc Hp Herr Hjs Hgr Htr".
  pose proof (HM.main_to_join registry wi ge) as Hmain.
  iApply (Hmain with "Hb Has Ht Hlit Hcells Hks Hcod Hs80 Hv Hh H61").
  all: try eassumption.
  (* --help's query of LC_MESSAGES, from the general query premise. *)
  1: intros ?m ?w ?h ?p ?t Hw Hk; eapply Hset_query_pre; [exact Hw | exact Hk | reflexivity].
  1: intros ?r ?args ?s ?m ?w ?h ?p ?t ?tr ?en ?s' ?m' ?w' Hw Hk Hi;
     eapply (Hset_query _ _ _ _ _ _ _ _ _ null); [exact Hw | exact Hk | reflexivity | exact Hi].
  iNext. iIntros (e b4 b6 i k q new c' Hf) "Hlit #Hl Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'".
  pose proof Hf as (_ & _ & _ & Hb6 & _).
  iApply (main_join
            with "Hl Hcod Hl6 Hy6 Hc6 Hc Hp Herr Hjs Hgr Htr"); try eassumption.
Qed.

End iris.

(** GNU Hello runs without memory faults or contract violations when its initial memory satisfies the stated ownership conditions.
    The runtime must be [[ready]], and the live objects must be disjoint.
    The result covers every execution length and uses the supplied audited codec. *)
Theorem hello_main_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    m s w h0 s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix b61 r61 rg rt rc rp xe ce fuel :
  R.ready s m -> live_disjoint m -> agrees m h0 -> wi m w h0 ->
  sargs = s0 :: srest -> argv_caps cs0 (map arg_ptr sargs) -> 0 <= ix <= Z.of_nat (length sargs) ->
  length xe = 4%nat -> length ce = 4%nat ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
     ([∗ map] l ↦ v ∈ h0, pointsto l (DfracOwn 1) v) ⊢
       pts (block_ps av ar 0 (argv_bytes (map arg_ptr sargs)) cs0) ∗ pts (flat_map arg_ps sargs) ∗
       pts (getopt_ps a ix) ∗
       HP.HN.literals r3 r4 ∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 ∗
       ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) ∗ pts (codec_ps c0) ∗
       string empty_ptr 69968 r80 [] ∗
       pts version_ps ∗ pts help_ps ∗ string (version_literal "hello#str.61") b61 r61 [101; 110; 95] ∗
       string c_ptr 65824 rc c_bytes ∗ string posix_ptr 65856 rp posix_bytes ∗
       pts (block_ps eb er eo xe ce) ∗ pts join_ps ∗
       string greeting_ptr 70000 rg greeting_bytes ∗ string traditional_ptr 69808 rt traditional_bytes) ->
  labelled_safe registry ge (invocation main_fn [WInt (Z.of_nat (length sargs)); WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hr Hd Ha Hw Hhd Hcs Hix Lxe Lce Hstart.
  apply (heap_labelled_safe Σ registry wi ge _ m s w h0 (fun _ => True) Hr Hd Ha Hw).
  intros HinvG HheapG. rewrite (Hstart HinvG HheapG).
  iIntros "(Hb & Has & Ht & Hlit & Hcells & Hks & Hcod & Hs80 & Hv & Hh & H61 & Hc & Hp & Herr & Hjs & Hgr & Htr)".
  iApply (main_full s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix b61 r61 rg rt rc rp xe ce
            with "Hb Has Ht Hlit Hcells Hks Hcod Hs80 Hv Hh H61 Hc Hp Herr Hjs Hgr Htr"); auto.
Qed.

End join.
End HelloJoinComplete.
