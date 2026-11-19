(** GNU Hello's main function uses one program logic for all its calls.
    This file supplies that logic, the linked function's data, and the
    call rules needed during initialization. [HelloMain] includes these
    definitions and proofs so that callers keep the same names. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia Permutation.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs HelloName
  HelloProgName Startup Getopt GetoptLogic HelloVersion.
Open Scope Z_scope.
Open Scope list_scope.

Module MainDefinitions.

(** The linked module supplies main's decoded function body. *)
Definition main_fn : func := Eval vm_compute in hello_fn "main".

Local Hint Opaque main_fn : typeclass_instances.

(** Each block is selected from main by its label. *)
Definition main_block (s : String.string) : block := hblk main_fn s.

(** A 16-aligned base is 8-aligned. *)
Lemma mod16_mod8 b : b mod 16 = 0 -> b mod 8 = 0.
Proof.
  intros H. apply Z.mod_divide in H; [|lia]. destruct H as [k ->].
  replace (k * 16) with ((2 * k) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(** Main passes the empty string to setlocale when it initializes the locale. *)
Definition empty_ptr : ptr := mkPtr 69968 (Ro 69968).
(** The default greeting points to the read-only string "Hello, world!". *)
Definition greeting_ptr : ptr := mkPtr 70000 (Ro 70000).
(** The default greeting has these character bytes. *)
Definition greeting_bytes : list Z := [72; 101; 108; 108; 111; 44; 32; 119; 111; 114; 108; 100; 33].
(** Main registers this pointer to close_stdout with atexit. *)
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

(** ## getopt_long's literals

    Main parses its options with getopt_long(argc, argv, "g:t",
    longopts, NULL). The option string and the table are Hello's
    read-only literals; every option's flag is null, so getopt_long
    returns its value. *)

(** The option string "g:t" requires an argument for the greeting option. *)
Definition optstring_ptr : ptr := mkPtr 69584 (Ro 69584).
(** The long options table starts at this read-only address. *)
Definition longopts_ptr : ptr := mkPtr 68672 (Ro 68672).
(** The traditional greeting points to the read-only string "hello, world". *)
Definition traditional_ptr : ptr := mkPtr 69808 (Ro 69808).

(** The greeting option takes an argument and returns 'g'. The other
    options return 't', 128, or 129 without taking an argument. *)
Definition hello_options : list long_option :=
  [mkLongOption (mkPtr 69456 (Ro 69456)) [103; 114; 101; 101; 116; 105; 110; 103] 1 null 103;
   mkLongOption (mkPtr 69488 (Ro 69488)) [116; 114; 97; 100; 105; 116; 105; 111; 110; 97; 108] 0 null 116;
   mkLongOption (mkPtr 69520 (Ro 69520)) [104; 101; 108; 112] 0 null 128;
   mkLongOption (mkPtr 69552 (Ro 69552)) [118; 101; 114; 115; 105; 111; 110] 0 null 129].

(** Hello's symbols put them there. *)
Lemma getopt_globals :
  lookup (TAtom "hello#str.69") hello_globals = Some optstring_ptr /\
  lookup (TAtom "hello#parse_options.longopts.64") hello_globals = Some longopts_ptr /\
  lookup (TAtom "hello#str.76") hello_globals = Some traditional_ptr /\
  map (fun o => Some (option_name o)) hello_options =
    map (fun s => lookup (TAtom s) hello_globals) ["hello#str.65"; "hello#str.66"; "hello#str.67"; "hello#str.68"]%string.
Proof. vm_compute. auto. Qed.

(** Each argument records its string pointer, containing object, region,
    and character bytes. *)
Record argument : Type := mkArgument {
  arg_ptr : ptr;
  arg_base : Z;
  arg_region : region;
  arg_text : list Z
}.

(** An argument owns the memory pieces that describe its string. *)
Definition arg_ps (s : argument) : list (piece * pval) :=
  string_ps (arg_ptr s) (arg_base s) (arg_region s) (arg_text s).

(** Every parser call uses the same argument vector and option table.
    The registry fixes this input for the entire run. *)
Definition hello_input (av : Z) (sargs : list argument) : getopt_input :=
  mkGetoptInput (Z.of_nat (length sargs)) (mkPtr av (Obj av))
    (map (fun s => (arg_ptr s, arg_text s)) sargs) optstring_ptr [103; 58; 116]
    longopts_ptr hello_options null.

(** Argv's order is that of the arguments. *)
Lemma hello_input_order av sargs : map fst (getopt_arguments (hello_input av sargs)) = map arg_ptr sargs.
Proof. cbn. rewrite map_map. reflexivity. Qed.

(** The literals getopt_long reads are in memory: the option string,
    the table's bounds and its records. *)
Definition hello_table_at (m : mem) : Prop :=
  c_string m optstring_ptr [103; 58; 116] /\
  access_res m (ptr_addr longopts_ptr) (ptr_cap longopts_ptr) (32 * (Z.of_nat (length hello_options) + 1))
    Read 8 = Some ok /\
  getopt_records m (ptr_addr longopts_ptr) hello_options.

(** The parser returns a C integer. A greeting option also returns
    a nonnull pointer borrowed from an argument string. *)
Lemma hello_code av sargs m' g code :
  getopt_result (hello_input av sargs) m' g code ->
  getopt_int code /\
  (code = 103 -> getopt_borrow (hello_input av sargs) (getopt_optarg g) /\ ptr_addr (getopt_optarg g) <> 0).
Proof.
  unfold getopt_int.
  intros [(-> & _) | [([-> | ->] & _) | [(byte & mode & Hb & _ & _ & -> & Hmode & Harg) |
           [(rest & Hs & _) | (i & o & Hi & Hflag & _ & Harg)]]]].
  - split; [lia | intros E; discriminate E].
  - split; [lia | intros E; discriminate E].
  - split; [lia | intros E; discriminate E].
  - destruct (Z.ltb_spec byte 128) as [Hlt | Hge].
    + split; [lia|]. intros ->. cbn in Hmode. assert (mode = 1) as -> by congruence.
      exact (getopt_required_argument _ _ Harg).
    + split; [lia | lia].
  - cbn in Hs. discriminate Hs.
  - destruct i as [|[|[|[|i]]]]; [| | | | destruct i; discriminate Hi];
      unfold hello_options in Hi; cbn in Hi; injection Hi as <-; cbn in Hflag; rewrite Hflag.
    + split; [lia|]. intros _. exact (getopt_required_argument _ _ Harg).
    + split; [lia | intros E; discriminate E].
    + split; [lia | intros E; discriminate E].
    + split; [lia | intros E; discriminate E].
Qed.

(** ## argv as one block

    Main lends the entire argument vector to getopt_long, including
    its terminating null pointer. The parser may reorder the pointers,
    but each slot retains its address bytes and [[capability]]. *)

(** An address occupies eight bytes, with the least significant byte first. *)
Definition slot_bytes (x : Z) : list Z := map (byte_of x) [0; 1; 2; 3; 4; 5; 6; 7].

(** The pointer slots concatenate the address bytes of the pointer list. *)
Definition slots_bytes (L : list ptr) : list Z := flat_map (fun q => slot_bytes (ptr_addr q)) L.

(** The argument vector stores its pointers followed by a null sentinel. *)
Definition argv_bytes (ps : list ptr) : list Z := slots_bytes (ps ++ [null]).

(** Each pointer's first auxiliary slot stores its capability.
    The auxiliary-slot list has the same length as the byte list. *)
Definition argv_caps (cs : list cap) (ps : list ptr) : Prop :=
  length cs = (8 * length (ps ++ [null]))%nat /\
  forall k q, (ps ++ [null]) !! k = Some q -> cs !! (8 * k)%nat = Some (ptr_cap q).

(** The memory m holds the pointer q at a: a word address, its eight
    bytes, and its capability in the aux slot. *)
Definition slot_at (m : mem) (a : Z) (q : ptr) : Prop :=
  0 <= ptr_addr q < 2 ^ 64 /\ (forall i, 0 <= i < 8 -> m_bytes m (a + i) = byte_of (ptr_addr q) i) /\
  m_aux m a = ptr_cap q.

(** Each pointer contributes eight bytes to the slot list. *)
Lemma length_slots_bytes L : length (slots_bytes L) = (8 * length L)%nat.
Proof. induction L as [|q L IH]; [reflexivity|]. cbn [slots_bytes flat_map]. rewrite length_app IH. cbn. lia. Qed.

(** A byte lookup selects the corresponding byte of its pointer's address. *)
Lemma slots_bytes_lookup L k q j :
  L !! k = Some q -> (j < 8)%nat -> slots_bytes L !! (8 * k + j)%nat = Some (byte_of (ptr_addr q) (Z.of_nat j)).
Proof.
  revert k. induction L as [|x L IH]; intros k Hk Hj; [discriminate Hk|].
  cbn [slots_bytes flat_map]. destruct k as [|k].
  - cbn in Hk. injection Hk as ->. rewrite lookup_app_l; [|cbn; lia].
    do 8 (destruct j as [|j]; [reflexivity|]). lia.
  - rewrite lookup_app_r; [|cbn; lia]. change (length (slot_bytes (ptr_addr x))) with 8%nat.
    replace (8 * S k + j - 8)%nat with (8 * k + j)%nat by lia. exact (IH k Hk Hj).
Qed.

(** Eight canonical bytes are determined by their little-endian value. *)
Lemma load_bytes_canonical m m' a :
  (forall i, 0 <= i < 8 -> 0 <= m_bytes m (a + i) < 256) ->
  (forall i, 0 <= i < 8 -> 0 <= m_bytes m' (a + i) < 256) ->
  load_bytes m a 8 = load_bytes m' a 8 -> forall i, 0 <= i < 8 -> m_bytes m (a + i) = m_bytes m' (a + i).
Proof.
  intros H H' E i Hi. unfold load_bytes in E. change (Z.to_nat 8) with 8%nat in E. simpl in E.
  pose proof (H 0 ltac:(lia)) as H0; pose proof (H 1 ltac:(lia)) as H1; pose proof (H 2 ltac:(lia)) as H2;
  pose proof (H 3 ltac:(lia)) as H3; pose proof (H 4 ltac:(lia)) as H4; pose proof (H 5 ltac:(lia)) as H5;
  pose proof (H 6 ltac:(lia)) as H6; pose proof (H 7 ltac:(lia)) as H7.
  pose proof (H' 0 ltac:(lia)) as H0'; pose proof (H' 1 ltac:(lia)) as H1'; pose proof (H' 2 ltac:(lia)) as H2';
  pose proof (H' 3 ltac:(lia)) as H3'; pose proof (H' 4 ltac:(lia)) as H4'; pose proof (H' 5 ltac:(lia)) as H5';
  pose proof (H' 6 ltac:(lia)) as H6'; pose proof (H' 7 ltac:(lia)) as H7'.
  change (Z.of_nat 0) with 0 in E; change (Z.of_nat 1) with 1 in E; change (Z.of_nat 2) with 2 in E;
  change (Z.of_nat 3) with 3 in E; change (Z.of_nat 4) with 4 in E; change (Z.of_nat 5) with 5 in E;
  change (Z.of_nat 6) with 6 in E; change (Z.of_nat 7) with 7 in E.
  assert (m_bytes m (a + 7) = m_bytes m' (a + 7)) by lia. assert (m_bytes m (a + 6) = m_bytes m' (a + 6)) by lia.
  assert (m_bytes m (a + 5) = m_bytes m' (a + 5)) by lia. assert (m_bytes m (a + 4) = m_bytes m' (a + 4)) by lia.
  assert (m_bytes m (a + 3) = m_bytes m' (a + 3)) by lia. assert (m_bytes m (a + 2) = m_bytes m' (a + 2)) by lia.
  assert (m_bytes m (a + 1) = m_bytes m' (a + 1)) by lia. assert (m_bytes m (a + 0) = m_bytes m' (a + 0)) by lia.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; assumption.
Qed.

(** A concrete pointer slot satisfies the parser's pointer-slot predicate. *)
Lemma slot_pointer m a q :
  slot_at m a q -> pointer_slot m a q /\ (forall k, 0 <= k < 8 -> 0 <= m_bytes m (a + k) < 256).
Proof.
  intros (Hr & Hb & Hc). split; [split; [exact Hr|split; [|exact Hc]]|].
  - rewrite <- (Z.mod_small (ptr_addr q) (2 ^ 64)); [|exact Hr]. change (2 ^ 64) with (256 ^ 8).
    rewrite <- (stored_bytes_value m a 8 (ptr_addr q)); [|lia].
    apply load_bytes_agree; [lia|]. intros i Hi. rewrite stored_byte; [|exact Hi]. exact (Hb i Hi).
  - intros k Hk. rewrite (Hb k Hk). unfold byte_of. apply Z.mod_pos_bound. lia.
Qed.

(** The parser's pointer-slot predicate also determines the concrete slot. *)
Lemma pointer_slot_at m a q :
  pointer_slot m a q -> (forall k, 0 <= k < 8 -> 0 <= m_bytes m (a + k) < 256) -> slot_at m a q.
Proof.
  intros (Hr & Hl & Hc) Hb. split; [exact Hr|]. split; [|exact Hc].
  intros i Hi. rewrite <- (stored_byte m a 8 (ptr_addr q) i Hi).
  apply (load_bytes_canonical m (store_bytes m a 8 (ptr_addr q)) a); [exact Hb | | | exact Hi].
  - intros k Hk. rewrite stored_byte; [|exact Hk]. unfold byte_of. apply Z.mod_pos_bound. lia.
  - rewrite Hl. rewrite stored_bytes_value; [|lia]. change (256 ^ 8) with (2 ^ 64).
    symmetry. apply Z.mod_small. exact Hr.
Qed.

(** [getopt_slots] is a slot at each eighth byte, for each pointer
    and the sentinel. *)
Lemma slots_of_at m a ps :
  (forall k q, (ps ++ [null]) !! k = Some q -> slot_at m (a + 8 * Z.of_nat k) q) -> getopt_slots m a ps.
Proof.
  revert a. induction ps as [|p ps IH]; intros a H.
  - cbn [getopt_slots]. apply slot_pointer. pose proof (H 0%nat null eq_refl) as H0.
    replace (a + 8 * Z.of_nat 0) with a in H0 by lia. exact H0.
  - cbn [getopt_slots]. pose proof (H 0%nat p eq_refl) as H0.
    replace (a + 8 * Z.of_nat 0) with a in H0 by lia.
    destruct (slot_pointer _ _ _ H0) as [Hp Hb]. split; [exact Hp|]. split; [exact Hb|].
    apply IH. intros k q Hk. replace (a + 8 + 8 * Z.of_nat k) with (a + 8 * Z.of_nat (S k)) by lia.
    exact (H (S k) q Hk).
Qed.

(** A list of concrete slots satisfies the parser's argument-vector predicate. *)
Lemma at_of_slots m a ps :
  getopt_slots m a ps -> forall k q, (ps ++ [null]) !! k = Some q -> slot_at m (a + 8 * Z.of_nat k) q.
Proof.
  revert a. induction ps as [|p ps IH]; intros a Hs k q Hk.
  - destruct k as [|k]; [|destruct k; discriminate Hk]. injection Hk as <-.
    replace (a + 8 * Z.of_nat 0) with a by lia. destruct Hs as [Hp Hb]. exact (pointer_slot_at _ _ _ Hp Hb).
  - destruct Hs as (Hp & Hb & Hr). destruct k as [|k].
    + injection Hk as <-. replace (a + 8 * Z.of_nat 0) with a by lia. exact (pointer_slot_at _ _ _ Hp Hb).
    + replace (a + 8 * Z.of_nat (S k)) with (a + 8 + 8 * Z.of_nat k) by lia. exact (IH _ Hr k q Hk).
Qed.

(** Memory whose slots hold ps holds argv's bytes and slots for ps. *)
Lemma argv_of_slots m a ps :
  getopt_slots m a ps ->
  mem_bytes m a (8 * length (ps ++ [null])) = argv_bytes ps /\
  argv_caps (mem_auxes m a (8 * length (ps ++ [null]))) ps.
Proof.
  intros Hs. pose proof (at_of_slots m a ps Hs) as H. split.
  - apply list_eq. intros i. unfold mem_bytes, argv_bytes. rewrite list_lookup_fmap.
    destruct (decide (i < 8 * length (ps ++ [null])))%nat as [Hi|Hi].
    + rewrite lookup_seq_lt; [|exact Hi]. cbn [fmap option_fmap option_map].
      pose proof (Nat.div_mod_eq i 8) as Ei. pose proof (Nat.mod_upper_bound i 8 ltac:(lia)) as Ej.
      destruct (lookup_lt_is_Some_2 (ps ++ [null]) (i / 8)) as [q Hq]; [lia|].
      rewrite Ei (slots_bytes_lookup _ _ _ _ Hq Ej). destruct (H _ _ Hq) as (_ & Hb & _).
      f_equal. rewrite <- Hb; [|lia]. f_equal. lia.
    + rewrite lookup_seq_ge; [|lia]. symmetry. apply lookup_ge_None_2. rewrite length_slots_bytes. lia.
  - split; [apply length_mem_auxes|]. intros k q Hk.
    pose proof (lookup_lt_Some _ _ _ Hk) as Hlt. unfold mem_auxes. rewrite list_lookup_fmap.
    rewrite lookup_seq_lt; [|lia]. cbn. destruct (H _ _ Hk) as (_ & _ & Hc). rewrite <- Hc. f_equal. f_equal. lia.
Qed.

(** The i-th aux piece is the i-th slot's. *)
Lemma aux_ps_lookup b o cs i c :
  cs !! i = Some c -> aux_ps b o cs !! i = Some (PAux b (o + Z.of_nat i), VAux c).
Proof.
  revert o i. induction cs as [|y cs IH]; intros o i H; [discriminate|].
  rewrite aux_ps_cons. destruct i as [|i]; cbn in H |- *.
  - injection H as ->. rewrite Z.add_0_r. reflexivity.
  - rewrite (IH (o + 1) i H). do 3 f_equal. lia.
Qed.

(** A pointer of a permitted order of argv is one of the arguments'. *)
Lemma order_in sargs ps q :
  getopt_order (map arg_ptr sargs) ps -> In q ps -> exists s, In s sargs /\ q = arg_ptr s.
Proof.
  intros H Hq. apply (Permutation_in _ (Permutation_sym (getopt_order_inventory _ _ H))) in Hq.
  apply in_map_iff in Hq as (s & <- & Hs). eauto.
Qed.

(** Truncating a C integer to 32 bits adds 2^32 only when it is negative. *)
Lemma int32_mod x : getopt_int x -> x mod 2 ^ 32 = if x <? 0 then x + 2 ^ 32 else x.
Proof.
  unfold getopt_int. intros Hx. destruct (Z.ltb_spec x 0).
  - symmetry. apply (Z.mod_unique x (2 ^ 32) (-1)); [left; lia | lia].
  - apply Z.mod_small. lia.
Qed.

(** A C int's 32 bits are those of a nonnegative C int k just if it
    is k. *)
Lemma int32_eq x k : getopt_int x -> 0 <= k < 2 ^ 31 -> (x mod 2 ^ 32 = k <-> x = k).
Proof.
  intros Hx Hk. rewrite (int32_mod x Hx). unfold getopt_int in Hx.
  destruct (Z.ltb_spec x 0); split; lia.
Qed.

(** A C int's 32 bits are all ones just if it is -1, getopt's end. *)
Lemma int32_end x : getopt_int x -> (x mod 2 ^ 32 = 4294967295 <-> x = -1).
Proof.
  intros Hx. rewrite (int32_mod x Hx). unfold getopt_int in Hx.
  destruct (Z.ltb_spec x 0); split; lia.
Qed.

(** A slot's bytes are a pointer cell's. *)
Lemma slot_cell b o x : byte_ps b o (slot_bytes x) = cell b o x.
Proof.
  unfold byte_ps, slot_bytes, cell, seqZ. simpl. rewrite !(Z.add_comm _ o) Z.add_0_r. reflexivity.
Qed.

(** Every slot contains either an argument pointer or the final null sentinel. *)
Lemma slot_kinds sargs ps k q :
  getopt_order (map arg_ptr sargs) ps -> (ps ++ [null]) !! k = Some q ->
  (k = length ps /\ q = null) \/ ((k < length ps)%nat /\ exists s, In s sargs /\ q = arg_ptr s).
Proof.
  intros Ho Hq. apply lookup_app_Some in Hq as [Hq | [Hle Hq]].
  - right. split; [exact (lookup_lt_Some _ _ _ Hq)|].
    apply (order_in sargs ps q Ho). apply list_elem_of_In. exact (list_elem_of_lookup_2 _ _ _ Hq).
  - left. revert Hq. destruct (k - length ps)%nat as [|j] eqn:E; intros Hq; [|destruct j; discriminate Hq].
    cbn in Hq. assert (q = null) as -> by congruence. split; [lia | reflexivity].
Qed.

(** Main prints the usage line, options, and translation-reporting hint
    to its output stream. Errors instead suggest trying --help on stderr. *)
Definition main_output_args (stream errstream pname : ptr) : list (name * list word) :=
  [(TAtom "fprintf", [WPtr stream; WPtr (version_literal "hello#str.54"); WPtr pname]);
   (TAtom "fputs", [WPtr (version_literal "hello#str.55"); WPtr stream]);
   (TAtom "fputs", [WPtr (version_literal "hello#str.56"); WPtr stream]);
   (TAtom "fputs", [WPtr (version_literal "hello#str.57"); WPtr stream]);
   (TAtom "fputs", [WPtr (version_literal "hello#str.58"); WPtr stream]);
   (TAtom "fputs", [WPtr (version_literal "hello#str.59"); WPtr stream]);
   (TAtom "fputs", [WPtr (version_literal "hello#str.60"); WPtr stream]);
   (TAtom "fprintf", [WPtr stream; WPtr (version_literal "hello#str.62");
                      WPtr (version_literal "hello#str.63")]);
   (TAtom "fprintf", [WPtr errstream; WPtr (version_literal "hello#str.79"); WPtr pname])].

(** The program's name as set_program_name leaves it: a suffix of the
    first argument's string. *)
Definition name_ok (sargs : list argument) (pname : ptr) : Prop :=
  exists s0 srest (i : nat), sargs = s0 :: srest /\ (i <= length (arg_text s0))%nat /\
    pname = mkPtr (ptr_addr (arg_ptr s0) + Z.of_nat i) (ptr_cap (arg_ptr s0)).

End MainDefinitions.
Import MainDefinitions.

Local Hint Opaque main_fn : typeclass_instances.

Module HelloMainBase (R : Runtime).
Module LG0.
Include Logic R.
End LG0.
Module HP.
Include HelloProgNameOn R LG0.
End HP.
Module GL.
Include GetoptLogicOn R LG0.
End GL.
Module HV.
Include HelloVersionOn R LG0.
End HV.
Module HLo.
Include HelloLocaleOn R LG0.
End HLo.
Import HLo HL ML LG.
Module GR.
Include GetoptRefinementOn R L.M.
End GR.
Import L LG SL ML LL HL.

Local Hint Opaque pts bytes auxes live pcell
  HP.HN.literals HP.HN.name_cells : typeclass_instances.

Section main.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The world interpretation connects this registry to the shared program logic. *)
Local Instance main_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

Local Hint Opaque main_irisGS : typeclass_instances.

(** Main's expressions use the language of the chosen registry. *)
Local Notation mexpr := (language.expr (nanofil_lang registry ge)).

(** The genv links Hello. *)
Context (Hlinked : hello_linked ge).

(** Allocating a fresh object preserves the world interpretation when ownership includes the new object. *)
Context (Kalloc : forall q m wd h base, fresh m q base -> wi m wd h ->
     wi (allocated m q base) wd (overwrite (obj_ps base q) h)).

(** memset has its contract, and zeroing eight bytes of a block the
    program owns keeps wi. *)
Context (Hmemset : registry (TAtom "memset") = Some (memset_contract libc_world))
  (Kmemset : forall b reg o xs cs m m' wd h, memset_result m (mkPtr (b + o) (Obj b)) 0 8 m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (replicate 8 0) (clear_slots o cs)) h)).

(** Setting the program name requires three writable pointer cells
    and the string-operation contracts used to find the name. *)
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

(** Setting the locale replaces the category names and the codec state.
    The caller owns the input string and may borrow the returned names. *)
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

(** The locale call returns either null or the selected category's new name.
    It updates the codec state and lends each category's replacement name. *)
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
Proof using Hlent Hlinked Hnb_cell Hsb_cell Hset_pre Hsetlocale Kset SafepointStable0.
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

(** Storing a pointer in an owned cell preserves the world interpretation. *)
Context (Kpstore : forall b reg o x xp m wd h,
  (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
     h !! l = Some v) ->
  wi m wd h ->
  wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
    (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)).

(** Registering close_stdout with atexit returns an integer and preserves
    the caller's memory. The registration itself belongs to libc's state. *)
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

(** Eight zero bytes and an empty slot at offset 0 are a null pointer
    cell. *)
Lemma zero_pcell b : bytes b 0 (replicate 8 0) ∗ auxes b 0 [CNone] ⊣⊢ pcell b 0 (mkPtr 0 CNone).
Proof using Type.
  change (pts (cell b 0 0) ∗ pts [(PAux b 0, VAux CNone)] ⊣⊢
    pts ([(PAux b 0, VAux CNone)] ++ cell b 0 0)).
  rewrite pts_app. apply bi.sep_comm.
Qed.

(** Enter a block of main. *)
Ltac mn_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (main_block s));
  [abstract (vm_cast_no_check (eq_refl (Some (main_block s)))) | word_premise |]; iNext;
  cbn [b_insts b_jump main_block hblk].

(** The conversion-state initializer clears the first eight bytes of its object. *)
Lemma mbszero_at b reg xs cs Φ :
  length xs = 8%nat -> length cs = 8%nat -> b mod 8 = 0 -> b + 8 <= r_end reg ->
  live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗
  ▷ (live b reg -∗ bytes b 0 (replicate 8 0) -∗ auxes b 0 (clear_slots 0 cs) -∗ Φ RetVoid) -∗
  WP (ERun (invocation mbszero_fn [WPtr (mkPtr b (Obj b))]) : mexpr) {{ Φ }}.
Proof using Hlinked Hmemset Kmemset SafepointStable0.
  intros Lx Lc Hb8 Hend.
  pose proof (mbszero_spec registry wi ge Hlinked b reg 0 xs cs Φ) as H. rewrite !Z.add_0_r in H.
  iApply H; [exact Hmemset | exact Lx | exact Lc | exact Hb8 | reflexivity | lia | exact Hend |].
  intros m m' wd h Hr Hin Hw. pose proof (Kmemset b reg 0 xs cs m m' wd h) as K.
  rewrite !Z.add_0_r in K. exact (K Hr Hin Hw).
Qed.

End main.
End HelloMainBase.
