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
From Stdlib Require Import ZArith Lia Permutation.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs HelloName
  HelloProgName Startup Getopt GetoptLogic HelloVersion.
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

(** ## getopt_long's literals

    Main parses its options with getopt_long(argc, argv, "g:t",
    longopts, NULL). The option string and the table are Hello's
    read-only literals; every option's flag is null, so getopt_long
    returns its value. *)

(** "g:t". *)
Definition optstring_ptr : ptr := mkPtr 69584 (Ro 69584).
(** The long options table. *)
Definition longopts_ptr : ptr := mkPtr 68672 (Ro 68672).
(** The traditional greeting, "hello, world". *)
Definition traditional_ptr : ptr := mkPtr 69808 (Ro 69808).

(** Hello's long options: greeting, taking an argument, as 'g';
    traditional as 't'; help and version as 128 and 129. *)
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

(** One of main's arguments: the C string at arg_ptr, in the object
    arg_base with the region arg_region, with contents arg_text. *)
Record argument : Type := mkArgument {
  arg_ptr : ptr;
  arg_base : Z;
  arg_region : region;
  arg_text : list Z
}.

(** Its pieces: the string's. *)
Definition arg_ps (s : argument) : list (piece * pval) :=
  string_ps (arg_ptr s) (arg_base s) (arg_region s) (arg_text s).

(** getopt_long's input for one run of main, whose argv is at av and
    whose arguments are sargs: the same at every call, as the registry
    is fixed for the run. *)
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

(** What main learns from getopt_long's code: a C int, and 'g'
    ('g' or --greeting) comes with a nonnull borrow of an argument,
    as both take one. *)
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

    Main hands argv to getopt_long whole, as HelloConv.v hands mbrtowc
    its cells: its life, the bytes of its argc + 1 pointer slots and
    every aux slot of them ([block_ps]). The bytes are those of the
    pointers ps argv holds, then null ([argv_bytes]); the aux slot at
    the start of each holds its capability ([argv_caps]). getopt_long
    may permute the arguments, and Campaign 4's [getopt_slots] says
    each slot's bytes are a byte each, so the block it hands back is
    of the same form. *)

(** The eight bytes of the address x, least significant first. *)
Definition slot_bytes (x : Z) : list Z := map (byte_of x) [0; 1; 2; 3; 4; 5; 6; 7].

(** The bytes of the slots holding the pointers L. *)
Definition slots_bytes (L : list ptr) : list Z := flat_map (fun q => slot_bytes (ptr_addr q)) L.

(** argv's bytes, holding ps and the null sentinel. *)
Definition argv_bytes (ps : list ptr) : list Z := slots_bytes (ps ++ [null]).

(** The aux slots cs of argv holding ps: as many as its bytes, the
    first of each pointer's eight holding its capability. *)
Definition argv_caps (cs : list cap) (ps : list ptr) : Prop :=
  length cs = (8 * length (ps ++ [null]))%nat /\
  forall k q, (ps ++ [null]) !! k = Some q -> cs !! (8 * k)%nat = Some (ptr_cap q).

(** The memory m holds the pointer q at a: a word address, its eight
    bytes, and its capability in the aux slot. *)
Definition slot_at (m : mem) (a : Z) (q : ptr) : Prop :=
  0 <= ptr_addr q < 2 ^ 64 /\ (forall i, 0 <= i < 8 -> m_bytes m (a + i) = byte_of (ptr_addr q) i) /\
  m_aux m a = ptr_cap q.

(** Eight bytes per pointer. *)
Lemma length_slots_bytes L : length (slots_bytes L) = (8 * length L)%nat.
Proof. induction L as [|q L IH]; [reflexivity|]. cbn [slots_bytes flat_map]. rewrite length_app IH. cbn. lia. Qed.

(** The j-th byte of the k-th slot. *)
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

(** A slot is Campaign 4's: a [pointer_slot] of canonical bytes. *)
Lemma slot_pointer m a q :
  slot_at m a q -> pointer_slot m a q /\ (forall k, 0 <= k < 8 -> 0 <= m_bytes m (a + k) < 256).
Proof.
  intros (Hr & Hb & Hc). split; [split; [exact Hr|split; [|exact Hc]]|].
  - rewrite <- (Z.mod_small (ptr_addr q) (2 ^ 64)); [|exact Hr]. change (2 ^ 64) with (256 ^ 8).
    rewrite <- (stored_bytes_value m a 8 (ptr_addr q)); [|lia].
    apply load_bytes_agree; [lia|]. intros i Hi. rewrite stored_byte; [|exact Hi]. exact (Hb i Hi).
  - intros k Hk. rewrite (Hb k Hk). unfold byte_of. apply Z.mod_pos_bound. lia.
Qed.

(** And back. *)
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

(** And back. *)
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

(** A C int cut to 32 bits: itself if nonnegative, else 2^32 more. *)
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

(** Slot k of argv holding a permitted order ps: an argument, before
    the sentinel, or the sentinel itself, null. *)
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

(** Main's proof over one Logic instance shared by every layer. *)
(** Main's output calls, in order: the help text's usage line with the
    program's name, its six lines of options and the hint that a
    translation's bugs go elsewhere, then, on stderr, the hint to try
    --help. *)
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

Module HelloMain (R : Runtime).
Module LG0 := Logic R.
Module HP := HelloProgNameOn R LG0.
Module GL := GetoptLogicOn R LG0.
Module HV := HelloVersionOn R LG0.
Module HLo := HelloLocaleOn R LG0.
Module HL := HLo.HL.
Module LL := HL.LL.
Module ML := HL.ML.
Module SL := ML.SL.
Module LG := LG0.
Module L := LG.L.
Module GR := GetoptRefinementOn R L.M.
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

(** A pointer store into a cell the program owns keeps wi. *)
Context (Kpstore : forall b reg o x xp m wd h,
  (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
     h !! l = Some v) ->
  wi m wd h ->
  wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
    (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)).

(** atexit has a contract returning an int, which admits the call
    main makes, registering close_stdout, and whose return keeps the
    program's pieces and wi: the registration is libc's state. *)
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
  iEval (rewrite (bytes_take_drop _ _ _ 8); [|rewrite length_replicate; vm_compute; lia]) in "Hy6".
  iEval (rewrite (auxes_take_drop _ _ _ 8); [|rewrite length_replicate; vm_compute; lia]) in "Hc6".
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

(** The rest of main's start block, from setlocale's call: setlocale
    lends every category's new name and sets the codec; the default
    greeting is stored in b4's cell; atexit registers close_stdout; and
    the option loop is entered. *)
Lemma main_start_rest e argc av b4 b6 old c0 r80 Φ :
  start_vars e argc av b4 b6 -> fresh_ok b4 ->
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗
  live b4 (mkRegion b4 (b4 + 16) Heap Live) -∗ bytes b4 0 (replicate 16 0) -∗
  auxes b4 0 (replicate 16 CNone) -∗
  ▷ (∀ e' q (new : Z -> ptr * list Z) c',
       ⌜start_vars e' argc av b4 b6 /\ lookup (TAtom "chk1") e' = Some (WPtr (mkPtr b4 (Obj b4))) /\
        (q = mkPtr 0 CNone \/ q = (new 6).1)⌝ -∗
       ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗ pts (codec_ps c') -∗
       string empty_ptr 69968 r80 [] -∗
       live b4 (mkRegion b4 (b4 + 16) Heap Live) -∗ pcell b4 0 greeting_ptr -∗
       bytes b4 8 (replicate 8 0) -∗ auxes b4 1 (replicate 15 CNone) -∗
       WP (ERun (mkFrame main_fn e' [] None (Enter (TAtom "iw_1.L8") (Some (TAtom "start")))) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (mkFrame main_fn e [] None (Exec (TAtom "start") start_rest (b_jump (main_block "start"))))
        : mexpr) {{ Φ }}.
Proof.
  intros (H0 & H2 & H4 & H6 & H11) (Hb40 & Hb416 & Hb448).
  iIntros "Hks Hcod Hs80 Hl4 Hy4 Hc4 HK".
  destruct main_globals as (G80 & G81 & Gcs). pose proof Hlinked as (Hm & Hg & _).
  rewrite /start_rest. cbn [b_jump main_block hblk].
  (* setlocale(LC_ALL, ""). *)
  iApply (wp_main_setlocale with "Hks Hcod Hs80"); [word_premise | word_premise | cbn; tauto |].
  iNext. iIntros (q new c' Hq) "Hs80 Hcod Hlent". gen_env.
  (* The default greeting, stored in b4's cell. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hg _ _ G81); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_check with "Hl4");
    [reflexivity | word_premise | reflexivity | addr_premise | cbn [ptr_addr r_end]; unfold raw_address; drop_wraps_goal; lia |
     cbn [ptr_addr]; unfold raw_address; drop_wraps_goal; rewrite Z.add_0_r; apply mod16_mod8; exact Hb416 |].
  iNext. iIntros "Hl4". gen_env.
  iEval (rewrite (bytes_take_drop _ _ _ 8); [|rewrite length_replicate; lia]) in "Hy4".
  iEval (rewrite (auxes_take_drop _ _ _ 1); [|rewrite length_replicate; lia]) in "Hc4".
  iDestruct "Hy4" as "[Hy4 Hy4']". iDestruct "Hc4" as "[Hc4 Hc4']".
  iAssert (pcell b4 0 (mkPtr 0 CNone)) with "[Hy4 Hc4]" as "Hp4"; [iApply zero_pcell; iFrame|].
  iApply (wp_raw_store_pointer with "Hl4 Hp4");
    [word_premise | word_premise | reflexivity | addr_premise |
     rewrite Z.add_0_r; apply mod16_mod8; exact Hb416 |
     intros m wd h Hin Hw; exact (Kpstore _ _ _ _ _ _ _ _ Hin Hw) |].
  iNext. iIntros "Hl4 Hp4".
  (* atexit(close_stdout). *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hg _ _ Gcs); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ atexit_spec [WPtr close_stdout_ptr] emp%I with "[//] [-]");
    [apply linked_outside; first [exact Hlinked | reflexivity] |
     apply linked_unbound; first [exact Hlinked | reflexivity] | reflexivity | exact Hatexit |
     cbn [map_option]; word_premise | exact Hatexit_abi | |].
  - iIntros (σ) "Hσ _". iDestruct "Hσ" as (h) "[_ %Hf]". destruct Hf as (_ & _ & _ & Hw).
    iPureIntro. exact (Hatexit_pre _ _ _ Hw).
  - iNext. iIntros (σ trace values s' m' w' Hi) "Hσ _".
    iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (Katexit _ _ _ _ _ _ _ _ _ _ _ Hw Ha Hd Hr Hi) as (x & -> & Hx & Ha' & Hd' & Hr' & Hw').
    iModIntro. iExists _. iSplit.
    + iPureIntro. unfold external_env. rewrite Hatexit_ret. cbn. reflexivity.
    + iSplitL "Hh"; [iExists h; iFrame; iPureIntro; auto|].
      iApply wp_goto. iNext. cbn [edge_label]. gen_env.
      iApply ("HK" $! _ q new c' with "[%] Hlent Hcod Hs80 Hl4 Hp4 Hy4' Hc4'").
      split; [repeat split; assumption|]. split; [assumption | exact Hq].
Qed.

(** Main's start block, from its entry to the option loop: the two
    segments above. *)
Lemma main_start argc av ar a0 b0 r0 ys0 r3 r4 x0 x1 y0 old c0 r80 Φ :
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live av ar -∗ pcell av 0 a0 -∗ string a0 b0 r0 ys0 -∗
  HP.HN.literals r3 r4 -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ pts (codec_ps c0) -∗
  string empty_ptr 69968 r80 [] -∗
  ▷ (∀ e b4 b6 (i k : nat) q (new : Z -> ptr * list Z) c',
       ⌜start_vars e argc av b4 b6 /\ lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) /\
        fresh_ok b4 /\ fresh_ok b6 /\ (i <= length ys0)%nat /\ (k <= length ys0)%nat /\
        (q = mkPtr 0 CNone \/ q = (new 6).1)⌝ -∗
       live av ar -∗ pcell av 0 a0 -∗ string a0 b0 r0 ys0 -∗ HP.HN.literals r3 r4 -∗
       HP.HN.name_cells pn nreg sreg nb sb
         (mkPtr (ptr_addr a0 + Z.of_nat i) (ptr_cap a0)) (mkPtr (ptr_addr a0 + Z.of_nat i) (ptr_cap a0))
         (mkPtr (ptr_addr a0 + Z.of_nat k) (ptr_cap a0)) -∗
       ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗ pts (codec_ps c') -∗
       string empty_ptr 69968 r80 [] -∗
       live b4 (mkRegion b4 (b4 + 16) Heap Live) -∗ pcell b4 0 greeting_ptr -∗
       bytes b4 8 (replicate 8 0) -∗ auxes b4 1 (replicate 15 CNone) -∗
       live b6 (mkRegion b6 (b6 + 16) Heap Live) -∗ bytes b6 0 (replicate 8 0) -∗
       bytes b6 8 (replicate 8 0) -∗ auxes b6 0 (clear_slots 0 (replicate 8 CNone)) -∗
       auxes b6 8 (replicate 8 CNone) -∗
       WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom "start")))) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))]) : mexpr) {{ Φ }}.
Proof.
  intros Hav Hav8 Haend Har48. iIntros "Hal Ha0 Hs0 Hlit Hcells Hks Hcod Hs80 HK".
  iApply (main_to_setlocale with "Hal Ha0 Hs0 Hlit Hcells"); [exact Hav | exact Hav8 | exact Haend | exact Har48 |].
  iNext. iIntros (e b4 b6 i k (Hv & Hf4 & Hf6 & Hi & Hk))
    "Hal Ha0 Hs0 Hlit Hcells Hl4 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'".
  iApply (main_start_rest with "Hks Hcod Hs80 Hl4 Hy4 Hc4"); [exact Hv | exact Hf4 |].
  iNext. iIntros (e' q new c' (Hv' & Hc1 & Hq)) "Hlent Hcod Hs80 Hl4 Hp4 Hy4 Hc4".
  iApply ("HK" $! e' b4 b6 i k q new c' with
           "[%] Hal Ha0 Hs0 Hlit Hcells Hlent Hcod Hs80 Hl4 Hp4 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'").
  auto 10.
Qed.

(** ## getopt_long's call

    The run's argv is at av, in an object of the region ar, and holds
    the arguments sargs; the launcher copies each into an object of its
    own. getopt_long's registry entry is Campaign 4's
    [libc_getopt_refined_contract] for this run's input, fixed for the
    run: the safety contract [libc_getopt_contract], whose admission,
    writes and prefixes it keeps, with a transition added to its
    ordinary returns. Main owns argv as one block, the arguments'
    strings and the getopt token; the call hands argv back permuted, the
    strings unchanged and the token naming the new optarg and optind. *)

(** argv: aligned, its argc + 1 slots in its region, argc a positive C
    int, each argument a C string. *)
Context (av : Z) (ar : region) (sargs : list argument)
  (Hav : 0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length sargs) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48)
  (Hargc : 1 <= Z.of_nat (length sargs) < 2 ^ 31)
  (Hargs : Forall (fun s => string_ok (arg_ptr s) (arg_base s) (arg_region s) (arg_text s)) sargs).

(** The number of argv's bytes and aux slots. *)
Local Notation argv_len := (8 * (length sargs + 1))%nat.

(** getopt_long has libc's refined contract for this run's input, over
    the native parser's initialized and running representations, its
    allocation requests and the transition an ordinary return makes. *)
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

(** wi admits getopt_long's libc side where main owns argv and the
    arguments: the parser's representation, its private roots and
    reads, and their separation from the call's inputs and outputs. *)
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

(** A return of getopt_long from a memory that agrees with the ghost
    heap, with its live objects apart and the runtime ready, keeps wi,
    with argv's block holding what the memory then holds and the token
    naming the new optarg and optind. *)
Context (Kgetopt : forall r args xs s m w h trace values s' m' w' bs cs,
   M.E.invoke getopt_spec r args xs s m w trace (CallReturn values) s' m' w' ->
   (forall l v, (l, v) ∈ block_ps av ar 0 bs cs -> h !! l = Some v) -> wi m w h ->
   agrees m h -> live_disjoint m -> R.ready s m ->
   wi m' w' (overwrite (block_ps av ar 0 (mem_bytes m' av argv_len) (mem_auxes m' av argv_len) ++
     getopt_ps (getopt_optarg (libc_getopt_view w')) (getopt_optind (libc_getopt_view w'))) h)).

(** A permitted order of argv has argc pointers. *)
Lemma order_length ps : getopt_order (map arg_ptr sargs) ps -> length ps = length sargs.
Proof.
  intros H. rewrite <- (length_map arg_ptr sargs).
  symmetry. apply Permutation_length. exact (getopt_order_inventory _ _ H).
Qed.

(** Owning argv's block holding ps, and the arguments, the memory's
    slots hold ps: [getopt_slots]. *)
Lemma argv_slots m h ps cs :
  agrees m h -> getopt_order (map arg_ptr sargs) ps -> argv_caps cs ps ->
  (forall l v, (l, v) ∈ block_ps av ar 0 (argv_bytes ps) cs -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ flat_map arg_ps sargs -> h !! l = Some v) ->
  getopt_slots m av ps.
Proof.
  intros Ha Ho [Lc Hc] Kb Ks.
  assert (Hlv : live_at m av ar).
  { apply (Ha (PLive av) (VLive ar)), Kb. apply elem_of_cons. left. reflexivity. }
  apply slots_of_at. intros k q Hk.
  assert (Hq : 0 <= ptr_addr q < 2 ^ 64 /\ ~ freed_in (m_regions m) (ptr_cap q)).
  { pose proof (list_elem_of_lookup_2 _ _ _ Hk) as Hq'.
    apply list_elem_of_In, in_app_or in Hq' as [Hq' | [<- | []]].
    - destruct (order_in _ _ _ Ho Hq') as (s & Hs & ->).
      pose proof (proj1 (List.Forall_forall _ _) Hargs s Hs) as (Hcap & Hb0 & Hbp & Hend & H48 & _).
      assert (Hlive : live_at m (arg_base s) (arg_region s)).
      { apply (Ha (PLive (arg_base s)) (VLive (arg_region s))), Ks. apply list_elem_of_In, in_flat_map.
        exists s. split; [exact Hs|]. unfold arg_ps, string_ps. left. reflexivity. }
      split; [lia|]. intros (b' & reg' & Hc' & E' & L'). destruct Hlive as [E1 L1].
      destruct Hcap as [Hc0|Hc0]; rewrite Hc0 in Hc'; destruct Hc' as [E0|E0]; try discriminate E0;
        injection E0 as <-; rewrite E1 in E'; injection E' as <-; congruence.
    - split; [cbn; lia|]. intros (b' & reg' & Hc' & _). destruct Hc' as [E0|E0]; discriminate E0. }
  destruct Hq as [Hr Hf]. split; [exact Hr|]. split.
  - intros i Hi.
    assert (Hin : (PByte av (0 + Z.of_nat (8 * k + Z.to_nat i)), VByte (byte_of (ptr_addr q) i)) ∈
                  block_ps av ar 0 (argv_bytes ps) cs).
    { apply elem_of_cons. right. apply elem_of_app. left.
      apply (list_elem_of_lookup_2 _ (8 * k + Z.to_nat i)%nat). apply byte_ps_lookup.
      unfold argv_bytes. rewrite (slots_bytes_lookup _ _ _ _ Hk); [|lia].
      rewrite Z2Nat.id; [reflexivity|lia]. }
    destruct (Ha _ _ (Kb _ _ Hin)) as [_ Hil]. destruct (Hil ar (proj1 Hlv) (proj2 Hlv)) as (_ & _ & Hx).
    rewrite <- Hx. f_equal. lia.
  - assert (Hin : (PAux av (0 + Z.of_nat (8 * k)), VAux (ptr_cap q)) ∈ block_ps av ar 0 (argv_bytes ps) cs).
    { apply elem_of_cons. right. apply elem_of_app. right.
      apply (list_elem_of_lookup_2 _ (8 * k)%nat). apply aux_ps_lookup. exact (Hc k q Hk). }
    pose proof (aux_piece_holds _ _ _ _ _ Hlv (Ha _ _ (Kb _ _ Hin))) as Hh.
    replace (av + 8 * Z.of_nat k) with (av + (0 + Z.of_nat (8 * k))) by lia.
    exact (aux_holds_kept _ _ _ Hh Hf).
Qed.

(** The arguments are admitted ([getopt_pre]) where main owns argv's
    block, holding a permitted order ps, the arguments' strings and the
    token, whose optind i is at most argc. *)
Lemma getopt_admitted m w h ps cs a i :
  wi m w h -> agrees m h -> live_disjoint m ->
  getopt_order (map arg_ptr sargs) ps -> argv_caps cs ps -> 0 <= i <= Z.of_nat (length sargs) ->
  (forall l v, (l, v) ∈ block_ps av ar 0 (argv_bytes ps) cs -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ flat_map arg_ps sargs -> h !! l = Some v) ->
  (forall l v, (l, v) ∈ getopt_ps a i -> h !! l = Some v) ->
  getopt_pre (hello_input av sargs) libc_getopt_view (libc_getopt_rep initialized)
    (getopt_words (hello_input av sargs)) m w.
Proof.
  intros Hw Ha Hd Ho Hc Hi Kb Ks Kt.
  assert (Hlv : live_at m av ar).
  { apply (Ha (PLive av) (VLive ar)), Kb. apply elem_of_cons. left. reflexivity. }
  pose proof Hav as (Hav0 & Hav8 & Haend & Har48).
  assert (Hin : getopt_input_at m (hello_input av sargs)).
  { destruct (Htable m w h Hw) as (T1 & T2 & T3).
    unfold getopt_input_at, getopt_vector, getopt_strings, hello_input.
    cbn [getopt_argc getopt_argv getopt_arguments getopt_optstring getopt_short_options getopt_longopts
         getopt_options getopt_longindex].
    split; [lia|]. split; [rewrite length_map; reflexivity|].
    split.
    {
      split; [|split; [|split]].
      - unfold writable_span. cbn [span_size span_ptr ptr_addr ptr_cap]. split; [lia|].
        exists av, ar. split; [reflexivity|]. split; [exact (proj1 Hlv)|]. split; [exact (proj2 Hlv)|].
        apply (access_obj _ _ ar); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
      - cbn [ptr_addr ptr_cap]. apply (access_obj _ _ ar); [exact (proj1 Hlv) | lia | lia | exact Hav8].
      - cbn [ptr_addr ptr_cap]. apply (access_obj _ _ ar); [exact (proj1 Hlv) | lia | lia | exact Hav8].
      - exists ps. split; [rewrite map_map; exact Ho|]. exact (argv_slots m h ps cs Ha Ho Hc Kb Ks). }
    split.
    { apply List.Forall_forall. intros [q t] Hq.
      apply in_map_iff in Hq as (s & E & Hs). injection E as <- <-. cbn [fst snd].
      apply (string_c_string _ _ (arg_base s) (arg_region s)); [exact (proj1 (List.Forall_forall _ _) Hargs s Hs)|].
      apply all_agree_intro. intros l v Hl. apply Ha, Ks. apply list_elem_of_In, in_flat_map.
      exists s. split; [exact Hs | apply list_elem_of_In; exact Hl]. }
    split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [left; reflexivity|].
    vm_compute. reflexivity. }
  assert (Kall : forall l v, (l, v) ∈ block_ps av ar 0 (argv_bytes ps) cs ++ flat_map arg_ps sargs ->
                   h !! l = Some v).
  { intros l v Hl. apply elem_of_app in Hl as [Hl|Hl]; [exact (Kb _ _ Hl) | exact (Ks _ _ Hl)]. }
  destruct (Hgetopt_env m w h _ _ Hw Ha Hd Kall Hin) as (Hrep & Hroots & Hreads & Hsep & Hdisj & Hpriv).
  destruct (Hgetopt_wi m w h Hw) as (Hst & _ & _ & Hcur).
  destruct (Hcur a i (Kt _ _ ltac:(left))) as [_ Hi'].
  split; [reflexivity|]. split; [exact Hin|]. split; [exact Hrep|]. split; [exact Hst|].
  split; [rewrite Hi'; unfold hello_input; cbn [getopt_argc]; lia|].
  split; [exact Hroots|]. split; [exact Hreads|]. split; [exact Hsep|]. split; [exact Hdisj | exact Hpriv].
Qed.

(** A return of getopt_long satisfies its postcondition. *)
Lemma getopt_returned r args xs s m w trace values s' m' w' :
  M.E.invoke getopt_spec r args xs s m w trace (CallReturn values) s' m' w' ->
  exists born, getopt_post (hello_input av sargs) libc_getopt_view (libc_getopt_rep initialized)
    xs m w born trace (CallReturn values) m' w'.
Proof.
  intros H. apply GR.refined_invoke_base in H.
  inversion H as [trace' ending s0 m0 w0 born Habi Hpre Hp Hpost | ]; subst. exists born. exact Hpost.
Qed.

(** What a return of getopt_long with values from the token a, i shows
    of the transition: a call from a memory and world where wi holds
    with the token's pieces made that transition. *)
Definition getopt_step (a : ptr) (i : Z) (values : list word) : Prop :=
  exists xs m w h born trace m' w',
    wi m w h /\ (forall l v, (l, v) ∈ getopt_ps a i -> h !! l = Some v) /\
    transition xs m w born trace values m' w'.

(** A return of getopt_long, from a memory and world where wi holds
    with the token's pieces, makes the transition: [refined_return]. *)
Lemma getopt_stepped r args xs s m w h trace values s' m' w' a i :
  M.E.invoke getopt_spec r args xs s m w trace (CallReturn values) s' m' w' -> wi m w h ->
  (forall l v, (l, v) ∈ getopt_ps a i -> h !! l = Some v) -> getopt_step a i values.
Proof.
  intros Hi Hw Kt. destruct (GR.refined_return _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Ht).
  exists xs, m, w, h, born, trace, m', w'. auto.
Qed.

(** A return of the call keeps every piece but argv's bytes and slots
    agreeing ([prefix_agrees_out]): its roots and libc's cells are apart
    from the program's objects, and argv is the one block of the
    program's it writes. So with argv's block holding what the memory
    then holds, and any token, the ghost heap agrees; the live objects
    stay apart and the runtime ready. *)
Lemma getopt_frame_ok r args s m w h trace values s' m' w' ps cs a' i' :
  M.E.invoke getopt_spec r args (getopt_words (hello_input av sargs)) s m w trace (CallReturn values) s' m' w' ->
  wi m w h -> agrees m h -> live_disjoint m -> R.ready s m ->
  length (argv_bytes ps) = argv_len -> length cs = argv_len ->
  (forall l v, (l, v) ∈ block_ps av ar 0 (argv_bytes ps) cs -> h !! l = Some v) ->
  agrees m' (overwrite (block_ps av ar 0 (mem_bytes m' av argv_len) (mem_auxes m' av argv_len) ++
                        getopt_ps a' i') h) /\
  live_disjoint m' /\ R.ready s' m'.
Proof.
  intros Hi Hw Ha Hd Hr Lx Lc Kb.
  pose proof Hav as (Hav0 & Hav8 & Haend & Har48).
  assert (Hlv : live_at m av ar).
  { apply (Ha (PLive av) (VLive ar)), Kb. apply elem_of_cons. left. reflexivity. }
  destruct (Hgetopt_apart m w h Hw) as [Hroots Hrel].
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  set (ks := (byte_ps av 0 (argv_bytes ps) ++ aux_ps av 0 cs).*1).
  set (outs := fun x => span_contains (mkSpan (mkPtr av (Obj av)) (8 * (Z.of_nat (length sargs) + 1))) x).
  assert (Hwr : contract_writes getopt_spec (getopt_words (hello_input av sargs)) m w =
                (getopt_roots (libc_getopt_view w) ++ getopt_cells (libc_getopt_view w)) ++
                  [mkSpan (mkPtr av (Obj av)) (8 * (Z.of_nat (length sargs) + 1))]).
  { rewrite <- app_assoc. reflexivity. }
  destruct (prefix_agrees_out _ _ _ _ _ _ _ _ _ _ _ h ks outs Hp Hr Hd) as (Ha' & _ & Hd' & _).
  - intros l v Hl _. exact (Ha l v Hl).
  - intros l v Hl Hm. exact (agree_piece_registered _ _ _ Hm (Ha l v Hl)).
  - rewrite Hwr. intros sp x Hin Hsp Hol. apply in_app_or in Hin as [Hin|Hin].
    + exfalso. exact (Hroots sp x Hin Hsp Hol).
    + destruct Hin as [<-|[]]. exact Hsp.
  - intros l v Hl Hk. destruct l as [b|b o|b o|k]; try exact I; intros reg Hlv' Ho' He' Hout; apply Hk;
      unfold outs, span_contains in Hout; cbn [span_ptr span_size ptr_addr] in Hout;
      (apply (block_key m av ar 0 (argv_bytes ps) cs _ b o reg Hd Hlv);
       [lia | rewrite Lx; lia | rewrite Lc Lx; reflexivity | auto | exact Hlv' | exact Ho' | exact He' |
        rewrite Lx; lia]).
  - exact Hrel.
  - assert (Hlv' : live_at m' av ar).
    { apply (Ha' (PLive av) (VLive ar)); [apply Kb; apply elem_of_cons; left; reflexivity|].
      exact (live_not_key _ _ _ _ _). }
    split; [|split; [exact Hd' | exact Hr']].
    intros l v Hl. apply lookup_overwrite in Hl as [Hin | [Hnk Hh]].
    + apply elem_of_app in Hin as [Hin|Hin].
      * pose proof (block_after m' av ar 0 argv_len l v Hlv') as H. rewrite !Z.add_0_r in H.
        apply H; [lia | lia | exact Hin].
      * apply list_elem_of_singleton in Hin. injection Hin as -> ->. exact I.
    + apply (Ha' l v Hh). intros Hk. apply Hnk. rewrite fmap_app. apply elem_of_app. left.
      pose proof (block_keys_after m' av ar 0 (argv_bytes ps) cs argv_len l Lx Lc Hk) as H.
      rewrite Z.add_0_r in H. exact H.
Qed.

(** getopt_long(argc, argv, "g:t", longopts, NULL)'s triple, from
    [libc_getopt_contract]: owning argv's block, holding a permitted
    order ps of the arguments, their strings, and the token, whose
    optind is at most argc, the call binds d to its code, a C int, and
    hands back argv holding another permitted order, the strings, and
    the token naming the new optarg and optind, in range; a 'g' comes
    with a nonnull borrow of an argument, and the code is a
    [getopt_step] from the token. *)
Lemma wp_main_getopt f e ls lab d va vv vs vl vi rest j ps cs a i Φ :
  map_option (arg_x ge e) [Arg W va; Arg P vv; Arg P vs; Arg P vl; Arg P vi] =
    Some (getopt_words (hello_input av sargs)) ->
  getopt_order (map arg_ptr sargs) ps -> argv_caps cs ps -> 0 <= i <= Z.of_nat (length sargs) ->
  pts (block_ps av ar 0 (argv_bytes ps) cs) -∗ pts (flat_map arg_ps sargs) -∗ pts (getopt_ps a i) -∗
  ▷ (∀ code ps' cs' a' i',
       ⌜getopt_order (map arg_ptr sargs) ps' /\ argv_caps cs' ps' /\ 0 <= i' <= Z.of_nat (length sargs) /\
        getopt_int code /\ (code = 103 -> getopt_borrow (hello_input av sargs) a' /\ ptr_addr a' <> 0) /\
        getopt_step a i [WInt (code mod 2 ^ 32)]⌝ -∗
       pts (block_ps av ar 0 (argv_bytes ps') cs') -∗ pts (flat_map arg_ps sargs) -∗ pts (getopt_ps a' i') -∗
       WP (ERun (mkFrame f (put d (WInt (code mod 2 ^ 32)) e) ls None (Exec lab rest j)) : mexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
     (Exec lab (Call (CResult d W) (Global (TAtom "getopt_long"))
                  [Arg W va; Arg P vv; Arg P vs; Arg P vl; Arg P vi] :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hx Ho Hc Hi. iIntros "Hb Hs Ht HK".
  assert (Lp : length ps = length sargs) by exact (order_length ps Ho).
  assert (Lx : length (argv_bytes ps) = argv_len).
  { unfold argv_bytes. rewrite length_slots_bytes length_app Lp. cbn [length]. lia. }
  assert (Lc : length cs = argv_len).
  { destruct Hc as [Lc _]. rewrite Lc length_app Lp. cbn [length]. lia. }
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ getopt_spec (getopt_words (hello_input av sargs))
            (pts (block_ps av ar 0 (argv_bytes ps) cs) ∗ pts (flat_map arg_ps sargs) ∗ pts (getopt_ps a i))
            with "[$Hb $Hs $Ht] [HK]");
    [apply linked_outside; first [exact Hlinked | reflexivity] |
     apply linked_unbound; first [exact Hlinked | reflexivity] | reflexivity | exact Hgetopt | exact Hx | | |].
  - split; [right; eexists; reflexivity | do 5 eexists; reflexivity].
  - iIntros (σ) "Hσ (Hb & Hs & Ht)". iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Hb") as %Kb. iDestruct (pts_lookup with "Hh Hs") as %Ks.
    iDestruct (pts_lookup with "Hh Ht") as %Kt. iPureIntro.
    exact (getopt_admitted _ _ _ _ _ _ _ Hw Ha Hd Ho Hc Hi Kb Ks Kt).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) (Hb & Hs & Ht)".
    destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Hb") as %Kb. iDestruct (pts_lookup with "Hh Ht") as %Kt.
    destruct (getopt_returned _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & _ & Hin' & _ & _ & code & Hend & Hres).
    injection Hend as ->.
    pose proof (getopt_stepped _ _ _ _ _ _ _ _ _ _ _ _ a i Hinv Hw Kt) as Hstep.
    change (getopt_argc (hello_input av sargs)) with (Z.of_nat (length sargs)) in Hres.
    assert (E : (Z.of_nat (length sargs) =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite E in Hres. destruct Hres as (_ & _ & Hrange & Hresult).
    destruct (hello_code _ _ _ _ _ Hresult) as [Hint Hg].
    destruct Hin' as (_ & _ & (_ & _ & _ & ps' & Ho' & Hsl') & _).
    rewrite hello_input_order in Ho'.
    change (ptr_addr (getopt_argv (hello_input av sargs))) with av in Hsl'.
    assert (Lp' : length ps' = length sargs) by exact (order_length ps' Ho').
    destruct (argv_of_slots m' av ps' Hsl') as [Eb Ec].
    assert (EL : (8 * length (ps' ++ [null]))%nat = argv_len) by (rewrite length_app Lp'; reflexivity).
    rewrite EL in Eb, Ec.
    set (a' := getopt_optarg (libc_getopt_view w')). set (i' := getopt_optind (libc_getopt_view w')).
    destruct (getopt_frame_ok _ _ _ _ _ _ _ _ _ _ _ ps cs a' i' Hinv Hw Ha Hd Hr Lx Lc Kb) as (Ha' & Hd' & Hr').
    pose proof (Kgetopt _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv Kb Hw Ha Hd Hr) as Hw'.
    rewrite Eb in Ha', Hw'.
    iMod (pts_update _ (block_ps av ar 0 (argv_bytes ps) cs ++ getopt_ps a i)
            (block_ps av ar 0 (argv_bytes ps') (mem_auxes m' av argv_len) ++ getopt_ps a' i')
            with "Hh [Hb Ht]") as "[Hh Hn]".
    { rewrite !fmap_app. rewrite (block_ps_keys av ar 0 (argv_bytes ps) cs); [reflexivity | |].
      - rewrite <- Eb, length_mem_bytes. symmetry. exact Lx.
      - rewrite length_mem_auxes. symmetry. exact Lc. }
    { rewrite pts_app. iFrame. }
    iModIntro. iExists (put d (WInt (code mod 2 ^ 32)) e). iSplit.
    { iPureIntro. unfold external_env. cbn. rewrite Z.mod_mod; [reflexivity | lia]. }
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. auto.
    + rewrite pts_app. iDestruct "Hn" as "[Hb Ht]".
      iApply ("HK" $! code ps' (mem_auxes m' av argv_len) a' i' with "[%] Hb Hs Ht").
      split; [exact Ho'|]. split; [exact Ec|]. split; [exact Hrange|]. split; [exact Hint|].
      split; [exact Hg | exact Hstep].
Qed.

(** ## The option loop

    Main calls getopt_long until it returns -1, at block iw_1.L8. A 'g'
    stores optarg in the greeting's cell b4 (iw_1.L35), a 't' the
    traditional greeting (iw_1.L42); any other code but --help and
    --version sets pr.2, the "lose" flag (iw_1.L52). Each goes back
    round. getopt_long promises no bound on its calls, so the loop is
    proved by Löb induction: each round enters a block, which takes a
    step. Its exits are the version and help blocks, iw_1.L21 and
    iw_1.L39, and the end of options, iw_1.L10, which the proof leaves
    to continuations. *)

(** libc's optarg cell is the global optarg, and both cells are at
    word addresses. *)
Context (Hoptarg_g : lookup (TAtom "optarg") (ge_globals ge) = Some optarg_cell)
  (Hcells : 0 <= ptr_addr optarg_cell < 2 ^ 64 /\ 0 <= ptr_addr optind_cell < 2 ^ 64).

(** The greetings b4's cell may hold in the loop: the default, the
    traditional one, or a nonnull borrow of an argument. *)
Definition greeting_ok (g : ptr) : Prop :=
  g = greeting_ptr \/ g = traditional_ptr \/ (getopt_borrow (hello_input av sargs) g /\ ptr_addr g <> 0).

(** What main owns in the loop: argv's block holding ps, the
    arguments' strings, the getopt token, and the greeting's cell b4
    holding g. *)
Definition loop_res (b4 : Z) (ps : list ptr) (cs : list cap) (a : ptr) (i : Z) (g : ptr) : iProp Σ :=
  pts (block_ps av ar 0 (argv_bytes ps) cs) ∗ pts (flat_map arg_ps sargs) ∗ pts (getopt_ps a i) ∗
  live b4 (mkRegion b4 (b4 + 16) Heap Live) ∗ pcell b4 0 g.

(** What main knows in the loop: its temporaries, argv's order, the
    token's optind in range and the greeting. *)
Definition loop_facts (e : env) (b4 b6 : Z) (ps : list ptr) (cs : list cap) (i : Z) (g : ptr) : Prop :=
  start_vars e (Z.of_nat (length sargs)) av b4 b6 /\
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr b4 (Obj b4))) /\ fresh_ok b4 /\
  getopt_order (map arg_ptr sargs) ps /\ argv_caps cs ps /\ 0 <= i <= Z.of_nat (length sargs) /\
  greeting_ok g.

(** The loop's entry by the edge from: from start with pr.2 0, from
    iw_1.L52 with 1, and from iw_1.L35 or iw_1.L42 with what pr.2 was. *)
Definition loop_entry (from : String.string) (e : env) (lose : Z) : Prop :=
  (from = "start"%string /\ lose = 0) \/ (from = "iw_1.L52"%string /\ lose = 1) \/
  ((from = "iw_1.L35"%string \/ from = "iw_1.L42"%string) /\
   lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ (lose = 0 \/ lose = 1)).

(** An exit of the loop: entering the block lab from the block from,
    with the loop's facts and pieces and pr.2 bound to 0 or 1. *)
Definition loop_exit (b4 b6 : Z) (lab from : String.string)
    (Φ : language.val (nanofil_lang registry ge) → iProp Σ) : iProp Σ :=
  ∀ e ps cs a i g lose,
    ⌜loop_facts e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ (lose = 0 \/ lose = 1)⌝ -∗
    loop_res b4 ps cs a i g -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom lab) (Some (TAtom from)))) : mexpr) {{ Φ }}.

(** The option loop, from its entry by any edge to one of its exits. *)
Lemma main_loop b4 b6 Φ :
  ⊢ ∀ from e lose ps cs a i g,
  ⌜loop_entry from e lose /\ loop_facts e b4 b6 ps cs i g⌝ -∗ loop_res b4 ps cs a i g -∗
  (loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ ∧ loop_exit b4 b6 "iw_1.L39"%string "iw_1.L50"%string Φ ∧
   loop_exit b4 b6 "iw_1.L10"%string "iw_1.L8"%string Φ) -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom from)))) : mexpr) {{ Φ }}.
Proof.
  unfold loop_res, loop_exit.
  iLöb as "IH". iIntros (from e lose ps cs a i g [Hent Hf]) "(Hb & Hs & Ht & Hl4 & Hp4) HK".
  destruct Hf as ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg).
  pose proof Hfr as (Hb40 & Hb416 & Hb448).
  assert (Hlose : lose = 0 \/ lose = 1).
  { destruct Hent as [[_ ->] | [[_ ->] | [_ [_ Hl]]]]; auto. }
  destruct getopt_globals as (G69 & G64 & G76 & _). pose proof Hlinked as (Hm & Hglob & _).
  pose proof Hargc as Hargc'.
  (* Enter iw_1.L8: pr.2 is lose. *)
  iApply (wp_enter _ _ _ _ _ _ _ _ (main_block "iw_1.L8") (put (TAtom "iw_1.pr.2") (WInt lose) e)).
  { vm_compute. reflexivity. }
  { destruct Hent as [[-> ->] | [[-> ->] | [[-> | ->] [Hpr _]]]]; word_premise. }
  iNext. cbn [b_insts b_jump main_block hblk]. gen_env.
  (* getopt_long(argc, argv, "g:t", longopts, NULL). *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hglob _ _ G69); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite (Hglob _ _ G64); reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_main_getopt with "Hb Hs Ht"); [word_premise | exact Ho | exact Hc | exact Hi |].
  iNext. iIntros (code ps' cs' a' i' (Ho' & Hc' & Hi' & Hint & Hgc & _)) "Hb Hs Ht".
  pose proof (int32_end code Hint) as Hcend. pose proof (fun k => int32_eq code k Hint) as Hceq.
  pose proof (Z.mod_pos_bound code (2 ^ 32) ltac:(lia)) as Hcr.
  set (c := code mod 2 ^ 32) in *. clearbody c. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 4294967295) as [-> | Hn1].
  { (* -1: the end of options. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iDestruct "HK" as "[_ [_ HK]]".
    iApply ("HK" $! _ ps' cs' a' i' g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
    split; [|split; [assumption | exact Hlose]].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  mn_enter "iw_1.L19".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 129) as [-> | H129].
  { (* --version. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iDestruct "HK" as "[HK _]".
    iApply ("HK" $! _ ps' cs' a' i' g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
    split; [|split; [assumption | exact Hlose]].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  mn_enter "iw_1.L48".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 103) as [-> | H103].
  { (* 'g': the greeting is optarg. *)
    pose proof (proj1 (Hceq 103 ltac:(lia)) eq_refl) as ->.
    destruct (Hgc eq_refl) as [Hborrow Hnz].
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
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
    iApply ("IH" $! "iw_1.L35"%string _ lose ps' cs' a' i' a' with "[%] [$Hb $Hs $Ht $Hl4 $Hp4] HK").
    split; [right; right; split; [left; reflexivity | split; [assumption | exact Hlose]]|].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|].
    split; [exact Ho'|]. split; [exact Hc'|]. split; [exact Hi'|]. right; right; split; assumption. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  mn_enter "iw_1.L50".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 128) as [-> | H128].
  { (* --help. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iDestruct "HK" as "[_ [HK _]]".
    iApply ("HK" $! _ ps' cs' a' i' g lose with "[%] [$Hb $Hs $Ht $Hl4 $Hp4]").
    split; [|split; [assumption | exact Hlose]].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto. }
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  mn_enter "iw_1.L52".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros ?m; word_premise |]. iNext. gen_env.
  destruct (Z.eq_dec c 116) as [-> | H116].
  { (* 't': the traditional greeting. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
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
    iApply ("IH" $! "iw_1.L42"%string _ lose ps' cs' a' i' traditional_ptr
              with "[%] [$Hb $Hs $Ht $Hl4 $Hp4] HK").
    split; [right; right; split; [right; reflexivity | split; [assumption | exact Hlose]]|].
    split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|].
    split; [exact Ho'|]. split; [exact Hc'|]. split; [exact Hi'|]. right; left; reflexivity. }
  (* Any other code: an unknown option; pr.2 is 1. *)
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  iApply ("IH" $! "iw_1.L52"%string _ 1 ps' cs' a' i' g with "[%] [$Hb $Hs $Ht $Hl4 $Hp4] HK").
  split; [right; left; split; reflexivity|].
  split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
Qed.

(** argv's block, holding q first: its life, q's cell, and the rest's
    bytes and slots. *)
Lemma argv_block_split b reg q rest cs :
  pts (block_ps b reg 0 (argv_bytes (q :: rest)) (ptr_cap q :: cs)) ⊣⊢
  live b reg ∗ pcell b 0 q ∗ bytes b 8 (argv_bytes rest) ∗ auxes b 1 cs.
Proof.
  rewrite block_pts /bytes /auxes /pcell /argv_bytes /slots_bytes. cbn [app flat_map].
  rewrite byte_ps_app aux_ps_cons. change (length (slot_bytes (ptr_addr q))) with 8%nat.
  change (0 + Z.of_nat 8) with 8. change (0 + 1) with 1.
  assert (E : byte_ps b 0 (slot_bytes (ptr_addr q)) = cell b 0 (ptr_addr q)) by reflexivity.
  rewrite E pts_app.
  change ((PAux b 0, VAux (ptr_cap q)) :: aux_ps b 1 cs) with ([(PAux b 0, VAux (ptr_cap q))] ++ aux_ps b 1 cs).
  change ((PAux b 0, VAux (ptr_cap q)) :: cell b 0 (ptr_addr q)) with
    ([(PAux b 0, VAux (ptr_cap q))] ++ cell b 0 (ptr_addr q)).
  rewrite !pts_app.
  iSplit; [iIntros "(Hl & [Hc Hy] & [Ha Hx])" | iIntros "(Hl & [Ha Hc] & Hy & Hx)"]; iFrame.
Qed.

(** Main from its entry to the option loop's first entry: [main_start],
    with argv's first slot and string out of argv's block and the
    arguments, then put back. The continuation is given the loop's
    pieces and facts, and everything the start block leaves outside the
    loop. *)
Lemma main_to_L8 s0 srest r3 r4 x0 x1 y0 old c0 r80 cs0 a ix Φ :
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
       ⌜loop_facts e b4 b6 (map arg_ptr sargs) cs0 ix greeting_ptr⌝ -∗
       loop_res b4 (map arg_ptr sargs) cs0 a ix greeting_ptr -∗
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
       WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L8") (Some (TAtom "start")))) : mexpr)
         {{ Φ }}) -∗
  WP (ERun (invocation main_fn [WInt (Z.of_nat (length sargs)); WPtr (mkPtr av (Obj av))]) : mexpr) {{ Φ }}.
Proof.
  intros Hhd [Lc Hc] Hix. iIntros "Hb Hs Ht Hlit Hcells Hks Hcod Hs80 HK".
  pose proof Hav as (Hav0 & Hav8 & Haend & Har48).
  assert (Hok0 : string_ok (arg_ptr s0) (arg_base s0) (arg_region s0) (arg_text s0)).
  { apply (proj1 (List.Forall_forall _ _) Hargs). rewrite Hhd. left. reflexivity. }
  assert (Ec0 : exists csr, cs0 = ptr_cap (arg_ptr s0) :: csr).
  { pose proof (Hc 0%nat (arg_ptr s0)) as H. rewrite Hhd in H. specialize (H eq_refl).
    destruct cs0 as [|c csr]; [discriminate H|]. cbn in H. injection H as ->. eauto. }
  destruct Ec0 as (csr & ->).
  assert (Eps : map arg_ptr sargs = arg_ptr s0 :: map arg_ptr srest) by (rewrite Hhd; reflexivity).
  assert (Efl : flat_map arg_ps sargs = arg_ps s0 ++ flat_map arg_ps srest) by (rewrite Hhd; reflexivity).
  iEval (rewrite Eps argv_block_split) in "Hb". iDestruct "Hb" as "(Hal & Ha0 & Hy & Hx)".
  iEval (rewrite Efl pts_app) in "Hs". iDestruct "Hs" as "[Hs0 Hsr]".
  iAssert (string (arg_ptr s0) (arg_base s0) (arg_region s0) (arg_text s0)) with "[Hs0]" as "Hstr".
  { iSplit; [iPureIntro; exact Hok0 | iExact "Hs0"]. }
  iApply (main_start with "Hal Ha0 Hstr Hlit Hcells Hks Hcod Hs80"); [lia | exact Hav8 | lia | exact Har48 |].
  iNext. iIntros (e b4 b6 i k q new c' (Hv & Hc1 & Hf4 & Hf6 & Hi & Hk & Hq))
    "Hal Ha0 Hstr Hlit Hcells Hlent Hcod Hs80 Hl4 Hp4 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'".
  iDestruct "Hstr" as "[_ Hs0]".
  iAssert (pts (block_ps av ar 0 (argv_bytes (map arg_ptr sargs)) (ptr_cap (arg_ptr s0) :: csr)))
    with "[Hal Ha0 Hy Hx]" as "Hb".
  { rewrite Eps argv_block_split. iFrame. }
  iAssert (pts (flat_map arg_ps sargs)) with "[Hs0 Hsr]" as "Hs".
  { rewrite Efl pts_app. iFrame. }
  iApply ("HK" $! e b4 b6 i k q new c' with
            "[%] [%] [Hb Hs Ht Hl4 Hp4] Hlit Hcells Hlent Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'").
  - auto 10.
  - split; [exact Hv|]. split; [exact Hc1|]. split; [exact Hf4|].
    split; [rewrite Eps; split; [reflexivity | apply Permutation_refl]|].
    split; [split; [exact Lc | exact Hc]|]. split; [exact Hix|]. left. reflexivity.
  - rewrite /loop_res. iFrame.
Qed.

(** Main from its entry to the option loop's exits: [main_to_L8], then
    [main_loop] from start. The continuation is given everything the
    start block leaves outside the loop, and builds the exits. *)
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
Proof.
  intros Hhd Hcs Hix. iIntros "Hb Hs Ht Hlit Hcells Hks Hcod Hs80 HK".
  iApply (main_to_L8 with "Hb Hs Ht Hlit Hcells Hks Hcod Hs80"); [exact Hhd | exact Hcs | exact Hix |].
  iNext. iIntros (e b4 b6 i k q new c' Hst Hf) "Hres Hlit Hcells Hlent Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'".
  iApply (main_loop b4 b6 Φ $! "start"%string e 0 (map arg_ptr sargs) cs0 a ix greeting_ptr
            with "[%] Hres [-]").
  - split; [left; split; reflexivity | exact Hf].
  - iApply ("HK" $! e b4 b6 i k q new c' with "[%] Hlit Hcells Hlent Hcod Hs80 Hy4 Hc4 Hl6 Hy6 Hy6' Hc6 Hc6'").
    exact Hst.
Qed.

(** ## The operand check

    After the options, main checks that no operand is left: unless pr.2
    is set, it compares optind with argc (iw_1.L59), and if an operand
    remains or pr.2 is set, it loads argv[optind] (iw_1.L55). A nonnull
    one is an extra operand (iw_1.L79); a null one, with pr.2 set,
    leads to the hint to try --help (iw_1.L113). Otherwise main goes on
    to greet (iw_1.join). optind is the token's, at most argc, so the
    load is of one of argv's argc + 1 slots. *)

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

(** argv's block holding ps: its life, the slots before slot k, slot
    k's pointer cell, and the slots after it. *)
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

(** An exit of the operand check: entering the block lab from the
    block from, with the loop's facts and pieces and pr.2 bound to
    lose, where P lose i holds of pr.2 and optind. *)
Definition operand_exit (b4 b6 : Z) (lab from : String.string) (P : Z -> Z -> Prop)
    (Φ : language.val (nanofil_lang registry ge) → iProp Σ) : iProp Σ :=
  ∀ e ps cs a i g lose,
    ⌜loop_facts e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\ P lose i⌝ -∗
    loop_res b4 ps cs a i g -∗
    WP (ERun (mkFrame main_fn e [] None (Enter (TAtom lab) (Some (TAtom from)))) : mexpr) {{ Φ }}.

(** iw_1.L55: argv[optind], at most argc, is loaded; a nonnull one
    goes to iw_1.L79 with optind below argc, a null one to iw_1.L113,
    which only pr.2 set reaches, as without it optind is below argc. *)
Lemma operand_L55 b4 b6 e ps cs a i g lose Φ :
  ⌜loop_facts e b4 b6 ps cs i g /\ lookup (TAtom "iw_1.pr.2") e = Some (WInt lose) /\
   (lose = 0 \/ lose = 1) /\ (lose = 0 -> i < Z.of_nat (length sargs))⌝ -∗
  loop_res b4 ps cs a i g -∗
  (operand_exit b4 b6 "iw_1.L79"%string "iw_1.L55"%string (fun _ i => i < Z.of_nat (length sargs)) Φ ∧
   operand_exit b4 b6 "iw_1.L113"%string "iw_1.L55"%string
     (fun lose i => lose = 1 /\ i = Z.of_nat (length sargs)) Φ) -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "iw_1.L55") (Some (TAtom "iw_1.L60")))) : mexpr) {{ Φ }}.
Proof.
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

(** The operand check, from iw_1.L10, entered at the end of options,
    to its three exits. *)
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
  iIntros ((Hf & Hpr & Hlose)) "Hr HK".
  pose proof Hf as ((H0 & H2 & H4 & H6 & H11) & Hc1 & Hfr & Ho & Hc & Hi & Hg).
  pose proof Hargc as Hargc'.
  mn_enter "iw_1.L10".
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ lose); [word_premise|]. iNext.
  destruct Hlose as [El | El]; subst lose; cbn [Z.eqb edge_label].
  - (* pr.2 clear: is optind below argc? *)
    mn_enter "iw_1.L59". unfold loop_res. iDestruct "Hr" as "(Hb & Hs & Ht & Hl4 & Hp4)".
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
  - (* pr.2 set: straight to argv[optind]. *)
    mn_enter "iw_1.L60". gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply (operand_L55 b4 b6 _ ps cs a i g 1 with "[%] Hr [HK]").
    + split; [|split; [assumption | split; [right; reflexivity | intros E; discriminate E]]].
      split; [repeat split; assumption|]. split; [assumption|]. split; [exact Hfr|]. auto.
    + iSplit; [iDestruct "HK" as "[H _]" | iDestruct "HK" as "[_ [H _]]"]; iExact "H".
Qed.

(** The operand check is the loop's end-of-options exit. *)
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

(** exit has a contract that admits any canonical status and never
    returns to main. The handlers it runs, close_stdout among them, are
    the ending's, not main's: in this language the call stalls. *)
Context (exit_spec : contract libc_world)
  (Hexit : registry (TAtom "exit") = Some exit_spec)
  (Hexit_abi : forall v, contract_abi exit_spec CVoid [Arg W v])
  (Hexit_pre : forall n m w h, 0 <= n < 2 ^ 32 -> wi m w h -> contract_pre exit_spec [WInt n] m w)
  (Hexit_post : forall args n s m w tr vs s' m' w',
    M.E.invoke exit_spec CVoid args [WInt n] s m w tr (CallReturn vs) s' m' w' -> False).

(** exit(n), for a canonical n, is safe under every postcondition. *)
Lemma wp_main_exit f e ls lab v rest j n Φ :
  arg_x ge e (Arg W v) = Some (WInt n) -> 0 <= n < 2 ^ 32 ->
  ⊢ WP (ERun (mkFrame f e ls None (Exec lab
    (Call CVoid (Global (TAtom "exit")) [Arg W v] :: rest) j)) : mexpr) {{ Φ }}.
Proof.
  intros Hv Hn.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ exit_spec [WInt n] True%I with "[] []").
  - apply linked_outside; [exact Hlinked|reflexivity].
  - apply linked_unbound; [exact Hlinked|reflexivity].
  - reflexivity.
  - exact Hexit.
  - cbn [map_option]. rewrite Hv. reflexivity.
  - apply Hexit_abi.
  - iIntros (σ) "Hσ _". iDestruct "Hσ" as (h) "[_ %Hσ]". iPureIntro.
    exact (Hexit_pre _ _ _ _ Hn (proj2 (proj2 (proj2 Hσ)))).
  - done.
  - iNext. iIntros (σ tr vs s' m' w' Hi) "_ _". exfalso. exact (Hexit_post _ _ _ _ _ _ _ _ _ _ Hi).
Qed.

(** libc's stdout: the world keeps its cell readable and holding the
    stream, as HelloVersion's footer assumes. *)
Context (stdout_cell stream : ptr)
  (Hstdout_g : lookup (TAtom "stdout") (ge_globals ge) = Some stdout_cell)
  (wi_stdout : forall m w h, wi m w h ->
    access_res m (raw_address (ptr_addr stdout_cell) 0) (ptr_cap stdout_cell) 8 Read 8 = Some ok /\
    pointer_load_effects m (raw_address (ptr_addr stdout_cell) 0)
      [AuxRead; LowerResolve; AddressRead] = Some stream).

(** version_etc's premises, as HelloVersion's [version_etc_spec] takes
    them: the literal pieces main owns, the authors' lives among them,
    the six output contracts and the frame of its allocations, stores
    and snapshot. *)
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

(** The version block's literals are linked where HelloVersion reads
    them. *)
Lemma main_version_lookup s :
  In s ["hello#str.70"; "hello#str.63"; "hello#str.71"; "hello#str.72";
        "hello#str.73"; "hello#str.74"; "hello#str.75"] ->
  lookup (TAtom s) (ge_globals ge) = Some (version_literal s).
Proof.
  intros Hin. apply (proj1 (proj2 Hlinked)).
  repeat destruct Hin as [<- | Hin]; try contradiction; vm_compute; reflexivity.
Qed.

(** proper_name(p), from main: the helper is the identity, so d is
    bound to p and nothing main owns changes. *)
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

(** --version, iw_1.L21: main loads stdout, names the four authors,
    calls version_etc and exits with 0. Only the version literals are
    needed; the loop's pieces are left behind, since exit does not
    return. *)
Lemma main_version b4 b6 Φ :
  pts version_ps -∗ loop_exit b4 b6 "iw_1.L21"%string "iw_1.L19"%string Φ.
Proof.
  pose proof (main_version_lookup "hello#str.70" ltac:(simpl; tauto)) as H70.
  pose proof (main_version_lookup "hello#str.63" ltac:(simpl; tauto)) as H63.
  pose proof (main_version_lookup "hello#str.71" ltac:(simpl; tauto)) as H71.
  pose proof (main_version_lookup "hello#str.72" ltac:(simpl; tauto)) as H72.
  pose proof (main_version_lookup "hello#str.73" ltac:(simpl; tauto)) as H73.
  pose proof (main_version_lookup "hello#str.74" ltac:(simpl; tauto)) as H74.
  pose proof (main_version_lookup "hello#str.75" ltac:(simpl; tauto)) as H75.
  iIntros "Hps". rewrite /loop_exit. iIntros (e ps cs a i g lose _) "_".
  mn_enter "iw_1.L21".
  (* stdout's stream. *)
  iApply wp_let; [reflexivity | reflexivity | cbn; rewrite Hstdout_g; reflexivity | intros ?m; word_premise |].
  iNext. gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_check. exact (proj1 (wi_stdout _ _ _ Hw)). }
  iNext. iIntros "_". gen_env.
  iApply (wp_world_let_with registry wi ge []); [reflexivity | reflexivity | word_premise | | rewrite /pts /=; done |].
  { intros m w h Hw _. apply op_raw_load_pointer; apply (wi_stdout _ _ _ Hw). }
  iNext. iIntros "_". gen_env.
  (* The heading's literals and the four authors. *)
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
  (* version_etc, then exit(0). *)
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

(** ## --version from main's entry

    Where getopt_long's first call can only return 129, main goes from
    its entry straight to --version: the loop's first round enters
    iw_1.L8, calls getopt_long, and with 129 branches by iw_1.L19 to
    iw_1.L21. No other exit of the loop is reached, so the greeting,
    --help and the diagnostics need none of their premises. *)

(** The option loop's first round, where every [getopt_step] from the
    token a, i returns 129: from its entry by any edge to the version
    exit. *)
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
  (* Enter iw_1.L8: pr.2 is lose. *)
  iApply (wp_enter _ _ _ _ _ _ _ _ (main_block "iw_1.L8") (put (TAtom "iw_1.pr.2") (WInt lose) e)).
  { vm_compute. reflexivity. }
  { destruct Hent as [[-> ->] | [[-> ->] | [[-> | ->] [Hpr _]]]]; word_premise. }
  iNext. cbn [b_insts b_jump main_block hblk]. gen_env.
  (* getopt_long(argc, argv, "g:t", longopts, NULL) returns 129. *)
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

(** Main from its entry to its exit by --version, where every
    [getopt_step] from the first token returns 129: [main_to_L8],
    [loop_version] and [main_version]. Main owns what the start block
    and the version block need, and nothing for the other paths. *)
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

(** setlocale's query of LC_MESSAGES, whose name is lent, is admitted,
    returns that name and changes nothing: LocaleLogic's
    [locale_wi_pre] and [locale_wi_query], for libc's world. *)
Context (Hquery_pre : forall m w h p t, wi m w h -> h !! PName 5 = Some (VName p t) ->
    contract_pre (libc_setlocale_contract rep requests) [WInt 5; WPtr null] m w)
  (Hquery : forall r args s m w h p t trace ending s' m' w',
    wi m w h -> h !! PName 5 = Some (VName p t) ->
    M.E.invoke (libc_setlocale_contract rep requests) r args [WInt 5; WPtr null] s m w trace ending s' m' w' ->
    s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr p]).

(** libc's stderr: the world keeps its cell readable and holding the
    stream, as for stdout. *)
Context (stderr_cell errstream : ptr)
  (Hstderr_g : lookup (TAtom "stderr") (ge_globals ge) = Some stderr_cell)
  (wi_stderr : forall m w h, wi m w h ->
    access_res m (raw_address (ptr_addr stderr_cell) 0) (ptr_cap stderr_cell) 8 Read 8 = Some ok /\
    pointer_load_effects m (raw_address (ptr_addr stderr_cell) 0)
      [AuxRead; LowerResolve; AddressRead] = Some errstream).

(** The output contracts of main's own calls and of the footer, as
    HelloVersion states the footer's: each is admitted with the
    literals' pieces (and, for a line naming the program, the
    arguments' strings, one of which holds its name), returns a
    canonical int and keeps the world interpretation, whether its
    output succeeded or not. *)
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

(** One of main's output calls: it is safe, binds d to some int and
    keeps the literals and the arguments' strings. *)
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

(** --help, iw_1.L39: main loads stdout, queries LC_MESSAGES' name,
    prints the usage line with the program's name and the option lines,
    calls the footer, and, unless the locale's name starts with "en_",
    a line on where to report translation bugs; then iw_1.iw_1.L32
    exits. The pieces it needs are the help literals, the "en_" string,
    the program's name cells and LC_MESSAGES' lent name. *)
Lemma main_help b4 b6 x0 x1 y0 p t b61 r61 Φ :
  name_ok sargs x0 ->
  LL.lent 5 p t -∗ pts help_ps -∗ string (version_literal "hello#str.61") b61 r61 [101; 110; 95] -∗
  HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  loop_exit b4 b6 "iw_1.L39"%string "iw_1.L50"%string Φ.
Proof.
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
  iIntros "#Hk Hps H61 (Hpl & Hpc & Hnl & Hnc & Hsl & Hsc)".
  rewrite /loop_exit. iIntros (e ps cs a ix g lose _) "(Hb & Has & Ht & Hl4 & Hp4)".
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
  iNext. iIntros "Hpl Hpc Has". gen_env.
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
  - (* Not English: where to report translation bugs. *)
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
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

(** The operand check's exit to the hint: the loop's pieces supply the
    arguments' strings, and the caller the literals and name cells. *)
Lemma hint_exit b4 b6 from P x0 x1 y0 Φ :
  name_ok sargs x0 ->
  pts help_ps -∗ HP.HN.name_cells pn nreg sreg nb sb x0 x1 y0 -∗
  operand_exit b4 b6 "iw_1.L113"%string from P Φ.
Proof.
  intros Hname. iIntros "Hps Hcells". rewrite /operand_exit.
  iIntros (e ps cs a i g lose _) "(_ & Has & _)".
  iApply (main_hint with "Hps Has Hcells"). exact Hname.
Qed.

(** error(0, 0, fmt, text, arg), the diagnostic for an extra operand,
    has a contract that returns: admitted with the literals' and the
    arguments' pieces for an argument's string, it keeps the world
    interpretation and every piece main owns. *)
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

(** iw_1.L79, an extra operand: main loads argv[optind] again, which is
    an argument as optind is below argc, reports it with error(0, ...),
    and goes on to the hint. *)
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

(** The loop's exits but the greeting: --version, --help, and, at the
    end of options, an extra operand or the hint. Each branch has every
    resource, as only one runs. *)
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

(** Main from its entry to the greeting: the start block, the option
    loop and every exit of it but the greeting are proved, and only
    iw_1.join, entered with pr.2 clear and optind at argc, is left to
    the continuation. The version and help paths use up the literals
    and the program's name cells; the greeting needs neither. *)
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
End HelloMain.
