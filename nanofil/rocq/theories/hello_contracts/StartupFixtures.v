(** These retained fixtures check Startup with the earlier libc-contract
    examples. The live foundation does not depend on these fixtures. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Identity ExternalCalls LibcCalls LibcCallFixtures ExternalMachine.
Import ListNotations.
Open Scope Z_scope.

From Nanofil Require Import Startup.

(** ## Entry regressions

    Two arguments of unequal lengths, including the empty string, and
    an empty environment distinguish argc, slot spacing and sentinels.
    The fixture reuses the independent hello string, not its fake ABI. *)

(** argv: a three-slot array at 4096. *)
Definition entry_argv : ptr := mkPtr 4096 (Obj 4096).
(** envp: a one-slot array at 4200, the sentinel alone. *)
Definition entry_envp : ptr := mkPtr 4200 (Obj 4200).
(** [hello_mem] plus the two arrays: argv's slots point at hello (with
    its read-only capability) and at an empty string in the object at
    3072, then null; envp's only slot is null. *)
Definition entry_mem : mem :=
  mkMem (fun a =>
    if (4096 <=? a) && (a <? 4104) then byte_of 1024 (a - 4096) else
    if (4104 <=? a) && (a <? 4112) then byte_of 3072 (a - 4104) else
    m_bytes hello_mem a)
    (mkRegion 4096 4120 Heap Live :: mkRegion 4200 4208 Heap Live :: m_regions hello_mem)
    (fun a => if a =? 4096 then Ro 1024 else if a =? 4104 then Obj 3072 else CNone).

(** [entry_mem] is an entry image with argc 2, arguments hello and the
    empty string, and no environment. *)
Example entry_two_arguments : startup_at entry_mem 2 entry_argv entry_envp [hello_bytes; []] [].
Proof.
  split; [lia|]. split; [reflexivity|]. split.
  - split; [reflexivity|]. exists hello_ptr. split; [vm_compute; repeat split; congruence|].
    split; [vm_compute; repeat split; congruence|]. exists (mkPtr 3072 (Obj 3072)).
    vm_compute. repeat split; congruence.
  - vm_compute. repeat split; congruence.
Qed.

(** argc must count the arguments. *)
Example entry_bad_count : ~ startup_at entry_mem 1 entry_argv entry_envp [hello_bytes; []] [].
Proof. intros (_ & H & _). discriminate H. Qed.

(** A nonzero address in argv's sentinel slot is not a [string_vector]. *)
Example entry_nonnull_sentinel :
  ~ string_vector (store_bytes entry_mem 4112 8 1024) entry_argv [hello_bytes; []].
Proof.
  intros [_ H]. pose proof (string_slots_sentinel _ _ _ H) as (_ & Hbits & _).
  discriminate Hbits.
Qed.

(** Nor is a slot whose [[aux]] lost its capability, though its address
    bytes are right. *)
Example entry_missing_capability :
  ~ string_vector (store_aux entry_mem 4096 CNone) entry_argv [hello_bytes; []].
Proof.
  intros [_ (p & (_ & Hbits & Hcap) & [Hread _] & _)].
  change (1024 = ptr_addr p) in Hbits. change (CNone = ptr_cap p) in Hcap.
  rewrite <- Hbits, <- Hcap in Hread. discriminate Hread.
Qed.

(** Nor an argv object too small to hold the sentinel slot. *)
Example entry_missing_sentinel_bounds :
  ~ string_vector (mkMem (m_bytes entry_mem)
    (mkRegion 4096 4112 Heap Live :: m_regions hello_mem) (m_aux entry_mem))
    entry_argv [hello_bytes; []].
Proof. intros [H _]. discriminate H. Qed.

(** Nor a slot whose address bytes point one byte into the string. *)
Example entry_wrong_address :
  ~ string_vector (store_bytes entry_mem 4096 8 1025) entry_argv [hello_bytes; []].
Proof.
  intros [_ (p & (_ & Hbits & _) & [_ Hstring] & _)].
  change (1025 = ptr_addr p) in Hbits. rewrite <- Hbits in Hstring.
  destruct Hstring as (_ & Hbyte & _). discriminate Hbyte.
Qed.

(** Nor a string whose NUL was overwritten. *)
Example entry_missing_nul :
  ~ string_vector (store_bytes entry_mem 1029 1 65) entry_argv [hello_bytes; []].
Proof.
  intros [_ (p & (_ & Hbits & _) & [_ Hstring] & _)].
  change (1024 = ptr_addr p) in Hbits. rewrite <- Hbits in Hstring.
  destruct Hstring as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnul).
  discriminate Hnul.
Qed.

(** The largest argc whose copy size is computable, INT_MAX - 1, gives
    17179869176 bytes; at INT_MAX, argc + 1 overflows int. *)
Example argv_copy_boundary :
  argv_copy_size (2 ^ 31 - 2) = 17179869176 /\
  ~ (0 < (2 ^ 31 - 1) + 1 < 2 ^ 31).
Proof. split; [reflexivity|lia]. Qed.

(** Status 513 reports 1, and -1 reports 255. *)
Example exit_status_low_byte : process_status 513 = 1 /\ process_status (-1) = 255.
Proof. split; reflexivity. Qed.

(** Construction, not a preassumed final entry image. All old argument
    table bytes/capabilities stay; high bytes are not interpreted as
    text, and the NUL must fit the new object's checked bounds. *)
Definition copied_entry_string : mem :=
  copy_c_bytes (allocated entry_mem (heap_req 16 4) 16384) 16384 [1; 128; 255].

(** An empty string needs one byte for its NUL, within a rounded 16-byte object. *)
Example copy_empty_string :
  c_string (copy_c_bytes (allocated entry_mem (heap_req 16 1) 16384) 16384 [])
    (mkPtr 16384 (Obj 16384)) [] /\ req_extent (heap_req 16 1) = 16.
Proof. repeat split; reflexivity. Qed.

(** High bytes survive exactly, along with the old pointer slot and environment. *)
Example copy_high_bytes_and_old_slot :
  c_string copied_entry_string (mkPtr 16384 (Obj 16384)) [1; 128; 255] /\
  m_bytes copied_entry_string 16387 = 0 /\
  pointer_slot copied_entry_string 4096 hello_ptr /\
  string_vector copied_entry_string entry_envp [].
Proof. vm_compute. repeat constructor; discriminate. Qed.

(** Sixteen payload bytes need a seventeenth NUL byte and a 32-byte extent. *)
Example copy_crosses_rounding_boundary :
  c_string (copy_c_bytes (allocated entry_mem (heap_req 16 17) 16384) 16384 (repeat 255 16))
    (mkPtr 16384 (Obj 16384)) (repeat 255 16) /\ req_extent (heap_req 16 17) = 32.
Proof. vm_compute. repeat constructor; discriminate. Qed.

(** Correct payload bytes are insufficient when the NUL lies outside the object. *)
Example copied_nul_needs_bounds :
  ~ c_string (mkMem (m_bytes copied_entry_string)
    [mkRegion 16384 16387 Heap Live] (m_aux copied_entry_string))
    (mkPtr 16384 (Obj 16384)) [1; 128; 255].
Proof. intros [H _]. discriminate H. Qed.

(** A pre-NUL payload contains neither a zero nor a value outside the byte range. *)
Example pre_nul_representation :
  ~ Forall (fun b => 0 < b < 256) [65; 0; 66] /\
  ~ Forall (fun b => 0 < b < 256) [65; 256].
Proof.
  split; intros H; inversion H as [|head rest Hb Hrest]; subst;
    inversion Hrest as [|head tail Hbad Htail]; subst; lia.
Qed.

(** Executable construction examples use the ordinary interpreter runtime. *)
Module StartupExamples := Startup InterpRuntime.

(** Table first, then three strings in forward order, with distinct
    sizes and contents. Old pointer bytes and read-only authority stay. *)
Example constructed_argv_order :
  match StartupExamples.copy_vector [[65; 66]; []; [1; 128; 255]] 16384 entry_mem [] with
  | Some (argv, next, m, born) =>
      argv = mkPtr 16384 (Obj 16384) /\ next = 16528 /\
      born = [16496; 16464; 16432; 16384] /\
      pointer_slot m 16384 (mkPtr 16432 (Obj 16432)) /\
      pointer_slot m 16392 (mkPtr 16464 (Obj 16464)) /\
      pointer_slot m 16400 (mkPtr 16496 (Obj 16496)) /\
      pointer_slot m 16408 (mkPtr 0 CNone) /\
      c_string m (mkPtr 16432 (Obj 16432)) [65; 66] /\
      c_string m (mkPtr 16464 (Obj 16464)) [] /\
      c_string m (mkPtr 16496 (Obj 16496)) [1; 128; 255] /\
      pointer_slot m 4096 hello_ptr /\ m_bytes m 1024 = 104
  | None => False
  end.
Proof. vm_compute. repeat constructor; discriminate. Qed.

(** The environment copy preserves the earlier argv and its strings;
    an empty environment still allocates a checked sentinel table. *)
Example constructed_entry_empty_environment :
  match StartupExamples.copy_vector [[65; 66]; []; [1; 128; 255]] 16384 entry_mem [] with
  | Some (argv, s, m, born) =>
      match StartupExamples.copy_vector [] s m born with
      | Some (envp, next, m', born') =>
          envp = mkPtr 16528 (Obj 16528) /\ next = 16560 /\
          born' = [16528; 16496; 16464; 16432; 16384] /\
          pointer_slot m' 16384 (mkPtr 16432 (Obj 16432)) /\
          pointer_slot m' 16408 (mkPtr 0 CNone) /\ pointer_slot m' 16528 (mkPtr 0 CNone) /\
          c_string m' (mkPtr 16496 (Obj 16496)) [1; 128; 255] /\
          access_res m' (ptr_addr envp) (ptr_cap envp) 8 Write 1 = Some ok /\
          pointer_slot m' 4096 hello_ptr
      | None => False
      end
  | None => False
  end.
Proof. vm_compute. repeat constructor; discriminate. Qed.

(** A populated environment uses its own forward copy loop and sentinel,
    retaining the earlier argv even through two further string allocations. *)
Example constructed_entry_environment_bytes :
  match StartupExamples.copy_vector [[65; 66]; []; [1; 128; 255]] 16384 entry_mem [] with
  | Some (argv, s, m, born) =>
      match StartupExamples.copy_vector [[78; 70; 61; 65]; [88; 61; 255]] s m born with
      | Some (envp, next, m', born') =>
          envp = mkPtr 16528 (Obj 16528) /\ next = 16640 /\
          born' = [16608; 16576; 16528; 16496; 16464; 16432; 16384] /\
          pointer_slot m' 16384 (mkPtr 16432 (Obj 16432)) /\
          pointer_slot m' 16408 (mkPtr 0 CNone) /\
          c_string m' (mkPtr 16432 (Obj 16432)) [65; 66] /\
          c_string m' (mkPtr 16464 (Obj 16464)) [] /\
          c_string m' (mkPtr 16496 (Obj 16496)) [1; 128; 255] /\
          pointer_slot m' 16528 (mkPtr 16576 (Obj 16576)) /\
          pointer_slot m' 16536 (mkPtr 16608 (Obj 16608)) /\
          pointer_slot m' 16544 (mkPtr 0 CNone) /\
          c_string m' (mkPtr 16576 (Obj 16576)) [78; 70; 61; 65] /\
          c_string m' (mkPtr 16608 (Obj 16608)) [88; 61; 255] /\ pointer_slot m' 4096 hello_ptr
      | None => False
      end
  | None => False
  end.
Proof. vm_compute. repeat constructor; discriminate. Qed.

(** A resource-refusing allocator does not produce a successful empty table. *)
Example constructed_table_refusal :
  StartupExamples.copy_vector [] (2 ^ 48 - 1) entry_mem [] = None.
Proof. reflexivity. Qed.

(** Environment counts above INT_MAX are not rejected by argv's int rule. *)
Example environment_count_not_int : forall n,
  Z.of_nat n = 2 ^ 31 ->
  2 ^ 31 - 1 < Z.of_nat n /\ 8 * (Z.of_nat n + 1) <= max_allocation_size.
Proof. intros n H. rewrite H. unfold max_allocation_size. lia. Qed.

(** An independent initialized module, not a preassumed cell predicate.
    Opaque stream storage is only raw data here, deliberately not FILE
    validity. Both names share a read-only object; short is interior. *)
Definition exposed_module : module :=
  [IData (TAtom "out_storage") LLocal 16 [Zero 224];
   IData (TAtom "err_storage") LLocal 16 [Zero 224];
   IData (TAtom "name_storage") (LRo (TAtom "local")) 1 [Str [120; 47; 104; 0]];
   IData (TAtom "stdout") LExport 8 [Sym (TAtom "out_storage") 0];
   IData (TAtom "stderr") LExport 8 [Sym (TAtom "err_storage") 0];
   IData (TAtom "program_invocation_name") LExport 8 [Sym (TAtom "name_storage") 0];
   IData (TAtom "program_invocation_short_name") LExport 8 [Sym (TAtom "name_storage") 2]].

(** The actual initialized symbol map and memory of [exposed_module]. *)
Definition exposed_image : list (name * ptr) * mem :=
  match initial_memory exposed_module with Some image => image | None => ([], empty_mem) end.

(** The initializer really succeeds at the hand-computed cell addresses. *)
Example exposed_initial_symbols :
  option_map fst (initial_memory exposed_module) = Some
    [(TAtom "program_invocation_short_name", mkPtr 66144 (Obj 66144));
     (TAtom "program_invocation_name", mkPtr 66112 (Obj 66112));
     (TAtom "stderr", mkPtr 66080 (Obj 66080));
     (TAtom "stdout", mkPtr 66048 (Obj 66048));
     (TAtom "name_storage", mkPtr 66016 (Ro 66016));
     (TAtom "err_storage", mkPtr 65776 (Obj 65776));
     (TAtom "out_storage", mkPtr 65536 (Obj 65536))].
Proof. vm_compute. reflexivity. Qed.

(** Exact cell identities, independent of the values stored in them. *)
Definition exposed_cells : libc_global_cells := mkLibcGlobalCells
  (mkPtr 66048 (Obj 66048)) (mkPtr 66080 (Obj 66080))
  (mkPtr 66112 (Obj 66112)) (mkPtr 66144 (Obj 66144)).

(** Symbol lookup reaches cells while the initialized contents point
    elsewhere, with the name's exact read-only capability. *)
Example exposed_initial_cells :
  libc_globals_bound (mkGenv exposed_module (fst exposed_image) free_res) exposed_cells /\
  libc_globals_at (snd exposed_image) exposed_cells
    (mkPtr 65536 (Obj 65536)) (mkPtr 65776 (Obj 65776))
    (mkPtr 66016 (Ro 66016)) (mkPtr 66018 (Ro 66016)).
Proof.
  split; [vm_compute; repeat split; reflexivity|].
  unfold libc_globals_at. repeat split;
    lazymatch goal with |- exists _, _ => idtac | _ => vm_compute; congruence end.
  - exists 66048, (mkRegion 66048 66056 GlobalData Live). repeat split; reflexivity.
  - exists 66080, (mkRegion 66080 66088 GlobalData Live). repeat split; reflexivity.
  - exists 66112, (mkRegion 66112 66120 GlobalData Live). repeat split; reflexivity.
  - exists 66144, (mkRegion 66144 66152 GlobalData Live). repeat split; reflexivity.
  - exists [120; 47; 104]. vm_compute. repeat split; reflexivity.
  - exists [104]. vm_compute. repeat split; reflexivity.
Qed.

(** Ordinary pointer loads recover different stored addresses and the
    exact mutable/read-only authority, not the cells' own capabilities. *)
Example exposed_initial_loads :
  pointer_load_effects (snd exposed_image) 66048 [AuxRead; LowerResolve; AddressRead] =
    Some (mkPtr 65536 (Obj 65536)) /\
  pointer_load_effects (snd exposed_image) 66144 [AuxRead; LowerResolve; AddressRead] =
    Some (mkPtr 66018 (Ro 66016)).
Proof. vm_compute. split; reflexivity. Qed.

(** A basename can be the empty suffix in the same name object. *)
Example exposed_empty_suffix :
  exposed_pointer_cell
    (store_aux (store_bytes (snd exposed_image) 66144 8 66019) 66144 (Ro 66016))
    (short_name_cell exposed_cells) (mkPtr 66019 (Ro 66016)) /\
  c_string (snd exposed_image) (mkPtr 66019 (Ro 66016)) [].
Proof.
  split; [|vm_compute; repeat split; reflexivity]. repeat split;
    lazymatch goal with |- exists _, _ => idtac | _ => vm_compute; congruence end.
  exists 66144, (mkRegion 66144 66152 GlobalData Live). repeat split; reflexivity.
Qed.

(** Right address bits do not compensate for missing stored authority. *)
Example exposed_lost_aux :
  ~ exposed_pointer_cell (store_aux (snd exposed_image) 66048 CNone)
    (stdout_cell exposed_cells) (mkPtr 65536 (Obj 65536)).
Proof. intros (_ & _ & _ & _ & _ & Haux). discriminate Haux. Qed.

(** Correct aux does not compensate for wrong stored address bits. *)
Example exposed_wrong_bits :
  ~ exposed_pointer_cell (store_bytes (snd exposed_image) 66048 8 65537)
    (stdout_cell exposed_cells) (mkPtr 65536 (Obj 65536)).
Proof. intros (_ & _ & _ & _ & Hbits & _). discriminate Hbits. Qed.

(** Pointee authority is not authority for accessing the pointer cell. *)
Example exposed_wrong_cell_identity :
  ~ exposed_pointer_cell (snd exposed_image) (mkPtr 66048 (Obj 65536))
    (mkPtr 65536 (Obj 65536)).
Proof. intros (_ & Hr & _). discriminate Hr. Qed.

(** The full aligned word must fit the cell's object. *)
Example exposed_short_cell :
  ~ exposed_pointer_cell
    (mkMem (m_bytes (snd exposed_image)) [mkRegion 66048 66055 GlobalData Live]
      (m_aux (snd exposed_image))) (stdout_cell exposed_cells) (mkPtr 65536 (Obj 65536)).
Proof. intros (_ & Hr & _). discriminate Hr. Qed.

(** Sufficient raw extent does not waive pointer-load alignment. *)
Example exposed_unaligned_cell :
  ~ exposed_pointer_cell
    (mkMem (m_bytes (snd exposed_image)) [mkRegion 66048 66064 GlobalData Live]
      (m_aux (snd exposed_image))) (mkPtr 66049 (Obj 66048)) (mkPtr 65536 (Obj 65536)).
Proof. intros (_ & Hr & _). discriminate Hr. Qed.
