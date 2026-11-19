(** The startup code of glibc calls
    `c: init_cpu_features (&_dl_x86_cpu_features)` once, before it
    reads any tunable. The call fills in a structure that describes
    the processor. The proof of `c: __libc_start_main` passes through
    this call, so it needs to know which global objects the call owns
    and what the call leaves in them. This module states that as a
    contract. The proof of the contract is in [CpuSpec](CpuSpec.v),
    and a caller can import this module without the proof.

    ## What the call owns

    The call reads and writes eighteen global objects. It fills the
    feature structure and fifteen small globals that hold cache sizes
    and thresholds. It reads the Intel cache descriptor table. It
    reads nine rows of the tunable table and writes six of them back.

    The contract asks little of the contents. The feature structure
    and the small globals may hold any bytes. The descriptor table
    holds the bytes of the image. The tunable table may hold any bytes
    except the type codes and the `initialized` flags of the rows that
    startup reads. The call gives every object back in the same form,
    so the tunable rows that later startup code reads still have their
    type codes and their cleared flags. *)

From Glibc Require Fix.
From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic StringLogic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld OsCpuid.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** ## The globals

    Each global is an object with a base address and a region. The
    record below holds both for every global the call touches. *)

(** This record holds the objects that `c: init_cpu_features` reads or
    writes. The list [icf_small] holds the fifteen small globals in
    the order of [icf_small_globals]. *)
Record icf_objs := {
  icf_cf : Z; icf_cfreg : region;   (* _dl_x86_cpu_features *)
  icf_tl : Z; icf_tlreg : region;   (* tunable_list *)
  icf_kn : Z; icf_knreg : region;   (* intel_02_known *)
  icf_small : list (Z * region)
}.

(** The call writes these fifteen small globals. Each one is as large
    as its alignment. *)
Definition icf_small_globals : list (string * Z) :=
  [("_dl_hwcap", 8); ("_dl_hwcap2", 8); ("_dl_platform", 8); ("_dl_minsigstacksize", 8);
   ("_dl_x86_features_tlsdesc_state_size", 8); ("__x86_data_cache_size_half", 8); ("__x86_data_cache_size", 8);
   ("__x86_shared_cache_size_half", 8); ("__x86_shared_cache_size", 8);
   ("__x86_shared_non_temporal_threshold", 8); ("__x86_memset_non_temporal_threshold", 8);
   ("__x86_rep_movsb_threshold", 8); ("__x86_rep_stosb_threshold", 8); ("__x86_rep_movsb_stop_threshold", 8);
   ("__x86_string_control", 4)]%string.

(** ## The descriptor table

    CPUID leaf 2 names caches by one-byte descriptors, and glibc looks
    each descriptor up in a sorted table. A row holds the descriptor,
    the associativity, the line size, the cache level and the size in
    bytes. *)
Definition icf_known_rows : list (Z * Z * Z * Z * Z) :=
  [(6, 4, 32, 0, 8192); (8, 4, 32, 0, 16384); (9, 4, 32, 0, 32768); (10, 2, 32, 3, 8192);
   (12, 4, 32, 3, 16384); (13, 4, 64, 3, 16384); (14, 6, 64, 3, 24576); (33, 8, 64, 6, 262144);
   (34, 4, 64, 9, 524288); (35, 8, 64, 9, 1048576); (37, 8, 64, 9, 2097152); (41, 8, 64, 9, 4194304);
   (44, 8, 64, 3, 32768); (48, 8, 64, 0, 32768); (57, 4, 64, 6, 131072); (58, 6, 64, 6, 196608);
   (59, 2, 64, 6, 131072); (60, 4, 64, 6, 262144); (61, 6, 64, 6, 393216); (62, 4, 64, 6, 524288);
   (63, 2, 64, 6, 262144); (65, 4, 32, 6, 131072); (66, 4, 32, 6, 262144); (67, 4, 32, 6, 524288);
   (68, 4, 32, 6, 1048576); (69, 4, 32, 6, 2097152); (70, 4, 64, 9, 4194304); (71, 8, 64, 9, 8388608);
   (72, 12, 64, 6, 3145728); (73, 16, 64, 6, 4194304); (74, 12, 64, 9, 6291456); (75, 16, 64, 9, 8388608);
   (76, 12, 64, 9, 12582912); (77, 16, 64, 9, 16777216); (78, 24, 64, 6, 6291456); (96, 8, 64, 3, 16384);
   (102, 4, 64, 3, 8192); (103, 4, 64, 3, 16384); (104, 4, 64, 3, 32768); (120, 8, 64, 6, 1048576);
   (121, 8, 64, 6, 131072); (122, 8, 64, 6, 262144); (123, 8, 64, 6, 524288); (124, 8, 64, 6, 1048576);
   (125, 8, 64, 6, 2097152); (127, 2, 64, 6, 524288); (128, 8, 64, 6, 524288); (130, 8, 32, 6, 262144);
   (131, 8, 32, 6, 524288); (132, 8, 32, 6, 1048576); (133, 8, 32, 6, 2097152); (134, 4, 64, 6, 524288);
   (135, 8, 64, 6, 1048576); (208, 4, 64, 9, 524288); (209, 4, 64, 9, 1048576); (210, 4, 64, 9, 2097152);
   (214, 8, 64, 9, 1048576); (215, 8, 64, 9, 2097152); (216, 8, 64, 9, 4194304); (220, 12, 64, 9, 2097152);
   (221, 12, 64, 9, 4194304); (222, 12, 64, 9, 8388608); (226, 16, 64, 9, 2097152); (227, 16, 64, 9, 4194304);
   (228, 16, 64, 9, 8388608); (234, 24, 64, 9, 12582912); (235, 24, 64, 9, 18874368);
   (236, 24, 64, 9, 25165824)].

(** A row occupies eight bytes. The four small fields take one byte
    each, and the size takes four bytes. *)
Definition icf_known_bytes : list Z :=
  flat_map (fun '(d, a, l, r, s) => [d; a; l; r] ++ le_bytes s 4) icf_known_rows.

(** ## The tunable table

    A tunable occupies a row of 136 bytes. Its type code is a
    four-byte number at offset 48, and its `initialized` flag is the
    byte at offset 104. *)

(** The contract fixes a few bytes of these rows, which the call or
    later startup code reads. Each triple gives a row, its type code,
    and whether its `initialized` flag must be clear. *)
Definition icf_tunable_rows : list (Z * Z * bool) :=
  [(0, 3, true); (1, 0, true); (2, 0, true); (3, 2, false); (5, 2, false); (6, 2, false); (7, 2, false);
   (8, 2, false); (9, 2, false); (14, 2, true); (15, 2, true); (17, 2, true); (18, 0, true); (19, 2, true);
   (21, 0, true); (22, 2, true); (23, 2, true); (24, 2, true); (25, 2, true); (27, 0, true)].

(** These are the fixed bytes of one row. Each pair gives an offset in
    the table and the byte there. Every type code is below 256, so
    its four bytes are the code and three zeros. *)
Definition icf_row_bytes (id ty : Z) (clear : bool) : list (Z * Z) :=
  [(id * 136 + 48, ty); (id * 136 + 49, 0); (id * 136 + 50, 0); (id * 136 + 51, 0)] ++
  if clear then [(id * 136 + 104, 0)] else [].

(** These are the fixed bytes of the whole table. *)
Definition icf_tunable_bytes : list (Z * Z) :=
  flat_map (fun '(id, ty, clear) => icf_row_bytes id ty clear) icf_tunable_rows.

(** The bytes xs can be the contents of the tunable table when the
    table has its full size, every byte is below 256, and the fixed
    bytes are in place. *)
Definition icf_tunables_ok (xs : list Z) : Prop :=
  length xs = 4896%nat /\ Forall (fun x => 0 <= x < 256) xs /\
  Forall (fun '(o, x) => nth_error xs (Z.to_nat o) = Some x) icf_tunable_bytes.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## Ownership *)

(** This assertion owns an object of n bytes whose contents the
    caller does not know. The contents are n bytes and n shadow slots,
    and every byte is a number below 256. The assertion [blk_any] is
    the same without that bound. *)
Definition blk_u8 (b n : Z) : iProp Σ :=
  ∃ xs cs, ⌜length xs = Z.to_nat n /\ length cs = Z.to_nat n /\ Forall (fun x => 0 <= x < 256) xs⌝ ∗
           pts (byte_ps b 0 xs ++ aux_ps b 0 cs).

(** A caller that does not need the bound can forget it. *)
Lemma blk_u8_any b n : blk_u8 b n ⊢ blk_any b 0 n.
Proof using Type. iIntros "(%xs & %cs & (% & % & _) & H)". iExists xs, cs. by iFrame. Qed.

(** A caller that knows the bytes and the shadow slots of an object
    can give them up as a block of unknown contents. *)
Lemma blk_u8_intro b n xs cs :
  length xs = Z.to_nat n -> length cs = Z.to_nat n -> Forall (fun x => 0 <= x < 256) xs ->
  bytes b 0 xs -∗ auxes b 0 cs -∗ blk_u8 b n.
Proof using Type.
  iIntros (Hx Hc Hb) "Hx Hc". iExists xs, cs. iSplit; [done|]. rewrite pts_app. iFrame.
Qed.

(** This assertion owns the feature structure. The structure may hold
    any bytes before the call, with one exception. It saves the ECX
    word of CPUID leaf 1, and bit 27 of that word says that the kernel
    enabled XSAVE. The function reads the extended control register
    when it finds the bit set, and the proof does not rely on the
    function writing the word first. So the bit may be set before the
    call only in a world where the kernel did enable XSAVE. The bit is
    bit 3 of the byte at offset 31. A structure of zeros meets the
    condition. *)
Definition icf_features (cf : Z) : iProp Σ :=
  ∃ xs cs, ⌜length xs = 528%nat /\ length cs = 528%nat /\ Forall (fun x => 0 <= x < 256) xs /\
            (Z.testbit (nth 31 xs 0) 3 = true -> ow_osxsave w0 = true)⌝ ∗
           pts (byte_ps cf 0 xs ++ aux_ps cf 0 cs).

(** This assertion owns the tunable table with contents that
    [icf_tunables_ok] allows. *)
Definition icf_tunables (tl : Z) : iProp Σ :=
  ∃ xs cs, ⌜icf_tunables_ok xs /\ length cs = 4896%nat⌝ ∗ pts (byte_ps tl 0 xs ++ aux_ps tl 0 cs).

(** This assertion owns the descriptor table with the bytes of the
    image. The table holds no pointer. *)
Definition icf_known (kn : Z) : iProp Σ :=
  bytes kn 0 icf_known_bytes ∗ auxes kn 0 (repeat CNone 544).

(** The program names each object as the global of that name. Each
    object is aligned and large enough. The descriptor table is
    read-only data, so its pointer carries a read-only capability. *)
Definition icf_ok (o : icf_objs) : Prop :=
  lookup (TAtom "_dl_x86_cpu_features") (ge_globals ge) = Some (mkPtr (icf_cf o) (Obj (icf_cf o))) /\
  lookup (TAtom "glibc_dl_tunables#tunable_list") (ge_globals ge) = Some (mkPtr (icf_tl o) (Obj (icf_tl o))) /\
  lookup (TAtom "glibc_libc_start#intel_02_known") (ge_globals ge) = Some (mkPtr (icf_kn o) (Ro (icf_kn o))) /\
  icf_cf o mod 8 = 0 /\ icf_cf o + 528 <= r_end (icf_cfreg o) /\
  icf_tl o mod 8 = 0 /\ icf_tl o + 4896 <= r_end (icf_tlreg o) /\
  icf_kn o mod 4 = 0 /\ icf_kn o + 544 <= r_end (icf_knreg o) /\
  Forall2 (fun g q => lookup (TAtom (fst g)) (ge_globals ge) = Some (mkPtr (fst q) (Obj (fst q))) /\
                      fst q mod snd g = 0 /\ fst q + snd g <= r_end (snd q))
    icf_small_globals (icf_small o).

(** This assertion owns all eighteen objects: their lifetimes and
    their contents in the forms above. *)
Definition icf_owns (o : icf_objs) : iProp Σ :=
  live (icf_cf o) (icf_cfreg o) ∗ icf_features (icf_cf o) ∗
  live (icf_tl o) (icf_tlreg o) ∗ icf_tunables (icf_tl o) ∗
  live (icf_kn o) (icf_knreg o) ∗ icf_known (icf_kn o) ∗
  [∗ list] g; q ∈ icf_small_globals; icf_small o, live (fst q) (snd q) ∗ blk_u8 (fst q) (snd g).

(** ## The contract *)

(** A call of `c: init_cpu_features (&_dl_x86_cpu_features)` returns,
    and it gives back every object it was given, in the same form. *)
Definition init_cpu_features_spec : fspec Σ :=
  FSpec icf_objs (fun o => [WPtr (mkPtr (icf_cf o) (Obj (icf_cf o)))])
    (fun o => ⌜icf_ok o⌝ ∗ icf_owns o)%I
    (fun o r => ⌜r = RetVoid⌝ ∗ icf_owns o)%I.

End spec.
