(** During early initialization glibc calls `c: __ptmalloc_init` to set
    up its allocator. The function picks a random key for the per-thread
    cache, links the main arena's bins to themselves, and reads the
    allocator's tunables. Its caller needs only which globals the call
    owns and what it leaves in them, so this module states that
    contract. [StartPtmallocInit](StartPtmallocInit.v) proves it.

    ## What the call owns

    The call reads and writes about a dozen globals, so the contract
    names their addresses in one record and their bounds in one
    proposition. It lends the errno cell to `c: getrandom` and restores
    errno afterwards, and it reads ten tunables without changing them.
    It does not write the field `c: mp_.tcache_max_bytes` that
    `c: malloc` later reads. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld StartTunableGetValSpec.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** ## The globals

    Each global is an object with a base address and a region. The
    record below holds both for every global the call touches. *)

(** This record holds the objects that `c: __ptmalloc_init` reads or
    writes. *)
Record pm_objs := {
  pm_tk : Z; pm_tkreg : region;   (* tcache_key *)
  pm_eb : Z; pm_ereg : region;    (* __libc_errno *)
  pm_li : Z; pm_lireg : region;   (* __libc_initial *)
  pm_af : Z; pm_afreg : region;   (* __always_fail_morecore *)
  pm_ta : Z; pm_tareg : region;   (* thread_arena *)
  pm_ma : Z; pm_mareg : region;   (* main_arena *)
  pm_mp : Z; pm_mpreg : region;   (* mp_ *)
  pm_tl : Z; pm_tlreg : region    (* tunable_list *)
}.

(** The call reads these eight tunables as sizes. *)
Definition pm_size_ids : list Z := [24; 19; 25; 14; 15; 23; 22; 17].

(** The call reads these two tunables as ints. *)
Definition pm_int_ids : list Z := [21; 18].

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The program names each object as the global of that name, and each
    object is large enough for the fields that the call touches. *)
Definition pm_ok (o : pm_objs) : Prop :=
  lookup (TAtom "glibc_malloc#tcache_key") (ge_globals ge) = Some (mkPtr (pm_tk o) (Obj (pm_tk o))) /\
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (pm_eb o) (Obj (pm_eb o))) /\
  lookup (TAtom "__libc_initial") (ge_globals ge) = Some (mkPtr (pm_li o) (Obj (pm_li o))) /\
  lookup (TAtom "glibc_malloc#__always_fail_morecore") (ge_globals ge) = Some (mkPtr (pm_af o) (Obj (pm_af o))) /\
  lookup (TAtom "thread_arena") (ge_globals ge) = Some (mkPtr (pm_ta o) (Obj (pm_ta o))) /\
  lookup (TAtom "glibc_malloc#main_arena") (ge_globals ge) = Some (mkPtr (pm_ma o) (Obj (pm_ma o))) /\
  lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr (pm_mp o) (Obj (pm_mp o))) /\
  ow_errno w0 = Some (mkPtr (pm_eb o) (Obj (pm_eb o))) /\
  pm_tk o + 8 <= r_end (pm_tkreg o) /\ pm_eb o + 4 <= r_end (pm_ereg o) /\
  pm_li o + 1 <= r_end (pm_lireg o) /\ pm_af o + 1 <= r_end (pm_afreg o) /\
  pm_ta o mod 8 = 0 /\ pm_ta o + 8 <= r_end (pm_tareg o) /\
  pm_ma o mod 8 = 0 /\ pm_ma o + 2056 <= r_end (pm_mareg o) /\
  pm_mp o mod 8 = 0 /\ pm_mp o + 88 <= r_end (pm_mpreg o) /\
  Forall (tunable_slot_ok (pm_tl o) (pm_tlreg o)) (pm_size_ids ++ pm_int_ids).

(** The main arena's bin pointers occupy 254 cells from offset 24. *)
Definition pm_bins (ma : Z) : iProp Σ := [∗ list] k ∈ seqZ 0 254, ∃ x, pcell ma (24 + 8 * k) x.

(** This assertion owns the objects' lifetimes, which the call gives
    back. *)
Definition pm_lives (o : pm_objs) : iProp Σ :=
  live (pm_tk o) (pm_tkreg o) ∗ live (pm_eb o) (pm_ereg o) ∗ live (pm_li o) (pm_lireg o) ∗
  live (pm_af o) (pm_afreg o) ∗ live (pm_ta o) (pm_tareg o) ∗ live (pm_ma o) (pm_mareg o) ∗
  live (pm_mp o) (pm_mpreg o) ∗ live (pm_tl o) (pm_tlreg o).

(** This assertion owns the ten tunables, where tunable id has value
    tv id. The call gives them back unchanged. *)
Definition pm_tunables (o : pm_objs) (tv : Z -> Z) : iProp Σ :=
  ([∗ list] id ∈ pm_size_ids, tunable_entry (pm_tl o) id 2 (tv id)) ∗
  ([∗ list] id ∈ pm_int_ids, tunable_entry (pm_tl o) id 0 (tv id)).

(** This assertion owns the fields that the call may write, with unknown
    contents. It covers the key, errno, the morecore flag, the arena's
    first link and its bins, and the `c: mp_` fields at 16, 56 and 80,
    which hold the mmap threshold, the huge page size and the flag that
    fixes the threshold. *)
Definition pm_fields (o : pm_objs) : iProp Σ :=
  blk_any (pm_tk o) 0 8 ∗ errno_any (pm_eb o) ∗ (∃ y, ibyte (pm_af o) 0 y) ∗
  (∃ x, pcell (pm_ma o) 8 x) ∗ pm_bins (pm_ma o) ∗
  (∃ v, icell (pm_mp o) 16 v) ∗ (∃ v, icell (pm_mp o) 56 v) ∗ (∃ xs, ⌜length xs = 4%nat⌝ ∗ bytes (pm_mp o) 80 xs).

(** A call of `c: __ptmalloc_init()` returns and points
    `c: thread_arena` at the main arena. It reads the initial flag x and
    the tunables, and it leaves the other fields with some contents. *)
Definition ptmalloc_init_spec : fspec Σ :=
  FSpec (pm_objs * (Z -> Z) * Z * ptr) (fun _ => [])
    (fun '(o, tv, x, t) =>
       ⌜pm_ok o⌝ ∗ pm_lives o ∗ pm_tunables o tv ∗ ibyte (pm_li o) 0 x ∗ pcell (pm_ta o) 0 t ∗ pm_fields o)%I
    (fun '(o, tv, x, t) r =>
       ⌜r = RetVoid⌝ ∗ pm_lives o ∗ pm_tunables o tv ∗ ibyte (pm_li o) 0 x ∗
       pcell (pm_ta o) 0 (mkPtr (pm_ma o) (Obj (pm_ma o))) ∗ pm_fields o)%I.

End spec.
