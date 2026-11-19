(** Before any constructor runs, `c: __libc_start_main` calls
    `c: __libc_early_init`, which sets glibc's single-thread flag, sets
    the per-thread character table pointers, sizes the default thread
    stack and sets up the allocator. The proof of main needs what this
    call leaves behind, and nothing about how it gets there. So this
    module states that contract, and
    [StartEarlyInit](StartEarlyInit.v) proves it.

    ## What the call owns

    The call owns what its callees own, as their contracts in
    [StartCtypeInitSpec](StartCtypeInitSpec.v) and
    [StartPtmallocInitSpec](StartPtmallocInitSpec.v) state, plus three
    objects of its own: the single-thread flag, the page size, and the
    default thread attributes. Its argument says whether this libc is
    the first one in the process, and the call stores it in the flag and
    in `c: __libc_initial`. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld StartTunableGetValSpec StartCtypeInitSpec StartPtmallocInitSpec.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

(** This record holds the base and region of each object that the call
    itself writes or reads. *)
Record ei_objs := {
  ei_st : Z; ei_streg : region;   (* __libc_single_threaded *)
  ei_pg : Z; ei_pgreg : region;   (* _dl_pagesize *)
  ei_da : Z; ei_dareg : region    (* __default_pthread_attr *)
}.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The program names the three objects. The flag has a second name,
    an alias, and the default attributes hold the guard size at offset
    16 and the stack size at offset 32. *)
Definition ei_ok (e : ei_objs) : Prop :=
  lookup (TAtom "__libc_single_threaded") (ge_globals ge) = Some (mkPtr (ei_st e) (Obj (ei_st e))) /\
  lookup (TAtom "__libc_single_threaded_internal") (ge_globals ge) = Some (mkPtr (ei_st e) (Obj (ei_st e))) /\
  lookup (TAtom "_dl_pagesize") (ge_globals ge) = Some (mkPtr (ei_pg e) (Obj (ei_pg e))) /\
  lookup (TAtom "__GI___default_pthread_attr") (ge_globals ge) = Some (mkPtr (ei_da e) (Obj (ei_da e))) /\
  ei_st e + 1 <= r_end (ei_streg e) /\
  ei_pg e mod 8 = 0 /\ ei_pg e + 8 <= r_end (ei_pgreg e) /\
  ei_da e mod 8 = 0 /\ ei_da e + 40 <= r_end (ei_dareg e).

(** This assertion owns the three objects' lives. *)
Definition ei_lives (e : ei_objs) : iProp Σ :=
  live (ei_st e) (ei_streg e) ∗ live (ei_pg e) (ei_pgreg e) ∗ live (ei_da e) (ei_dareg e).

(** This assertion owns the three per-thread table pointers with some
    contents. *)
Definition ct_cells_any (c : ct_objs) : iProp Σ :=
  (∃ x, pcell (ct_cb c) 0 x) ∗ (∃ x, pcell (ct_cu c) 0 x) ∗ (∃ x, pcell (ct_cl c) 0 x).

(** This assertion owns the three per-thread table pointers as
    `c: __ctype_init` leaves them. *)
Definition ct_cells_set (c : ct_objs) : iProp Σ :=
  pcell (ct_cb c) 0 (mkPtr (ct_xc c + 256) (Ro (ct_xc c))) ∗
  pcell (ct_cu c) 0 (mkPtr (ct_xu c + 512) (Ro (ct_xu c))) ∗
  pcell (ct_cl c) 0 (mkPtr (ct_xl c + 512) (Ro (ct_xl c))).

(** A call of `c: __libc_early_init(a)` stores the low byte of a in
    the single-thread flag and in the initial flag. It points
    `c: thread_arena` at the main arena, sets the character table
    pointers, and copies the page size ps into the guard size. The
    stack size, and the fields that the allocator's contract leaves
    unknown, come back with some contents. *)
Definition early_init_spec : fspec Σ :=
  FSpec (ei_objs * pm_objs * ct_objs * (Z -> Z) * Z * Z) (fun '(_, _, _, _, a, _) => [WInt a])
    (fun '(e, o, c, tv, a, ps) =>
       ⌜0 <= a < 2 ^ 32 /\ 0 <= ps < 2 ^ 64 /\ ei_ok e /\ pm_ok o /\ ct_ok c /\
        tunable_slot_ok (pm_tl o) (pm_tlreg o) 27⌝ ∗
       ei_lives e ∗ (∃ y, ibyte (ei_st e) 0 y) ∗ icell (ei_pg e) 0 ps ∗
       (∃ v, icell (ei_da e) 16 v) ∗ (∃ v, icell (ei_da e) 32 v) ∗
       ct_ro c ∗ ct_locale c ∗ ct_lives c ∗ ct_cells_any c ∗
       pm_lives o ∗ pm_tunables o tv ∗ tunable_entry (pm_tl o) 27 0 (tv 27) ∗
       (∃ y, ibyte (pm_li o) 0 y) ∗ (∃ t, pcell (pm_ta o) 0 t) ∗ pm_fields o)%I
    (fun '(e, o, c, tv, a, ps) r =>
       ⌜r = RetVoid⌝ ∗
       ei_lives e ∗ ibyte (ei_st e) 0 (a mod 256) ∗ icell (ei_pg e) 0 ps ∗
       icell (ei_da e) 16 ps ∗ (∃ v, icell (ei_da e) 32 v) ∗
       ct_locale c ∗ ct_lives c ∗ ct_cells_set c ∗
       pm_lives o ∗ pm_tunables o tv ∗ tunable_entry (pm_tl o) 27 0 (tv 27) ∗
       ibyte (pm_li o) 0 (a mod 256) ∗ pcell (pm_ta o) 0 (mkPtr (pm_ma o) (Obj (pm_ma o))) ∗ pm_fields o)%I.

(** A call of `c: __getrandom_early_init(a)` returns and changes
    nothing, because its body in this image is empty. *)
Definition getrandom_early_init_spec : fspec Σ :=
  FSpec Z (fun a => [WInt a]) (fun a => ⌜0 <= a < 2 ^ 32⌝)%I (fun _ r => ⌜r = RetVoid⌝)%I.

End spec.
