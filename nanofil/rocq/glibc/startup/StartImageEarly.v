(** Before `c: main` runs, `c: __libc_start_main` calls
    `c: __libc_early_init` and then the constructor runner. The contract
    of the first call, in [StartEarlyInitSpec](StartEarlyInitSpec.v),
    asks for about twenty globals of glibc: the single-thread flag, the
    page size, the default thread attributes, the character type data of
    the C locale and the allocator's state. The runner, in
    [StartCtorRunnerSpec](StartCtorRunnerSpec.v), asks for its did-run
    flag and the life of its table. The proof of startup must take all of
    these from the memory that the loader builds. This module states
    that memory's part for any image whose symbols name the globals, and
    shows that the hi_atexit image holds it.

    The lists of pieces are written once, over records of addresses and
    regions, so that Hello repeats only the computation that fills the
    records ([HelloImageEarly](../hello/HelloImageEarly.v)). The tunable
    table is not here. The contract of `c: init_cpu_features` owns it,
    and the caller passes its life on. *)

From Glibc Require Export ImageObjectPieces.
From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Semantics Pieces Heap Runtime Logic StringLogic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld OsRegistry StartCtors StartTunableGetValSpec StartCtypeInitSpec
  StartPtmallocInitSpec StartEarlyInitSpec StartImageUnique.
From Glibc Require Import HelloImageErase HelloImageEraseMem HelloImagePieces HiAtexitModule HiAtexitInitial HiAtexitImage HiAtexitGe.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## Records from an image's symbols

    The contracts name each object by a record of its address and its
    region. These functions fill the records from an image's symbols g
    and the regions rs that its loader registers. A missing symbol gives
    address zero, and the checks below then fail. *)

(** This function returns the address of a symbol, or zero. *)
Definition sym_addr (g : list (name * ptr)) (n : string) : Z :=
  match lookup (TAtom n) g with Some p => ptr_addr p | None => 0 end.

(** This function returns the region that the loader registers at a
    symbol's address. *)
Definition sym_reg (g : list (name * ptr)) (rs : list region) (n : string) : region :=
  match object_region (sym_addr g n) rs with Some r => r | None => mkRegion 0 0 GlobalData Live end.

Definition ei_objs_in g rs : ei_objs :=
  {| ei_st := sym_addr g "__libc_single_threaded"; ei_streg := sym_reg g rs "__libc_single_threaded";
     ei_pg := sym_addr g "_dl_pagesize"; ei_pgreg := sym_reg g rs "_dl_pagesize";
     ei_da := sym_addr g "__GI___default_pthread_attr"; ei_dareg := sym_reg g rs "__GI___default_pthread_attr" |}.

Definition ct_objs_in g rs : ct_objs :=
  {| ct_lt := sym_addr g "__libc_tsd_LOCALE"; ct_ltreg := sym_reg g rs "__libc_tsd_LOCALE";
     ct_gl := sym_addr g "_nl_global_locale"; ct_glreg := sym_reg g rs "_nl_global_locale";
     ct_cc := sym_addr g "_nl_C_LC_CTYPE"; ct_ccreg := sym_reg g rs "_nl_C_LC_CTYPE";
     ct_xc := sym_addr g "_nl_C_LC_CTYPE_class"; ct_xcreg := sym_reg g rs "_nl_C_LC_CTYPE_class";
     ct_xu := sym_addr g "_nl_C_LC_CTYPE_toupper"; ct_xureg := sym_reg g rs "_nl_C_LC_CTYPE_toupper";
     ct_xl := sym_addr g "_nl_C_LC_CTYPE_tolower"; ct_xlreg := sym_reg g rs "_nl_C_LC_CTYPE_tolower";
     ct_cb := sym_addr g "__libc_tsd_CTYPE_B"; ct_cbreg := sym_reg g rs "__libc_tsd_CTYPE_B";
     ct_cu := sym_addr g "__libc_tsd_CTYPE_TOUPPER"; ct_cureg := sym_reg g rs "__libc_tsd_CTYPE_TOUPPER";
     ct_cl := sym_addr g "__libc_tsd_CTYPE_TOLOWER"; ct_clreg := sym_reg g rs "__libc_tsd_CTYPE_TOLOWER" |}.

Definition pm_objs_in g rs : pm_objs :=
  {| pm_tk := sym_addr g "glibc_malloc#tcache_key"; pm_tkreg := sym_reg g rs "glibc_malloc#tcache_key";
     pm_eb := sym_addr g "__libc_errno"; pm_ereg := sym_reg g rs "__libc_errno";
     pm_li := sym_addr g "__libc_initial"; pm_lireg := sym_reg g rs "__libc_initial";
     pm_af := sym_addr g "glibc_malloc#__always_fail_morecore"; pm_afreg := sym_reg g rs "glibc_malloc#__always_fail_morecore";
     pm_ta := sym_addr g "thread_arena"; pm_tareg := sym_reg g rs "thread_arena";
     pm_ma := sym_addr g "glibc_malloc#main_arena"; pm_mareg := sym_reg g rs "glibc_malloc#main_arena";
     pm_mp := sym_addr g "glibc_malloc#mp_"; pm_mpreg := sym_reg g rs "glibc_malloc#mp_";
     pm_tl := sym_addr g "glibc_dl_tunables#tunable_list"; pm_tlreg := sym_reg g rs "glibc_dl_tunables#tunable_list" |}.

(** The runner's flag and table, as address and region pairs. *)
Definition runner_objs_in g rs : (Z * region) * (Z * region) :=
  let a n := match lookup n g with Some p => ptr_addr p | None => 0 end in
  let r b := match object_region b rs with Some r => r | None => mkRegion 0 0 GlobalData Live end in
  ((a ctor_flag_name, r (a ctor_flag_name)), (a ctor_table_name, r (a ctor_table_name))).

(** A check keeps these objects whole in the erased image. *)
Definition early_names : list string :=
  ["__libc_single_threaded"; "__libc_single_threaded_internal"; "_dl_pagesize"; "__GI___default_pthread_attr";
   "__libc_tsd_LOCALE"; "_nl_global_locale"; "_nl_C_LC_CTYPE"; "_nl_C_LC_CTYPE_class"; "_nl_C_LC_CTYPE_toupper";
   "_nl_C_LC_CTYPE_tolower"; "__libc_tsd_CTYPE_B"; "__libc_tsd_CTYPE_TOUPPER"; "__libc_tsd_CTYPE_TOLOWER";
   "glibc_malloc#tcache_key"; "__libc_errno"; "errno"; "__libc_initial"; "glibc_malloc#__always_fail_morecore";
   "thread_arena"; "glibc_malloc#main_arena"; "glibc_malloc#mp_";
   "zrun_deferred_global_ctors#did_run"; "zrun_deferred_global_ctors#table"]%string.

Definition early_keep (n : name) : bool := existsb (name_eqb n) (map TAtom early_names).

(** A lookup in the erased memory passes every byte that it keeps, and
    the character tables hold most of those. The arena's many pieces
    are therefore checked in a memory that keeps only the arena. *)
Definition arena_keep (n : name) : bool := name_eqb n (TAtom "glibc_malloc#main_arena").

(** ## The pieces *)

(** The main arena's 254 bins are empty at the start. *)
Definition bins_ps (ma : Z) : list (piece * pval) :=
  List.concat (map (fun k => ptr_ps ma (24 + 8 * k) null) (seqZ 0 254)).

(** Early init reads and writes about twenty globals, and the proof of
    startup must find them in the memory the loader builds. This list
    holds that memory, apart from the tunable table. The flag is clear, the page size is
    4096, and the default attributes are zero. The thread's locale names
    the global locale, whose first slot names the C character data,
    whose slots name the three tables. The three per-thread table
    pointers already point where `c: __ctype_init` would set them, 256
    bytes into the class table and 512 bytes into the case tables. The
    allocator's objects are zero, except that `c: mp_` holds the
    default mmap threshold at 16.
    The largest cached size at 120 of `c: mp_` is not here, because no
    call of startup touches it, so it stays in the frame that reaches
    `c: main`. *)
Definition early_main_ps (e : ei_objs) (o : pm_objs) (c : ct_objs) : list (piece * pval) :=
  List.concat [
    [(PLive (ei_st e), VLive (ei_streg e))]; [(PByte (ei_st e) 0, VByte 0)];
    [(PLive (ei_pg e), VLive (ei_pgreg e))]; cell (ei_pg e) 0 4096;
    [(PLive (ei_da e), VLive (ei_dareg e))]; cell (ei_da e) 16 0; cell (ei_da e) 32 0;
    [(PLive (ct_lt c), VLive (ct_ltreg c))]; ptr_ps (ct_lt c) 0 (mkPtr (ct_gl c) (Obj (ct_gl c)));
    [(PLive (ct_gl c), VLive (ct_glreg c))]; ptr_ps (ct_gl c) 0 (mkPtr (ct_cc c) (Ro (ct_cc c)));
    [(PLive (ct_cc c), VLive (ct_ccreg c))];
    ptr_ps (ct_cc c) 56 (mkPtr (ct_xc c) (Ro (ct_xc c))); ptr_ps (ct_cc c) 64 (mkPtr (ct_xu c) (Ro (ct_xu c)));
    ptr_ps (ct_cc c) 80 (mkPtr (ct_xl c) (Ro (ct_xl c)));
    [(PLive (ct_xc c), VLive (ct_xcreg c))]; [(PLive (ct_xu c), VLive (ct_xureg c))];
    [(PLive (ct_xl c), VLive (ct_xlreg c))];
    [(PLive (ct_cb c), VLive (ct_cbreg c))]; ptr_ps (ct_cb c) 0 (mkPtr (ct_xc c + 256) (Ro (ct_xc c)));
    [(PLive (ct_cu c), VLive (ct_cureg c))]; ptr_ps (ct_cu c) 0 (mkPtr (ct_xu c + 512) (Ro (ct_xu c)));
    [(PLive (ct_cl c), VLive (ct_clreg c))]; ptr_ps (ct_cl c) 0 (mkPtr (ct_xl c + 512) (Ro (ct_xl c)));
    [(PLive (pm_tk o), VLive (pm_tkreg o))]; (byte_ps (pm_tk o) 0 (repeat 0 8) ++ aux_ps (pm_tk o) 0 (repeat CNone 8))%list;
    [(PLive (pm_eb o), VLive (pm_ereg o))]; (byte_ps (pm_eb o) 0 (repeat 0 4) ++ aux_ps (pm_eb o) 0 (repeat CNone 4))%list;
    [(PLive (pm_li o), VLive (pm_lireg o))]; [(PByte (pm_li o) 0, VByte 0)];
    [(PLive (pm_af o), VLive (pm_afreg o))]; [(PByte (pm_af o) 0, VByte 0)];
    [(PLive (pm_ta o), VLive (pm_tareg o))]; ptr_ps (pm_ta o) 0 null;
    [(PLive (pm_mp o), VLive (pm_mpreg o))]; cell (pm_mp o) 16 131072; cell (pm_mp o) 56 0;
    byte_ps (pm_mp o) 80 (repeat 0 4)].

(** The main arena is alive, and its first link and its 254 bins are
    null. *)
Definition arena_ps (o : pm_objs) : list (piece * pval) :=
  List.concat [[(PLive (pm_ma o), VLive (pm_mareg o))]; ptr_ps (pm_ma o) 8 null; bins_ps (pm_ma o)].

Definition early_ps e o c : list (piece * pval) := early_main_ps e o c ++ arena_ps o.

(** The runner's flag is clear, and its table is alive. The loader does
    not write the table's contents; the starting state does. *)
Definition runner_ps (fr : (Z * region) * (Z * region)) : list (piece * pval) :=
  let '((fl, flreg), (tb, treg)) := fr in
  [(PLive fl, VLive flreg); (PByte fl 0, VByte 0); (PLive tb, VLive treg)].

(** ## What the pieces give the contracts

    Each list turns into the assertions that the contracts of early init
    and the runner ask for. Read-only data becomes persistent on the
    way. *)

Section own.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

Lemma early_pts_concat pss : pts (List.concat pss) ⊣⊢ [∗ list] ps ∈ pss, pts ps.
Proof using Type. induction pss as [|ps pss IH]; cbn [List.concat]; rewrite ?pts_app ?IH; done. Qed.

Lemma pts_bins_gen ma ks :
  pts (List.concat (map (fun k => ptr_ps ma (24 + 8 * k) null) ks)) ⊢ [∗ list] k ∈ ks, ∃ x, pcell ma (24 + 8 * k) x.
Proof using Type.
  induction ks as [|k ks IH]; cbn [map List.concat big_opL]; [iIntros "_"; done|].
  rewrite pts_app. iIntros "[H Hs]". iSplitL "H"; [iExists null; iExact "H"|]. iApply IH. iExact "Hs".
Qed.

Lemma pts_bins ma : pts (bins_ps ma) ⊢ pm_bins ma.
Proof using Type. exact (pts_bins_gen ma (seqZ 0 254)). Qed.

Local Opaque cell byte_ps aux_ps.

(** The pieces give early init everything it takes from memory, given
    the life of the tunable table, which the CPU globals hold. The
    read-only character data is made persistent. *)
Lemma early_own e o c :
  live (pm_tl o) (pm_tlreg o) -∗ pts (early_ps e o c) ==∗
  ei_lives e ∗ (∃ y, ibyte (ei_st e) 0 y) ∗ icell (ei_pg e) 0 4096 ∗
  (∃ v, icell (ei_da e) 16 v) ∗ (∃ v, icell (ei_da e) 32 v) ∗
  ct_ro c ∗ ct_locale c ∗ ct_lives c ∗ ct_cells_any c ∗
  pm_lives o ∗ (∃ y, ibyte (pm_li o) 0 y) ∗ (∃ t, pcell (pm_ta o) 0 t) ∗ pm_fields o.
Proof using Type.
  rewrite /early_ps /early_main_ps /arena_ps pts_app !early_pts_concat. cbn [big_opL].
  iIntros "Ltl [(Lst & Bst & Lpg & Cpg & Lda & Cda16 & Cda32 & Llt & Plt & Lgl & Pgl & Lcc & P56 & P64 & P80 &
    Lxc & Lxu & Lxl & Lcb & Pcb & Lcu & Pcu & Lcl & Pcl & Ltk & Btk & Leb & Beb & Lli & Bli & Laf & Baf &
    Lta & Pta & Lmp & C16 & C56 & B80 & _) (Lma & Pma & Bins & _)]".
  iMod (ptsq_persist with "Lcc") as "#Lcc". iMod (ptsq_persist with "P56") as "#P56".
  iMod (ptsq_persist with "P64") as "#P64". iMod (ptsq_persist with "P80") as "#P80".
  iMod (ptsq_persist with "Lxc") as "#Lxc". iMod (ptsq_persist with "Lxu") as "#Lxu".
  iMod (ptsq_persist with "Lxl") as "#Lxl".
  iDestruct (pts_bins with "Bins") as "Bins". iModIntro.
  rewrite /ei_lives /ct_ro /ct_locale /ct_lives /ct_cells_any /pm_lives /pm_fields /errno_any /errno_own /blk_any.
  iFrame "Lst Lpg Lda Cpg Llt Plt Lgl Pgl Lcb Lcu Lcl Pcb Pcu Pcl Ltl Ltk Leb Lli Laf Lta Lma Lmp Bins
    Lcc P56 P64 P80 Lxc Lxu Lxl Bst Cda16 Cda32 Bli Pta Baf Pma C16 C56".
  iSplitL "Btk"; [iExists _, _; iFrame "Btk"; done|].
  iSplitL "Beb"; [iExists _, _; iFrame "Beb"; done|].
  iExists _. iFrame "B80". done.
Qed.

(** The runner's pieces give its clear flag and the life of its table. *)
Lemma runner_own fr :
  pts (runner_ps fr) ⊢ live fr.1.1 fr.1.2 ∗ ibyte fr.1.1 0 0 ∗ live fr.2.1 fr.2.2.
Proof using Type.
  destruct fr as [[fl flreg] [tb treg]]. rewrite /runner_ps /pts. cbn [big_opL fst snd].
  iIntros "(A & B & C & _)". rewrite /live /ibyte /pts. cbn [big_opL]. iFrame.
Qed.

End own.

(** ## The hi_atexit image *)

Definition hi_ei_objs : ei_objs := Eval vm_compute in ei_objs_in hi_globals hi_image_regions.
Definition hi_ct_objs : ct_objs := Eval vm_compute in ct_objs_in hi_globals hi_image_regions.
Definition hi_pm_objs : pm_objs := Eval vm_compute in pm_objs_in hi_globals hi_image_regions.
Definition hi_runner_objs := Eval vm_compute in runner_objs_in hi_globals hi_image_regions.

Definition hi_early_ps : list (piece * pval) := early_ps hi_ei_objs hi_pm_objs hi_ct_objs.
Definition hi_runner_ps : list (piece * pval) := runner_ps hi_runner_objs.

(** A check that keeps objects by name, rather than by the bases of its
    pieces, avoids collecting and deduplicating those bases. *)
Lemma hi_m0_pieces_by keep ps :
  pieces_ok keep hi_module hi_globals (hi_erased keep) ps = true -> all_agree hi_m0 ps.
Proof.
  destruct (image_pieces keep hi_module hi_module hi_globals hi_m0 ps (incl_refl _)
    hi_initial hi_module_names hi_module_zeros) as (m' & E & _ & H).
  unfold hi_erased. rewrite E. exact H.
Qed.

(** The linked hi_atexit program starts with both lists, and neither
    list names a piece twice. *)
Lemma hi_early_agree : all_agree hi_m0 hi_early_ps.
Proof.
  unfold hi_early_ps, early_ps. apply all_agree_app. split.
  - apply (hi_m0_pieces_by early_keep). vm_cast_no_check (eq_refl true).
  - apply (hi_m0_pieces_by arena_keep). vm_cast_no_check (eq_refl true).
Qed.

Lemma hi_early_nodup : NoDup hi_early_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.

Lemma hi_runner_agree : all_agree hi_m0 hi_runner_ps.
Proof. apply (hi_m0_pieces_by early_keep). vm_cast_no_check (eq_refl true). Qed.

Lemma hi_runner_nodup : NoDup hi_runner_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.

Section hi.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Local Notation hi_program := (program_of w0 glibc_os_registry hge).

(** The program names the objects of early init where the records say,
    and each object is aligned and large enough. The allocator's
    `c: errno` must be the world's. *)
Lemma hi_early_ok :
  ow_errno w0 = Some (mkPtr (pm_eb hi_pm_objs) (Obj (pm_eb hi_pm_objs))) ->
  ei_ok (glibc_program := hi_program) hi_ei_objs /\ ct_ok (glibc_program := hi_program) hi_ct_objs /\
  pm_ok (glibc_program := hi_program) hi_pm_objs /\
  tunable_slot_ok (glibc_program := hi_program) (pm_tl hi_pm_objs) (pm_tlreg hi_pm_objs) 27.
Proof using Type.
  intros Herr. unfold ei_ok, ct_ok, pm_ok, tunable_slot_ok, program_ge, program_world. cbn [program_of].
  cbv [pm_size_ids pm_int_ids app].
  repeat match goal with
  | |- _ /\ _ => split
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor
  end.
  all: first [exact Herr | vm_compute; reflexivity | vm_compute; congruence].
Qed.

(** The program names the runner's flag and table where the record
    says, and both fit. *)
Lemma hi_runner_ok :
  lookup ctor_flag_name (ge_globals hge) = Some (mkPtr hi_runner_objs.1.1 (Obj hi_runner_objs.1.1)) /\
  lookup ctor_table_name (ge_globals hge) = Some (mkPtr hi_runner_objs.2.1 (Ro hi_runner_objs.2.1)) /\
  hi_runner_objs.1.1 + 1 <= r_end hi_runner_objs.1.2 /\ hi_runner_objs.2.1 mod 8 = 0 /\
  hi_runner_objs.2.1 + ctor_table_size 3 <= r_end hi_runner_objs.2.2.
Proof using Type. repeat split; first [vm_compute; reflexivity | vm_compute; congruence]. Qed.

End hi.
