(** When glibc's startup code calls GNU Hello's `c: main`, it must hand
    main the objects that main's proof starts with. This module says
    which resources startup holds at that call, the startup post, and
    proves that they give main's starting state. It mirrors
    [HiAtexitStartBridge](../hi_atexit/HiAtexitStartBridge.v), which
    does the same for hi_atexit.

    ## Where main's state comes from

    Most of main's state is memory that startup never writes, the kept
    frame of [HelloStartKept](HelloStartKept.v). Startup's calls give
    back the rest. `c: _IO_stdfiles_init` links the three streams and
    returns their lives, and `c: check_stdfiles_vtables` returns each
    stream's pointer to its jump table and the table's life.
    `c: __libc_early_init` sets the single-thread flag and returns the
    lives of `c: errno` and of the allocator's parameters `c: mp_`.
    `c: _init_first` sets the two names of the program, and the loader's
    start state holds the arguments. The thread's cleanup fields come
    from `c: __libc_start_call_main`.

    Some library calls that main makes are not proved yet, and their
    contracts may keep memory of their own. This module does not build
    that memory, because those contracts are still assumptions. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic StringLogic MemLogic HelloName.
From Glibc Require Import OsBlocks OsWorld FileInv FileIdle WordString LibioStdfiles HelloGlibcDebts HelloVersionLits
  HelloGetoptStart HelloImageModule HelloImageLoad HelloImageCtors HelloImageEarly HelloImageLayout
  HelloImageStart HelloStartKeptAlloc HelloStartKept.
From Glibc Require AllocLogic AtexitLogic ExitRun HelloGlibcJoin.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## The strings *)

(** Every string of the frame has the shape that the string routines
    read, at its own read-only object. The check covers the wide string
    of Hello as well, whose words go on past its first zero. *)
Lemma hello_lit_shapes : forallb (fun ns => str_shape_b (mkPtr (img_addr ns.1.1) (Ro (img_addr ns.1.1)))
  (img_addr ns.1.1) (snd (img_obj ns.1.1)) ns.2 ns.1.2) hello_lit_strs = true.
Proof. vm_compute. reflexivity. Qed.

(** The frame's list of strings is one literal object for each string. *)
Lemma hello_lit_kept_eq :
  hello_lit_kept_ps = List.concat ((fun ns : string * list Z * list Z => lit_ps (img_addr ns.1.1) (snd (img_obj ns.1.1)) ns.2) <$> hello_lit_strs).
Proof. vm_compute. reflexivity. Qed.

(** These are the first three strings, which are not Hello's own. *)
Lemma hello_lit_heads : take 3 ((fun ns : string * list Z * list Z => (ns.1.1, ns.1.2)) <$> hello_lit_strs) =
  [("progname#str.3", libs_bytes); ("progname#str.4", lt_bytes);
   ("glibc_getopt#str.145", [80;79;83;73;88;76;89;95;67;79;82;82;69;67;84])]%string.
Proof. vm_compute. reflexivity. Qed.

(** The next strings are Hello's literals. *)
Lemma hello_lit_rest_names : (fun ns : string * list Z * list Z => ns.1.1) <$> take 24 (drop 3 hello_lit_strs) = hello_lits_rest.
Proof. vm_compute. reflexivity. Qed.

(** The last strings are those of gnulib's version text, with the bytes
    that [version_lits] gives them. *)
Lemma hello_lit_version : (fun ns : string * list Z * list Z => (ns.1.1, ns.1.2)) <$> drop 24 (drop 3 hello_lit_strs) = version_lits.
Proof. vm_compute. reflexivity. Qed.

Section post.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (g : list (name * ptr)) (m : mem) (fr : word -> mem -> option (res unit * mem))
  (Hi : initial_memory hello_image_module = Some (g, m)).

Local Abbreviation ge := (mkGenv hello_image_module g fr).
Local Abbreviation o := hello_image_objs.

Local Lemma pts_concat pss : pts (List.concat pss) ⊣⊢ [∗ list] ps ∈ pss, pts ps.
Proof using Type. induction pss as [|ps pss IH]; cbn [List.concat]; rewrite ?pts_app ?IH; done. Qed.

Local Lemma ptsq_concat dq pss : ptsq dq (List.concat pss) ⊣⊢ [∗ list] ps ∈ pss, ptsq dq ps.
Proof using Type. induction pss as [|ps pss IH]; cbn [List.concat]; rewrite ?ptsq_app ?IH; done. Qed.

(** Each literal's symbol points at its object read-only. *)
Lemma hello_lit_syms : (fun ns : string * list Z * list Z => sym_ptr ge ns.1.1) <$> hello_lit_strs =
  (fun ns : string * list Z * list Z => mkPtr (img_addr ns.1.1) (Ro (img_addr ns.1.1))) <$> hello_lit_strs.
Proof using Hi.
  destruct (hello_loaded_tables g m Hi) as [Eg _]. unfold sym_ptr. cbn [ge_globals]. rewrite Eg.
  vm_compute. reflexivity.
Qed.

(** The strings of the frame become read-only strings. *)
Lemma hello_lits_own : pts hello_lit_kept_ps ==∗
  [∗ list] ns ∈ hello_lit_strs, word_string DfracDiscarded (sym_ptr ge ns.1.1) ns.1.2.
Proof using Hi.
  rewrite hello_lit_kept_eq pts_concat big_sepL_fmap. iIntros "H".
  iApply big_sepL_bupd. iApply (big_sepL_impl with "H"). iIntros "!>" (k ns Hk) "H".
  pose proof (f_equal (fun l => l !! k) hello_lit_syms) as E. cbn beta in E.
  rewrite !list_lookup_fmap Hk in E. injection E as ->.
  pose proof hello_lit_shapes as S. rewrite forallb_forall in S.
  specialize (S ns (proj1 (list_elem_of_In _ _) (list_elem_of_lookup_2 _ _ _ Hk))).
  iDestruct (word_string_literal with "H") as "H"; [exact (str_shape_b_sound _ _ _ _ _ S)|].
  iMod (word_string_persist with "H") as "#H". done.
Qed.

(** ## The streams *)

(** The stream's field offsets are numbers, and rewriting with them
    lets the stream's pieces match its fields without unfolding the
    layout. *)
Local Lemma file_offsets : off_flags = 0 /\ off_fileno = 112 /\ off_flags2 = 116 /\ off_old_offset = 120 /\
  off_column = 128 /\ off_lock = 136 /\ off_offset = 144 /\ off_codecvt = 152 /\ off_wide = 160 /\
  off_freeres_list = 168 /\ off_freeres_buf = 176 /\ off_mode = 192 /\ off_total_written = 200 /\
  off_vtable = 216.
Proof. vm_compute. repeat split. Qed.

Local Lemma lock_offsets : off_lk_lock = 0 /\ off_lk_cnt = 4 /\ off_lk_owner = 8.
Proof. vm_compute. repeat split. Qed.

(** This is the state in which the linker leaves a stream: unoriented,
    with no buffer, both offsets at minus one and the lock free. *)
Definition hello_kept_state (fl fd lk wd vb : Z) : fstate :=
  mkFstate fl (replicate 12 null) fd 0 (2 ^ 64 - 1) (replicate 8 0) (mkPtr lk (Obj lk)) (2 ^ 64 - 1)
    null (mkPtr wd (Obj wd)) null null 0 0 (mkPtr (vb + vt_file) (Ro vb)).

(** The linker's wide data object of a stream is the wide data that an
    idle stream owns. *)
Lemma hello_start_wide_own wd wreg vb :
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  pts (hello_wide_kept_ps wd wreg vb) -∗ wide_idle vb (mkPtr wd (Obj wd)) null.
Proof using Type.
  intros H0 H8 He Hr. iIntros "H". rewrite /hello_wide_kept_ps.
  change ((PLive wd, VLive wreg) :: ?l) with ([(PLive wd, VLive wreg)] ++ l).
  rewrite !pts_app. iDestruct "H" as "(Hl & Hb & Ha & Hp)".
  iExists wd, wreg. iSplit; [iPureIntro; split_and!; done|].
  iFrame "Hl Hb Ha". iExact "Hp".
Qed.

(** Main prints through a stream only when the stream is whole: it must
    own the stream, its fields and its lock. Startup gives back the
    stream's life and its table pointer, and the linker set the rest. *)
Lemma hello_start_file_own fb fl fd lk lkreg wd wreg vb self :
  flags_ok (hello_kept_state fl fd lk wd vb) -> (fd = 0 \/ fd = 1 \/ fd = 2) ->
  (fd <> 0 -> has fl io_no_writes = false) -> has fl io_is_appending = false ->
  (has fl io_unbuffered = true -> has fl io_line_buf = false) -> has fl io_currently_putting = false ->
  0 <= fd < 2 ^ 32 ->
  lk mod 8 = 0 -> lk + 16 <= r_end lkreg -> r_end lkreg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  stream_live (mkPtr fb (Obj fb)) -∗ pcell fb 216 (mkPtr (vb + 336) (Ro vb)) -∗
  pts (hello_stream_kept_ps fb fl fd lk lkreg wd) -∗ pts (hello_wide_kept_ps wd wreg vb) -∗
  file_idle vb self (mkPtr fb (Obj fb)) fd.
Proof using Type.
  intros Hok H012 Hnw Hap Hlb Hpt Hfd Hlk Hlke Hlkr Hw0 Hw8 Hwe Hwr. iIntros "Hlv Hvt H Hw".
  iDestruct (hello_start_wide_own with "Hw") as "Hw"; [done..|].
  iDestruct "Hlv" as (b freg (Heq & Hb & Hal & Hend & Htop)) "Hl". injection Heq as <-.
  rewrite /hello_stream_kept_ps pts_concat.
  change (seqZ 0 12) with [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11].
  cbn [big_opL map List.concat]. rewrite !pts_app.
  iDestruct "H" as "(Hfl & (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _) & Hfd & Hf2 &
    Hold & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb & Hmd & Htot & Hlv & Hl0 & Hl4 & Hl8 & _)".
  iExists fb, freg, (hello_kept_state fl fd lk wd vb), NbNone.
  iSplit.
  { iPureIntro. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hb|]. split; [exact Hend|].
    split; [lia|]. split; [exact Hok|]. split; [|split_and!; first [reflexivity | exact (conj (conj Hlb (fun _ => Hpt)) Hpt)]].
    unfold idle_ok, hello_kept_state, fs_ptr; cbn [fs_fileno fs_mode fs_ptrs fs_flags fs_flags2 fs_column].
    cbn. split_and!; auto; lia. }
  iFrame "Hl". iSplitL "Hfl P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 Hfd Hf2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvt".
  - destruct Hok as (Hfl & _). cbn [hello_kept_state fs_flags] in Hfl.
    rewrite /file_fields /hello_kept_state.
    cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
      fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable replicate big_opL].
    destruct file_offsets as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
    iSplit; [done|]. iSplitL "Hfl"; [iSplit; [done|iExact "Hfl"]|].
    iSplitL "P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11"; [iFrame "P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11"|].
    iSplitL "Hfd"; [iSplit; [done|iExact "Hfd"]|]. iSplitL "Hf2"; [iSplit; [iPureIntro; lia|iExact "Hf2"]|].
    iSplitL "Hold"; [iExact "Hold"|]. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hcol"; [iExact "Hcol"|]. iSplitL "Hlp"; [iExact "Hlp"|]. iSplitL "Hoff"; [iExact "Hoff"|].
    iSplitL "Hcv"; [iExact "Hcv"|]. iSplitL "Hwd"; [iExact "Hwd"|].
    iSplitL "Hfrl"; [iExact "Hfrl"|]. iSplitL "Hfrb"; [iExact "Hfrb"|].
    iSplitL "Hmd"; [iSplit; [iPureIntro; lia|iExact "Hmd"]|]. iSplitL "Htot"; [iExact "Htot"|]. iExact "Hvt".
  - iSplitL "Hlv Hl0 Hl4 Hl8"; [|iSplit; [cbv [buf_idle]; done | iExact "Hw"]]. iExists lk, lkreg. iSplit; [iPureIntro; reflexivity|].
    rewrite /lock_state /int_cell. destruct lock_offsets as (-> & -> & ->).
    iSplitR; [iPureIntro; split_and!; lia|]. iSplitL "Hlv"; [iExact "Hlv"|].
    iSplitL "Hl0"; [iSplit; [iPureIntro; lia|iExact "Hl0"]|].
    iSplitL "Hl4"; [iSplit; [iPureIntro; lia|iExact "Hl4"]|]. iExact "Hl8".
Qed.

(** Hello never reads stdin, and the exit path's cleanup only checks
    that stdin has nothing pending and its lock is free. So main holds
    stdin in the form that cleanup reads ([exit_stream] with false),
    together with the stream's life. The linker's state of stdin already
    has that form: its buffer pointers are null and its lock is free. *)
Lemma hello_start_stdin_own fb fl fd lk lkreg wd :
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 -> 0 <= fd < 2 ^ 31 ->
  lk mod 8 = 0 -> lk + 16 <= r_end lkreg -> r_end lkreg <= 2 ^ 63 ->
  stream_live (mkPtr fb (Obj fb)) -∗ pts (hello_stream_kept_ps fb fl fd lk lkreg wd) -∗
  LibioFlushInv.stream_life (mkPtr fb (Obj fb)) ∗ LibioFlushInv.exit_stream false (mkPtr fb (Obj fb)).
Proof using Type.
  intros Hfl Hbits Hfd Hlk Hlke Hlkr. iIntros "Hlv H".
  iSplitL "Hlv"; [rewrite /stream_live /LibioFlushInv.stream_life; iExact "Hlv"|].
  rewrite /hello_stream_kept_ps pts_concat.
  change (seqZ 0 12) with [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11].
  cbn [big_opL map List.concat]. rewrite !pts_app.
  iDestruct "H" as "(Hfl & (P0 & P1 & _ & P3 & P4 & _ & _ & _ & _ & P9 & _) & Hfd & Hf2 &
    _ & _ & Hlp & _ & _ & _ & _ & _ & Hmd & _ & Hlv & Hl0 & Hl4 & Hl8 & _)".
  iExists fb, fl, 0, fd, 0, lk, lkreg, CNone, (mkRegion 0 0 Heap Live), 0, 0, 0, 0.
  iSplitR; [iPureIntro; split_and!; try reflexivity; try assumption; try lia; right; reflexivity|].
  rewrite /lock_state /int_cell. destruct file_offsets as (-> & -> & -> & _ & _ & -> & _ & _ & _ & _ & _ & -> & _).
  destruct lock_offsets as (-> & -> & ->).
  iFrame "Hfl Hf2 Hfd Hmd Hlp Hlv Hl0 Hl4 Hl8 P0 P1 P3 P4 P9". iPureIntro; split_and!; lia.
Qed.

(** ## The post *)

(** These are the three standard streams in the order of the list of
    all streams. *)
Definition hello_streams : list ptr := [ho_err o; ho_out o; ho_in o].

(** Startup must hand main everything main will touch, so we list what
    startup owns when it calls `c: main`. It owns the kept frame and the
    memory that its calls gave back. The program's two names point at y
    and z, and the vector av holds the arguments p0 :: ps. *)
Definition hello_start_post (av : Z) (ar : region) (p0 : ptr) (ps : list ptr) (y z : ptr) : iProp Σ :=
  pts hello_start_kept_ps ∗
  io_list_inv ge hello_streams ∗ ([∗ list] f ∈ hello_streams, stream_live f) ∗
  pcell (img_a "_IO_2_1_stdin_") 216 (mkPtr (img_a "__io_vtables" + 336) (Ro (img_a "__io_vtables"))) ∗
  pcell (img_a "_IO_2_1_stdout_") 216 (mkPtr (img_a "__io_vtables" + 336) (Ro (img_a "__io_vtables"))) ∗
  pcell (img_a "_IO_2_1_stderr_") 216 (mkPtr (img_a "__io_vtables" + 336) (Ro (img_a "__io_vtables"))) ∗
  live (ho_vb o) (ho_vreg o) ∗
  live (ho_sb o) (ho_sreg o) ∗ ibyte (ho_sb o) 0 1 ∗
  live (ho_eb o) (ho_ereg o) ∗ errno_any (ho_eb o) ∗ live (ho_mp o) (ho_mpreg o) ∗
  live (ho_nb o) (ho_nreg o) ∗ pcell (ho_nb o) 0 y ∗ live (ho_nsb o) (ho_nsreg o) ∗ pcell (ho_nsb o) 0 z ∗
  ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps).

(** This is the memory that main starts with. The startup run in
    [HelloStartWp](HelloStartWp.v) builds it before main's proof uses it. *)
Definition hello_start_main_res (w : os_world) (av : Z) (ar : region) (p0 : ptr) (ps : list ptr) (y z : ptr) : iProp Σ :=
  hello_ro_rest ge o ∗
  word_string DfracDiscarded (sym_ptr ge "glibc_getopt#str.145") [80;79;83;73;88;76;89;95;67;79;82;82;69;67;84] ∗
  pts hello_start_ps ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
  ncells o null y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] 0 ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
  hello_stdio w ge o ∗ getopt_cells o null 1.

(** A full allocator cache can be given up for a read-only one. *)
Lemma tcache_idle_discard mp tc dm mpreg tcreg dmreg :
  AllocLogic.tcache_idle (DfracOwn 1) mp tc dm mpreg tcreg dmreg ==∗
  AllocLogic.tcache_idle DfracDiscarded mp tc dm mpreg tcreg dmreg.
Proof using Type.
  rewrite /AllocLogic.tcache_idle /liveq /icellq /pcellq.
  iIntros "(% & A & B & C & D & E & F)".
  iMod (ptsq_persist with "A") as "#A". iMod (ptsq_persist with "B") as "#B".
  iMod (ptsq_persist with "C") as "#C". iMod (ptsq_persist with "D") as "#D".
  iMod (ptsq_persist with "E") as "#E".
  iMod (big_sepL_bupd with "[F]") as "F".
  { iApply (big_sepL_mono with "F"). iIntros (k i _) "H". iMod (ptsq_persist with "H") as "#H". done. }
  iModIntro. iFrame "A B C D E F". done.
Qed.

(** The jump table of the frame holds ge's file functions. *)
Lemma hello_jumps_syms : hello_jumps_kept_ps =
  List.concat ((fun sl : Z * string => hello_pointer_ps (ho_vb o) (vt_file + sl.1) (sym_ptr ge sl.2)) <$> file_jumps).
Proof using Hi.
  destruct (hello_loaded_tables g m Hi) as [Eg _]. unfold sym_ptr. cbn [ge_globals]. rewrite Eg.
  vm_compute. reflexivity.
Qed.

(** We want main to start from what startup leaves behind. This lemma
    shows that startup's memory and the thread's cleanup fields are
    enough. *)
Lemma hello_start_post_main w av ar p0 ps y z :
  hello_start_post av ar p0 ps y z -∗ tcb_cleanup_inv (ow_self w) -∗ error_progname_ro ge -∗ error_count ge ==∗
  hello_start_main_res w av ar p0 ps y z.
Proof using Hi.
  pose proof hello_jumps_syms as Ej.
  assert (E3 : sym_ptr ge "progname#str.3" = ho_lp o /\ sym_ptr ge "progname#str.4" = ho_tp o).
  { destruct (hello_loaded_tables g m Hi) as [Eg _]. unfold sym_ptr. cbn [ge_globals]. rewrite Eg.
    vm_compute. split; reflexivity. }
  assert (Pv : lookup (TAtom "__io_vtables") (ge_globals ge) = Some (mkPtr (ho_vb o) (Ro (ho_vb o))) /\
    lookup (TAtom "__libc_single_threaded_internal") (ge_globals ge) = Some (mkPtr (ho_sb o) (Obj (ho_sb o)))).
  { destruct (hello_loaded_tables g m Hi) as [Eg _]. cbn [ge_globals]. rewrite Eg.
    vm_compute. split; reflexivity. }
  destruct E3 as [E3 E4]. destruct Pv as [Pv Ps].
  rewrite /hello_start_post /hello_start_kept_ps.
  iIntros "(Hk & Hlist & (Le & Lo & Li & _) & Vi & Vo & Ve & Lvt & Lsb & Hsb & Leb & Herr & Lmp &
    Lnb & Hnb & Lns & Hns & #Hargs & Hav) Htcb #Hepn Hec".
  iDestruct (pts_app with "Hk") as "[Hal Hk]". iDestruct (pts_app with "Hk") as "[Hex Hk]".
  iDestruct (pts_app with "Hk") as "[Hst Hk]". iDestruct (pts_app with "Hk") as "[Hio Hlit]".
  iDestruct (hello_alloc_kept_own with "Lmp Hal") as "HM". iMod (tcache_idle_discard with "HM") as "#HM".
  iDestruct (hello_exit_kept_own with "Hex") as "[Hxi Hxl]". iMod (hello_lits_own with "Hlit") as "Hlit".
  iEval (rewrite -(take_drop 3 hello_lit_strs) big_sepL_app) in "Hlit". iDestruct "Hlit" as "[Hl3 #Hlr]".
  iEval (rewrite -(take_drop 24 (drop 3 hello_lit_strs)) big_sepL_app) in "Hlr". iDestruct "Hlr" as "[#Hlr #Hlv]".
  iEval (cbv [take hello_lit_strs]; cbn [big_opL fst snd]) in "Hl3".
  iDestruct "Hl3" as "(#Hlp & #Htp & #Hkey & _)". iEval (rewrite E3) in "Hlp". iEval (rewrite E4) in "Htp".
  iEval (rewrite /hello_io_kept_ps pts_concat; cbn [big_opL]) in "Hio".
  iDestruct "Hio" as "(Ser & Sout & Sin & Lso & Hso & Lse & Hse & Hjmp & Lpn & Hpn & Loa & Hoa & Loi & Hoi &
    Wer & Wout & _)".
  iDestruct (hello_start_file_own _ _ _ _ _ _ _ _ (ow_self w) with "Lo Vo Sout Wout") as "Fo";
    [vm_compute; intuition congruence..|].
  iDestruct (hello_start_stdin_own with "Li Sin") as "Fi";
    [vm_compute; intuition congruence..|].
  iDestruct (hello_start_file_own _ _ _ _ _ _ _ _ (ow_self w) with "Le Ve Ser Wer") as "Fe";
    [vm_compute; intuition congruence..|].
  iMod (ptsq_persist with "Lso") as "#Lso". iMod (ptsq_persist with "Hso") as "#Hso".
  iMod (ptsq_persist with "Lse") as "#Lse". iMod (ptsq_persist with "Hse") as "#Hse".
  iMod (ptsq_persist with "Lvt") as "#Lvt". iMod (ptsq_persist with "Hjmp") as "#Hjmp".
  iMod (ptsq_persist with "Lsb") as "#Lsb". iMod (ptsq_persist with "Hsb") as "#Hsb".
  iMod (ptsq_persist with "Leb") as "#Leb".
  iEval (rewrite Ej ptsq_concat big_sepL_fmap) in "Hjmp".
  iModIntro. rewrite /hello_start_main_res.
  iSplitR.
  { rewrite /hello_ro_rest.
    iSplitR.
    { rewrite /vtables_ro. iSplitR; [iPureIntro; split; [exact Pv|vm_compute; intuition congruence]|].
      iSplitR; [iExact "Lvt"|iExact "Hjmp"]. }
    iSplitR.
    { rewrite /single_ro. iSplitR; [iPureIntro; split; [exact Ps|vm_compute; intuition congruence]|].
      iSplitR; [iExact "Lsb"|iExact "Hsb"]. }
    iSplitR; [iExact "Lso"|]. iSplitR; [iExact "Hso"|]. iSplitR; [iExact "Lse"|]. iSplitR; [iExact "Hse"|].
    iSplitR; [iExact "Leb"|]. iSplitR; [iExact "HM"|]. iSplitR; [iExact "Hlp"|]. iSplitR; [iExact "Htp"|].
    iSplit.
    { rewrite -hello_lit_rest_names big_sepL_fmap. iApply (big_sepL_mono with "Hlr").
      iIntros (k ns _) "H". iExists _. iExact "H". }
    iSplitR; [rewrite /version_ro -hello_lit_version big_sepL_fmap; iExact "Hlv"|]. iSplitR; [iExact "Hepn"|].
    iAssert ([∗ list] ns ∈ (fun ns : string * list Z * list Z => (ns.1.1, ns.1.2)) <$> take 24 (drop 3 hello_lit_strs),
      word_string DfracDiscarded (sym_ptr ge ns.1) ns.2)%I as "#Hlf"; [rewrite big_sepL_fmap; iExact "Hlr"|].
    rewrite /print_fmt_ro /print_fmts. cbn [big_opL].
    iSplitR; [iApply (big_sepL_lookup (fun _ ns => word_string DfracDiscarded (sym_ptr ge ns.1) ns.2) _ 17
      ("hello#str.77"%string, [37; 115; 58; 32; 37; 115]) with "Hlf"); vm_compute; reflexivity|].
    iSplitR; [iApply (big_sepL_lookup (fun _ ns => word_string DfracDiscarded (sym_ptr ge ns.1) ns.2) _ 0
      ("hello#str.54"%string, [85; 115; 97; 103; 101; 58; 32; 37; 115; 32; 91; 79; 80; 84; 73; 79; 78; 93; 46; 46; 46; 10]) with "Hlf"); vm_compute; reflexivity|].
    iSplitR; [iApply (big_sepL_lookup (fun _ ns => word_string DfracDiscarded (sym_ptr ge ns.1) ns.2) _ 8
      ("hello#str.62"%string, [82; 101; 112; 111; 114; 116; 32; 37; 115; 32; 116; 114; 97; 110; 115; 108; 97; 116; 105; 111; 110; 32; 98; 117; 103; 115; 32; 116; 111; 32; 60; 104; 116; 116; 112; 115; 58; 47; 47; 116; 114; 97; 110; 115; 108; 97; 116; 105; 111; 110; 112; 114; 111; 106; 101; 99; 116; 46; 111; 114; 103; 47; 116; 101; 97; 109; 47; 62; 10]) with "Hlf"); vm_compute; reflexivity|].
    iSplitR; [iApply (big_sepL_lookup (fun _ ns => word_string DfracDiscarded (sym_ptr ge ns.1) ns.2) _ 19
      ("hello#str.79"%string, [84; 114; 121; 32; 39; 37; 115; 32; 45; 45; 104; 101; 108; 112; 39; 32; 102; 111; 114; 32; 109; 111; 114; 101; 32; 105; 110; 102; 111; 114; 109; 97; 116; 105; 111; 110; 46; 10]) with "Hlf"); vm_compute; reflexivity|].
    done. }
  iSplitR; [iExact "Hkey"|]. iSplitL "Hst"; [iExact "Hst"|]. iSplitR; [iExact "Hargs"|].
  iSplitL "Hav"; [iExact "Hav"|].
  iSplitL "Lpn Hpn Lnb Hnb Lns Hns".
  { rewrite /ncells. iSplitL "Lpn"; [iExact "Lpn"|]. iSplitL "Hpn"; [iExact "Hpn"|].
    iSplitL "Lnb"; [iExact "Lnb"|]. iSplitL "Hnb"; [iExact "Hnb"|]. iSplitL "Lns"; [iExact "Lns"|iExact "Hns"]. }
  iSplitL "Hxi Hxl"; [iSplitL "Hxi"; [iExact "Hxi"|iExact "Hxl"]|].
  iSplitR "Loa Hoa Loi Hoi".
  { rewrite /hello_stdio. iSplitL "Fo"; [iExact "Fo"|]. iSplitL "Fe"; [iExact "Fe"|].
    iSplitL "Fi"; [iExact "Fi"|]. iSplitL "Hlist"; [iExact "Hlist"|]. iSplitL "Htcb"; [iExact "Htcb"|]. iSplitL "Herr"; [iExact "Herr"|iExact "Hec"]. }
  rewrite /getopt_cells. iSplitL "Loa"; [iExact "Loa"|]. iSplitL "Hoa"; [iExact "Hoa"|].
  iSplitL "Loi"; [iExact "Loi"|]. rewrite /int_cell. iSplitR; [iPureIntro; lia|iExact "Hoi"].
Qed.

End post.
