(** Before `c: main` runs, glibc calls `c: _init_first` to record the
    arguments of the program and its name. The contract of that call
    in [StartInitFirstSpec](StartInitFirstSpec.v) asks for five
    globals of glibc and for the argument array of the program. This
    module shows that the hi_atexit program starts with the five
    globals in a state that the contract accepts, so that the proof of
    its startup can make the call.

    The memory of a program at its start is fixed when the program is
    linked. In hi_atexit the count is zero, the two pointers to the
    arguments and to the environment are null, and both names of the
    program point at an empty string. The argument array is not part
    of that memory. The system builds it when the program starts, so
    the caller supplies it. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv HiAtexitGe HiAtexitInitial HiAtexitInitialAlloc
  StartInitMiscSpec StartInitFirstSpec.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv.
Open Scope Z_scope.

(** Both names of the program start as pointers to this empty string,
    which is read-only data of the image. *)
Definition hi_empty_name : ptr := mkPtr 84928 (Ro 84928).

(** This list is the part of the initial memory that the call writes.
    It holds the lifetime and the contents of the count, of the two
    argument pointers and of the two names. *)
Definition hi_init_first_ps : list (piece * pval) :=
  concat [[(PLive 84752, VLive (mkRegion 84752 84760 GlobalData Live))]; byte_ps 84752 0 (int_bytes 0);
    [(PLive 84784, VLive (mkRegion 84784 84792 GlobalData Live))]; hi_pointer_ps 84784 0 null;
    [(PLive 78768, VLive (mkRegion 78768 78776 GlobalData Live))]; hi_pointer_ps 78768 0 null;
    [(PLive 84864, VLive (mkRegion 84864 84872 GlobalData Live))]; hi_pointer_ps 84864 0 hi_empty_name;
    [(PLive 84896, VLive (mkRegion 84896 84904 GlobalData Live))]; hi_pointer_ps 84896 0 hi_empty_name].

(** The linked program really starts with these contents. *)
Lemma hi_init_first_agree : all_agree hi_m0 hi_init_first_ps.
Proof. apply hi_m0_pieces. vm_compute. reflexivity. Qed.

(** The three globals that hold the arguments lie here in hi_atexit. *)
Definition hi_init_first_objs : if_objs :=
  {| if_ac := 84752; if_acreg := mkRegion 84752 84760 GlobalData Live;
     if_lv := 84784; if_lvreg := mkRegion 84784 84792 GlobalData Live;
     if_en := 78768; if_enreg := mkRegion 78768 78776 GlobalData Live |}.

(** The two names of the program lie at fixed addresses in this
    image. The argument array does not, because the system places it
    when the program starts. The caller gives its address av and its
    region. *)
Definition hi_init_misc_objs (av : Z) (avreg : region) : im_objs :=
  {| im_pn := 84864; im_pnreg := mkRegion 84864 84872 GlobalData Live;
     im_pf := 84896; im_pfreg := mkRegion 84896 84904 GlobalData Live;
     im_av := av; im_avreg := avreg |}.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Local Notation hi_program := (program_of w0 glibc_os_registry hge).

(** The program may call the constructor at its start. It needs the
    five globals as they are in the initial memory. It also needs a
    share of the argument array, whose first slot points at the name
    of the program. The count must fit in an `c: int`. The argument
    array must be aligned, and it must not lie at address zero. *)
Lemma hi_init_first_pre av avreg dq argc envp a s :
  0 <= argc < 2 ^ 32 -> 0 < av -> av mod 8 = 0 -> av + 8 <= r_end avreg ->
  pts hi_init_first_ps -∗ im_args (glibc_program := hi_program) (hi_init_misc_objs av avreg) dq a s -∗
  fs_pre (init_first_spec (glibc_program := hi_program))
    (hi_init_first_objs, hi_init_misc_objs av avreg, dq, argc, envp, a, s,
     hi_empty_name, hi_empty_name, null, null).
Proof using Type.
  intros Hargc Hav0 Hava Have.
  rewrite /hi_init_first_ps hi_pts_concat. cbn [big_opL fs_pre init_first_spec].
  iIntros "(Lac & Hac & Llv & Hlv & Len & Hen & Lpn & Hpn & Lpf & Hpf & _) Ha".
  iSplit.
  { iPureIntro. split; [vm_compute; intuition congruence|]. split; [exact Hargc|].
    unfold im_ok. cbn [im_pn im_pnreg im_pf im_pfreg im_av im_avreg hi_init_misc_objs].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [vm_compute; congruence|]. split; [reflexivity|]. split; [vm_compute; congruence|].
    split; [exact Hav0|]. split; [exact Hava|exact Have]. }
  iSplitL "Lac Llv Len"; [rewrite /if_lives; iFrame "Lac Llv Len"|].
  iSplitL "Hac"; [iExists (int_bytes 0); iSplit; [done|iExact "Hac"]|].
  iSplitL "Hlv"; [iExact "Hlv"|]. iSplitL "Hen"; [iExact "Hen"|].
  iSplitR "Ha"; [|iExact "Ha"]. rewrite /im_names. iFrame "Lpn Hpn Lpf Hpf".
Qed.

End image.
