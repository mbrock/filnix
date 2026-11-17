(** Before `c: main` runs, startup calls `c: check_stdfiles_vtables`,
    which checks that each standard stream points into glibc's array of
    stream tables. Its contract in
    [StartCtorVtablesSpec](StartCtorVtablesSpec.v) reads one pointer in
    each stream and needs the array to stay alive. This module shows that
    hi_atexit starts with those pointers and that array, so that the
    proof of its startup can make the call. The streams must stay alive
    too, but another constructor owns them and lends them to the check. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv HiAtexitGe HiAtexitInitial HiAtexitInitialAlloc
  HiAtexitInitialStdout StartCtorVtablesSpec.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv.
Open Scope Z_scope.

(** The array of stream tables, `c: __io_vtables`, starts at 73504 in
    hi_atexit and is read-only data. *)
Definition hi_vtables_reg : region := mkRegion 73504 75856 GlobalData Live.

(** This list holds the table pointer of each stream, which points 336
    bytes into the array, and the life of the array. The streams are
    stdin at 72000, stdout at 72240 and stderr at 71760. *)
Definition hi_vtables_ps : list (piece * pval) :=
  concat [hi_pointer_ps 72000 216 (mkPtr (73504 + 336) (Ro 73504));
          hi_pointer_ps 72240 216 (mkPtr (73504 + 336) (Ro 73504));
          hi_pointer_ps 71760 216 (mkPtr (73504 + 336) (Ro 73504));
          [(PLive 73504, VLive hi_vtables_reg)]].

(** The linked program really starts with these contents. *)
Lemma hi_vtables_agree : all_agree hi_m0 hi_vtables_ps.
Proof. apply hi_m0_pieces. vm_compute. reflexivity. Qed.

Section image.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world).
Local Notation hi_program := (program_of w0 glibc_os_registry hge).

(** The check asks that the program names the three streams and the
    array, and that each stream is aligned and large enough. hi_atexit
    meets that. *)
Lemma hi_vtables_ok :
  vtables_globals (glibc_program := hi_program) 72000 72240 71760 73504 /\
  stream_ok 72000 (mkRegion 72000 72224 GlobalData Live) /\ stream_ok 72240 hi_stdout_reg /\
  stream_ok 71760 (mkRegion 71760 71984 GlobalData Live).
Proof using Type.
  unfold vtables_globals, stream_ok, hi_stdout_reg. cbn [program_of ge_globals].
  split_and!; first [vm_compute; reflexivity | cbn [r_end]; lia].
Qed.

(** Startup hands the check the memory it reads, and this list holds
    all of it except the streams' lives, each piece owned whole. *)
Lemma hi_vtables_cells :
  pts hi_vtables_ps ⊢
  pcell 72000 216 (mkPtr (73504 + 336) (Ro 73504)) ∗ pcell 72240 216 (mkPtr (73504 + 336) (Ro 73504)) ∗
  pcell 71760 216 (mkPtr (73504 + 336) (Ro 73504)) ∗ live 73504 hi_vtables_reg.
Proof using Type.
  rewrite /hi_vtables_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hi & Ho & He & Hv & _)". iFrame.
Qed.

End image.
