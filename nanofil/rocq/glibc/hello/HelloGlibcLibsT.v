(** This file states the linking and object-layout facts needed by
    Hello's concrete library bridges. The linked environment binds each
    call to its compiled implementation and leaves OS calls external.
    The proof fixes no symbol addresses.

    The interfaces keep the bridges on the same resource definitions.
    They hide internal proofs from later substitutions while exposing
    the concrete predicates needed to compose registration and exit. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import base list fin_maps.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic HelloLeaf HelloName.
From Nanofil Require HelloClose.
From Glibc Require Import OsWorld FileInv LibioLogic SysWrappers StrlenLogic StrncmpCode MemrchrCode MemcmpCode
  MemFwdCode StrchrCode AllocLogic LeavesLogic AtexitLogic ExitRunCode LibioGenCode SysCode LibioFlushCode
  LibioCleanupCode HelloGlibcDebts.
From Glibc Require AtexitLogic HelloGlibcDebts.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** The linked environment supplies the functions and global objects
    read by the library proofs. OS entry points remain external. *)
Record hello_link (ge : genv) (o : hello_objs) : Prop := mkHelloLink {
  hk_mbszero : find_fn ge (TAtom "mbszero") = Some (Defined mbszero_fn);
  hk_memset : find_fn ge (TAtom "memset") = Some (Defined glibc_memset);
  hk_zmemset : find_fn ge (TAtom "zmemset") = None /\ lookup (TAtom "zmemset") (ge_globals ge) = None;
  hk_name : find_fn ge (TAtom "set_program_name") = Some (Defined set_program_name_fn);
  hk_strrchr : find_fn ge (TAtom "strrchr") = Some (Defined glibc_strrchr);
  hk_gi_strlen : find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen);
  hk_memrchr : find_fn ge (TAtom "__GI___memrchr") = Some (Defined glibc_memrchr);
  hk_memcmp : find_fn ge (TAtom "memcmp") = Some (Defined glibc_memcmp);
  hk_memeq : find_fn ge (TAtom "memeq") = Some (Defined memeq_fn);
  hk_strncmp : find_fn ge (TAtom "strncmp") = Some (Defined glibc_strncmp);
  hk_pb : lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr (ho_pb o) (Obj (ho_pb o)));
  hk_nb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr (ho_nb o) (Obj (ho_nb o)));
  hk_nsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr (ho_nsb o) (Obj (ho_nsb o)));
  hk_lp : lookup (TAtom "progname#str.3") (ge_globals ge) = Some (ho_lp o);
  hk_tp : lookup (TAtom "progname#str.4") (ge_globals ge) = Some (ho_tp o);
  hk_pb_at : 0 <= ho_pb o /\ ho_pb o mod 8 = 0 /\ ho_pb o + 8 <= r_end (ho_preg o) /\ r_end (ho_preg o) <= 2 ^ 48;
  hk_nb_at : 0 <= ho_nb o /\ ho_nb o mod 8 = 0 /\ ho_nb o + 8 <= r_end (ho_nreg o) /\ r_end (ho_nreg o) <= 2 ^ 48;
  hk_nsb_at : 0 <= ho_nsb o /\ ho_nsb o mod 8 = 0 /\ ho_nsb o + 8 <= r_end (ho_nsreg o) /\ r_end (ho_nsreg o) <= 2 ^ 48;
  hk_strlen : find_fn ge (TAtom "strlen") = Some (Defined glibc_strlen);
  hk_errno : find_fn ge (TAtom "__errno_location") = Some (Defined errno_location_fn);
  hk_errno_at : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (ho_eb o) (Obj (ho_eb o)));
  hk_xmalloc : find_fn ge (TAtom "xmalloc") = Some (Defined xmalloc_fn);
  hk_malloc : find_fn ge (TAtom "malloc") = Some (Defined malloc_fn);
  hk_malloc2 : find_fn ge (TAtom "malloc#__libc_malloc2") = Some (Defined malloc2_fn);
  hk_mp : lookup (TAtom "malloc#mp_") (ge_globals ge) = Some (mkPtr (ho_mp o) (Obj (ho_mp o)));
  hk_tc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr (ho_tc o) (Obj (ho_tc o)));
  hk_free : find_fn ge (TAtom "free") = Some (Defined free_fn);
  hk_frees : frees_heap (ge_free ge) /\ find_fn ge zgc_free_name = None /\
             lookup zgc_free_name (ge_globals ge) = None;
  hk_atexit : find_fn ge (TAtom "atexit") = Some (Defined atexit_fn);
  hk_exit_fns : exit_fns ge;
  hk_exit_layout : exit_layout (ho_x o);
  hk_exit_globals : exit_globals ge (ho_x o);
  hk_exit : find_fn ge (TAtom "exit") = Some (Defined glibc_exit);
  hk_run_exit : find_fn ge (TAtom "__run_exit_handlers") = Some (Defined glibc___run_exit_handlers);
  hk_exit_soft : find_fn ge (TAtom "zsys_exit_soft") = None /\ lookup (TAtom "zsys_exit_soft") (ge_globals ge) = None;
  hk_cookie : find_fn ge (TAtom "zthread_self_cookie") = None /\
              lookup (TAtom "zthread_self_cookie") (ge_globals ge) = None;
  hk_el : 0 < ho_el o /\ ho_el o mod 8 = 0 /\ ho_el o + 16 <= r_end (ho_elr o) <= 2 ^ 64 /\
          lookup (TAtom "glibc_exit#__exit_lock") (ge_globals ge) = Some (mkPtr (ho_el o) (Obj (ho_el o)));
  hk_dtors : find_fn ge (TAtom "__GI___call_tls_dtors") = Some (Defined glibc___call_tls_dtors);
  hk_sys : sys_external ge;
  hk_push : find_fn ge (TAtom "__GI___libc_cleanup_push_defer") = Some (Defined glibc___libc_cleanup_push_defer);
  hk_pop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") = Some (Defined glibc___libc_cleanup_pop_restore);
  hk_flush : find_fn ge (TAtom "__GI__IO_flush_all") = Some (Defined glibc__IO_flush_all);
  hk_cleanup : find_fn ge (TAtom "_IO_cleanup") = Some (Defined glibc__IO_cleanup);
  hk_fcp : lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some (ho_fcp o) /\
           0 <= ptr_addr (ho_fcp o) < 2 ^ 64;
  hk_close_stdout : find_fn ge (TAtom "close_stdout") = Some (Defined HelloClose.close_stdout_fn);
  hk_cp : ptr_cap (ho_cp o) = Fn (TAtom "close_stdout") /\ function_check_res ge (ho_cp o) = Some ok /\
          0 < ptr_addr (ho_cp o) < 2 ^ 64
}.

(** The exit objects are distinct from the registered errno object, and
    the thread cookie is non-null. These are layout facts, not assumptions
    about preservation by any program step. *)
Definition hello_os_layout (w0 : os_world) (o : hello_objs) : Prop :=
  0 < ptr_addr (ow_self w0) < 2 ^ 64 /\
  forall p, ow_errno w0 = Some p -> forall b,
    In b [xo_lock (ho_x o); xo_done (ho_x o); xo_called (ho_x o);
          xo_funcs (ho_x o); xo_init (ho_x o); ho_el o] -> b <> ptr_addr p.

(** Writes to the exit objects preserve errno's registered live object.
    This fact depends only on the memory and object layout, not on Iris. *)
Lemma hello_os_write w ob b e : hello_os_layout w ob ->
  In b [xo_lock (ho_x ob); xo_done (ho_x ob); xo_called (ho_x ob);
        xo_funcs (ho_x ob); xo_init (ho_x ob); ho_el ob] ->
  forall m wd h ps a n x c, b <= a -> a + n <= e ->
    (forall l, l ∈ ps.*1 -> piece_id l = b) -> os_wi w m wd h ->
    os_wi w (store_bytes m a n x) wd (overwrite ps h) /\
    os_wi w (store_bytes (store_aux m a c) a n x) wd (overwrite ps h).
Proof.
  intros [_ Hapart] Hb m wd h ps a n x c Ha He Hps [-> Hw].
  assert (Hkeep : forall eb, ow_errno w = Some (mkPtr eb (Obj eb)) ->
    errno_life_global h eb -> errno_life_global (overwrite ps h) eb).
  { intros eb Herr Hg. apply errno_life_overwrite; [|exact Hg].
    intros reg' Hin. exfalso. specialize (Hps (PLive eb) (list_elem_of_fmap_2 _ _ _ Hin)).
    cbn in Hps. apply (Hapart _ Herr b Hb). cbn. congruence. }
  assert (Hinv : forall m', m_regions m' = m_regions m -> os_inv m' w (overwrite ps h)).
  { intros m' E. eapply (os_inv_step m m' w h (overwrite ps h)); [rewrite E; auto | |exact Hw].
    intros eb reg Herr Hl Hkind Hg. rewrite E. split; [exact (proj1 Hl)|eapply Hkeep; eauto]. }
  split; split; try reflexivity; apply Hinv; reflexivity.
Qed.

(** The bridge interfaces share the concrete debt and resource definitions. *)
Module Type HelloDebtsT.
Include HelloGlibcDebts.
End HelloDebtsT.

(** The exit-resource interface hides registration proofs from later substitutions. *)
Module Type AtexitT.
(** The cells use the caller's memory logic. *)
Module ML := MemLogicOn R LG0.
Import LG0 LG0.L ML.
Section resources.
Context `{!gen_heapGS piece pval Σ}.
(** Each handler slot stores its flavor, function, argument and DSO handle. *)
Definition slot (b o v : Z) (x y z : ptr) : iProp Σ :=
  icell b o v ∗ pcell b (o + 8) x ∗ pcell b (o + 16) y ∗ pcell b (o + 24) z.
(** A registered slot has the cxa flavor and the selected callback. *)
Definition entry (b o : Z) (e : ptr * ptr * ptr) : iProp Σ := slot b o 4 e.1.1 e.1.2 e.2.
(** An unused slot may hold any flavor and pointer values. *)
Definition spare (b o : Z) : iProp Σ := ∃ v x y z, slot b o v x y z.
(** The initial block owns its registered entries and remaining spare slots. *)
Definition exit_block (b : Z) (reg : region) (ents : list (ptr * ptr * ptr)) : iProp Σ :=
  live b reg ∗ pcell b 0 null ∗ icell b 8 (Z.of_nat (List.length ents)) ∗
  ([∗ list] i ↦ e ∈ ents, entry b (16 + 32 * Z.of_nat i) e) ∗
  ([∗ list] i ∈ seqZ (Z.of_nat (List.length ents)) (32 - Z.of_nat (List.length ents)), spare b (16 + 32 * i)).
(** Registration owns the free lock, unfinished-exit flag, counter and initial block. *)
Definition exit_funcs_inv (x : exit_objs) (ents : list (ptr * ptr * ptr)) (c : Z) : iProp Σ :=
  ⌜(List.length ents <= 32)%nat /\ 0 <= c < 2 ^ 64⌝ ∗
  live (xo_lock x) (xo_lock_reg x) ∗ bytes (xo_lock x) 0 [0; 0; 0; 0] ∗
  live (xo_done x) (xo_done_reg x) ∗ ibyte (xo_done x) 0 0 ∗
  live (xo_called x) (xo_called_reg x) ∗ icell (xo_called x) 0 c ∗
  live (xo_funcs x) (xo_funcs_reg x) ∗ pcell (xo_funcs x) 0 (mkPtr (xo_init x) (Obj (xo_init x))) ∗
  exit_block (xo_init x) (xo_init_reg x) ents.
End resources.
(** Writes within an exit object leave the world interpretation unchanged. *)
Definition wi_ignores {world : Type} (wi : mem -> world -> gmap piece pval -> Prop) (b e : Z) : Prop :=
  forall m wd h ps a n x c, b <= a -> a + n <= e -> (forall l, l ∈ ps.*1 -> piece_id l = b) -> wi m wd h ->
    wi (store_bytes m a n x) wd (overwrite ps h) /\ wi (store_bytes (store_aux m a c) a n x) wd (overwrite ps h).
End AtexitT.

(** Signature checking verifies that these are exactly AtexitLogic.v's predicates. *)
Module HelloGlibcAtexitOn : AtexitT.
Include AtexitLogic.
End HelloGlibcAtexitOn.
