(** The proof that GNU Hello never panics from `c: __libc_start_main`
    joins the startup body to main's proof. That join needs a few plain
    facts about Hello's linked image and the world that startup ends in.
    [StartWpHiAtexit](../startup/StartWpHiAtexit.v) proves the same
    facts for hi_atexit. This module proves them for Hello, by
    computation over the image's symbols wherever it can. *)

From Glibc Require Import GlibcTactics GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic.
From Glibc Require Import FileInv OsWorld OsRegistry OsStart StartCtors StartLogic StartCallMainSpec
  StartLibcStartMain StartLsmImage StartLsmHello ImageObjectPieces StartInitFirstSpec StartJoin
  HelloImageModule HelloImageLoad HelloImageEarly HelloImageLsm HelloImageCtors HelloImageFnLink
  HelloImageLayout HelloGlibcLibsT HelloStartCtors StartPtmallocInitSpec StartCtorChain.
From Glibc Require AtexitLogic SysWrappers.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## The world after startup *)

(** Main's contract needs three facts about the world it runs in. When
    startup ends, `c: errno` lives where the image puts
    `c: __libc_errno`, the thread object tb names the thread, and the
    descriptors are those that the process started with. *)
Lemma hello_final_world_facts w0 tb :
  lookup (TAtom "__libc_errno") img_globals = Some (ow_errno_cell w0) -> 0 < tb < 2 ^ 64 ->
  ow_errno (final_world w0 tb) = Some (mkPtr (pm_eb hello_pm_objs) (Obj (pm_eb hello_pm_objs))) /\
  ow_self (final_world w0 tb) = mkPtr tb (Obj tb) /\
  ow_fds (final_world w0 tb) = ow_fds w0.
Proof.
  intros He _. unfold final_world. cbn [start_world ow_errno ow_self ow_fds].
  split; [|split; reflexivity].
  assert (E : lookup (TAtom "__libc_errno") img_globals = Some (mkPtr (pm_eb hello_pm_objs) (Obj (pm_eb hello_pm_objs))))
    by (vm_compute; reflexivity).
  rewrite E in He. injection He as <-. reflexivity.
Qed.

(** ## The startup body's own globals *)

Section lsm.
Context `{!gen_heapGS piece pval Σ}.

(** The startup body writes five globals of its own. Each splits into
    its life and its bytes, and the two that hold pointers also give
    the slots for their capabilities. *)
Lemma hello_lsm_split :
  pts hello_lsm_ps ⊢
  live (lo_dx hello_lsm_objs) (lo_dxreg hello_lsm_objs) ∗ bytes (lo_dx hello_lsm_objs) 0 (repeat 0 8%nat) ∗
  auxes (lo_dx hello_lsm_objs) 0 (repeat CNone 8%nat) ∗
  live (lo_es hello_lsm_objs) (lo_esreg hello_lsm_objs) ∗ bytes (lo_es hello_lsm_objs) 0 [1; 0; 0; 0] ∗
  live (lo_dm hello_lsm_objs) (lo_dmreg hello_lsm_objs) ∗ bytes (lo_dm hello_lsm_objs) 0 (repeat 0 4%nat) ∗
  live (lo_re hello_lsm_objs) (lo_rereg hello_lsm_objs) ∗ bytes (lo_re hello_lsm_objs) 0 [0] ∗
  live (lo_se hello_lsm_objs) (lo_sereg hello_lsm_objs) ∗ bytes (lo_se hello_lsm_objs) 0 (repeat 0 8%nat) ∗
  auxes (lo_se hello_lsm_objs) 0 (repeat CNone 8%nat).
Proof using Type.
  rewrite /hello_lsm_ps (pts_app (obj_ps _ _)) (pts_app (obj_ps _ _)) (pts_app (obj_ps _ _)) (pts_app (obj_ps _ _))
    !obj_ps_own.
  iIntros "((? & ? & ?) & (? & ? & _) & (? & ? & _) & (? & ? & _) & (? & ? & ?))". iFrame.
Qed.

End lsm.

(** ## The call of main *)

(** Main is a function of the image, at the address that the loader
    gives its symbol. *)
Lemma hello_main_sym : lookup (TAtom "main") img_globals = Some (mkPtr (img_a "main") (Fn (TAtom "main"))).
Proof. vm_compute. reflexivity. Qed.

Section cm.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** Startup may call main in any world with any argument count and any
    two arrays. The call is checked before it happens, and it succeeds
    because the pointer names main, the environment pointer is one
    aligned global, and Hello's main takes argc and argv. *)
Lemma hello_cm_ok w fr argc avb envb avreg evreg :
  0 <= argc < 2 ^ 32 -> 0 <= avb < 2 ^ 64 -> 0 <= envb < 2 ^ 64 ->
  cm_ok (glibc_program := program_of w glibc_os_registry (mkGenv hello_image_module img_globals fr))
    (TAtom "main") [WInt argc; WPtr (mkPtr avb (Obj avb))]
    {| cm_en := if_en hello_init_first_objs; cm_enreg := if_enreg hello_init_first_objs;
       cm_avreg := avreg; cm_evreg := evreg |}
    (mkPtr (img_a "main") (Fn (TAtom "main"))) argc (mkPtr avb (Obj avb)) (mkPtr envb (Obj envb)).
Proof using Type.
  intros Ha Hv He. unfold cm_ok. cbn [ptr_cap ptr_addr cm_en cm_enreg]. split_and!.
  - reflexivity.
  - change (function_check_res (mkGenv hello_image_module img_globals fr) (mkPtr (img_a "main") (Fn (TAtom "main")))
      = Some ok).
    unfold function_check_res. cbn [ptr_cap ptr_addr ge_globals]. rewrite hello_main_sym. vm_compute. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - change (lookup (TAtom "__environ") img_globals =
      Some (mkPtr (if_en hello_init_first_objs) (Obj (if_en hello_init_first_objs)))).
    vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. congruence.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros gf Hf. change (find_fn (mkGenv hello_image_module img_globals fr) (TAtom "main") = Some (Defined gf)) in Hf.
    rewrite hello_image_main in Hf. injection Hf as <-. split; [vm_compute; reflexivity|].
    intros d a b c. vm_compute. reflexivity.
Qed.

End cm.

(** ## The constructor table *)

(** Every pointer in the constructor table names its constructor and
    passes the function check, in every order of the table. *)
Lemma hello_ctor_ptrs_ok fr order : Permutation order (ctor_names hello_image_module) ->
  Forall2 (fun g p => ptr_cap p = Fn g /\
    function_check_res (mkGenv hello_image_module img_globals fr) p = Some ok /\ 0 <= ptr_addr p < 2 ^ 64)
    order (ctor_ptrs img_globals order).
Proof.
  intros Hp. assert (Hin : forall g, In g order -> In g [ctor_stdfiles; ctor_vtables; ctor_init_first]).
  { intros g H. apply (Permutation_in _ (perm_trans Hp hello_ctor_names) H). }
  clear Hp. unfold ctor_ptrs. induction order as [|g0 rest IH]; cbn [List.map]; constructor.
  - destruct (Hin g0 (or_introl eq_refl)) as [<-|[<-|[<-|[]]]];
      split_and!; vm_compute; first [reflexivity | intros H; discriminate H].
  - apply IH. intros g H. apply Hin. right. exact H.
Qed.

(** ## The whole link

    Main calls into many library functions, and each of their proofs
    assumes something about the program they are linked into: that a
    called name finds the right body, that a system call stays outside
    the program, and that a global lies at its symbol. One record,
    [hello_link], gathers those assumptions. This section shows that
    Hello's linked image meets all of them. *)

(** Hello's linked image satisfies the whole link record, whatever
    free the runtime supplies, as long as that free releases heap
    objects. *)
Lemma hello_link_all fr : frees_heap fr -> hello_link (mkGenv hello_image_module img_globals fr) hello_image_objs.
Proof.
  intros Hf. destruct hello_image_memory as (g & m & Hi).
  destruct (hello_loaded_tables g m Hi) as [Eg _]. subst g.
  destruct (hello_image_fn_link _ _ fr Hi) as (_ & Hfns & Habs).
  pose proof (hello_image_link_objects _ _ fr Hi) as O. cbv zeta in O.
  unfold hello_image_fns in Hfns. unfold hello_image_absent in Habs.
  do 28 (let a := fresh "F" in pose proof (List.Forall_inv Hfns) as a; apply List.Forall_inv_tail in Hfns;
    cbn [fst snd] in a).
  do 2 (let a := fresh "A" in pose proof (List.Forall_inv Habs) as a; apply List.Forall_inv_tail in Habs).
  pose proof Habs as Hsys. unfold SysWrappers.sys_externals in Hsys.
  do 8 (let a := fresh "S" in pose proof (List.Forall_inv Hsys) as a; apply List.Forall_inv_tail in Hsys).
  destruct O as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16).
  constructor; try assumption.
  - split; [exact Hf | assumption].
  - unfold AtexitLogic.exit_fns. split_and!; assumption.
Qed.

(** When startup ends, the thread has an address and none of the exit
    objects is the errno object. *)
Lemma hello_os_layout_final w0 tb :
  lookup (TAtom "__libc_errno") img_globals = Some (ow_errno_cell w0) -> 0 < tb < 2 ^ 64 ->
  hello_os_layout (final_world w0 tb) hello_image_objs.
Proof.
  intros He Htb. destruct (hello_final_world_facts w0 tb He Htb) as (Herr & Hself & _).
  split; [rewrite Hself; exact Htb|].
  intros p Hp b Hb. rewrite Herr in Hp. injection Hp as <-.
  revert b Hb. apply List.Forall_forall.
  repeat constructor; apply Z.eqb_neq; vm_compute; reflexivity.
Qed.
