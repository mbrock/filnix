(** Hello's safety proof runs main_fn and uses the link record hello_link
    to identify the functions that its calls reach. This file shows that
    the complete image resolves those calls to the functions named by
    the record. The library proofs and the linked image refer to the same
    captured glibc definitions.

    The rest of the file checks that OS calls are left external and that
    malloc's parameter object has a symbol in the loaded image. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Heap.
From Glibc Require Import HelloBodies.

From Glibc Require Import Unit_libio_genops_os Unit_nptl_libcZ2dcleanup_os Unit_stdlib_cxa_thread_atexit_impl_os Unit_stdlib_exit_os Unit_string_memcmp_os.
From Glibc Require Import Unit_string_memrchr_os Unit_string_memset_os Unit_string_strncmp_os Unit_string_strrchr_os.
From Glibc Require Import SysWrappers StrlenLogic
  AllocLogic LeavesLogic AtexitLogic
  HelloGlibcLibsT.
From Glibc Require Import HelloImageEraseMem HelloImageModule HelloImageGettextLink HelloImageLoad.
Import ListNotations.

(** ## Hello's entry *)

(** A safety proof of Hello is only about the linked program if the
    program's main is the body that the proof runs. In the whole image,
    the name main finds exactly the body main_fn. *)
Lemma hello_image_main g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "main") = Some (Defined main_fn).
Proof. vm_compute. reflexivity. Qed.

(** If the check accepted any main, it would prove nothing. So we build
    a copy of the image whose main lacks its last block, and the check
    refuses that copy. *)
Local Definition changed_main : func :=
  mkFunc (fn_name main_fn) (fn_linkage main_fn) (fn_ret main_fn)
    (fn_params main_fn) (removelast (fn_blocks main_fn)).

Local Definition changed_image : module :=
  map (fun it => match it with
    | IFunc f => if name_eqb (fn_name f) (TAtom "main") then IFunc changed_main else it
    | _ => it end) hello_image_module.

Example hello_image_changed_main g fr :
  find_fn (mkGenv changed_image g fr) (TAtom "main") <> Some (Defined main_fn).
Proof. vm_compute. discriminate. Qed.

(** ## The function fields that hold *)

(** These are all the calls of hello_link, paired with the bodies that
    the record names. *)
Definition hello_image_fns : list (string * func) :=
  [("mbszero", mbszero_fn); ("memset", Unit_string_memset_os.fn___GI_memset); ("set_program_name", set_program_name_fn);
   ("strrchr", Unit_string_strrchr_os.fn___GI_strrchr); ("__GI_strlen", glibc_strlen); ("__GI___memrchr", Unit_string_memrchr_os.fn___GI___memrchr);
   ("memcmp", Unit_string_memcmp_os.fn___GI_memcmp); ("memeq", memeq_fn); ("strncmp", Unit_string_strncmp_os.fn___GI_strncmp); ("strlen", glibc_strlen);
   ("__errno_location", errno_location_fn); ("xmalloc", xmalloc_fn); ("malloc", malloc_fn);
   ("glibc_malloc#__libc_malloc2", malloc2_fn); ("free", free_fn); ("atexit", atexit_fn);
   ("__new_exitfn", new_exitfn_fn); ("__internal_atexit", internal_atexit_fn);
   ("__cxa_atexit", cxa_atexit_fn); ("exit", Unit_stdlib_exit_os.fn___GI_exit);
   ("__run_exit_handlers", Unit_stdlib_exit_os.fn___run_exit_handlers); ("__GI___call_tls_dtors", Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors);
   ("__GI___libc_cleanup_push_defer", Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer);
   ("__GI___libc_cleanup_pop_restore", Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore);
   ("__GI__IO_flush_all", Unit_libio_genops_os.fn___GI__IO_flush_all); ("_IO_cleanup", Unit_libio_genops_os.fn__IO_cleanup);
   ("close_stdout", close_stdout_fn); ("proper_name", proper_name_fn)]%string.

(** These names must stay outside the program, so that calls to them
    reach the OS contracts or the runtime's free. *)
Definition hello_image_absent : list string := ("zmemset" :: "zgc_free" :: sys_externals)%string.

(** The list holds exactly what hello_link asks: any environment with
    the record finds these bodies and leaves these names out. *)
Lemma hello_link_fns ge o : hello_link ge o ->
  Forall (fun nf => find_fn ge (TAtom (fst nf)) = Some (Defined (snd nf))) hello_image_fns /\
  Forall (fun s => find_fn ge (TAtom s) = None /\ lookup (TAtom s) (ge_globals ge) = None) hello_image_absent.
Proof.
  intros H. destruct (hk_exit_fns _ _ H) as (Hn & Hi & Hc). destruct (hk_frees _ _ H) as (_ & Hz).
  split.
  - unfold hello_image_fns.
    apply Forall_cons; [exact (hk_mbszero _ _ H)|]. apply Forall_cons; [exact (hk_memset _ _ H)|].
    apply Forall_cons; [exact (hk_name _ _ H)|]. apply Forall_cons; [exact (hk_strrchr _ _ H)|].
    apply Forall_cons; [exact (hk_gi_strlen _ _ H)|]. apply Forall_cons; [exact (hk_memrchr _ _ H)|].
    apply Forall_cons; [exact (hk_memcmp _ _ H)|]. apply Forall_cons; [exact (hk_memeq _ _ H)|].
    apply Forall_cons; [exact (hk_strncmp _ _ H)|]. apply Forall_cons; [exact (hk_strlen _ _ H)|].
    apply Forall_cons; [exact (hk_errno _ _ H)|]. apply Forall_cons; [exact (hk_xmalloc _ _ H)|].
    apply Forall_cons; [exact (hk_malloc _ _ H)|]. apply Forall_cons; [exact (hk_malloc2 _ _ H)|].
    apply Forall_cons; [exact (hk_free _ _ H)|]. apply Forall_cons; [exact (hk_atexit _ _ H)|].
    apply Forall_cons; [exact Hn|]. apply Forall_cons; [exact Hi|]. apply Forall_cons; [exact Hc|]. apply Forall_cons; [exact (hk_exit _ _ H)|].
    apply Forall_cons; [exact (hk_run_exit _ _ H)|]. apply Forall_cons; [exact (hk_dtors _ _ H)|].
    apply Forall_cons; [exact (hk_push _ _ H)|]. apply Forall_cons; [exact (hk_pop _ _ H)|].
    apply Forall_cons; [exact (hk_flush _ _ H)|]. apply Forall_cons; [exact (hk_cleanup _ _ H)|].
    apply Forall_cons; [exact (hk_close_stdout _ _ H)|].
    apply Forall_cons; [exact (hk_proper_name _ _ H)|]. apply Forall_nil.
  - apply Forall_cons; [exact (hk_zmemset _ _ H)|]. apply Forall_cons; [exact Hz|]. exact (hk_sys _ _ H).
Qed.

(** In the whole image, main and each listed call find the expected
    body, and no item carries a name that must stay outside. *)
Theorem hello_image_fn_link g m fr : initial_memory hello_image_module = Some (g, m) ->
  find_fn (mkGenv hello_image_module g fr) (TAtom "main") = Some (Defined main_fn) /\
  Forall (fun nf => find_fn (mkGenv hello_image_module g fr) (TAtom (fst nf)) = Some (Defined (snd nf))) hello_image_fns /\
  Forall (fun s => find_fn (mkGenv hello_image_module g fr) (TAtom s) = None /\ lookup (TAtom s) g = None)
    hello_image_absent.
Proof.
  intros Hi. split; [apply hello_image_main|]. split.
  - unfold hello_image_fns. repeat constructor; reflexivity.
  - assert (C : forallb (absent_ok hello_image_module) hello_image_absent = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in C. apply List.Forall_forall. intros s Hs. exact (absent_ok_sound _ _ _ fr _ Hi (C s Hs)).
Qed.

(** ## malloc's names

    malloc calls a private helper and reads a private parameter object.
    The genuine link names both with the prefix glibc_malloc, and so does
    the record now. The lemmas below show that the object has a symbol,
    and that the old unprefixed names are gone from the image. *)

(** The parameter object glibc_malloc#mp_ has its own symbol. *)
Lemma hello_image_mp g m : initial_memory hello_image_module = Some (g, m) ->
  lookup (TAtom "glibc_malloc#mp_") g = Some (mkPtr (img_a "glibc_malloc#mp_") (Obj (img_a "glibc_malloc#mp_"))).
Proof.
  intros Hi.
  assert (C : option_map (fun gm => lookup (TAtom "glibc_malloc#mp_") (fst gm)) (initial_memory hello_image_module) =
    Some (Some (mkPtr (img_a "glibc_malloc#mp_") (Obj (img_a "glibc_malloc#mp_"))))) by (rewrite HelloImageLoad.hello_loaded_eq; vm_compute; reflexivity).
  rewrite Hi in C. injection C as C. exact C.
Qed.

(** The old names malloc#__libc_malloc2 and malloc#mp_ are absent. *)
Lemma hello_image_old_malloc_absent g m fr : initial_memory hello_image_module = Some (g, m) ->
  find_fn (mkGenv hello_image_module g fr) (TAtom "malloc#__libc_malloc2") = None /\
  lookup (TAtom "malloc#mp_") g = None.
Proof.
  intros Hi. assert (C1 : absent_ok hello_image_module "malloc#__libc_malloc2" = true) by (vm_compute; reflexivity).
  assert (C2 : absent_ok hello_image_module "malloc#mp_" = true) by (vm_compute; reflexivity).
  split; [exact (proj1 (absent_ok_sound _ _ _ fr _ Hi C1)) | exact (proj2 (absent_ok_sound _ _ _ fr _ Hi C2))].
Qed.

(** The check tells bodies apart: a call of __new_exitfn does not find
    the body of __internal_atexit. *)
Example hello_image_swapped_refused g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "__new_exitfn") <> Some (Defined internal_atexit_fn).
Proof. vm_compute. discriminate. Qed.
