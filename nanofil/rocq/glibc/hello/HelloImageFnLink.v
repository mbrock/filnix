(** Hello's safety proof runs main_fn, the body of main in Hello's own
    module, and its library bridges assume the record hello_link. That
    record says which body each call finds and which names are left to
    the OS. A proof about the whole linked program needs those facts for
    the whole decoded image, because the linker could have placed a
    different main or a different malloc there.

    This file checks main and every function field of hello_link against
    the whole decoded image, with the bodies that the record names. The
    stdlib and hi_atexit fixtures, from which the malloc and atexit
    bodies come, name the private objects of malloc and cxa_atexit as
    the genuine link does, glibc_malloc#... and glibc_cxa_atexit#..., so
    those bodies match the image too.

    The file checks names and bodies only. It does not say that Hello
    starts from this image. Apart from the symbol of malloc's parameter
    object, it proves no object or layout field. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Heap HelloLeaf HelloName.
From Nanofil Require HelloClose HelloMain.
From Glibc Require Import SysWrappers StrlenLogic StrncmpCode MemrchrCode MemcmpCode MemFwdCode StrchrCode
  AllocLogic LeavesLogic AtexitLogic ExitRunCode LibioGenCode SysCode LibioFlushCode LibioCleanupCode
  HelloGlibcLibsT.
From Glibc Require Import HelloImageEraseMem HelloImageModule HelloImageGettextLink HelloImageLoad.
Import ListNotations.

(** ## Hello's entry *)

(** A safety proof of Hello is only about the linked program if the
    program's main is the body that the proof runs. In the whole image,
    the name main finds exactly the body main_fn. *)
Lemma hello_image_main g fr :
  find_fn (mkGenv hello_image_module g fr) (TAtom "main") = Some (Defined HelloMain.main_fn).
Proof. vm_compute. reflexivity. Qed.

(** If the check accepted any main, it would prove nothing. So we build
    a copy of the image whose main lacks its last block, and the check
    refuses that copy. *)
Local Definition changed_main : func :=
  mkFunc (fn_name HelloMain.main_fn) (fn_linkage HelloMain.main_fn) (fn_ret HelloMain.main_fn)
    (fn_params HelloMain.main_fn) (removelast (fn_blocks HelloMain.main_fn)).

Local Definition changed_image : module :=
  map (fun it => match it with
    | IFunc f => if name_eqb (fn_name f) (TAtom "main") then IFunc changed_main else it
    | _ => it end) hello_image_module.

Example hello_image_changed_main g fr :
  find_fn (mkGenv changed_image g fr) (TAtom "main") <> Some (Defined HelloMain.main_fn).
Proof. vm_compute. discriminate. Qed.

(** ## The function fields that hold *)

(** These are all the calls of hello_link, paired with the bodies that
    the record names. *)
Definition hello_image_fns : list (string * func) :=
  [("mbszero", mbszero_fn); ("memset", glibc_memset); ("set_program_name", set_program_name_fn);
   ("strrchr", glibc_strrchr); ("__GI_strlen", glibc_strlen); ("__GI___memrchr", glibc_memrchr);
   ("memcmp", glibc_memcmp); ("memeq", memeq_fn); ("strncmp", glibc_strncmp); ("strlen", glibc_strlen);
   ("__errno_location", errno_location_fn); ("xmalloc", xmalloc_fn); ("malloc", malloc_fn);
   ("glibc_malloc#__libc_malloc2", malloc2_fn); ("free", free_fn); ("atexit", atexit_fn);
   ("__new_exitfn", new_exitfn_fn); ("__internal_atexit", internal_atexit_fn);
   ("__cxa_atexit", cxa_atexit_fn); ("exit", glibc_exit);
   ("__run_exit_handlers", glibc___run_exit_handlers); ("__GI___call_tls_dtors", glibc___call_tls_dtors);
   ("__GI___libc_cleanup_push_defer", glibc___libc_cleanup_push_defer);
   ("__GI___libc_cleanup_pop_restore", glibc___libc_cleanup_pop_restore);
   ("__GI__IO_flush_all", glibc__IO_flush_all); ("_IO_cleanup", glibc__IO_cleanup);
   ("close_stdout", HelloClose.close_stdout_fn)]%string.

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
    apply Forall_cons; [exact (hk_close_stdout _ _ H)|]. apply Forall_nil.
  - apply Forall_cons; [exact (hk_zmemset _ _ H)|]. apply Forall_cons; [exact Hz|]. exact (hk_sys _ _ H).
Qed.

(** A name that no item of a module carries finds no function and has
    no symbol, so a check of the decoded items settles both. *)
Definition absent_ok (md : module) (s : string) : bool :=
  match find_direct (TAtom s) md, find_alias (TAtom s) md with
  | None, None => negb (existsb (name_eqb (TAtom s)) (map item_key md))
  | _, _ => false
  end.

Lemma absent_ok_sound md g m fr s : initial_memory md = Some (g, m) -> absent_ok md s = true ->
  find_fn (mkGenv md g fr) (TAtom s) = None /\ lookup (TAtom s) g = None.
Proof.
  intros Hi. unfold absent_ok. destruct (find_direct (TAtom s) md) eqn:Hd; [discriminate|].
  destruct (find_alias (TAtom s) md) eqn:Ha; [discriminate|]. intros Hk. split.
  - unfold find_fn. cbn [ge_module]. rewrite Hd, Ha. reflexivity.
  - apply (loaded_absent _ _ m _ Hi). intros Hin.
    assert (E : existsb (name_eqb (TAtom s)) (map item_key md) = true).
    { apply existsb_exists. exists (TAtom s). split; [exact Hin | apply term_eqb_refl]. }
    rewrite E in Hk. discriminate.
Qed.

(** In the whole image, main and each listed call find the expected
    body, and no item carries a name that must stay outside. *)
Theorem hello_image_fn_link g m fr : initial_memory hello_image_module = Some (g, m) ->
  find_fn (mkGenv hello_image_module g fr) (TAtom "main") = Some (Defined HelloMain.main_fn) /\
  Forall (fun nf => find_fn (mkGenv hello_image_module g fr) (TAtom (fst nf)) = Some (Defined (snd nf))) hello_image_fns /\
  Forall (fun s => find_fn (mkGenv hello_image_module g fr) (TAtom s) = None /\ lookup (TAtom s) g = None)
    hello_image_absent.
Proof.
  intros Hi. split; [apply hello_image_main|]. split.
  - unfold hello_image_fns. repeat (apply Forall_cons; [cbn [fst snd]; vm_compute; reflexivity|]). apply Forall_nil.
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
