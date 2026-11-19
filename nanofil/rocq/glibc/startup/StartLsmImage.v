(** The proof of `c: __libc_start_main` in
    [StartLibcStartMain](StartLibcStartMain.v) serves every program that
    links glibc's startup code, so it takes the facts it needs about the
    linked image as premises. Most of them are pure: a global has a
    symbol, its address is aligned, and its region is large enough. Some
    say that the image leaves a function to the runtime or has no symbol
    for it. This module collects those premises in one statement,
    [lsm_image_ok], for a linked image. The module
    [StartLsmHello](../hello/StartLsmHello.v) proves it for Hello.

    The facts that a caller owns, such as the lifetime of a global, are
    not here. The startup proof takes them from the pieces of the
    initial memory. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces.
From Glibc Require Import OsStartCalls StartLogic.
Import ListNotations.
Open Scope Z_scope.

(** ## The statement *)

(** The startup body reads these globals and calls these two handlers.
    The record gives each global's address and the region that the
    loader registers for it, and it gives the pointers of the handlers
    and of the CPU feature structure. *)
Record lsm_objs := {
  lo_en : Z; lo_enreg : region;   (* __environ *)
  lo_dx : Z; lo_dxreg : region;   (* _dl_auxv *)
  lo_es : Z; lo_esreg : region;   (* __libc_enable_secure *)
  lo_dm : Z; lo_dmreg : region;   (* _dl_debug_mask *)
  lo_re : Z; lo_rereg : region;   (* __nptl_initial_report_events *)
  lo_se : Z; lo_sereg : region;   (* __libc_stack_end *)
  lo_cfp : ptr;                   (* _dl_x86_cpu_features *)
  lo_hp : ptr;                    (* the errno handler *)
  lo_dp : ptr; lo_dn : name       (* the dlerror handler and the function it names *)
}.

(** These are the pure premises of [wp_libc_start_main] that depend only
    on the image, in the order in which the lemma takes them. The image
    leaves the three startup calls to the runtime and does not link
    `c: __pthread_initialize_minimal`. Each global that the body reads
    has a symbol with a capability of its own object, is aligned, and
    fits in its region. Both handlers have symbols that carry the right
    to call a function. *)
Definition lsm_image_ok (ge : genv) (o : lsm_objs) : Prop :=
  os_ext ge "zmake_setjmp_save_sigmask" /\ os_ext ge "zregister_sys_errno_handler" /\
  os_ext ge "zregister_sys_dlerror_handler" /\
  lookup (TAtom "__pthread_initialize_minimal") (ge_globals ge) = None /\
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr (lo_en o) (Obj (lo_en o))) /\
  lo_en o mod 8 = 0 /\ lo_en o + 8 <= r_end (lo_enreg o) /\
  lookup (TAtom "_dl_auxv") (ge_globals ge) = Some (mkPtr (lo_dx o) (Obj (lo_dx o))) /\
  lo_dx o mod 8 = 0 /\ lo_dx o + 8 <= r_end (lo_dxreg o) /\
  lookup (TAtom "__libc_enable_secure") (ge_globals ge) = Some (mkPtr (lo_es o) (Obj (lo_es o))) /\
  lo_es o + 4 <= r_end (lo_esreg o) /\
  lookup (TAtom "_dl_debug_mask") (ge_globals ge) = Some (mkPtr (lo_dm o) (Obj (lo_dm o))) /\
  lo_dm o mod 4 = 0 /\ lo_dm o + 4 <= r_end (lo_dmreg o) /\
  lookup (TAtom "_dl_x86_cpu_features") (ge_globals ge) = Some (lo_cfp o) /\
  lookup (TAtom "__nptl_initial_report_events") (ge_globals ge) = Some (mkPtr (lo_re o) (Obj (lo_re o))) /\
  lookup (TAtom "__libc_stack_end") (ge_globals ge) = Some (mkPtr (lo_se o) (Obj (lo_se o))) /\
  lo_re o + 1 <= r_end (lo_rereg o) /\ lo_se o mod 8 = 0 /\ lo_se o + 8 <= r_end (lo_sereg o) /\
  lookup errno_handler_name (ge_globals ge) = Some (lo_hp o) /\ ptr_cap (lo_hp o) = Fn errno_handler_name /\
  lookup (TAtom "glibc_libc_start#dlerror_handler") (ge_globals ge) = Some (lo_dp o) /\
  ptr_cap (lo_dp o) = Fn (lo_dn o).

(** The proofs for each image read the symbols in this order. *)
Definition lsm_names : list name :=
  [TAtom "__environ"; TAtom "_dl_auxv"; TAtom "__libc_enable_secure"; TAtom "_dl_debug_mask";
   TAtom "__nptl_initial_report_events"; TAtom "__libc_stack_end"; TAtom "_dl_x86_cpu_features";
   errno_handler_name; TAtom "glibc_libc_start#dlerror_handler"].

(** This function builds the record from an image's symbols g and the
    regions rs that its loader registers. A missing symbol gives the
    null pointer, and the checks of [lsm_image_ok] then fail. *)
Definition lsm_objs_in (g : list (name * ptr)) (rs : list region) : lsm_objs :=
  let p n := match lookup n g with Some p => p | None => null end in
  let b n := ptr_addr (p (TAtom n)) in
  let r n := match object_region (b n) rs with Some r => r | None => mkRegion 0 0 GlobalData Live end in
  {| lo_en := b "__environ"; lo_enreg := r "__environ";
     lo_dx := b "_dl_auxv"; lo_dxreg := r "_dl_auxv";
     lo_es := b "__libc_enable_secure"; lo_esreg := r "__libc_enable_secure";
     lo_dm := b "_dl_debug_mask"; lo_dmreg := r "_dl_debug_mask";
     lo_re := b "__nptl_initial_report_events"; lo_rereg := r "__nptl_initial_report_events";
     lo_se := b "__libc_stack_end"; lo_sereg := r "__libc_stack_end";
     lo_cfp := p (TAtom "_dl_x86_cpu_features");
     lo_hp := p errno_handler_name;
     lo_dp := p (TAtom "glibc_libc_start#dlerror_handler");
     lo_dn := match ptr_cap (p (TAtom "glibc_libc_start#dlerror_handler")) with Fn n => n | _ => TAtom "" end |}.
