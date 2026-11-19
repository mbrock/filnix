(** The checker of [AbsRun](../../theories/exec/AbsRun.v) verifies one
    function against one specification. A proof about
    `c: init_cpu_features` runs it on every function of the call tree,
    bottom up, and gives each caller the specifications of its callees.
    This module holds what those runs share. It reads the functions and
    the initial data from the captured translation units, numbers the
    global objects that the call tree touches, and names the shapes of
    memory that the specifications start from.

    A run has two halves. The first half infers a specification and
    the loop invariants of a function, and nothing depends on it being
    right. The second half checks the result with `verify`, and the
    theorem of [AbsSound](../../theories/exec/AbsSound.v) turns a
    passed check into a triple of the program logic. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics.
From Nanofil Require Import AbsRun AbsInfer.
From Glibc Require Import CpuRules Unit_csu_libcZ2dstart_os Unit_elf_dlZ2dtunables_os.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** * The linked image *)

(** These are the captured function bodies that the CPU initialization proof checks.
    A linked program supplies evidence that each name resolves to the same body. *)
Definition cpu_bodies : list func :=
  [fn_glibc_libc_start'23init_cpu_features;
   fn_glibc_libc_start'23get_isa_level;
   fn_glibc_libc_start'23get_common_indices;
   fn_glibc_libc_start'23update_active;
   fn_glibc_libc_start'23dl_init_cacheinfo;
   fn_glibc_libc_start'23get_common_cache_info;
   fn_glibc_libc_start'23handle_intel;
   fn_glibc_libc_start'23handle_amd;
   fn_glibc_libc_start'23handle_zhaoxin;
   fn_glibc_libc_start'23handle_hygon;
   fn_glibc_libc_start'23intel_check_word;
   fn_glibc_libc_start'23intel_02_known_compare;
   fn___tunable_get_val;
   fn___tunable_set_val;
   fn___tunable_is_initialized;
   fn_glibc_dl_tunables'23do_tunable_update_val].

Definition nofn : func := mkFunc (TAtom "") (TAtom "") RVoid [] [].

Definition fn (n : string) : func :=
  match find (fun f => name_eqb (fn_name f) (TAtom n)) cpu_bodies with
  | Some f => f | None => nofn end.

(** A data item of the image describes its initial bytes exactly,
    except a symbol, whose eight bytes hold an address that the linker
    chooses. *)
Definition item_bytes (it : data_item) : list abyte :=
  match it with
  | Item w z => map (fun i => BK (byte_of z (Z.of_nat i))) (seq 0 (Z.to_nat (width_bytes w)))
  | Str cs => map BK cs
  | Sym _ _ => repeat BR 8
  | Zero n => repeat (BK 0) (Z.to_nat n)
  | ItemOther _ => []
  end.

Definition item_aux (it : data_item) : list aaux :=
  match it with
  | Sym _ _ => XAny :: repeat XNone 7
  | _ => repeat XNone (Z.to_nat (item_size it))
  end.

(** The function [gobj_in] gives the initial contents of a global
    object of a module. *)
Definition gobj_in (md : module) (n : string) : option aobj :=
  match find (fun it => match it with IData m _ _ _ => name_eqb m (TAtom n) | _ => false end) md with
  | Some (IData _ lk al its) =>
      Some (mkObj (match lk with LRo _ => true | _ => false end) al (flat_map item_bytes its) (flat_map item_aux its))
  | _ => None
  end.

(** * The functions *)

(** A call of `c: init_cpu_features` runs these sixteen functions.
    The list names the function itself, the helpers that it calls,
    and the four tunable functions. *)
Definition cpu_fns : list string :=
  ["glibc_libc_start#init_cpu_features"; "glibc_libc_start#get_isa_level"; "glibc_libc_start#get_common_indices";
   "glibc_libc_start#update_active"; "glibc_libc_start#dl_init_cacheinfo"; "glibc_libc_start#get_common_cache_info";
   "glibc_libc_start#handle_intel"; "glibc_libc_start#handle_amd"; "glibc_libc_start#handle_zhaoxin";
   "glibc_libc_start#handle_hygon"; "glibc_libc_start#intel_check_word"; "glibc_libc_start#intel_02_known_compare";
   "__tunable_get_val"; "__tunable_set_val"; "__tunable_is_initialized"; "glibc_dl_tunables#do_tunable_update_val"].

(** The function f is the body of the function named n in that list. *)
Definition cpu_fn (n : string) (f : func) : Prop := existsb (String.eqb n) cpu_fns = true /\ fn n = f.

(** * The global objects *)

(** The call tree of `c: init_cpu_features` reads and writes these
    eighteen global objects. Every state of every run numbers them
    first, in this order. *)
Definition G : list string :=
  ["_dl_x86_cpu_features"; "glibc_dl_tunables#tunable_list"; "glibc_libc_start#intel_02_known";
   "_dl_hwcap"; "_dl_hwcap2"; "_dl_platform"; "_dl_minsigstacksize"; "_dl_x86_features_tlsdesc_state_size";
   "__x86_data_cache_size_half"; "__x86_data_cache_size"; "__x86_shared_cache_size_half"; "__x86_shared_cache_size";
   "__x86_shared_non_temporal_threshold"; "__x86_memset_non_temporal_threshold"; "__x86_rep_movsb_threshold";
   "__x86_rep_stosb_threshold"; "__x86_rep_movsb_stop_threshold"; "__x86_string_control"].
Definition gobjs : list name := map TAtom G.
Definition ng : nat := length G.

(** One function of the call tree is called through a pointer. It is
    the comparison that the binary search of the Intel descriptor
    table uses. *)
Definition fnames : list (name * (list class * ret_type)) :=
  [(TAtom "glibc_libc_start#intel_02_known_compare", ([P; P], RClass W))].

(** * Shapes of memory *)

(** A weak object holds any bytes and any capabilities. A local holds
    any bytes and no capability. *)
Definition weak (al : Z) (n : nat) : aobj := mkObj false al (repeat BR n) (repeat XAny n).
Definition loc (n : nat) : aobj := mkObj false 16 (repeat BR n) (repeat XNone n).
Definition with_bytes (k : Z) (bs : list abyte) (ob : aobj) : aobj :=
  mkObj (o_ro ob) (o_align ob) (splice k bs (o_bytes ob)) (o_aux ob).

(** A specification lists the contents of the global objects it needs
    by name, and then the contents of the objects its pointer
    parameters name. *)
Definition gmem (l : list (string * aobj)) : list (option aobj) :=
  map (fun g => option_map snd (find (fun p => String.eqb (fst p) g) l)) G.

Definition spec (args : list cval) (globals : list (string * aobj)) (params : list (option aobj)) : fspec :=
  mkSpec args (gmem globals ++ params ++ repeat None (length args - length params)) false [] false None.
Definition par (j : nat) : cval := CP (ng + j) 0 0.
Definition glo (g : string) : cval :=
  match index_of (TAtom g) gobjs with Some o => CP o 0 0 | None => CA end.

Definition get {A} (d : A) (o : option A) : A := match o with Some x => x | None => d end.
Definition somes {A} (l : list (option A)) : list A :=
  flat_map (fun o => match o with Some s => [s] | None => [] end) l.

(** The feature structure may hold any bytes when the function starts.
    One bit of it matters to the checker. Bit 27 of the saved leaf 1
    ECX word says that the kernel enabled XSAVE, so that byte carries
    the guard. *)
Definition cpu : string := "_dl_x86_cpu_features".
Definition cpu0 : aobj := with_bytes 31 [BGuard 3] (weak 8 528).

(** The Intel paths run after the vendor field has been set to 1. *)
Definition cpu1 : aobj := with_bytes 0 [BK 1; BK 0; BK 0; BK 0] cpu0.

(** The Intel descriptor table is read-only data, so the checker knows
    its bytes. *)
Definition kn : string := "glibc_libc_start#intel_02_known".
Definition known : aobj := get (loc 0) (gobj_in [item_glibc_libc_start'23intel_02_known] kn).

(** * Running the checker *)

(** A table gives the specifications that callers may use, by callee. *)
Definition table := list (string * list fspec).
Definition specs_of (t : table) : name -> list fspec :=
  fun g => match find (fun p => name_eqb (TAtom (fst p)) g) t with Some p => snd p | None => [] end.

(** The hook assumes that the leaf 4 list ends. *)
Definition hook : hook := cpu_builtin true.

(** The function [plan_of] infers a completed specification and the
    invariants at the cut points of a function. It answers nothing
    when the inference meets an instruction it cannot justify. *)
Definition plan_of (t : table) (f : func) (nocut split : list name) (sp : fspec)
    : option (fspec * list (name * cstate)) :=
  let a := plan hook gobjs fnames (specs_of t) f nocut split 3000 20000 3 sp in
  match a_fail a with
  | [] => Some (complete sp a, map (fun e => (e_lab e, e_inv e)) (a_tab a))
  | _ => None
  end.

(** The function [verified] checks an inferred specification with its
    invariants. Only this half is trusted by the proofs. *)
Definition verified (t : table) (f : func) (nocut : list name) (p : fspec * list (name * cstate)) : bool :=
  verify hook gobjs fnames (specs_of t) f (filter (fun l => negb (mem_name l nocut)) (default_cuts f)) 3000
    (fst p) (snd p).
