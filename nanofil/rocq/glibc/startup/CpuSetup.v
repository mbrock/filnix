(** The checker of [AbsRun](../../theories/exec/AbsRun.v) verifies one
    function against one specification. A proof about
    `c: init_cpu_features` runs it on every function of the call tree,
    bottom up, and gives each caller the specifications of its callees.
    This module holds what those runs share. It reads the functions and
    the initial data out of the linked hi_atexit image, numbers the
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
From Glibc Require Import HiAtexitModule CpuRules.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** * The linked image *)

(** The function [fn] finds a function of the linked image by name. A
    name that the image lacks gives an empty function, which no check
    passes. *)
Definition nofn : func := mkFunc (TAtom "") (TAtom "") RVoid [] [].

Definition fn (n : string) : func :=
  match find (fun it => match it with IFunc f => name_eqb (fn_name f) (TAtom n) | _ => false end) hi_module with
  | Some (IFunc f) => f
  | _ => nofn
  end.

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

(** The function [gobj] gives the initial contents of a global object
    of the image. *)
Definition gobj (n : string) : option aobj :=
  match find (fun it => match it with IData m _ _ _ => name_eqb m (TAtom n) | _ => false end) hi_module with
  | Some (IData _ lk al its) =>
      Some (mkObj (match lk with LRo _ => true | _ => false end) al (flat_map item_bytes its) (flat_map item_aux its))
  | _ => None
  end.

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
Definition real (g : string) : aobj := get (loc 0) (gobj g).
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
Definition known : aobj := real kn.

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
