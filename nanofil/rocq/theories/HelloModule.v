(** GNU Hello as the model sees it: one checked module, linked from the
    objects nanofil compiles for `nanofil-hello-O`
    ([[campaign|Campaign]] 7, docs/logic.md).

    The fixture [hello_term] is the link rocq/link.pl makes of the real
    build's checked terms (nix/hello-fixture.nix regenerates it):
    each object's `local` items renamed `OBJECT#NAME`, the exported
    items shared, and only the items a run from `main` can name kept,
    32 functions and their data. This file reads it as a module
    ([hello_module]), checks that the [[validator]] accepts it
    ([hello_valid]), names the functions a proof is about
    ([hello_fn]) and lists the calls the module leaves to libc
    ([hello_externals]): the contracts the proof needs. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Transport Validate Semantics HelloCode.
Import ListNotations.
Open Scope string_scope.

(** ## The module *)

(** The linked module ([hello_term]). *)
Definition hello_module : module :=
  match decode_module hello_term with Some md => md | None => [] end.

(** The fixture decodes to [hello_module]. *)
Lemma hello_decodes : decode_module hello_term = Some hello_module.
Proof. vm_compute. reflexivity. Qed.

(** The [[validator]] accepts the linked module: every function of the
    [[core subset]], every name unique ([valid]). Each object was
    valid alone; this is the link. *)
Lemma hello_valid : valid hello_module = Some true.
Proof. vm_compute. reflexivity. Qed.

(** The function of the module named n, or an empty one. *)
Definition hello_fn (n : string) : func :=
  match find_direct (TAtom n) hello_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom "none") (TAtom "export") RVoid [] []
  end.

(** ## What it leaves to libc *)

(** The names the function f calls directly. *)
Definition called (f : func) : list name :=
  flat_map (fun b => flat_map (fun i => match i with
                                        | Call _ (Global g) _ => [g]
                                        | _ => []
                                        end) (b_insts b)) (fn_blocks f).

(** The names some function of md calls that md does not define, each
    once, in order of first call. *)
Definition externals (md : module) : list name :=
  fold_left (fun acc g => if existsb (name_eqb g) acc then acc else app acc [g])
    (flat_map (fun it => match it with
                         | IFunc f => filter (fun g => match find_direct g md with
                                                       | Some _ => false
                                                       | None => true
                                                       end) (called f)
                         | _ => []
                         end) md) [].

(** The 33 libc functions Hello calls: the contracts its proof needs.
    They are the plain entries, not the fortified ones (`printf`, not
    `__printf_chk`), and `zmemmove` is Fil-C's. The ones only quotearg
    calls (`iswprint`, `mbrtoc32`, `__ctype_b_loc`,
    `__ctype_get_mb_cur_max`, `mbsinit`, `zmemmove`, `realloc`) are
    reached only through close_stdout's diagnostic for a named file,
    which Hello never names. *)
Definition hello_externals : list string :=
  ["iswprint"; "__fpending"; "ferror"; "fclose"; "__errno_location"; "error"; "_exit";
   "mbrtoc32"; "mbrtowc"; "abort"; "memset"; "memcmp"; "strrchr"; "strncmp";
   "__ctype_get_mb_cur_max"; "strlen"; "__ctype_b_loc"; "mbsinit"; "zmemmove"; "free";
   "setlocale"; "memcpy"; "strcmp"; "memchr"; "fprintf"; "fputs"; "printf"; "malloc";
   "realloc"; "atexit"; "getopt_long"; "exit"; "wprintf"].

(** They are exactly the calls the module leaves undefined. *)
Lemma hello_externals_exact :
  map (fun g => match g with TAtom s => s | _ => "" end) (externals hello_module) = hello_externals.
Proof. vm_compute. reflexivity. Qed.
