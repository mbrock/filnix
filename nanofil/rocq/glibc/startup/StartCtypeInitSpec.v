(** The character class macros of `c: <ctype.h>` read three per-thread
    pointers into the current locale's tables. Early initialization
    sets them through `c: __ctype_init`, which follows the thread's
    locale pointer to the locale's character type data and stores
    pointers into its class, upper-case and lower-case tables. A caller
    needs only which cells the call reads and what it stores, so this
    module states that contract. [StartCtypeInit](StartCtypeInit.v)
    proves it.

    ## What the call reads and writes

    The thread's locale pointer and the locale object are writable
    globals, which the call reads and gives back. The character type
    data and its three tables are read-only, so the contract needs only
    persistent shares of them. The call writes the three per-thread
    table pointers. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** This record holds the base and region of each object that the call
    touches. *)
Record ct_objs := {
  ct_lt : Z; ct_ltreg : region;   (* __libc_tsd_LOCALE *)
  ct_gl : Z; ct_glreg : region;   (* _nl_global_locale *)
  ct_cc : Z; ct_ccreg : region;   (* _nl_C_LC_CTYPE *)
  ct_xc : Z; ct_xcreg : region;   (* the class table *)
  ct_xu : Z; ct_xureg : region;   (* the upper-case table *)
  ct_xl : Z; ct_xlreg : region;   (* the lower-case table *)
  ct_cb : Z; ct_cbreg : region;   (* __libc_tsd_CTYPE_B *)
  ct_cu : Z; ct_cureg : region;   (* __libc_tsd_CTYPE_TOUPPER *)
  ct_cl : Z; ct_clreg : region    (* __libc_tsd_CTYPE_TOLOWER *)
}.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The program names the five globals, and every cell that the call
    reads or writes is an aligned word inside its object. *)
Definition ct_ok (o : ct_objs) : Prop :=
  lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (mkPtr (ct_lt o) (Obj (ct_lt o))) /\
  lookup (TAtom "__libc_tsd_CTYPE_B") (ge_globals ge) = Some (mkPtr (ct_cb o) (Obj (ct_cb o))) /\
  lookup (TAtom "__libc_tsd_CTYPE_TOUPPER") (ge_globals ge) = Some (mkPtr (ct_cu o) (Obj (ct_cu o))) /\
  lookup (TAtom "__libc_tsd_CTYPE_TOLOWER") (ge_globals ge) = Some (mkPtr (ct_cl o) (Obj (ct_cl o))) /\
  ct_lt o mod 8 = 0 /\ ct_lt o + 8 <= r_end (ct_ltreg o) /\
  ct_gl o mod 8 = 0 /\ ct_gl o + 8 <= r_end (ct_glreg o) /\
  ct_cc o mod 8 = 0 /\ ct_cc o + 88 <= r_end (ct_ccreg o) /\
  ct_cb o mod 8 = 0 /\ ct_cb o + 8 <= r_end (ct_cbreg o) /\
  ct_cu o mod 8 = 0 /\ ct_cu o + 8 <= r_end (ct_cureg o) /\
  ct_cl o mod 8 = 0 /\ ct_cl o + 8 <= r_end (ct_clreg o) /\
  0 <= ct_xc o + 256 < 2 ^ 64 /\ 0 <= ct_xu o + 512 < 2 ^ 64 /\ 0 <= ct_xl o + 512 < 2 ^ 64 /\
  0 <= ct_xc o /\ 0 <= ct_xu o /\ 0 <= ct_xl o /\ 0 <= ct_gl o < 2 ^ 64 /\ 0 <= ct_cc o < 2 ^ 64.

(** This assertion holds persistent shares of the read-only character
    type data and its tables: the data's three table pointers at
    offsets 56, 64 and 80, and the tables' lives. *)
Definition ct_ro (o : ct_objs) : iProp Σ :=
  liveq DfracDiscarded (ct_cc o) (ct_ccreg o) ∗
  pcellq DfracDiscarded (ct_cc o) 56 (mkPtr (ct_xc o) (Ro (ct_xc o))) ∗
  pcellq DfracDiscarded (ct_cc o) 64 (mkPtr (ct_xu o) (Ro (ct_xu o))) ∗
  pcellq DfracDiscarded (ct_cc o) 80 (mkPtr (ct_xl o) (Ro (ct_xl o))) ∗
  liveq DfracDiscarded (ct_xc o) (ct_xcreg o) ∗ liveq DfracDiscarded (ct_xu o) (ct_xureg o) ∗
  liveq DfracDiscarded (ct_xl o) (ct_xlreg o).

(** This assertion owns the writable objects that the call reads: the
    thread's locale pointer, which names the global locale, and the
    global locale's first slot, which names the character type data. *)
Definition ct_locale (o : ct_objs) : iProp Σ :=
  live (ct_lt o) (ct_ltreg o) ∗ pcell (ct_lt o) 0 (mkPtr (ct_gl o) (Obj (ct_gl o))) ∗
  live (ct_gl o) (ct_glreg o) ∗ pcell (ct_gl o) 0 (mkPtr (ct_cc o) (Ro (ct_cc o))).

(** This assertion owns the lives of the three per-thread table
    pointers. *)
Definition ct_lives (o : ct_objs) : iProp Σ :=
  live (ct_cb o) (ct_cbreg o) ∗ live (ct_cu o) (ct_cureg o) ∗ live (ct_cl o) (ct_clreg o).

(** A call of `c: __ctype_init()` points the class pointer 256 bytes
    into the class table, and the two case pointers 512 bytes into
    their tables, so that the tables can be indexed from -128. *)
Definition ctype_init_spec : fspec Σ :=
  FSpec (ct_objs * ptr * ptr * ptr) (fun _ => [])
    (fun '(o, x, y, z) =>
       ⌜ct_ok o⌝ ∗ ct_ro o ∗ ct_locale o ∗ ct_lives o ∗
       pcell (ct_cb o) 0 x ∗ pcell (ct_cu o) 0 y ∗ pcell (ct_cl o) 0 z)%I
    (fun '(o, x, y, z) r =>
       ⌜r = RetVoid⌝ ∗ ct_locale o ∗ ct_lives o ∗
       pcell (ct_cb o) 0 (mkPtr (ct_xc o + 256) (Ro (ct_xc o))) ∗
       pcell (ct_cu o) 0 (mkPtr (ct_xu o + 512) (Ro (ct_xu o))) ∗
       pcell (ct_cl o) 0 (mkPtr (ct_xl o + 512) (Ro (ct_xl o))))%I.

End spec.
