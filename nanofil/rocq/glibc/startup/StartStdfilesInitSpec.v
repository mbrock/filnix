(** glibc builds its three standard streams as static data. Each
    stream names the next one, and `c: _IO_list_all` names the first,
    which is stderr. The links that point backwards are left null,
    because a static initializer cannot fill them in. The constructor
    `c: _IO_stdfiles_init` fills them in before `c: main` runs. This
    module states what a call of the constructor needs and what it
    leaves behind, so that the proof of startup can use the call as
    one step. [StartStdfilesInit](StartStdfilesInit.v) proves the
    contract.

    ## What the call owns

    The constructor reads `c: _IO_list_all` and writes one pointer in
    each of the three streams, so the call owns those four objects.
    glibc protects the list of streams with a lock, and it keeps a
    pointer named `c: run_fp` beside it. The constructor uses neither.
    The call owns them anyway, because the proofs that run later treat
    the list, its lock and that pointer as one unit, and the call
    hands the unit over complete.

    The proof that the constructor links the streams this way was
    written earlier, in [LibioStdfiles](../libio/LibioStdfiles.v).
    This module only puts the same statement into the form that a
    call from another function needs. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv LibioStdfiles.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioStdfiles.
Open Scope Z_scope.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The contract needs to know where three globals lie. The variable
    `c: _IO_list_all` is at la, the lock of the stream list is at lk,
    and `c: run_fp` is at rf. The first and the last hold a pointer
    each, so they are aligned to eight bytes and have room for one. *)
Definition stdfiles_init_ok (la : Z) (lareg : region) (lk rf : Z) (rfreg : region) : Prop :=
  lookup (TAtom "__GI__IO_list_all") (ge_globals ge) = Some (mkPtr la (Obj la)) /\
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) /\
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) /\
  la mod 8 = 0 /\ la + 8 <= r_end lareg /\ rf mod 8 = 0 /\ rf + 8 <= r_end rfreg.

(** The constructor takes no argument. Before the call the three
    streams are linked forwards only. The head of the list points at
    stderr fe, stderr points at stdout fo, and stdout points at stdin
    fi. Nobody holds the lock of the list, and `c: run_fp` is null.
    After the call every stream also points back at the link before
    it. The assertion [io_list_inv] says that for the whole list, and
    the proofs of `c: puts`, `c: fclose` and `c: exit` start from it.
    The call also gives back the lifetime of each stream. *)
Definition stdfiles_init_spec : fspec Σ :=
  FSpec (ptr * ptr * ptr * Z * region * Z * region * Z * region) (fun _ => [])
    (fun '(fe, fo, fi, la, lareg, lk, lkreg, rf, rfreg) =>
       ⌜stdfiles_init_ok la lareg lk rf rfreg⌝ ∗ live la lareg ∗ pcell la 0 fe ∗
       stdfile_pre fe fo ∗ stdfile_pre fo fi ∗ stdfile_pre fi null ∗
       lock_state lk lkreg 0 0 null ∗ live rf rfreg ∗ pcell rf 0 null)%I
    (fun '(fe, fo, fi, la, lareg, lk, lkreg, rf, rfreg) r =>
       ⌜r = RetVoid⌝ ∗ io_list_inv ge [fe; fo; fi] ∗ [∗ list] f ∈ [fe; fo; fi], stream_live f)%I.

End spec.
