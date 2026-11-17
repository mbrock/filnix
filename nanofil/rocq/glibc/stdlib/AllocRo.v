(** Several glibc functions call `c: malloc` on a path that a caller
    cannot rule out. A stream gets its buffer on the first write, so a
    print to a stream that has no buffer yet allocates one. A contract
    for such a function must lend what `c: malloc` needs.

    Glibc's `c: malloc` reads three objects before it asks the runtime
    for memory: its parameters `c: mp_`, the thread's cache pointer
    `c: tcache`, and the empty cache that the pointer starts at. It
    writes none of them while the cache is unused, and the proof of
    Hello already holds them read-only for the whole run. So a caller
    can lend them read-only, and it keeps them across every call. This file names that loan, so that
    the contracts of the functions that may allocate all ask for the
    same thing. *)

From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic.
From Glibc Require Import Fix AllocLogic.
Import ListNotations ProgramAbbreviations LG0 LG0.L.
Open Scope string_scope.
Open Scope Z_scope.

Section ro.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A contract that may reach `c: malloc` asks its caller for the
    predicate [malloc_ro]. The predicate lets its owner read the three
    objects, and it says that the cache is still the empty one. It
    gives nobody the right to write them, so the cache stays empty for
    the rest of the run. The predicate also says where the program
    keeps the parameters and the cache pointer, because `c: malloc`
    finds them by their symbols. The proof of `c: malloc` in
    [AllocLogic](AllocLogic.v) calls this state [tcache_idle]. *)
Definition malloc_ro : iProp Σ :=
  ∃ mp tc dm mpreg tcreg dmreg,
    ⌜lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)) /\
     lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))⌝ ∗
    tcache_idle DfracDiscarded mp tc dm mpreg tcreg dmreg.

(** A caller keeps the loan across a call, because anyone may read
    these objects at any time. *)
#[global] Instance malloc_ro_persistent : Persistent malloc_ro.
Proof using Type. rewrite /malloc_ro /tcache_idle /liveq /pcellq /icellq. apply _. Qed.

End ro.
