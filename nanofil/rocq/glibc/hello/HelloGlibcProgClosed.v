(** This file proves GNU Hello's `set_program_name` and `memeq` when
    they are linked with glibc's own memrchr and memcmp, with no
    premise about either function.

    HelloGlibcProgName.v proves `set_program_name` from two premises.
    One is a call triple for glibc's memrchr, and the other is a call
    triple for memcmp on fewer than 16 bytes. HelloGlibcLeaf.v proves
    `memeq` from the same memcmp triple. MemrchrLogic.v proves the first
    premise of glibc's compiled memrchr, and MemcmpLogic.v proves the
    second of glibc's compiled memcmp.

    | Lemma | What it closes |
    | --- | --- |
    | [leaf_memcmp_spec] | HelloGlibcLeaf.v's [memcmp_spec], for [memeq_glibc] |
    | [cells_memcmp_spec] | HelloGlibcProgCells.v's [memcmp_spec] |
    | [set_program_name_closed] | `set_program_name` with no premise about memrchr or memcmp |

    The triples are for fewer than 16 bytes, which is all Hello
    compares: `set_program_name` compares the seven bytes of "/.libs/".
    From 16 bytes on, glibc's memcmp traps (MemcmpLogic.v's header). *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloName.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop OsWorld StrchrCode MemchrLast StrlenWord
  StrrchrLogic StrncmpCode HelloGlibcLeaf HelloGlibcProgCells HelloGlibcProgLibs HelloGlibcProgName MemcmpCode MemcmpLogic
  MemrchrCode MemrchrLogic.
From Glibc Require HelloGlibcLeaf HelloGlibcProgCells HelloGlibcProgName MemcmpLogic MemrchrLogic OsWorld.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.


(** `set_program_name` over its two premises. *)
(** Hello's leaves over their premises. *)
(** glibc's memrchr. *)
(** glibc's memcmp. *)
(** The Logic instance. *)
Module LG := LG0.
(** Its language. *)
Module L := LG.L.
Import L LG MemcmpLogic.ML.

Section closed.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** [os_wi] w0 survives safepoints. *)
Local Instance pc_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The Iris instance of the registry and [os_wi] w0. *)
Local Instance pc_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry (os_wi w0) ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** glibc's own memcmp at `memcmp` meets HelloGlibcLeaf.v's
    [memcmp_spec], so its [memeq_glibc] needs no premise about it. *)
Lemma leaf_memcmp_spec : find_fn ge (TAtom "memcmp") = Some (Defined glibc_memcmp) -> HelloGlibcLeaf.memcmp_spec w0 registry ge.
Proof. intros Hf. exact (MemcmpLogic.glibc_memcmp_small registry (os_wi w0) ge Hf). Qed.

(** glibc's own memcmp at `memcmp` meets HelloGlibcProgCells.v's
    [memcmp_spec]. *)
Lemma cells_memcmp_spec : find_fn ge (TAtom "memcmp") = Some (Defined glibc_memcmp) ->
  HelloGlibcProgCells.memcmp_spec w0 registry ge.
Proof. intros Hf. exact (MemcmpLogic.glibc_memcmp_small registry (os_wi w0) ge Hf). Qed.

(** Hello's callees: glibc's strrchr, which calls glibc's strlen and
    memrchr, Hello's memeq, which calls glibc's memcmp, and glibc's
    strncmp. *)
Context (Hstrrchr : find_fn ge (TAtom "strrchr") = Some (Defined glibc_strrchr))
  (Hstrlen : find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen))
  (Hmemrchr : find_fn ge (TAtom "__GI___memrchr") = Some (Defined glibc_memrchr))
  (Hmemcmp : find_fn ge (TAtom "memcmp") = Some (Defined glibc_memcmp))
  (Hmemeq : find_fn ge (TAtom "memeq") = Some (Defined memeq_fn))
  (Hstrncmp : find_fn ge (TAtom "strncmp") = Some (Defined glibc_strncmp)).
(** The globals, as HelloGlibcProgName.v has them. *)
Context (pb nb sb : Z) (preg nreg sreg : region) (lp tp : ptr)
  (Hpb : lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr pb (Obj pb)))
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hlp : lookup (TAtom "progname#str.3") (ge_globals ge) = Some lp)
  (Htp : lookup (TAtom "progname#str.4") (ge_globals ge) = Some tp)
  (Hpb_cell : 0 <= pb /\ pb mod 8 = 0 /\ pb + 8 <= r_end preg /\ r_end preg <= 2 ^ 48)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48).

(** The three cells, holding x, y and z. *)
Local Notation name_cells := (HelloGlibcProgCells.name_cells pb nb sb preg nreg sreg).

(** HelloGlibcProgName.v's [set_program_name_glibc] over glibc's own
    memrchr and memcmp, with no premise about either: on the string s
    at p, at any fraction or read-only, it stores into `program_name`
    and `program_invocation_name` a pointer to the byte [name_idx] of
    s, and into `program_invocation_short_name` one to its byte
    [short_idx], and hands the string back. *)
Lemma set_program_name_closed dq p s x0 y0 z0 Φ :
  (dq = DfracDiscarded \/ exists q, dq = DfracOwn q) ->
  word_string dq p s -∗ word_string DfracDiscarded lp libs_bytes -∗ word_string DfracDiscarded tp lt_bytes -∗
  name_cells x0 y0 z0 -∗
  ▷ (word_string dq p s -∗ name_cells (ptr_add p (Z.of_nat (name_idx s))) (ptr_add p (Z.of_nat (name_idx s)))
       (ptr_add p (Z.of_nat (short_idx s))) -∗ Φ RetVoid) -∗
  WP (ERun (invocation set_program_name_fn [WPtr p]) : gexpr) {{ Φ }}.
Proof.
  apply (HelloGlibcProgName.set_program_name_glibc w0 registry ge Hstrrchr Hstrlen Hmemeq Hstrncmp pb nb sb preg nreg sreg lp tp
           Hpb Hnb Hsb Hlp Htp Hpb_cell Hnb_cell Hsb_cell (MemrchrLogic.glibc_memrchr_spec registry (os_wi w0) ge Hmemrchr)
           (cells_memcmp_spec Hmemcmp)).
Qed.

End closed.
