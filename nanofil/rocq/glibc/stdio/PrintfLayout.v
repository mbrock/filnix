(** The formatter of glibc writes through a `c: struct __printf_buffer`,
    and a buffer that feeds a stream is a
    `c: struct __printf_buffer_to_file`. This module names the two
    structures for the proofs. Each predicate is the general one of
    [CStruct](../tactics/CStruct.v) applied to the layout table that the code
    generator wrote for this fixture, so no proof here writes a field
    offset. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Pieces Heap.
From Glibc Require Import Fix FileInv CStruct PrintfBufferFileLayout.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope string_scope.
Open Scope Z_scope.

Definition pbuf_tag : string := "struct __printf_buffer".
Definition pbuf_file_tag : string := "struct __printf_buffer_to_file".
Definition file_tag : string := "struct _IO_FILE".

(** The staging array of a file-backed buffer starts at this offset
    and ends before this one. *)
Definition stage_off : Z := Eval vm_compute in field_off PrintfBufferFileLayout.fields pbuf_file_tag "stage".
Definition stage_end : Z := Eval vm_compute in field_end PrintfBufferFileLayout.fields pbuf_file_tag "stage".

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** The predicate [pbuf] owns the listed fields of the printf buffer at
    the object b. *)
Definition pbuf (b : Z) (vs : list (string * fval)) : iProp Σ :=
  struct_at PrintfBufferFileLayout.fields pbuf_tag b vs.

(** The object b is alive and has room for a printf buffer. *)
Definition pbuf_live (b : Z) (reg : region) : iProp Σ :=
  struct_live PrintfBufferFileLayout.records pbuf_tag b reg.

(** The predicate [pbuf_file] owns the listed fields of the file-backed
    buffer at the object b. *)
Definition pbuf_file (b : Z) (vs : list (string * fval)) : iProp Σ :=
  struct_at PrintfBufferFileLayout.fields pbuf_file_tag b vs.

(** The object b is alive and has room for a file-backed buffer. *)
Definition pbuf_file_live (b : Z) (reg : region) : iProp Σ :=
  struct_live PrintfBufferFileLayout.records pbuf_file_tag b reg.

(** The formatter reads a stream's write pointer and write end when it
    sets up a buffer. At that point a contract needs to own those two
    fields and nothing else of the stream. The predicate [file_cells]
    owns the listed fields of the stream at the object b. A proof that
    owns a whole stream uses the invariant [file_fields] of
    [FileInv](../libio/FileInv.v) instead. *)
Definition file_cells (b : Z) (vs : list (string * fval)) : iProp Σ :=
  struct_at PrintfBufferFileLayout.fields file_tag b vs.

(** A function that only reads a stream needs to know that the stream
    is alive, and it must leave the rest of the lifetime to the
    stream's owner. The predicate [file_liveq] owns such a share for
    the stream at the object b. *)
Definition file_liveq (dq : dfrac) (b : Z) (reg : region) : iProp Σ :=
  struct_liveq dq PrintfBufferFileLayout.records file_tag b reg.

End own.

#[global] Hint Unfold pbuf pbuf_file pbuf_live pbuf_file_live file_cells file_liveq : structs.

(** The layout table has the five fields of a printf buffer, and a
    buffer is forty bytes with eight-byte alignment. A change of the
    structure in glibc would fail this check. *)
Lemma pbuf_layout :
  map (field_at PrintfBufferFileLayout.fields pbuf_tag) ["write_base"; "write_ptr"; "write_end"; "written"; "mode"] =
    [Some (0, 8); Some (8, 8); Some (16, 8); Some (24, 8); Some (32, 4)] /\
  record_at PrintfBufferFileLayout.records pbuf_tag = (40, 8) /\
  record_at PrintfBufferFileLayout.records pbuf_file_tag = (176, 8).
Proof. vm_compute. repeat split; reflexivity. Qed.
