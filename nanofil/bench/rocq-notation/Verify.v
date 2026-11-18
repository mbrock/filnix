(** Rocq checks both spellings against the functions in the Hello capture.
    The first goal displays three instructions from the original allocator.
    The second gives a [[flight]] a different [[lower]] donor. *)

From Stdlib Require Import String List ZArith.
From Nanofil Require Import Term Syntax.
Require Baseline Compact Assembly.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Example compact_alloc :
  Compact.hello_image_fn___alloc_dir =
  Baseline.hello_image_fn___alloc_dir := eq_refl.
Example assembly_alloc :
  Assembly.hello_image_fn___alloc_dir =
  Baseline.hello_image_fn___alloc_dir := eq_refl.
Example compact_alias :
  Compact.hello_image_fn_glibc_localealias'23alias_compare =
  Baseline.hello_image_fn_glibc_localealias'23alias_compare := eq_refl.
Example assembly_alias :
  Assembly.hello_image_fn_glibc_localealias'23alias_compare =
  Baseline.hello_image_fn_glibc_localealias'23alias_compare := eq_refl.

Require Import AssemblySyntax.
Goal forall (accept : list inst -> Prop), accept
  (List.firstn 3 (b_insts (List.last (fn_blocks Baseline.hello_image_fn___alloc_dir)
    (mkBlock (TAtom "") [] [] JUnreachable)))) -> True.
Proof.
  intro accept.
  cbv [Baseline.hello_image_fn___alloc_dir fn_blocks List.last b_insts List.firstn].
  Show.
  auto.
Qed.

Goal forall (accept : inst -> Prop), accept
  (Flight (TAtom "result") Add [FAddress (Tmp (TAtom "p")); FValue (Const 4)]
    (LowerOf (Tmp (TAtom "other")))) -> True.
Proof.
  intro accept.
  Show.
  auto.
Qed.

Require Import ByteSyntax.
Require DataBaseline DataLiteral.
Example literal_errnames :
  DataLiteral.hello_image_item_glibc_errname'23_sys_errname =
  DataBaseline.hello_image_item_glibc_errname'23_sys_errname := eq_refl.

Example negative_fallback : bytes_of_literal (Str [-1]) = None := eq_refl.
Example overflow_fallback : bytes_of_literal (Str [256]) = None := eq_refl.
