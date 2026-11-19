(** A conversion borrows the thread's locale pointer and the global locale's
    character category. The generated placement supplies both addresses. *)

From Stdlib Require Import List String ZArith.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Values Memory Pieces Heap.
From Glibc Require Import FileInv HelloImagePlacement.
Import FileInv.LG.
Open Scope Z_scope.

(** Each lookup must find the named symbol in the generated placement. *)
Ltac conv_bounds n :=
  let row := eval vm_compute in
    (List.find (fun row : string * Z * Z => String.eqb (fst (fst row)) n) placement) in
  lazymatch row with
  | Some (_, ?base, ?limit) => constr:((base, limit))
  end.

Abbreviation conv_addr n := (ltac:(let r := conv_bounds n%string in let b := eval cbv in (fst r) in exact b)) (only parsing).
Abbreviation conv_region n := (ltac:(let r := conv_bounds n%string in
  let v := eval cbv in (mkRegion (fst r) (snd r) GlobalData Live) in exact v)) (only parsing).

Section cells.
Context `{!gen_heapGS piece pval Σ}.

(** The thread's locale pointer names the global locale, and its
    character category names the C data. The caller takes both cells
    back after each character. *)
Definition mbr_locale dq : iProp Σ :=
  let ts := conv_addr "__libc_tsd_LOCALE" in
  let gl := conv_addr "_nl_global_locale" in
  let cc := conv_addr "_nl_C_LC_CTYPE" in
  live ts (conv_region "__libc_tsd_LOCALE") ∗ pcell ts 0 (mkPtr gl (Obj gl)) ∗
  live gl (conv_region "_nl_global_locale") ∗ pcellq dq gl 0 (mkPtr cc (Ro cc)).

End cells.
