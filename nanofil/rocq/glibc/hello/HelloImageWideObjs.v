(** Before Hello prints its greeting as wide characters, glibc reads
    constant data that the narrow calls never touch. It copies the C
    locale's converters into stdout, converts the wide characters back
    to bytes through tables of replacement characters, and releases the
    converters when it closes stdout. All of this data lies in Hello's
    executable and never changes. Four modules check it against the
    loaded image, and this file joins their lists, so that the start
    state holds the data in one place beside the constants of the
    narrow conversion. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap.
From Glibc Require Import HelloImageModule HelloImageWFwideObjs HelloImageWReleaseObjs
  HelloImageWConvObjs HelloImageWPrintfObjs.
Import ListNotations.

(** Making stdout wide copies words from the C locale's table of
    converters, and closing it reads the slots that release them.
    Converting wide characters back to bytes reads the replacement
    tables, the words that lead to them and the zero word that ends
    each table of strings. Formatting the greeting reads entries of the
    formatter's jump tables. *)
Definition hello_wide_objs_ps : list (piece * pval) :=
  hello_wfwide_ps ++ hello_wrelease_ps ++ hello_wc_tables_ps ++ hello_wc_words_ps ++ hello_wc_tails_ps ++
  hello_wprintf_tables_ps.

(** Hello starts with each of these constants as listed, because each
    part was checked against the loaded image. *)
Lemma hello_wide_objs_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_wide_objs_ps.
Proof.
  intros Hi. unfold hello_wide_objs_ps.
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_wfwide_agree g m Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_wrelease_agree g m Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_wc_tables_agree g m Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_wc_words_agree g m Hi)|].
  apply (proj2 (all_agree_app _ _ _)). split; [exact (hello_wc_tails_agree g m Hi)|].
  exact (hello_wprintf_agree g m Hi).
Qed.
