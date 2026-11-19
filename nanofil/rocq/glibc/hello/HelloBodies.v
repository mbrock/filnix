(** GNU Hello's proofs step through the checked IR that the glibc link
    contains. This file names the generated functions and checks the block
    labels and entry frames used by the proofs. It does not load the whole
    linked image or specify any of the functions' effects. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Semantics Ops.
From Glibc Require Import IRFrames.
From Glibc Require HelloImage_hello HelloImage_mbszero HelloImage_memeq HelloImage_streq
  HelloImage_strnlen1 HelloImage_xmalloc HelloImage_closeZ2dstream HelloImage_closeout
  HelloImage_progname HelloImage_setlocale_nullZ2dunlocked HelloImage_setlocale_null
  HelloImage_hardZ2dlocale HelloImage_mbrtowc HelloImage_mbsrtowcs HelloImage_propername
  HelloImage_versionZ2detc.
Import ListNotations.
Open Scope Z_scope.

(** ## Entry and leaf functions

    Hello starts at [main_fn] and reaches small helpers for allocation,
    string comparisons and resetting conversion state. The entry facts
    record which temporaries receive the caller's arguments. *)

(** The linked Hello object supplies the body of `c: main`. *)
Abbreviation main_fn := HelloImage_hello.fn_main.

(** Main's entry binds argc and argv. *)
Lemma main_entry argc argv :
  invocation main_fn [WInt argc; WPtr argv] =
  mkFrame main_fn [(TAtom "v2", WPtr argv); (TAtom "v0", WInt argc)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The allocation helper calls malloc and checks the returned pointer. *)
Abbreviation xmalloc_fn := HelloImage_xmalloc.fn_xmalloc.

(** The reset helper zeros the eight bytes of the conversion state. *)
Abbreviation mbszero_fn := HelloImage_mbszero.fn_mbszero.

(** The byte comparison tests whether memcmp returns zero. *)
Abbreviation memeq_fn := HelloImage_memeq.fn_memeq.

(** The string comparison tests whether strcmp returns zero. *)
Abbreviation streq_fn := HelloImage_streq.fn_streq.

(** The bounded scan returns the count through the NUL, or the bound if none is found. *)
Abbreviation strnlen1_fn := HelloImage_strnlen1.fn_strnlen1.

(** `mbszero`'s one block. *)
Definition z_start : block := Eval vm_compute in hblk mbszero_fn "start".

(** `memeq`'s one block. *)
Definition e_start : block := Eval vm_compute in hblk memeq_fn "start".

(** `streq`'s one block. *)
Definition q_start : block := Eval vm_compute in hblk streq_fn "start".

(** The entry block calls `memchr` and tests its result for null. *)
Definition n_start : block := Eval vm_compute in hblk strnlen1_fn "start".

(** When `memchr` finds a zero, this block counts the bytes through it. *)
Definition n_L8 : block := Eval vm_compute in hblk strnlen1_fn "L8".

(** When `memchr` finds no zero, this block returns the scan limit. *)
Definition n_L9 : block := Eval vm_compute in hblk strnlen1_fn "L9".

(** `mbszero` has its block. *)
Lemma find_z_start : find_block (TAtom "start") (fn_blocks mbszero_fn) = Some z_start.
Proof. vm_compute. reflexivity. Qed.

(** `memeq` has its block. *)
Lemma find_e_start : find_block (TAtom "start") (fn_blocks memeq_fn) = Some e_start.
Proof. vm_compute. reflexivity. Qed.

(** `streq` has its block. *)
Lemma find_q_start : find_block (TAtom "start") (fn_blocks streq_fn) = Some q_start.
Proof. vm_compute. reflexivity. Qed.

(** `strnlen1` has its entry. *)
Lemma find_n_start : find_block (TAtom "start") (fn_blocks strnlen1_fn) = Some n_start.
Proof. vm_compute. reflexivity. Qed.

(** `strnlen1` has its hit block. *)
Lemma find_n_L8 : find_block (TAtom "L8") (fn_blocks strnlen1_fn) = Some n_L8.
Proof. vm_compute. reflexivity. Qed.

(** `strnlen1` has its miss block. *)
Lemma find_n_L9 : find_block (TAtom "L9") (fn_blocks strnlen1_fn) = Some n_L9.
Proof. vm_compute. reflexivity. Qed.

(** `mbszero`'s entry binds its pointer. *)
Lemma mbszero_entry p :
  invocation mbszero_fn [WPtr p] =
  mkFrame mbszero_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** `memeq`'s entry binds its pointers and length. *)
Lemma memeq_entry p q n :
  invocation memeq_fn [WPtr p; WPtr q; WInt n] =
  mkFrame memeq_fn [(TAtom "v4", WInt n); (TAtom "v2", WPtr q); (TAtom "v0", WPtr p)] []
    None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** `streq`'s entry binds its pointers. *)
Lemma streq_entry p q :
  invocation streq_fn [WPtr p; WPtr q] =
  mkFrame streq_fn [(TAtom "v2", WPtr q); (TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** `strnlen1`'s entry binds its pointer and bound. *)
Lemma strnlen1_entry p n :
  invocation strnlen1_fn [WPtr p; WInt n] =
  mkFrame strnlen1_fn [(TAtom "v2", WInt n); (TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** ## Program names and diagnostics

    The program-name helper sets three pointers into the invocation string.
    The other functions in this section handle version output and close
    standard output on exit. *)

(** The program-name helper reads the first argument and records the chosen name. *)
Abbreviation set_program_name_fn := HelloImage_progname.fn_set_program_name.

(** The entry block asks `strrchr` for the last slash in the path. *)
Definition s_start : block := Eval vm_compute in hblk set_program_name_fn "start".

(** The base name starts after the slash. *)
Definition s_L6 : block := Eval vm_compute in hblk set_program_name_fn "L6".

(** Do seven bytes precede the base name? *)
Definition s_L8 : block := Eval vm_compute in hblk set_program_name_fn "L8".

(** Are they "/.libs/"? *)
Definition s_L25 : block := Eval vm_compute in hblk set_program_name_fn "L25".

(** Branch on that answer. *)
Definition s_L26 : block := Eval vm_compute in hblk set_program_name_fn "L26".

(** Does the base name start with "lt-"? *)
Definition s_L16 : block := Eval vm_compute in hblk set_program_name_fn "L16".

(** Skip "lt-". *)
Definition s_L35 : block := Eval vm_compute in hblk set_program_name_fn "L35".

(** Store the three names. *)
Definition s_L18 : block := Eval vm_compute in hblk set_program_name_fn "L18".

(** `set_program_name` has its entry. *)
Lemma find_s_start : find_block (TAtom "start") (fn_blocks set_program_name_fn) = Some s_start.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name` has L6. *)
Lemma find_s_L6 : find_block (TAtom "L6") (fn_blocks set_program_name_fn) = Some s_L6.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name` has L8. *)
Lemma find_s_L8 : find_block (TAtom "L8") (fn_blocks set_program_name_fn) = Some s_L8.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name` has L25. *)
Lemma find_s_L25 : find_block (TAtom "L25") (fn_blocks set_program_name_fn) = Some s_L25.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name` has L26. *)
Lemma find_s_L26 : find_block (TAtom "L26") (fn_blocks set_program_name_fn) = Some s_L26.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name` has L16. *)
Lemma find_s_L16 : find_block (TAtom "L16") (fn_blocks set_program_name_fn) = Some s_L16.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name` has L35. *)
Lemma find_s_L35 : find_block (TAtom "L35") (fn_blocks set_program_name_fn) = Some s_L35.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name` has L18. *)
Lemma find_s_L18 : find_block (TAtom "L18") (fn_blocks set_program_name_fn) = Some s_L18.
Proof. vm_compute. reflexivity. Qed.

(** `set_program_name`'s entry binds argv[0]. *)
Lemma set_program_name_entry p :
  invocation set_program_name_fn [WPtr p] =
  mkFrame set_program_name_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The proper-name helper looks up the translation of a name. *)
Abbreviation proper_name_fn := HelloImage_propername.fn_proper_name.

(** The diagnostic helper prints the address for bug reports. *)
Abbreviation emit_bug_reporting_address_fn := HelloImage_versionZ2detc.fn_emit_bug_reporting_address.

(** Its single block loads stdout and makes four output calls. *)
Definition emit_bug_reporting_address_start : block := Eval vm_compute in
  hblk emit_bug_reporting_address_fn "start".

(** The stream helper checks the stream and closes it. *)
Abbreviation close_stream_fn := HelloImage_closeZ2dstream.fn_close_stream.

(** Hello registers the standard-output helper as an exit callback. *)
Abbreviation close_stdout_fn := HelloImage_closeout.fn_close_stdout.

(** A close_stream block. *)
Definition cs_block (s : String.string) : block := hblk close_stream_fn s.

(** A close_stdout block. *)
Definition co_block (s : String.string) : block := hblk close_stdout_fn s.

(** An integer load interprets these four bytes as a little-endian word. *)
Definition close_w (xs : list Z) : Z :=
  match xs with
  | [a; b; c; d] => extension Sw (((d * 256 + c) * 256 + b) * 256 + a) mod 2 ^ 32
  | _ => 0
  end.

(** ## Locale and conversion

    Gnulib queries the current locale and uses it to choose how to convert
    input bytes. The entry facts below bind the category, buffer and size
    arguments that the corresponding calls pass. *)

(** The unlocked locale helper reads the current name for a category. *)
Abbreviation snu_fn := HelloImage_setlocale_nullZ2dunlocked.fn_setlocale_null_unlocked.

(** The unlocked buffer variant copies the locale name into caller storage. *)
Abbreviation snru_fn := HelloImage_setlocale_nullZ2dunlocked.fn_setlocale_null_r_unlocked.

(** The buffer variant takes the locale lock where the implementation needs it. *)
Abbreviation snr_fn := HelloImage_setlocale_null.fn_setlocale_null_r.

(** The locale test checks whether the named category uses a locale other than C or POSIX. *)
Abbreviation hard_locale_fn := HelloImage_hardZ2dlocale.fn_hard_locale.

(** `setlocale_null_unlocked`'s entry binds its category. *)
Lemma snu_entry k :
  invocation snu_fn [WInt k] = mkFrame snu_fn [(TAtom "v0", WInt k)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** `setlocale_null_r_unlocked`'s entry binds its category, buffer and size. *)
Lemma snru_entry k p n :
  invocation snru_fn [WInt k; WPtr p; WInt n] =
  mkFrame snru_fn [(TAtom "v4", WInt n); (TAtom "v2", WPtr p); (TAtom "v0", WInt k)] []
    None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** `setlocale_null_r`'s entry binds its category, buffer and size. *)
Lemma snr_entry k p n :
  invocation snr_fn [WInt k; WPtr p; WInt n] =
  mkFrame snr_fn [(TAtom "v4", WInt n); (TAtom "v2", WPtr p); (TAtom "v0", WInt k)] []
    None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** `hard_locale`'s entry binds its category. *)
Lemma hard_locale_entry k :
  invocation hard_locale_fn [WInt k] =
  mkFrame hard_locale_fn [(TAtom "v0", WInt k)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The character helper wraps mbrtowc and handles an invalid or incomplete sequence. *)
Abbreviation rpl_fn := HelloImage_mbrtowc.fn_rpl_mbrtowc.

(** The string helper repeats character conversion until it reaches NUL or the output limit. *)
Abbreviation mbs_fn := HelloImage_mbsrtowcs.fn_rpl_mbsrtowcs.

(** rpl_mbrtowc's entry binds its four arguments. *)
Lemma rpl_entry pwc src n ps :
  invocation rpl_fn [WPtr pwc; WPtr src; WInt n; WPtr ps] =
  mkFrame rpl_fn [(TAtom "v6", WPtr ps); (TAtom "v4", WInt n); (TAtom "v2", WPtr src); (TAtom "v0", WPtr pwc)]
    [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The string conversion proof selects each block by its label. *)
Definition mbs_block (s : String.string) : block := hblk mbs_fn s.
