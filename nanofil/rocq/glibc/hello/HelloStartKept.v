(** When startup calls GNU Hello's `c: main`, most of the memory that
    main's proof reads still holds what the linker put there, because no
    startup call writes it. This module lists that memory, the kept
    frame, and shows that the loader's memory for Hello holds it. The
    startup proof carries the list unchanged from the start to the call
    of `c: main`.

    ## What the frame leaves out

    Startup hands memory from one call to the next, and each byte must
    have exactly one owner on the way. So memory that some startup call
    reads or writes travels with that call and is not in this frame, even
    when the call gives it back unchanged. The streams' lives and links
    are such memory, and so are the program's names, its arguments and
    the errno cell.

    Every address is read from the loader's symbols, and every string
    is read from the image, so a relink of Hello changes no line here. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Bool Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Pieces Heap StringLogic MemLogic.
From Glibc Require Import HelloVersionLits FileInv StrlenLogic WordString HelloGetoptTable HelloGetoptStart StartImageUnique
  HelloImageErase HelloImageEraseMem HelloImagePieces HelloImageModule HelloImageLoad HelloImageCtors
  HelloImageStart HelloStartKeptAlloc.
Import ListNotations.
Open Scope Z_scope.

(** ## The streams and the globals

    Main prints through the three streams and closes them at exit, so
    it needs every field that the stream code reads. The linker leaves
    every buffer pointer null, both offsets at minus one, and each
    stream's lock free.*)

(** These are the fields of the stream fb that no startup call touches,
    with the lock object lk and the wide data object wd. The stream's
    flags are fl and its descriptor is fd. *)
Definition hello_stream_kept_ps (fb fl fd lk : Z) (lkreg : region) (wd : Z) : list (piece * pval) :=
  List.concat [byte_ps fb 0 (int_bytes fl);
    List.concat (map (fun i => hello_pointer_ps fb (8 + 8 * i) null) (seqZ 0 12));
    byte_ps fb 112 (int_bytes fd); byte_ps fb 116 (int_bytes 0);
    cell fb 120 (2 ^ 64 - 1); byte_ps fb 128 (repeat 0 8%nat);
    hello_pointer_ps fb 136 (mkPtr lk (Obj lk)); cell fb 144 (2 ^ 64 - 1);
    hello_pointer_ps fb 152 null; hello_pointer_ps fb 160 (mkPtr wd (Obj wd));
    hello_pointer_ps fb 168 null; hello_pointer_ps fb 176 null;
    byte_ps fb 192 (int_bytes 0); cell fb 200 0;
    [(PLive lk, VLive lkreg)]; byte_ps lk 0 (int_bytes 0); byte_ps lk 4 (int_bytes 0);
    hello_pointer_ps lk 8 null].

(** The jump table of narrow file streams lies 336 bytes into
    `c: __io_vtables`, and its slots point at glibc's file functions. *)
Definition hello_jumps_kept_ps : list (piece * pval) := Eval vm_compute in
  List.concat (map (fun sl => hello_pointer_ps (img_addr "__io_vtables") (vt_file + sl.1)
    (mkPtr (img_addr sl.2) (Fn (TAtom sl.2)))) file_jumps).

(** This list holds the three streams' fields and the globals stdout
    and stderr that point at two of them. It also holds the jump table,
    gnulib's program name, which starts null, and the parser's globals
    optarg, which starts null, and optind, which starts at one. *)
Definition hello_io_kept_ps : list (piece * pval) :=
  List.concat [
    hello_stream_kept_ps (img_a "_IO_2_1_stderr_") 4222427270 2 (img_a "glibc_stdfiles#_IO_stdfile_2_lock")
      (img_gd "glibc_stdfiles#_IO_stdfile_2_lock") (img_a "glibc_stdfiles#_IO_wide_data_2");
    hello_stream_kept_ps (img_a "_IO_2_1_stdout_") 4222427268 1 (img_a "glibc_stdfiles#_IO_stdfile_1_lock")
      (img_gd "glibc_stdfiles#_IO_stdfile_1_lock") (img_a "glibc_stdfiles#_IO_wide_data_1");
    hello_stream_kept_ps (img_a "_IO_2_1_stdin_") 4222427272 0 (img_a "glibc_stdfiles#_IO_stdfile_0_lock")
      (img_gd "glibc_stdfiles#_IO_stdfile_0_lock") (img_a "glibc_stdfiles#_IO_wide_data_0");
    [(PLive (img_a "stdout"), VLive (img_gd "stdout"))];
    hello_pointer_ps (img_a "stdout") 0 (mkPtr (img_a "_IO_2_1_stdout_") (Obj (img_a "_IO_2_1_stdout_")));
    [(PLive (img_a "stderr"), VLive (img_gd "stderr"))];
    hello_pointer_ps (img_a "stderr") 0 (mkPtr (img_a "_IO_2_1_stderr_") (Obj (img_a "_IO_2_1_stderr_")));
    hello_jumps_kept_ps;
    [(PLive (img_a "program_name"), VLive (img_gd "program_name"))]; hello_pointer_ps (img_a "program_name") 0 null;
    [(PLive (img_a "optarg"), VLive (img_gd "optarg"))]; hello_pointer_ps (img_a "optarg") 0 null;
    [(PLive (img_a "optind"), VLive (img_gd "optind"))]; byte_ps (img_a "optind") 0 (int_bytes 1)].

(** ## The strings *)

(** Main passes these strings to its callees: the two strings of
    gnulib's program name module, getopt's environment key, the other
    literals of Hello and the strings of gnulib's version text. *)
Definition hello_lit_names : list string :=
  ["progname#str.3"; "progname#str.4"; "glibc_getopt#str.145"] ++ hello_lits_rest ++ map fst version_lits.

(** ## The check on a smaller copy

    The lists are checked in a copy of the image that keeps only the
    objects named here and blanks every other one. *)

Definition hello_io_names : list string :=
  ["_IO_2_1_stderr_"; "_IO_2_1_stdout_"; "_IO_2_1_stdin_"; "glibc_stdfiles#_IO_stdfile_0_lock";
   "glibc_stdfiles#_IO_stdfile_1_lock"; "glibc_stdfiles#_IO_stdfile_2_lock"; "stdout"; "stderr";
   "__io_vtables"; "program_name"; "optarg"; "optind"]%string.

Definition hello_kept_main_keep (n : name) : bool :=
  existsb (name_eqb n) (map TAtom (hello_io_names ++ hello_lit_names)).

Definition hello_kept_main_skel : module := Eval vm_compute in erase hello_kept_main_keep hello_image_module.
Lemma hello_kept_main_skel_eq : erase hello_kept_main_keep hello_image_module = hello_kept_main_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_kept_main_kept : module := Eval vm_compute in kept_objects hello_kept_main_keep hello_image_module.
Lemma hello_kept_main_kept_incl : incl hello_kept_main_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_kept_main_keep hello_image_module = hello_kept_main_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

(** These are the bytes that the image gives the object named n, in
    order. A wide string stores four bytes for each character. *)
Definition data_bytes (md : module) (n : string) : list Z :=
  match find (fun it => match it with IData k _ _ _ => name_eqb k (TAtom n) | _ => false end) md with
  | Some (IData _ _ _ its) => flat_map (fun it => match it with
      | Str c => c | Item Wb x => [x] | Item Ww x => le_bytes x 4 | _ => [] end) its
  | _ => []
  end.

(** The C string that starts the bytes xs ends at their first zero. *)
Fixpoint upto_zero (xs : list Z) : list Z :=
  match xs with [] => [] | x :: xs' => if x =? 0 then [] else x :: upto_zero xs' end.

(** The bytes xs form little-endian 64-bit words, the last one padded
    with zeros, and the first k words are kept. *)
Definition bytes_words (xs : list Z) (k : nat) : list Z :=
  map (fun i => fold_right (fun j acc => nth (8 * i + j) xs 0 + 256 * acc) 0 (seq 0 8)) (seq 0 k).

(** This list pairs each string with its bytes in the image and with
    the words of its object that main's string routines read. Those are
    the words up to and including the one that holds the terminating
    zero. *)
Definition hello_lit_strs : list (string * list Z * list Z) := Eval vm_compute in
  map (fun n => let xs := data_bytes hello_kept_main_kept n in let s := upto_zero xs in
    (n, s, bytes_words xs ((length s + 8) / 8))) hello_lit_names.

(** Each string's object holds its words. *)
Definition hello_lit_kept_ps : list (piece * pval) := Eval vm_compute in
  List.concat (map (fun ns => lit_ps (img_addr ns.1.1) (snd (img_obj ns.1.1)) ns.2) hello_lit_strs).

(** Every string is a C string, and the words spell it with its
    terminating zero. *)
Lemma hello_lit_strs_ok : Forall (fun ns => lit_ok ns.1.2 = true /\
  take (S (length ns.1.2)) (wbytes ns.2) = ns.1.2 ++ [0]) hello_lit_strs.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma hello_kept_main_check :
  match initial_memory hello_kept_main_skel with
  | Some (g, m') => pieces_ok hello_kept_main_keep hello_kept_main_kept g m' (hello_io_kept_ps ++ hello_lit_kept_ps)
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** ## The frame in the real memory *)

(** Main needs its allocator, its exit handlers, the option parser's
    state, the streams and its strings, and startup writes none of them.
    So the frame holds all of them, the first three from earlier
    modules and the rest from the lists above. *)
Definition hello_start_kept_ps : list (piece * pval) :=
  hello_alloc_kept_ps ++ hello_exit_kept_ps ++ hello_start_ps ++ hello_io_kept_ps ++ hello_lit_kept_ps.

(** Hello starts with the whole frame, in whatever memory the loader
    builds for it. *)
Lemma hello_start_kept_agree g m : initial_memory hello_image_module = Some (g, m) ->
  all_agree m hello_start_kept_ps.
Proof.
  intros E.
  destruct (image_pieces hello_kept_main_keep hello_kept_main_kept hello_image_module g m
    (hello_io_kept_ps ++ hello_lit_kept_ps) hello_kept_main_kept_incl E hello_image_names hello_image_zero)
    as (m' & E' & _ & P).
  pose proof hello_kept_main_check as C. rewrite <- hello_kept_main_skel_eq, E' in C.
  destruct hello_image_start as (g1 & m1 & E1 & _ & _ & _ & _ & As & _).
  rewrite E in E1. injection E1 as <- <-.
  unfold hello_start_kept_ps. rewrite !all_agree_app.
  split; [exact (hello_alloc_kept_agree g m E)|]. split; [exact (hello_exit_kept_agree g m E)|].
  split; [exact As|]. apply all_agree_app. exact (P C).
Qed.

(** No piece of the frame is listed twice. *)
Lemma hello_start_kept_nodup : NoDup hello_start_kept_ps.*1.
Proof. apply pieces_unique_sound. vm_compute. reflexivity. Qed.
