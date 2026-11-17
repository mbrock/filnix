(** GNU Hello prints through glibc's formatter with constant format
    strings. The formatter's contract, [vfprintf_spec] of
    [PrintfSpec](../stdio/PrintfSpec.v), covers a format when the
    parser [parse_narrow] accepts its bytes. This module lists the
    format strings of Hello's linked image that reach the formatter and
    shows that the parser accepts every one of them.

    The check is a computation over the image. It reads each string's
    bytes from the image's data, so a rebuilt image with a new format
    either passes the same check or fails it here. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax.
From Glibc Require Import NarrowFormat HelloImageModule HelloStartKept.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## The formats *)

(** Hello has five formats of its own. They are the usage line, the
    two lines after the help text, and the two formats that Hello
    gives `c: error`. *)
Definition hello_own_formats : list string :=
  ["hello#str.54"; "hello#str.62"; "hello#str.79"; "hello#str.77"; "xalloc-die#str.41"].

(** These formats print the version text of gnulib's
    `c: version_etc` and the bug-report lines of
    `c: emit_bug_reporting_address`. The copyright line is the only
    format with `%d`. *)
Definition hello_version_formats : list string :=
  ["version-etc#str.41"; "version-etc#str.42"; "version_etc_copyright"; "version-etc#str.46";
   "version-etc#str.48"; "version-etc#str.49"; "version-etc#str.50"; "version-etc#str.51";
   "version-etc#str.52"; "version-etc#str.53"; "version-etc#str.54"; "version-etc#str.55";
   "version-etc#str.56"; "version-etc#str.57"; "version-etc#str.58"; "version-etc#str.60";
   "version-etc#str.63"].

(** These formats belong to gnulib's `c: close_stdout` and to glibc's
    `c: error`, which prints the program's name and the error text. *)
Definition hello_error_formats : list string :=
  ["closeout#str.54"; "closeout#str.55"; "glibc_error#str.252"; "glibc_error#str.255"].

(** These formats are the diagnostics of glibc's `c: getopt_long`.
    The last two are the only formats with `%c`. *)
Definition hello_getopt_formats : list string :=
  ["glibc_getopt#str.138"; "glibc_getopt#str.139"; "glibc_getopt#str.140"; "glibc_getopt#str.142";
   "glibc_getopt#str.143"; "glibc_getopt#str.144"; "glibc_getopt#str.148"; "glibc_getopt#str.149"].

Definition hello_formats : list string :=
  hello_own_formats ++ hello_version_formats ++ hello_error_formats ++ hello_getopt_formats.

(** ## The check *)

(** The function [hello_format] reads the string named n from the
    image and parses it. It gives nothing for a name that the image
    lacks. *)
Definition hello_format (n : string) : option (list narrow_directive) :=
  match upto_zero (data_bytes hello_image_module n) with
  | [] => None
  | bs => parse_narrow bs
  end.

(** The list [hello_formats_parsed] holds the result of parsing every
    listed format. It is computed once, when this module is compiled. *)
Definition hello_formats_parsed : list (option (list narrow_directive)) :=
  Eval vm_compute in map hello_format hello_formats.

(** The image has every listed format, and the parser accepts it. *)
Lemma hello_formats_narrow n :
  In n hello_formats -> exists ds, hello_format n = Some ds.
Proof.
  intros Hin.
  assert (H : forallb (fun o => match o with Some _ => true | None => false end) hello_formats_parsed = true)
    by (vm_compute; reflexivity).
  assert (E : hello_formats_parsed = map hello_format hello_formats) by (vm_compute; reflexivity).
  rewrite E in H. rewrite forallb_forall in H. specialize (H (hello_format n) (in_map _ _ _ Hin)).
  destruct (hello_format n) as [ds|]; [exists ds; reflexivity | discriminate H].
Qed.

(** The parser knows only the four conversions that the formatter's
    contract covers, so no listed format has another one. The function
    [conversion_counts] counts how often the listed formats use each of
    the four: strings, characters, integers and percent signs. *)
Definition conversion_counts (ps : list (option (list narrow_directive))) : Z * Z * Z * Z :=
  fold_left (fun '(s, c, i, p) d =>
      match d with
      | FmtStr => (s + 1, c, i, p) | FmtChar => (s, c + 1, i, p)
      | FmtInt => (s, c, i + 1, p) | FmtPercent => (s, c, i, p + 1) | FmtLit _ => (s, c, i, p)
      end)
    (flat_map (fun o => match o with Some ds => ds | None => [] end) ps) (0, 0, 0, 0).

Lemma hello_conversions : conversion_counts hello_formats_parsed = (95, 2, 1, 0).
Proof. vm_compute. reflexivity. Qed.
