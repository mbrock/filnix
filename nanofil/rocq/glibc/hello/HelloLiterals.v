(** Hello's main passes these globals to its callees. The option string and
    table sit between the first ten literals and the remaining strings.
    Startup supplies that pair when it lends the table to getopt. *)

From Stdlib Require Import List String.
Import ListNotations.

Local Definition before_options : list string :=
  ["hello#str.54"; "hello#str.55"; "hello#str.56"; "hello#str.57"; "hello#str.58";
   "hello#str.59"; "hello#str.60"; "hello#str.61"; "hello#str.62"; "hello#str.63"]%string.

Local Definition after_options : list string :=
  ["hello#str.70"; "hello#str.71"; "hello#str.72"; "hello#str.73"; "hello#str.74";
   "hello#str.75"; "hello#str.76"; "hello#str.77"; "hello#str.78"; "hello#str.79";
   "hello#str.80"; "hello#str.81"; "hello#str.82"; "hello#str.83"]%string.

(** These symbols identify the literals passed by main to its callees. *)
Definition hello_lits : list string :=
  (before_options ++ ["hello#str.69"; "hello#parse_options.longopts.64"]%string ++ after_options)%list.

(** Startup supplies these literals alongside the option string and table. *)
Definition hello_lits_rest : list string := (before_options ++ after_options)%list.
