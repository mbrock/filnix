(** GNU Hello's version text and its bug-report lines come from
    gnulib's `c: version_etc` and `c: emit_bug_reporting_address`. Their
    formats and fixed arguments are read-only strings of Hello's image.
    The proofs of those two functions need each string's exact bytes,
    because the formatter's contract reads the format to see which
    arguments it takes. This module lists the strings that Hello's calls
    reach, with their bytes, without importing the image. The start
    proof checks the list against the image in
    [HelloStartKept](HelloStartKept.v). *)

From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope Z_scope.

(** Each entry is a string's symbol and its bytes without the
    terminating zero. Hello passes four authors, so of the author
    formats only the one for four names is listed. *)
Definition version_lits : list (string * list Z) := [
  ("version-etc#str.41"%string,
    [37; 115; 32; 40; 37; 115; 41; 32; 37; 115; 10]);
  ("version_etc_copyright"%string,
    [67; 111; 112; 121; 114; 105; 103; 104; 116; 32; 37; 115; 32; 37; 100; 32; 70; 114; 101; 101;
     32; 83; 111; 102; 116; 119; 97; 114; 101; 32; 70; 111; 117; 110; 100; 97; 116; 105; 111;
     110; 44; 32; 73; 110; 99; 46]);
  ("version-etc#str.44"%string,
    [40; 67; 41]);
  ("version-etc#str.45"%string,
    [10]);
  ("version-etc#str.46"%string,
    [76; 105; 99; 101; 110; 115; 101; 32; 71; 80; 76; 118; 51; 43; 58; 32; 71; 78; 85; 32; 71;
     80; 76; 32; 118; 101; 114; 115; 105; 111; 110; 32; 51; 32; 111; 114; 32; 108; 97; 116; 101;
     114; 32; 60; 37; 115; 62; 46; 10; 84; 104; 105; 115; 32; 105; 115; 32; 102; 114; 101; 101;
     32; 115; 111; 102; 116; 119; 97; 114; 101; 58; 32; 121; 111; 117; 32; 97; 114; 101; 32; 102;
     114; 101; 101; 32; 116; 111; 32; 99; 104; 97; 110; 103; 101; 32; 97; 110; 100; 32; 114; 101;
     100; 105; 115; 116; 114; 105; 98; 117; 116; 101; 32; 105; 116; 46; 10; 84; 104; 101; 114;
     101; 32; 105; 115; 32; 78; 79; 32; 87; 65; 82; 82; 65; 78; 84; 89; 44; 32; 116; 111; 32;
     116; 104; 101; 32; 101; 120; 116; 101; 110; 116; 32; 112; 101; 114; 109; 105; 116; 116; 101;
     100; 32; 98; 121; 32; 108; 97; 119; 46; 10]);
  ("version-etc#str.47"%string,
    [104; 116; 116; 112; 115; 58; 47; 47; 103; 110; 117; 46; 111; 114; 103; 47; 108; 105; 99;
     101; 110; 115; 101; 115; 47; 103; 112; 108; 46; 104; 116; 109; 108]);
  ("version-etc#str.51"%string,
    [87; 114; 105; 116; 116; 101; 110; 32; 98; 121; 32; 37; 115; 44; 32; 37; 115; 44; 32; 37;
     115; 44; 10; 97; 110; 100; 32; 37; 115; 46; 10]);
  ("version-etc#str.58"%string,
    [82; 101; 112; 111; 114; 116; 32; 98; 117; 103; 115; 32; 116; 111; 58; 32; 37; 115; 10]);
  ("version-etc#str.59"%string,
    [98; 117; 103; 45; 104; 101; 108; 108; 111; 64; 103; 110; 117; 46; 111; 114; 103]);
  ("version-etc#str.60"%string,
    [37; 115; 32; 104; 111; 109; 101; 32; 112; 97; 103; 101; 58; 32; 60; 37; 115; 62; 10]);
  ("version-etc#str.61"%string,
    [71; 78; 85; 32; 72; 101; 108; 108; 111]);
  ("version-etc#str.62"%string,
    [104; 116; 116; 112; 115; 58; 47; 47; 119; 119; 119; 46; 103; 110; 117; 46; 111; 114; 103;
     47; 115; 111; 102; 116; 119; 97; 114; 101; 47; 104; 101; 108; 108; 111; 47]);
  ("version-etc#str.63"%string,
    [71; 101; 110; 101; 114; 97; 108; 32; 104; 101; 108; 112; 32; 117; 115; 105; 110; 103; 32;
     71; 78; 85; 32; 115; 111; 102; 116; 119; 97; 114; 101; 58; 32; 60; 37; 115; 62; 10]);
  ("version-etc#str.64"%string,
    [104; 116; 116; 112; 115; 58; 47; 47; 119; 119; 119; 46; 103; 110; 117; 46; 111; 114; 103;
     47; 103; 101; 116; 104; 101; 108; 112; 47])
].
