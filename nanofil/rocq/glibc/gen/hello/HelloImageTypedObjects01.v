(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_item_closeout'23file_name : item :=
  (IData (a "closeout#file_name") LLocal 8 [(Zero 8)]).

Definition hello_image_item_closeout'23ignore_EPIPE : item :=
  (IData (a "closeout#ignore_EPIPE") LLocal 1 [(Zero 1)]).

Definition hello_image_item_closeout'23str'2e52 : item :=
  (IData (a "closeout#str.52") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).

Definition hello_image_item_closeout'23str'2e53 : item :=
  (IData (a "closeout#str.53") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_closeout'23str'2e54 : item :=
  (IData (a "closeout#str.54") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_closeout'23str'2e55 : item :=
  (IData (a "closeout#str.55") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_exit_failure : item :=
  (IData (a "exit_failure") LExport 4 [(Item Ww 1)]).

Definition hello_image_item_hard'2dlocale'23str'2e31 : item :=
  (IData (a "hard-locale#str.31") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 0)]).

Definition hello_image_item_hard'2dlocale'23str'2e32 : item :=
  (IData (a "hard-locale#str.32") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 79); (Item Wb 83); (Item Wb 73); (Item Wb 88); (Item Wb 0)]).

Definition hello_image_item_mbrtoc32'23internal_state : item :=
  (IData (a "mbrtoc32#internal_state") LLocal 4 [(Zero 8)]).

Definition hello_image_item_mbrtoc32'23str'2e36 : item :=
  (IData (a "mbrtoc32#str.36") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item__gl_mbsrtowcs_state : item :=
  (IData (a "_gl_mbsrtowcs_state") LExport 4 [(Zero 8)]).

Definition hello_image_item_program_name : item :=
  (IData (a "program_name") LExport 8 [(Item Wl 0)]).

Definition hello_image_item_progname'23str'2e3 : item :=
  (IData (a "progname#str.3") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 46); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 115); (Item Wb 47); (Item Wb 0)]).

Definition hello_image_item_progname'23str'2e4 : item :=
  (IData (a "progname#str.4") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 116); (Item Wb 45); (Item Wb 0)]).

Definition hello_image_item_quotearg'23default_quoting_options : item :=
  (IData (a "quotearg#default_quoting_options") LLocal 8 [(Zero 56)]).

Definition hello_image_item_quotearg'23gettext_quote'2equote'2e83 : item :=
  (IData (a "quotearg#gettext_quote.quote.83") (LRo (a "local")) 1 [(Str [226; 128; 152]); (Zero 1); (Str [226; 128; 153]); (Zero 1)]).

Definition hello_image_item_quotearg'23nslots : item :=
  (IData (a "quotearg#nslots") LLocal 4 [(Item Ww 1)]).

Definition hello_image_item_quotearg'23slot0 : item :=
  (IData (a "quotearg#slot0") LLocal 1 [(Zero 256)]).

Definition hello_image_item_quotearg'23slotvec : item :=
  (IData (a "quotearg#slotvec") LLocal 8 [(Sym (a "quotearg#slotvec0") 0)]).

Definition hello_image_item_quotearg'23slotvec0 : item :=
  (IData (a "quotearg#slotvec0") LLocal 8 [(Item Wl 256); (Sym (a "quotearg#slot0") 0)]).

Definition hello_image_item_quotearg'23str'2e82 : item :=
  (IData (a "quotearg#str.82") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).

Definition hello_image_item_quotearg'23str'2e84 : item :=
  (IData (a "quotearg#str.84") (LRo (a "local")) 1 [(Item Wb 34); (Item Wb 0)]).

Definition hello_image_item_quotearg'23str'2e85 : item :=
  (IData (a "quotearg#str.85") (LRo (a "local")) 1 [(Item Wb 39); (Item Wb 0)]).

Definition hello_image_item_quotearg'23str'2e86 : item :=
  (IData (a "quotearg#str.86") (LRo (a "local")) 1 [(Item Wb 96); (Item Wb 0)]).

Definition hello_image_item_version_etc_copyright : item :=
  (IData (a "version_etc_copyright") (LRo (a "export")) 1 [(Str [67; 111; 112; 121; 114; 105; 103; 104; 116; 32; 37; 115; 32; 37; 100; 32; 70; 114; 101; 101; 32; 83; 111; 102; 116; 119; 97; 114; 101; 32; 70; 111; 117; 110; 100; 97; 116; 105; 111; 110; 44; 32; 73; 110; 99; 46]); (Zero 1)]).

Definition hello_image_item_version'2detc'23str'2e41 : item :=
  (IData (a "version-etc#str.41") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 40); (Item Wb 37); (Item Wb 115); (Item Wb 41); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e42 : item :=
  (IData (a "version-etc#str.42") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e43 : item :=
  (IData (a "version-etc#str.43") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e44 : item :=
  (IData (a "version-etc#str.44") (LRo (a "local")) 1 [(Item Wb 40); (Item Wb 67); (Item Wb 41); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e45 : item :=
  (IData (a "version-etc#str.45") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e46 : item :=
  (IData (a "version-etc#str.46") (LRo (a "local")) 1 (app (app [(Item Wb 76); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 110); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 71); (Item Wb 80); (Item Wb 76); (Item Wb 118); (Item Wb 51); (Item Wb 43); (Item Wb 58); (Item Wb 32); (Item Wb 71); (Item Wb 78); (Item Wb 85); (Item Wb 32); (Item Wb 71); (Item Wb 80); (Item Wb 76); (Item Wb 32); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 51); (Item Wb 32); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 114)] [(Item Wb 32); (Item Wb 60); (Item Wb 37); (Item Wb 115); (Item Wb 62); (Item Wb 46); (Item Wb 10); (Item Wb 84); (Item Wb 104); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 32); (Item Wb 115); (Item Wb 111); (Item Wb 102); (Item Wb 116); (Item Wb 119); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 58); (Item Wb 32); (Item Wb 121); (Item Wb 111); (Item Wb 117); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 102); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 32)]) (app [(Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 103); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 105); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 105); (Item Wb 98); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 116); (Item Wb 46); (Item Wb 10); (Item Wb 84); (Item Wb 104); (Item Wb 101); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 78); (Item Wb 79); (Item Wb 32)] [(Item Wb 87); (Item Wb 65); (Item Wb 82); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 84); (Item Wb 89); (Item Wb 44); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 109); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 108); (Item Wb 97); (Item Wb 119); (Item Wb 46); (Item Wb 10); (Item Wb 0)]))).

Definition hello_image_item_version'2detc'23str'2e47 : item :=
  (IData (a "version-etc#str.47") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 116); (Item Wb 116); (Item Wb 112); (Item Wb 115); (Item Wb 58); (Item Wb 47); (Item Wb 47); (Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 110); (Item Wb 115); (Item Wb 101); (Item Wb 115); (Item Wb 47); (Item Wb 103); (Item Wb 112); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 116); (Item Wb 109); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e48 : item :=
  (IData (a "version-etc#str.48") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e49 : item :=
  (IData (a "version-etc#str.49") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e50 : item :=
  (IData (a "version-etc#str.50") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e51 : item :=
  (IData (a "version-etc#str.51") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e52 : item :=
  (IData (a "version-etc#str.52") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e53 : item :=
  (IData (a "version-etc#str.53") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e54 : item :=
  (IData (a "version-etc#str.54") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e55 : item :=
  (IData (a "version-etc#str.55") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e56 : item :=
  (IData (a "version-etc#str.56") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e57 : item :=
  (IData (a "version-etc#str.57") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 121); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 10); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 44); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 111); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e58 : item :=
  (IData (a "version-etc#str.58") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 103); (Item Wb 115); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e59 : item :=
  (IData (a "version-etc#str.59") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 103); (Item Wb 45); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 64); (Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e60 : item :=
  (IData (a "version-etc#str.60") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 104); (Item Wb 111); (Item Wb 109); (Item Wb 101); (Item Wb 32); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 58); (Item Wb 32); (Item Wb 60); (Item Wb 37); (Item Wb 115); (Item Wb 62); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e61 : item :=
  (IData (a "version-etc#str.61") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 78); (Item Wb 85); (Item Wb 32); (Item Wb 72); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e62 : item :=
  (IData (a "version-etc#str.62") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 116); (Item Wb 116); (Item Wb 112); (Item Wb 115); (Item Wb 58); (Item Wb 47); (Item Wb 47); (Item Wb 119); (Item Wb 119); (Item Wb 119); (Item Wb 46); (Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 47); (Item Wb 115); (Item Wb 111); (Item Wb 102); (Item Wb 116); (Item Wb 119); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 47); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 47); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e63 : item :=
  (IData (a "version-etc#str.63") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 101); (Item Wb 110); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 71); (Item Wb 78); (Item Wb 85); (Item Wb 32); (Item Wb 115); (Item Wb 111); (Item Wb 102); (Item Wb 116); (Item Wb 119); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 58); (Item Wb 32); (Item Wb 60); (Item Wb 37); (Item Wb 115); (Item Wb 62); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_version'2detc'23str'2e64 : item :=
  (IData (a "version-etc#str.64") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 116); (Item Wb 116); (Item Wb 112); (Item Wb 115); (Item Wb 58); (Item Wb 47); (Item Wb 47); (Item Wb 119); (Item Wb 119); (Item Wb 119); (Item Wb 46); (Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 47); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 47); (Item Wb 0)]).

Definition hello_image_item_xalloc'2ddie'23str'2e41 : item :=
  (IData (a "xalloc-die#str.41") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_xalloc'2ddie'23str'2e42 : item :=
  (IData (a "xalloc-die#str.42") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).

Definition hello_image_item_xalloc'2ddie'23str'2e43 : item :=
  (IData (a "xalloc-die#str.43") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 104); (Item Wb 97); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_hello'23parse_options'2elongopts'2e64 : item :=
  (IData (a "hello#parse_options.longopts.64") (LRo (a "local")) 8 [(Sym (a "hello#str.65") 0); (Item Ww 1); (Zero 4); (Item Wl 0); (Item Ww 103); (Zero 4); (Sym (a "hello#str.66") 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 116); (Zero 4); (Sym (a "hello#str.67") 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 128); (Zero 4); (Sym (a "hello#str.68") 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 129); (Zero 4); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 0); (Zero 4)]).

Definition hello_image_item_hello'23str'2e54 : item :=
  (IData (a "hello#str.54") (LRo (a "local")) 1 [(Item Wb 85); (Item Wb 115); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 91); (Item Wb 79); (Item Wb 80); (Item Wb 84); (Item Wb 73); (Item Wb 79); (Item Wb 78); (Item Wb 93); (Item Wb 46); (Item Wb 46); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e55 : item :=
  (IData (a "hello#str.55") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 102); (Item Wb 114); (Item Wb 105); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 121); (Item Wb 44); (Item Wb 32); (Item Wb 99); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 105); (Item Wb 122); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e56 : item :=
  (IData (a "hello#str.56") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e57 : item :=
  (IData (a "hello#str.57") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 32); (Item Wb 45); (Item Wb 116); (Item Wb 44); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 100); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 100); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e58 : item :=
  (IData (a "hello#str.58") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 32); (Item Wb 45); (Item Wb 103); (Item Wb 44); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 61); (Item Wb 84); (Item Wb 69); (Item Wb 88); (Item Wb 84); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 84); (Item Wb 69); (Item Wb 88); (Item Wb 84); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 32); (Item Wb 116); (Item Wb 104); (Item Wb 101); (Item Wb 32); (Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 109); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e59 : item :=
  (IData (a "hello#str.59") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 115); (Item Wb 112); (Item Wb 108); (Item Wb 97); (Item Wb 121); (Item Wb 32); (Item Wb 116); (Item Wb 104); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e60 : item :=
  (IData (a "hello#str.60") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 32); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 109); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e61 : item :=
  (IData (a "hello#str.61") (LRo (a "local")) 1 [(Item Wb 101); (Item Wb 110); (Item Wb 95); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e62 : item :=
  (IData (a "hello#str.62") (LRo (a "local")) 1 (app [(Item Wb 82); (Item Wb 101); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 103); (Item Wb 115); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 60); (Item Wb 104); (Item Wb 116); (Item Wb 116); (Item Wb 112)] [(Item Wb 115); (Item Wb 58); (Item Wb 47); (Item Wb 47); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 106); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 46); (Item Wb 111); (Item Wb 114); (Item Wb 103); (Item Wb 47); (Item Wb 116); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 47); (Item Wb 62); (Item Wb 10); (Item Wb 0)])).

Definition hello_image_item_hello'23str'2e63 : item :=
  (IData (a "hello#str.63") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 78); (Item Wb 85); (Item Wb 32); (Item Wb 72); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e65 : item :=
  (IData (a "hello#str.65") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 114); (Item Wb 101); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e66 : item :=
  (IData (a "hello#str.66") (LRo (a "local")) 1 [(Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 100); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e67 : item :=
  (IData (a "hello#str.67") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e68 : item :=
  (IData (a "hello#str.68") (LRo (a "local")) 1 [(Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e69 : item :=
  (IData (a "hello#str.69") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 58); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e70 : item :=
  (IData (a "hello#str.70") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e71 : item :=
  (IData (a "hello#str.71") (LRo (a "local")) 1 [(Item Wb 50); (Item Wb 46); (Item Wb 49); (Item Wb 50); (Item Wb 46); (Item Wb 51); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e72 : item :=
  (IData (a "hello#str.72") (LRo (a "local")) 1 [(Item Wb 75); (Item Wb 97); (Item Wb 114); (Item Wb 108); (Item Wb 32); (Item Wb 66); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e73 : item :=
  (IData (a "hello#str.73") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 97); (Item Wb 109); (Item Wb 105); (Item Wb 32); (Item Wb 75); (Item Wb 101); (Item Wb 114); (Item Wb 111); (Item Wb 108); (Item Wb 97); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e74 : item :=
  (IData (a "hello#str.74") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 105); (Item Wb 109); (Item Wb 32); (Item Wb 77); (Item Wb 101); (Item Wb 121); (Item Wb 101); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e75 : item :=
  (IData (a "hello#str.75") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 117); (Item Wb 98); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 84); (Item Wb 104); (Item Wb 111); (Item Wb 109); (Item Wb 97); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e76 : item :=
  (IData (a "hello#str.76") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 44); (Item Wb 32); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 108); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e77 : item :=
  (IData (a "hello#str.77") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e78 : item :=
  (IData (a "hello#str.78") (LRo (a "local")) 1 [(Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e79 : item :=
  (IData (a "hello#str.79") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 104); (Item Wb 101); (Item Wb 108); (Item Wb 112); (Item Wb 39); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 109); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 46); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e80 : item :=
  (IData (a "hello#str.80") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item_hello'23str'2e81 : item :=
  (IData (a "hello#str.81") (LRo (a "local")) 1 [(Item Wb 72); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 44); (Item Wb 32); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 108); (Item Wb 100); (Item Wb 33); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e82 : item :=
  (IData (a "hello#str.82") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 109); (Item Wb 117); (Item Wb 108); (Item Wb 116); (Item Wb 105); (Item Wb 98); (Item Wb 121); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_hello'23str'2e83 : item :=
  (IData (a "hello#str.83") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 108); (Item Ww 115); (Item Ww 10); (Item Ww 0)]).

Definition hello_image_item_glibc___libc_assert_fail'23str'2e21 : item :=
  (IData (a "glibc___libc_assert_fail#str.21") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc___libc_assert_fail'23str'2e22 : item :=
  (IData (a "glibc___libc_assert_fail#str.22") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 32); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 40); (Item Wb 37); (Item Wb 115); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item___errno_location : item :=
  (IAlias (a "__errno_location") (a "export") (a "__GI___errno_location")).

Definition hello_image_item___libc_errno : item :=
  (IAlias (a "__libc_errno") (a "export") (a "errno")).

Definition hello_image_item_errno : item :=
  (IData (a "errno") (LTls (a "export")) 4 [(Zero 4)]).

Definition hello_image_item___ctype32_b : item :=
  (IData (a "__ctype32_b") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_class32") 0)]).

Definition hello_image_item___ctype32_tolower : item :=
  (IData (a "__ctype32_tolower") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_tolower") 512)]).

Definition hello_image_item___ctype32_toupper : item :=
  (IData (a "__ctype32_toupper") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_toupper") 512)]).

Definition hello_image_item___ctype_b : item :=
  (IData (a "__ctype_b") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_class") 256)]).

Definition hello_image_item___ctype_tolower : item :=
  (IData (a "__ctype_tolower") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_tolower") 512)]).

Definition hello_image_item___ctype_toupper : item :=
  (IData (a "__ctype_toupper") LExport 8 [(Sym (a "_nl_C_LC_CTYPE_toupper") 512)]).

Definition hello_image_item___libc_tsd_CTYPE_B : item :=
  (IData (a "__libc_tsd_CTYPE_B") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_class") 256)]).

Definition hello_image_item___libc_tsd_CTYPE_TOLOWER : item :=
  (IData (a "__libc_tsd_CTYPE_TOLOWER") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_tolower") 512)]).

Definition hello_image_item___libc_tsd_CTYPE_TOUPPER : item :=
  (IData (a "__libc_tsd_CTYPE_TOUPPER") (LTls (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE_toupper") 512)]).

Definition hello_image_item_glibc_chk_fail'23str'2e134 : item :=
  (IData (a "glibc_chk_fail#str.134") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 111); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 102); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_fortify_fail'23str'2e19 : item :=
  (IData (a "glibc_fortify_fail#str.19") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_fortify_fail'23str'2e20 : item :=
  (IData (a "glibc_fortify_fail#str.20") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 58); (Item Wb 32); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 109); (Item Wb 105); (Item Wb 110); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_readonly_area_fallback'23str'2e252 : item :=
  (IData (a "glibc_readonly_area_fallback#str.252") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 47); (Item Wb 115); (Item Wb 101); (Item Wb 108); (Item Wb 102); (Item Wb 47); (Item Wb 109); (Item Wb 97); (Item Wb 112); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_readonly_area_fallback'23str'2e253 : item :=
  (IData (a "glibc_readonly_area_fallback#str.253") (LRo (a "local")) 1 [(Item Wb 114); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item___libc_stack_end : item :=
  (IData (a "__libc_stack_end") LExport 8 [(Zero 8)]).

Definition hello_image_item__dl_auxv : item :=
  (IData (a "_dl_auxv") LExport 8 [(Zero 8)]).

Definition hello_image_item__dl_clktck : item :=
  (IData (a "_dl_clktck") LExport 4 [(Zero 4)]).

Definition hello_image_item__dl_debug_mask : item :=
  (IData (a "_dl_debug_mask") LExport 4 [(Zero 4)]).

Definition hello_image_item__dl_hwcap : item :=
  (IData (a "_dl_hwcap") LExport 8 [(Zero 8)]).

Definition hello_image_item__dl_hwcap2 : item :=
  (IData (a "_dl_hwcap2") LExport 8 [(Zero 8)]).

Definition hello_image_item__dl_minsigstacksize : item :=
  (IData (a "_dl_minsigstacksize") LExport 8 [(Item Wl 0)]).

Definition hello_image_item__dl_pagesize : item :=
  (IData (a "_dl_pagesize") LExport 8 [(Item Wl 4096)]).

Definition hello_image_item__dl_platform : item :=
  (IData (a "_dl_platform") LExport 8 [(Zero 8)]).

Definition hello_image_item__dl_thp_mode : item :=
  (IData (a "_dl_thp_mode") LExport 4 [(Zero 4)]).

Definition hello_image_item__dl_x86_cpu_features : item :=
  (IData (a "_dl_x86_cpu_features") LExport 8 [(Zero 528)]).

Definition hello_image_item__dl_x86_feature_control : item :=
  (IData (a "_dl_x86_feature_control") LExport 4 [(Item Wb 0); (Zero 3)]).

Definition hello_image_item_glibc_dl_tunables'23tunable_list : item :=
  (IData (a "glibc_dl_tunables#tunable_list") LLocal 8 (app (app (app [(Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 104; 119; 99; 97; 112; 115]); (Zero 32); (Item Ww 3); (Zero 4); (Item Wl 0); (Item Wl 0); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 112; 108; 116; 95; 114; 101; 119; 114; 105; 116; 101]); (Zero 27); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 2); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 112; 114; 101; 102; 101; 114; 95; 109; 97; 112; 95; 51; 50; 98; 105; 116; 95; 101; 120; 101; 99]); (Zero 17); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [76; 68; 95; 80; 82; 69; 70; 69; 82; 95; 77; 65; 80; 95; 51; 50; 66; 73; 84; 95; 69; 88; 69; 67]); (Zero 6); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 100; 97; 116; 97; 95; 99; 97; 99; 104; 101; 95; 115; 105; 122; 101]); (Zero 19); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 105; 98; 116]); (Zero 31); (Item Ww 3); (Zero 4); (Item Wl 0); (Item Wl 0); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0])] [(Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 109; 101; 109; 115; 101; 116; 95; 110; 111; 110; 95; 116; 101; 109; 112; 111; 114; 97; 108; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 5); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 110; 111; 110; 95; 116; 101; 109; 112; 111; 114; 97; 108; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 12); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 114; 101; 112; 95; 109; 111; 118; 115; 98; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 15); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 114; 101; 112; 95; 115; 116; 111; 115; 98; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 15); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl (-1)); (Item Wl 2048); (Zero 8); (Item Wl 2048); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 115; 104; 97; 114; 101; 100; 95; 99; 97; 99; 104; 101; 95; 115; 105; 122; 101]); (Zero 17); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1))]) (app [(Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 99; 112; 117; 46; 120; 56; 54; 95; 115; 104; 115; 116; 107]); (Zero 29); (Item Ww 3); (Zero 4); (Item Wl 0); (Item Wl 0); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 101; 108; 102; 46; 116; 104; 112]); (Zero 35); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 103; 109; 111; 110; 46; 109; 97; 120; 97; 114; 99; 115]); (Zero 30); (Item Ww 0); (Zero 4); (Item Wl 50); (Item Wl 2147483647); (Item Wl 1048576); (Zero 8); (Item Wl 1048576); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 103; 109; 111; 110; 46; 109; 105; 110; 97; 114; 99; 115]); (Zero 30); (Item Ww 0); (Zero 4); (Item Wl 50); (Item Wl 2147483647); (Item Wl 50); (Zero 8); (Item Wl 50); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0])] [(Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 97; 114; 101; 110; 97; 95; 109; 97; 120]); (Zero 26); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 65; 82; 69; 78; 65; 95; 77; 65; 88]); (Zero 14); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 97; 114; 101; 110; 97; 95; 116; 101; 115; 116]); (Zero 25); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 65; 82; 69; 78; 65; 95; 84; 69; 83; 84]); (Zero 13); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 99; 104; 101; 99; 107]); (Zero 30); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 3); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 67; 72; 69; 67; 75; 95]); (Zero 17); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 104; 117; 103; 101; 116; 108; 98]); (Zero 28); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 109; 109; 97; 112; 95; 109; 97; 120]); (Zero 27); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 2147483647); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 77; 77; 65; 80; 95; 77; 65; 88; 95])])) (app (app [(Zero 14); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 109; 109; 97; 112; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 21); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 77; 77; 65; 80; 95; 84; 72; 82; 69; 83; 72; 79; 76; 68; 95]); (Zero 8); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 109; 120; 102; 97; 115; 116]); (Zero 29); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 112; 101; 114; 116; 117; 114; 98]); (Zero 28); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 255); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 80; 69; 82; 84; 85; 82; 66; 95]); (Zero 15); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 116; 99; 97; 99; 104; 101; 95; 99; 111; 117; 110; 116]); (Zero 23); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 116; 99; 97; 99; 104; 101; 95; 109; 97; 120]); (Zero 25); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0)] [(Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 116; 111; 112; 95; 112; 97; 100]); (Zero 28); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Item Wl 131072); (Zero 8); (Item Wl 131072); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 84; 79; 80; 95; 80; 65; 68; 95]); (Zero 15); (Str [103; 108; 105; 98; 99; 46; 109; 97; 108; 108; 111; 99; 46; 116; 114; 105; 109; 95; 116; 104; 114; 101; 115; 104; 111; 108; 100]); (Zero 21); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [77; 65; 76; 76; 79; 67; 95; 84; 82; 73; 77; 95; 84; 72; 82; 69; 83; 72; 79; 76; 68; 95]); (Zero 8); (Str [103; 108; 105; 98; 99; 46; 109; 101; 109; 46; 100; 101; 99; 111; 114; 97; 116; 101; 95; 109; 97; 112; 115]); (Zero 25); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Zero 32); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 112; 116; 104; 114; 101; 97; 100; 46; 109; 117; 116; 101; 120; 95; 115; 112; 105; 110; 95; 99; 111; 117; 110; 116]); (Zero 18); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 32767); (Item Wl 100); (Zero 8); (Item Wl 100); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 112; 116; 104; 114; 101; 97; 100; 46; 114; 115; 101; 113]); (Zero 30); (Item Ww 0)]) (app [(Zero 4); (Item Wl 0); (Item Wl 1); (Item Wl 1); (Zero 8); (Item Wl 1); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 112; 116; 104; 114; 101; 97; 100; 46; 115; 116; 97; 99; 107; 95; 99; 97; 99; 104; 101; 95; 115; 105; 122; 101]); (Zero 18); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Item Wl 41943040); (Zero 8); (Item Wl 41943040); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 112; 116; 104; 114; 101; 97; 100; 46; 115; 116; 97; 99; 107; 95; 104; 117; 103; 101; 116; 108; 98]); (Zero 21); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Item Wl 1); (Zero 8); (Item Wl 1); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 100; 121; 110; 97; 109; 105; 99; 95; 115; 111; 114; 116]); (Zero 25); (Item Ww 0); (Zero 4); (Item Wl 1); (Item Wl 2); (Item Wl 2); (Zero 8); (Item Wl 2); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 101; 110; 97; 98; 108; 101; 95; 115; 101; 99; 117; 114; 101])] [(Zero 24); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 1); (Item Wl 0); (Zero 8); (Item Wl 0); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 101; 120; 101; 99; 115; 116; 97; 99; 107]); (Zero 28); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Wl 2); (Item Wl 1); (Zero 8); (Item Wl 1); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 110; 110; 115]); (Zero 34); (Item Ww 2); (Zero 4); (Item Wl 1); (Item Wl 16); (Item Wl 4); (Zero 8); (Item Wl 4); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29); (Str [103; 108; 105; 98; 99; 46; 114; 116; 108; 100; 46; 111; 112; 116; 105; 111; 110; 97; 108; 95; 115; 116; 97; 116; 105; 99; 95; 116; 108; 115]); (Zero 18); (Item Ww 2); (Zero 4); (Item Wl 0); (Item Wl (-1)); (Item Wl 512); (Zero 8); (Item Wl 512); (Zero 8); (Item Wb 0); (Item Wb 0); (Str [0]); (Zero 29)])))).

Definition hello_image_item___libc_enable_secure : item :=
  (IData (a "__libc_enable_secure") LExport 4 [(Item Ww 1)]).

Definition hello_image_item_glibc_gconv'23str'2e269 : item :=
  (IData (a "glibc_gconv#str.269") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 114); (Item Wb 114); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 105); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv'23str'2e270 : item :=
  (IData (a "glibc_gconv#str.270") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv'23str'2e271 : item :=
  (IData (a "glibc_gconv#str.271") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv'23str'2e272 : item :=
  (IData (a "glibc_gconv#str.272") (LRo (a "local")) 1 [(Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 42); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23map : item :=
  (IData (a "glibc_gconv_builtin#map") (LRo (a "local")) 8 (app [(Sym (a "glibc_gconv_builtin#str.247") 0); (Sym (a "__gconv_transform_internal_ucs4") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.248") 0); (Sym (a "__gconv_transform_ucs4_internal") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.249") 0); (Sym (a "__gconv_transform_internal_ucs4le") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.250") 0); (Sym (a "__gconv_transform_ucs4le_internal") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.251") 0); (Sym (a "__gconv_transform_internal_utf8") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 1); (Item Wb 6); (Zero 4); (Sym (a "glibc_gconv_builtin#str.252") 0); (Sym (a "__gconv_transform_utf8_internal") 0); (Sym (a "__gconv_btwoc_ascii") 0); (Item Wb 1); (Item Wb 6); (Item Wb 4); (Item Wb 4); (Zero 4)] [(Sym (a "glibc_gconv_builtin#str.253") 0); (Sym (a "__gconv_transform_ucs2_internal") 0); (Item Wl 0); (Item Wb 2); (Item Wb 2); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.254") 0); (Sym (a "__gconv_transform_internal_ucs2") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 2); (Item Wb 2); (Zero 4); (Sym (a "glibc_gconv_builtin#str.255") 0); (Sym (a "__gconv_transform_ascii_internal") 0); (Sym (a "__gconv_btwoc_ascii") 0); (Item Wb 1); (Item Wb 1); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.256") 0); (Sym (a "__gconv_transform_internal_ascii") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 1); (Item Wb 1); (Zero 4); (Sym (a "glibc_gconv_builtin#str.257") 0); (Sym (a "__gconv_transform_ucs2reverse_internal") 0); (Item Wl 0); (Item Wb 2); (Item Wb 2); (Item Wb 4); (Item Wb 4); (Zero 4); (Sym (a "glibc_gconv_builtin#str.258") 0); (Sym (a "__gconv_transform_internal_ucs2reverse") 0); (Item Wl 0); (Item Wb 4); (Item Wb 4); (Item Wb 2); (Item Wb 2); (Zero 4)])).

Definition hello_image_item_glibc_gconv_builtin'23str'2e244 : item :=
  (IData (a "glibc_gconv_builtin#str.244") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 40); (Item Wb 109); (Item Wb 97); (Item Wb 112); (Item Wb 41); (Item Wb 32); (Item Wb 47); (Item Wb 32); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 111); (Item Wb 102); (Item Wb 32); (Item Wb 40); (Item Wb 109); (Item Wb 97); (Item Wb 112); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 41); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e245 : item :=
  (IData (a "glibc_gconv_builtin#str.245") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 105); (Item Wb 108); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e246 : item :=
  (IData (a "glibc_gconv_builtin#str.246") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 95); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 105); (Item Wb 108); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 95); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e247 : item :=
  (IData (a "glibc_gconv_builtin#str.247") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 52); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e248 : item :=
  (IData (a "glibc_gconv_builtin#str.248") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 52); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e249 : item :=
  (IData (a "glibc_gconv_builtin#str.249") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 52); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e250 : item :=
  (IData (a "glibc_gconv_builtin#str.250") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 52); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e251 : item :=
  (IData (a "glibc_gconv_builtin#str.251") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 116); (Item Wb 102); (Item Wb 56); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e252 : item :=
  (IData (a "glibc_gconv_builtin#str.252") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 116); (Item Wb 102); (Item Wb 56); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e253 : item :=
  (IData (a "glibc_gconv_builtin#str.253") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 50); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e254 : item :=
  (IData (a "glibc_gconv_builtin#str.254") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 50); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e255 : item :=
  (IData (a "glibc_gconv_builtin#str.255") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 97); (Item Wb 115); (Item Wb 99); (Item Wb 105); (Item Wb 105); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e256 : item :=
  (IData (a "glibc_gconv_builtin#str.256") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 97); (Item Wb 115); (Item Wb 99); (Item Wb 105); (Item Wb 105); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e257 : item :=
  (IData (a "glibc_gconv_builtin#str.257") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 50); (Item Wb 114); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_builtin'23str'2e258 : item :=
  (IData (a "glibc_gconv_builtin#str.258") (LRo (a "local")) 1 [(Item Wb 61); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 45); (Item Wb 62); (Item Wb 117); (Item Wb 99); (Item Wb 115); (Item Wb 50); (Item Wb 114); (Item Wb 101); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_cache'23cache_malloced : item :=
  (IData (a "glibc_gconv_cache#cache_malloced") LLocal 4 [(Zero 4)]).

Definition hello_image_item_glibc_gconv_cache'23cache_size : item :=
  (IData (a "glibc_gconv_cache#cache_size") LLocal 8 [(Zero 8)]).

Definition hello_image_item_glibc_gconv_cache'23gconv_cache : item :=
  (IData (a "glibc_gconv_cache#gconv_cache") LLocal 8 [(Zero 8)]).

Definition hello_image_item_glibc_gconv_cache'23str'2e281 : item :=
  (IData (a "glibc_gconv_cache#str.281") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 80); (Item Wb 65); (Item Wb 84); (Item Wb 72); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_cache'23str'2e282 : item :=
  (IData (a "glibc_gconv_cache#str.282") (LRo (a "local")) 1 (app [(Item Wb 47); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 101); (Item Wb 47); (Item Wb 55); (Item Wb 104); (Item Wb 104); (Item Wb 52); (Item Wb 53); (Item Wb 99); (Item Wb 118); (Item Wb 119); (Item Wb 122); (Item Wb 114); (Item Wb 113); (Item Wb 121); (Item Wb 113); (Item Wb 118); (Item Wb 112); (Item Wb 107); (Item Wb 110); (Item Wb 110); (Item Wb 108); (Item Wb 106); (Item Wb 56); (Item Wb 50); (Item Wb 118); (Item Wb 114); (Item Wb 113); (Item Wb 100); (Item Wb 109); (Item Wb 103); (Item Wb 54); (Item Wb 107); (Item Wb 120); (Item Wb 119); (Item Wb 45); (Item Wb 102); (Item Wb 105)] [(Item Wb 108); (Item Wb 99); (Item Wb 45); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 45); (Item Wb 112); (Item Wb 112); (Item Wb 45); (Item Wb 50); (Item Wb 46); (Item Wb 52); (Item Wb 52); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 47); (Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 47); (Item Wb 103); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 118); (Item Wb 45); (Item Wb 109); (Item Wb 111); (Item Wb 100); (Item Wb 117); (Item Wb 108); (Item Wb 101); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 0)])).

Definition hello_image_item_glibc_gconv_cache'23str'2e284 : item :=
  (IData (a "glibc_gconv_cache#str.284") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 69); (Item Wb 82); (Item Wb 78); (Item Wb 65); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_charset'23str'2e244 : item :=
  (IData (a "glibc_gconv_charset#str.244") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 84); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 83); (Item Wb 76); (Item Wb 73); (Item Wb 84); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_charset'23str'2e245 : item :=
  (IData (a "glibc_gconv_charset#str.245") (LRo (a "local")) 1 [(Item Wb 44); (Item Wb 84); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 83); (Item Wb 76); (Item Wb 73); (Item Wb 84); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_charset'23str'2e246 : item :=
  (IData (a "glibc_gconv_charset#str.246") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 73); (Item Wb 71); (Item Wb 78); (Item Wb 79); (Item Wb 82); (Item Wb 69); (Item Wb 0)]).

Definition hello_image_item_glibc_gconv_charset'23str'2e247 : item :=
  (IData (a "glibc_gconv_charset#str.247") (LRo (a "local")) 1 [(Item Wb 44); (Item Wb 73); (Item Wb 71); (Item Wb 78); (Item Wb 79); (Item Wb 82); (Item Wb 69); (Item Wb 0)]).

Definition hello_image_item___gconv_max_path_elem_len : item :=
  (IData (a "__gconv_max_path_elem_len") LExport 8 [(Zero 8)]).

Definition hello_image_item___gconv_path_elem : item :=
  (IData (a "__gconv_path_elem") LExport 8 [(Zero 8)]).

Definition hello_image_item___gconv_path_envvar : item :=
  (IData (a "__gconv_path_envvar") LExport 8 [(Zero 8)]).
