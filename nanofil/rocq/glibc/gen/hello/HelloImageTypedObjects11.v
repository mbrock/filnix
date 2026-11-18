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

Definition hello_image_item__itowa_upper_digits : item :=
  (IData (a "_itowa_upper_digits") (LRo (a "export")) 4 [(Str (app (app [48; 0; 0; 0; 49; 0; 0; 0; 50; 0; 0; 0; 51; 0; 0; 0; 52; 0; 0; 0; 53; 0; 0; 0; 54; 0; 0; 0; 55; 0; 0; 0; 56; 0; 0; 0] [57; 0; 0; 0; 65; 0; 0; 0; 66; 0; 0; 0; 67; 0; 0; 0; 68; 0; 0; 0; 69; 0; 0; 0; 70; 0; 0; 0; 71; 0; 0; 0; 72; 0; 0; 0]) (app [73; 0; 0; 0; 74; 0; 0; 0; 75; 0; 0; 0; 76; 0; 0; 0; 77; 0; 0; 0; 78; 0; 0; 0; 79; 0; 0; 0; 80; 0; 0; 0; 81; 0; 0; 0] [82; 0; 0; 0; 83; 0; 0; 0; 84; 0; 0; 0; 85; 0; 0; 0; 86; 0; 0; 0; 87; 0; 0; 0; 88; 0; 0; 0; 89; 0; 0; 0; 90; 0; 0; 0])))]).

Definition hello_image_item_printf : item :=
  (IAlias (a "printf") (a "export") (a "__printf")).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e266 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.266") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e267 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.267") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e268 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.268") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 99); (Item Wb 111); (Item Wb 109); (Item Wb 109); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e269 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.269") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e270 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.270") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_as_file'23str'2e271 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.271") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_flush'23str'2e39 : item :=
  (IData (a "glibc_printf_buffer_flush#str.39") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_flush'23str'2e40 : item :=
  (IData (a "glibc_printf_buffer_flush#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_flush'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_flush#str.41") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_pad_1'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_pad_1#str.41") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_pad_1'23str'2e42 : item :=
  (IData (a "glibc_printf_buffer_pad_1#str.42") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 49); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_pad_1'23str'2e43 : item :=
  (IData (a "glibc_printf_buffer_pad_1#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_putc_1'23str'2e39 : item :=
  (IData (a "glibc_printf_buffer_putc_1#str.39") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_putc_1'23str'2e40 : item :=
  (IData (a "glibc_printf_buffer_putc_1#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 99); (Item Wb 95); (Item Wb 49); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_putc_1'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_putc_1#str.41") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 99); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_to_file'23str'2e266 : item :=
  (IData (a "glibc_printf_buffer_to_file#str.266") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 46); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 102); (Item Wb 112); (Item Wb 45); (Item Wb 62); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_to_file'23str'2e267 : item :=
  (IData (a "glibc_printf_buffer_to_file#str.267") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 116); (Item Wb 111); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_to_file'23str'2e268 : item :=
  (IData (a "glibc_printf_buffer_to_file#str.268") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 95); (Item Wb 116); (Item Wb 111); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_write'23str'2e41 : item :=
  (IData (a "glibc_printf_buffer_write#str.41") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_write'23str'2e42 : item :=
  (IData (a "glibc_printf_buffer_write#str.42") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_buffer_write'23str'2e43 : item :=
  (IData (a "glibc_printf_buffer_write#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e295 : item :=
  (IData (a "glibc_printf_fp#str.295") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 65); (Item Wb 78); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e296 : item :=
  (IData (a "glibc_printf_fp#str.296") (LRo (a "local")) 1 [(Item Wb 110); (Item Wb 97); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e297 : item :=
  (IData (a "glibc_printf_fp#str.297") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 78); (Item Wb 70); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e298 : item :=
  (IData (a "glibc_printf_fp#str.298") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e301 : item :=
  (IData (a "glibc_printf_fp#str.301") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 32); (Item Wb 62); (Item Wb 32); (Item Wb 38); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 105); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 95); (Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 49); (Item Wb 48); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e302 : item :=
  (IData (a "glibc_printf_fp#str.302") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e303 : item :=
  (IData (a "glibc_printf_fp#str.303") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e304 : item :=
  (IData (a "glibc_printf_fp#str.304") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 121); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 49); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 40); (Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 91); (Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 45); (Item Wb 32); (Item Wb 50); (Item Wb 93); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 41); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e305 : item :=
  (IData (a "glibc_printf_fp#str.305") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 38); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 105); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 95); (Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 49); (Item Wb 48); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e306 : item :=
  (IData (a "glibc_printf_fp#str.306") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 99); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 45); (Item Wb 62); (Item Wb 112); (Item Wb 95); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 111); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e307 : item :=
  (IData (a "glibc_printf_fp#str.307") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 121); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 46); (Item Wb 116); (Item Wb 109); (Item Wb 112); (Item Wb 91); (Item Wb 112); (Item Wb 46); (Item Wb 116); (Item Wb 109); (Item Wb 112); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 45); (Item Wb 32); (Item Wb 49); (Item Wb 93); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 50); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e308 : item :=
  (IData (a "glibc_printf_fp#str.308") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 91); (Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 45); (Item Wb 32); (Item Wb 49); (Item Wb 93); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 49); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e309 : item :=
  (IData (a "glibc_printf_fp#str.309") (LRo (a "local")) 1 (app [(Item Wb 48); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 112); (Item Wb 46); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 111); (Item Wb 110); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 112); (Item Wb 46); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 111); (Item Wb 110); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 51); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 112); (Item Wb 46)] [(Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 111); (Item Wb 110); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 43); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 95); (Item Wb 115); (Item Wb 104); (Item Wb 105); (Item Wb 102); (Item Wb 116); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 66); (Item Wb 73); (Item Wb 84); (Item Wb 83); (Item Wb 95); (Item Wb 80); (Item Wb 69); (Item Wb 82); (Item Wb 95); (Item Wb 77); (Item Wb 80); (Item Wb 95); (Item Wb 76); (Item Wb 73); (Item Wb 77); (Item Wb 66); (Item Wb 0)])).

Definition hello_image_item_glibc_printf_fp'23str'2e310 : item :=
  (IData (a "glibc_printf_fp#str.310") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 46); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 110); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 100); (Item Wb 105); (Item Wb 103); (Item Wb 95); (Item Wb 109); (Item Wb 97); (Item Wb 120); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e311 : item :=
  (IData (a "glibc_printf_fp#str.311") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 99); (Item Wb 112); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 119); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 114); (Item Wb 116); (Item Wb 112); (Item Wb 32); (Item Wb 43); (Item Wb 32); (Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e312 : item :=
  (IData (a "glibc_printf_fp#str.312") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 114); (Item Wb 116); (Item Wb 112); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 39); (Item Wb 49); (Item Wb 39); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fp'23str'2e313 : item :=
  (IData (a "glibc_printf_fp#str.313") (LRo (a "local")) 1 [(Item Wb 48); (Item Wb 46); (Item Wb 48); (Item Wb 48); (Item Wb 48); (Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fphex'23str'2e287 : item :=
  (IData (a "glibc_printf_fphex#str.287") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 45); (Item Wb 62); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fphex'23str'2e288 : item :=
  (IData (a "glibc_printf_fphex#str.288") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 116); (Item Wb 100); (Item Wb 105); (Item Wb 111); (Item Wb 45); (Item Wb 99); (Item Wb 111); (Item Wb 109); (Item Wb 109); (Item Wb 111); (Item Wb 110); (Item Wb 47); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 104); (Item Wb 101); (Item Wb 120); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fphex'23str'2e289 : item :=
  (IData (a "glibc_printf_fphex#str.289") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 104); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fphex'23str'2e290 : item :=
  (IData (a "glibc_printf_fphex#str.290") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 65); (Item Wb 78); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fphex'23str'2e291 : item :=
  (IData (a "glibc_printf_fphex#str.291") (LRo (a "local")) 1 [(Item Wb 110); (Item Wb 97); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fphex'23str'2e292 : item :=
  (IData (a "glibc_printf_fphex#str.292") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 78); (Item Wb 70); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fphex'23str'2e293 : item :=
  (IData (a "glibc_printf_fphex#str.293") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 0)]).

Definition hello_image_item_glibc_printf_fphex'23str'2e295 : item :=
  (IData (a "glibc_printf_fphex#str.295") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 0)]).

Definition hello_image_item___printf_modifier_table : item :=
  (IData (a "__printf_modifier_table") LExport 8 [(Zero 8)]).

Definition hello_image_item___printf_arginfo_table : item :=
  (IData (a "__printf_arginfo_table") LExport 8 [(Zero 8)]).

Definition hello_image_item___printf_function_table : item :=
  (IData (a "__printf_function_table") LExport 8 [(Zero 8)]).

Definition hello_image_item___printf_va_arg_table : item :=
  (IData (a "__printf_va_arg_table") LExport 8 [(Zero 8)]).

Definition hello_image_item_glibc_translated_number_width'23str'2e45 : item :=
  (IData (a "glibc_translated_number_width#str.45") (LRo (a "local")) 1 [(Item Wb 39); (Item Wb 48); (Item Wb 39); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 42); (Item Wb 112); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 42); (Item Wb 112); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 39); (Item Wb 57); (Item Wb 39); (Item Wb 0)]).

Definition hello_image_item_glibc_translated_number_width'23str'2e46 : item :=
  (IData (a "glibc_translated_number_width#str.46") (LRo (a "local")) 1 [(Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 95); (Item Wb 110); (Item Wb 117); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 116); (Item Wb 104); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_translated_number_width'23str'2e47 : item :=
  (IData (a "glibc_translated_number_width#str.47") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 108); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 95); (Item Wb 110); (Item Wb 117); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 116); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep0_jumps'2e277 : item :=
  (IData (a "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 1); (Item Ww 2); (Item Ww 3); (Item Ww 4); (Item Ww 5); (Item Ww 6); (Item Ww 7); (Item Ww 8); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 29); (Item Ww 30); (Item Ww 31)]).

Definition hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep1_jumps'2e278 : item :=
  (IData (a "glibc_vfprintf_internal#__printf_buffer.step1_jumps.278") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 0); (Item Ww 30); (Item Ww 31)]).

Definition hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep2_jumps'2e279 : item :=
  (IData (a "glibc_vfprintf_internal#__printf_buffer.step2_jumps.279") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 0); (Item Ww 30); (Item Ww 31)]).

Definition hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep3a_jumps'2e280 : item :=
  (IData (a "glibc_vfprintf_internal#__printf_buffer.step3a_jumps.280") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 32); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 23); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep3b_jumps'2e281 : item :=
  (IData (a "glibc_vfprintf_internal#__printf_buffer.step3b_jumps.281") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 12); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23__printf_buffer'2estep4_jumps'2e282 : item :=
  (IData (a "glibc_vfprintf_internal#__printf_buffer.step4_jumps.282") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23jump_table : item :=
  (IData (a "glibc_vfprintf_internal#jump_table") (LRo (a "local")) 1 [(Str (app [1; 0; 0; 4; 0; 14; 0; 6; 0; 0; 7; 2; 0; 3; 9; 0; 5; 8; 8; 8; 8; 8; 8; 8; 8; 8; 0; 0; 0; 0; 0; 0; 0; 26; 30; 25; 0; 19; 19; 19; 0; 29; 0; 0; 12] [0; 0; 0; 0; 0; 0; 21; 0; 0; 0; 0; 18; 0; 13; 0; 0; 0; 0; 0; 0; 26; 30; 20; 15; 19; 19; 19; 10; 15; 28; 0; 11; 24; 23; 17; 22; 12; 0; 21; 27; 16; 0; 31; 18; 0; 13]))]).

Definition hello_image_item_glibc_vfprintf_internal'23null : item :=
  (IData (a "glibc_vfprintf_internal#null") (LRo (a "local")) 1 [(Str [40; 110; 117; 108; 108; 41]); (Zero 1)]).

Definition hello_image_item_glibc_vfprintf_internal'23printf_positional'2estep4_jumps'2e294 : item :=
  (IData (a "glibc_vfprintf_internal#printf_positional.step4_jumps.294") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 1); (Item Ww 2); (Item Ww 3); (Item Ww 4); (Item Ww 5); (Item Ww 6); (Item Ww 7); (Item Ww 8); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23str'2e284 : item :=
  (IData (a "glibc_vfprintf_internal#str.284") (LRo (a "local")) 1 [(Item Wb 40); (Item Wb 110); (Item Wb 105); (Item Wb 108); (Item Wb 41); (Item Wb 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23str'2e285 : item :=
  (IData (a "glibc_vfprintf_internal#str.285") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 37); (Item Wb 110); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 103); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 115); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23str'2e286 : item :=
  (IData (a "glibc_vfprintf_internal#str.286") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 102); (Item Wb 115); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 117); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23str'2e289 : item :=
  (IData (a "glibc_vfprintf_internal#str.289") (LRo (a "local")) 4 [(Item Ww 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23str'2e290 : item :=
  (IData (a "glibc_vfprintf_internal#str.290") (LRo (a "local")) 1 [(Item Wb 40); (Item Wb 109); (Item Wb 111); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 97); (Item Wb 103); (Item Wb 115); (Item Wb 32); (Item Wb 38); (Item Wb 32); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 70); (Item Wb 95); (Item Wb 70); (Item Wb 79); (Item Wb 82); (Item Wb 84); (Item Wb 73); (Item Wb 70); (Item Wb 89); (Item Wb 41); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23str'2e291 : item :=
  (IData (a "glibc_vfprintf_internal#str.291") (LRo (a "local")) 1 [(Item Wb 118); (Item Wb 102); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23str'2e292 : item :=
  (IData (a "glibc_vfprintf_internal#str.292") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 112); (Item Wb 111); (Item Wb 115); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_vfprintf_internal'23str'2e293 : item :=
  (IData (a "glibc_vfprintf_internal#str.293") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 78); (Item Wb 36); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep0_jumps'2e278 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 1); (Item Ww 2); (Item Ww 3); (Item Ww 4); (Item Ww 5); (Item Ww 6); (Item Ww 7); (Item Ww 8); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 29); (Item Ww 30); (Item Ww 31)]).

Definition hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep1_jumps'2e279 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step1_jumps.279") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 0); (Item Ww 30); (Item Ww 31)]).

Definition hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep2_jumps'2e280 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step2_jumps.280") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 27); (Item Ww 28); (Item Ww 0); (Item Ww 30); (Item Ww 31)]).

Definition hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep3a_jumps'2e281 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step3a_jumps.281") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 32); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 23); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep3b_jumps'2e282 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 12); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23__wprintf_buffer'2estep4_jumps'2e283 : item :=
  (IData (a "glibc_vfwprintf_internal#__wprintf_buffer.step4_jumps.283") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 15); (Item Ww 16); (Item Ww 17); (Item Ww 18); (Item Ww 19); (Item Ww 20); (Item Ww 21); (Item Ww 22); (Item Ww 23); (Item Ww 24); (Item Ww 25); (Item Ww 26); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 30); (Item Ww 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23jump_table : item :=
  (IData (a "glibc_vfwprintf_internal#jump_table") (LRo (a "local")) 1 [(Str (app [1; 0; 0; 4; 0; 14; 0; 6; 0; 0; 7; 2; 0; 3; 9; 0; 5; 8; 8; 8; 8; 8; 8; 8; 8; 8; 0; 0; 0; 0; 0; 0; 0; 26; 30; 25; 0; 19; 19; 19; 0; 29; 0; 0; 12] [0; 0; 0; 0; 0; 0; 21; 0; 0; 0; 0; 18; 0; 13; 0; 0; 0; 0; 0; 0; 26; 30; 20; 15; 19; 19; 19; 10; 15; 28; 0; 11; 24; 23; 17; 22; 12; 0; 21; 27; 16; 0; 31; 18; 0; 13]))]).

Definition hello_image_item_glibc_vfwprintf_internal'23null : item :=
  (IData (a "glibc_vfwprintf_internal#null") (LRo (a "local")) 4 [(Str [40; 0; 0; 0; 110; 0; 0; 0; 117; 0; 0; 0; 108; 0; 0; 0; 108; 0; 0; 0; 41; 0; 0; 0]); (Zero 4)]).

Definition hello_image_item_glibc_vfwprintf_internal'23printf_positional'2estep4_jumps'2e295 : item :=
  (IData (a "glibc_vfwprintf_internal#printf_positional.step4_jumps.295") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 1); (Item Ww 2); (Item Ww 3); (Item Ww 4); (Item Ww 5); (Item Ww 6); (Item Ww 7); (Item Ww 8); (Item Ww 9); (Item Ww 10); (Item Ww 11); (Item Ww 12); (Item Ww 13); (Item Ww 0); (Item Ww 0); (Item Ww 0); (Item Ww 14); (Item Ww 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23str'2e285 : item :=
  (IData (a "glibc_vfwprintf_internal#str.285") (LRo (a "local")) 4 [(Item Ww 40); (Item Ww 110); (Item Ww 105); (Item Ww 108); (Item Ww 41); (Item Ww 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23str'2e286 : item :=
  (IData (a "glibc_vfwprintf_internal#str.286") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 37); (Item Wb 110); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 97); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 115); (Item Wb 101); (Item Wb 103); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 115); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23str'2e287 : item :=
  (IData (a "glibc_vfwprintf_internal#str.287") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 102); (Item Wb 115); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 117); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23str'2e290 : item :=
  (IData (a "glibc_vfwprintf_internal#str.290") (LRo (a "local")) 4 [(Item Ww 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23str'2e291 : item :=
  (IData (a "glibc_vfwprintf_internal#str.291") (LRo (a "local")) 1 [(Item Wb 40); (Item Wb 109); (Item Wb 111); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 97); (Item Wb 103); (Item Wb 115); (Item Wb 32); (Item Wb 38); (Item Wb 32); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 78); (Item Wb 84); (Item Wb 70); (Item Wb 95); (Item Wb 70); (Item Wb 79); (Item Wb 82); (Item Wb 84); (Item Wb 73); (Item Wb 70); (Item Wb 89); (Item Wb 41); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23str'2e292 : item :=
  (IData (a "glibc_vfwprintf_internal#str.292") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 118); (Item Wb 102); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23str'2e293 : item :=
  (IData (a "glibc_vfwprintf_internal#str.293") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 112); (Item Wb 111); (Item Wb 115); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_vfwprintf_internal'23str'2e294 : item :=
  (IData (a "glibc_vfwprintf_internal#str.294") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 37); (Item Wb 78); (Item Wb 36); (Item Wb 32); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_as_file'23str'2e266 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.266") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_as_file'23str'2e267 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.267") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_as_file'23str'2e268 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.268") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 99); (Item Wb 111); (Item Wb 109); (Item Wb 109); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_as_file'23str'2e269 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.269") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_as_file'23str'2e270 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.270") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_as_file'23str'2e271 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.271") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_flush'23str'2e39 : item :=
  (IData (a "glibc_wprintf_buffer_flush#str.39") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_flush'23str'2e40 : item :=
  (IData (a "glibc_wprintf_buffer_flush#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_flush'23str'2e41 : item :=
  (IData (a "glibc_wprintf_buffer_flush#str.41") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 102); (Item Wb 108); (Item Wb 117); (Item Wb 115); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_pad_1'23str'2e41 : item :=
  (IData (a "glibc_wprintf_buffer_pad_1#str.41") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_pad_1'23str'2e42 : item :=
  (IData (a "glibc_wprintf_buffer_pad_1#str.42") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 49); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_pad_1'23str'2e43 : item :=
  (IData (a "glibc_wprintf_buffer_pad_1#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_putc_1'23str'2e39 : item :=
  (IData (a "glibc_wprintf_buffer_putc_1#str.39") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_putc_1'23str'2e40 : item :=
  (IData (a "glibc_wprintf_buffer_putc_1#str.40") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 99); (Item Wb 95); (Item Wb 49); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_putc_1'23str'2e41 : item :=
  (IData (a "glibc_wprintf_buffer_putc_1#str.41") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 99); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_write'23str'2e41 : item :=
  (IData (a "glibc_wprintf_buffer_write#str.41") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_write'23str'2e42 : item :=
  (IData (a "glibc_wprintf_buffer_write#str.42") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 47); (Item Wb 88); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_wprintf_buffer_write'23str'2e43 : item :=
  (IData (a "glibc_wprintf_buffer_write#str.43") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item___GI___abort_msg : item :=
  (IData (a "__GI___abort_msg") LExport 8 [(Zero 8)]).

Definition hello_image_item_glibc_abort'23str'2e268 : item :=
  (IData (a "glibc_abort#str.268") (LRo (a "local")) 1 [(Item Wb 97); (Item Wb 98); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 40); (Item Wb 51); (Item Wb 41); (Item Wb 32); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition hello_image_item_glibc_abort'23str'2e269 : item :=
  (IData (a "glibc_abort#str.269") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109)] [(Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110); (Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 104); (Item Wb 108); (Item Wb 116); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 104); (Item Wb 108); (Item Wb 116); (Item Wb 0)])).

Definition hello_image_item_abort : item :=
  (IAlias (a "abort") (a "export") (a "__GI_abort")).

Definition hello_image_item___exit_funcs : item :=
  (IData (a "__exit_funcs") LExport 8 [(Sym (a "glibc_cxa_atexit#initial") 0)]).

Definition hello_image_item___exit_funcs_lock : item :=
  (IData (a "__exit_funcs_lock") LExport 4 [(Zero 4)]).

Definition hello_image_item___new_exitfn_called : item :=
  (IData (a "__new_exitfn_called") LExport 8 [(Zero 8)]).

Definition hello_image_item_glibc_cxa_atexit'23initial : item :=
  (IData (a "glibc_cxa_atexit#initial") LLocal 8 [(Zero 1040)]).

Definition hello_image_item_glibc_cxa_atexit'23str'2e233 : item :=
  (IData (a "glibc_cxa_atexit#str.233") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 110); (Item Wb 99); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_cxa_atexit'23str'2e234 : item :=
  (IData (a "glibc_cxa_atexit#str.234") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 120); (Item Wb 97); (Item Wb 95); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_cxa_atexit'23str'2e235 : item :=
  (IData (a "glibc_cxa_atexit#str.235") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 95); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_cxa_atexit'23str'2e236 : item :=
  (IData (a "glibc_cxa_atexit#str.236") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 78); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 0)]).

Definition hello_image_item_glibc_cxa_atexit'23str'2e237 : item :=
  (IData (a "glibc_cxa_atexit#str.237") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 110); (Item Wb 101); (Item Wb 119); (Item Wb 95); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 116); (Item Wb 102); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item___cxa_atexit : item :=
  (IAlias (a "__cxa_atexit") (a "export") (a "__GI___cxa_atexit")).

Definition hello_image_item___exit_funcs_done : item :=
  (IData (a "__exit_funcs_done") LExport 1 [(Item Wb 0)]).

Definition hello_image_item_glibc_exit'23__exit_lock : item :=
  (IData (a "glibc_exit#__exit_lock") LLocal 8 [(Item Ww 0); (Item Ww 0); (Item Wl 0)]).

Definition hello_image_item_exit : item :=
  (IAlias (a "exit") (a "export") (a "__GI_exit")).
