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

Definition hello_image_item_glibc_mbsrtowcs_l'23str'2e272 : item :=
  (IData (a "glibc_mbsrtowcs_l#str.272") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 119); (Item Wb 99); (Item Wb 115); (Item Wb 95); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_mbsrtowcs_l'23str'2e273 : item :=
  (IData (a "glibc_mbsrtowcs_l#str.273") (LRo (a "local")) 1 [(Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 117); (Item Wb 108); (Item Wb 116); (Item Wb 32); (Item Wb 62); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_mbsrtowcs_l'23str'2e274 : item :=
  (IData (a "glibc_mbsrtowcs_l#str.274") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 116); (Item Wb 32); (Item Wb 40); (Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 46); (Item Wb 95); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 112); (Item Wb 41); (Item Wb 0)]).

Definition hello_image_item_glibc_mbsrtowcs_l'23str'2e275 : item :=
  (IData (a "glibc_mbsrtowcs_l#str.275") (LRo (a "local")) 1 (app (app [(Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 79); (Item Wb 75); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78)] [(Item Wb 86); (Item Wb 95); (Item Wb 69); (Item Wb 77); (Item Wb 80); (Item Wb 84); (Item Wb 89); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 76); (Item Wb 76); (Item Wb 69); (Item Wb 71)]) (app [(Item Wb 65); (Item Wb 76); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 67); (Item Wb 79); (Item Wb 77); (Item Wb 80); (Item Wb 76); (Item Wb 69); (Item Wb 84); (Item Wb 69)] [(Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 70); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 79); (Item Wb 85); (Item Wb 84); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 0)]))).

Definition hello_image_item_glibc_wcsrtombs'23state : item :=
  (IData (a "glibc_wcsrtombs#state") LLocal 4 [(Zero 8)]).

Definition hello_image_item_glibc_wcsrtombs'23str'2e270 : item :=
  (IData (a "glibc_wcsrtombs#str.270") (LRo (a "local")) 1 [(Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 46); (Item Wb 95); (Item Wb 95); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 91); (Item Wb 45); (Item Wb 49); (Item Wb 93); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 39); (Item Wb 92); (Item Wb 48); (Item Wb 39); (Item Wb 0)]).

Definition hello_image_item_glibc_wcsrtombs'23str'2e271 : item :=
  (IData (a "glibc_wcsrtombs#str.271") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 99); (Item Wb 115); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_wcsrtombs'23str'2e272 : item :=
  (IData (a "glibc_wcsrtombs#str.272") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 99); (Item Wb 115); (Item Wb 114); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_wcsrtombs'23str'2e273 : item :=
  (IData (a "glibc_wcsrtombs#str.273") (LRo (a "local")) 1 [(Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 46); (Item Wb 95); (Item Wb 95); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 110); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 32); (Item Wb 42); (Item Wb 41); (Item Wb 32); (Item Wb 100); (Item Wb 115); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_wcsrtombs'23str'2e274 : item :=
  (IData (a "glibc_wcsrtombs#str.274") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 109); (Item Wb 98); (Item Wb 115); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 116); (Item Wb 32); (Item Wb 40); (Item Wb 100); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 46); (Item Wb 95); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 112); (Item Wb 41); (Item Wb 0)]).

Definition hello_image_item_glibc_wcsrtombs'23str'2e275 : item :=
  (IData (a "glibc_wcsrtombs#str.275") (LRo (a "local")) 1 (app (app [(Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 79); (Item Wb 75); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78)] [(Item Wb 86); (Item Wb 95); (Item Wb 69); (Item Wb 77); (Item Wb 80); (Item Wb 84); (Item Wb 89); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 76); (Item Wb 76); (Item Wb 69); (Item Wb 71)]) (app [(Item Wb 65); (Item Wb 76); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 67); (Item Wb 79); (Item Wb 77); (Item Wb 80); (Item Wb 76); (Item Wb 69); (Item Wb 84); (Item Wb 69)] [(Item Wb 95); (Item Wb 73); (Item Wb 78); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 95); (Item Wb 95); (Item Wb 71); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 86); (Item Wb 95); (Item Wb 70); (Item Wb 85); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 79); (Item Wb 85); (Item Wb 84); (Item Wb 80); (Item Wb 85); (Item Wb 84); (Item Wb 0)]))).

Definition hello_image_item___x86_data_cache_size : item :=
  (IData (a "__x86_data_cache_size") LExport 8 [(Item Wl 32768)]).

Definition hello_image_item___x86_data_cache_size_half : item :=
  (IData (a "__x86_data_cache_size_half") LExport 8 [(Item Wl 16384)]).

Definition hello_image_item___x86_memset_non_temporal_threshold : item :=
  (IData (a "__x86_memset_non_temporal_threshold") LExport 8 [(Zero 8)]).

Definition hello_image_item___x86_rep_movsb_stop_threshold : item :=
  (IData (a "__x86_rep_movsb_stop_threshold") LExport 8 [(Zero 8)]).

Definition hello_image_item___x86_rep_movsb_threshold : item :=
  (IData (a "__x86_rep_movsb_threshold") LExport 8 [(Item Wl 2048)]).

Definition hello_image_item___x86_rep_stosb_threshold : item :=
  (IData (a "__x86_rep_stosb_threshold") LExport 8 [(Item Wl 2048)]).

Definition hello_image_item___x86_shared_cache_size : item :=
  (IData (a "__x86_shared_cache_size") LExport 8 [(Item Wl 1048576)]).

Definition hello_image_item___x86_shared_cache_size_half : item :=
  (IData (a "__x86_shared_cache_size_half") LExport 8 [(Item Wl 524288)]).

Definition hello_image_item___x86_shared_non_temporal_threshold : item :=
  (IData (a "__x86_shared_non_temporal_threshold") LExport 8 [(Zero 8)]).

Definition hello_image_item___x86_string_control : item :=
  (IData (a "__x86_string_control") LExport 4 [(Zero 4)]).

Definition hello_image_item__dl_x86_features_tlsdesc_state_size : item :=
  (IData (a "_dl_x86_features_tlsdesc_state_size") LExport 8 [(Zero 8)]).

Definition hello_image_item_glibc_libc_start'23intel_02_known : item :=
  (IData (a "glibc_libc_start#intel_02_known") (LRo (a "local")) 4 (app (app (app [(Item Wb 6); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 8192); (Item Wb 8); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 16384); (Item Wb 9); (Item Wb 4); (Item Wb 32); (Item Wb 0); (Item Ww 32768); (Item Wb 10); (Item Wb 2); (Item Wb 32); (Item Wb 3); (Item Ww 8192); (Item Wb 12); (Item Wb 4); (Item Wb 32); (Item Wb 3); (Item Ww 16384); (Item Wb 13); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 14); (Item Wb 6); (Item Wb 64); (Item Wb 3); (Item Ww 24576); (Item Wb 33); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 34); (Item Wb 4)] [(Item Wb 64); (Item Wb 9); (Item Ww 524288); (Item Wb 35); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 37); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 41); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 44); (Item Wb 8); (Item Wb 64); (Item Wb 3); (Item Ww 32768); (Item Wb 48); (Item Wb 8); (Item Wb 64); (Item Wb 0); (Item Ww 32768); (Item Wb 57); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 131072); (Item Wb 58); (Item Wb 6); (Item Wb 64); (Item Wb 6); (Item Ww 196608); (Item Wb 59); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 131072)]) (app [(Item Wb 60); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 61); (Item Wb 6); (Item Wb 64); (Item Wb 6); (Item Ww 393216); (Item Wb 62); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 63); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 65); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 131072); (Item Wb 66); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 262144); (Item Wb 67); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 524288); (Item Wb 68); (Item Wb 4); (Item Wb 32); (Item Wb 6); (Item Ww 1048576); (Item Wb 69); (Item Wb 4)] [(Item Wb 32); (Item Wb 6); (Item Ww 2097152); (Item Wb 70); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 71); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 72); (Item Wb 12); (Item Wb 64); (Item Wb 6); (Item Ww 3145728); (Item Wb 73); (Item Wb 16); (Item Wb 64); (Item Wb 6); (Item Ww 4194304); (Item Wb 74); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 6291456); (Item Wb 75); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 76); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 12582912); (Item Wb 77); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 16777216)])) (app (app [(Item Wb 78); (Item Wb 24); (Item Wb 64); (Item Wb 6); (Item Ww 6291456); (Item Wb 96); (Item Wb 8); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 102); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 8192); (Item Wb 103); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 16384); (Item Wb 104); (Item Wb 4); (Item Wb 64); (Item Wb 3); (Item Ww 32768); (Item Wb 120); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 121); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 131072); (Item Wb 122); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 262144); (Item Wb 123); (Item Wb 8)] [(Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 124); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 125); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 2097152); (Item Wb 127); (Item Wb 2); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 128); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 130); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 262144); (Item Wb 131); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 524288); (Item Wb 132); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 1048576); (Item Wb 133); (Item Wb 8); (Item Wb 32); (Item Wb 6); (Item Ww 2097152)]) (app [(Item Wb 134); (Item Wb 4); (Item Wb 64); (Item Wb 6); (Item Ww 524288); (Item Wb 135); (Item Wb 8); (Item Wb 64); (Item Wb 6); (Item Ww 1048576); (Item Wb 208); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 524288); (Item Wb 209); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 210); (Item Wb 4); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 214); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 1048576); (Item Wb 215); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 216); (Item Wb 8); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 220); (Item Wb 12)] [(Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 221); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 222); (Item Wb 12); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 226); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 2097152); (Item Wb 227); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 4194304); (Item Wb 228); (Item Wb 16); (Item Wb 64); (Item Wb 9); (Item Ww 8388608); (Item Wb 234); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 12582912); (Item Wb 235); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 18874368); (Item Wb 236); (Item Wb 24); (Item Wb 64); (Item Wb 9); (Item Ww 25165824)])))).

Definition hello_image_item_glibc_libc_start'23sigall_set : item :=
  (IData (a "glibc_libc_start#sigall_set") (LRo (a "local")) 8 [(Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615); (Item Wl 18446744073709551615)]).

Definition hello_image_item_glibc_libc_start'23str'2e301 : item :=
  (IData (a "glibc_libc_start#str.301") (LRo (a "local")) 1 [(Item Wb 111); (Item Wb 102); (Item Wb 102); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 50); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e302 : item :=
  (IData (a "glibc_libc_start#str.302") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 120); (Item Wb 56); (Item Wb 54); (Item Wb 47); (Item Wb 100); (Item Wb 108); (Item Wb 45); (Item Wb 99); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e303 : item :=
  (IData (a "glibc_libc_start#str.303") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 108); (Item Wb 95); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 99); (Item Wb 107); (Item Wb 95); (Item Wb 119); (Item Wb 111); (Item Wb 114); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e304 : item :=
  (IData (a "glibc_libc_start#str.304") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 122); (Item Wb 104); (Item Wb 97); (Item Wb 111); (Item Wb 120); (Item Wb 105); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e319 : item :=
  (IData (a "glibc_libc_start#str.319") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109); (Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110)] [(Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 10); (Item Wb 9); (Item Wb 0)])).

Definition hello_image_item_glibc_libc_start'23str'2e320 : item :=
  (IData (a "glibc_libc_start#str.320") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 105); (Item Wb 110); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 103); (Item Wb 114); (Item Wb 97); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e321 : item :=
  (IData (a "glibc_libc_start#str.321") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 110); (Item Wb 115); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 116); (Item Wb 114); (Item Wb 111); (Item Wb 108); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e322 : item :=
  (IData (a "glibc_libc_start#str.322") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e323 : item :=
  (IData (a "glibc_libc_start#str.323") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 110); (Item Wb 112); (Item Wb 116); (Item Wb 108); (Item Wb 47); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e324 : item :=
  (IData (a "glibc_libc_start#str.324") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 107); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e325 : item :=
  (IData (a "glibc_libc_start#str.325") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e326 : item :=
  (IData (a "glibc_libc_start#str.326") (LRo (a "local")) 1 [(Item Wb 120); (Item Wb 101); (Item Wb 111); (Item Wb 110); (Item Wb 95); (Item Wb 112); (Item Wb 104); (Item Wb 105); (Item Wb 0)]).

Definition hello_image_item_glibc_libc_start'23str'2e327 : item :=
  (IData (a "glibc_libc_start#str.327") (LRo (a "local")) 1 [(Item Wb 104); (Item Wb 97); (Item Wb 115); (Item Wb 119); (Item Wb 101); (Item Wb 108); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item___pthread_initialize_minimal : item :=
  (IData (a "__pthread_initialize_minimal") LExternWeak 1 []).

Definition hello_image_item___libc_initial : item :=
  (IData (a "__libc_initial") LExport 1 [(Zero 1)]).

Definition hello_image_item___nptl_initial_report_events : item :=
  (IData (a "__nptl_initial_report_events") LExport 1 [(Zero 1)]).

Definition hello_image_item___GI___default_pthread_attr : item :=
  (IData (a "__GI___default_pthread_attr") LExport 8 [(Zero 56)]).

Definition hello_image_item___GI___nptl_nthreads : item :=
  (IData (a "__GI___nptl_nthreads") LExport 4 [(Item Ww 1)]).

Definition hello_image_item___GI___mutex_aconf : item :=
  (IData (a "__GI___mutex_aconf") LExport 4 [(Item Ww 100)]).

Definition hello_image_item___libc_dlerror_result_string : item :=
  (IData (a "__libc_dlerror_result_string") (LTls (a "export")) 8 [(Zero 8)]).

Definition hello_image_item___libc_argc : item :=
  (IData (a "__libc_argc") LExport 4 [(Zero 4)]).

Definition hello_image_item___libc_argv : item :=
  (IData (a "__libc_argv") LExport 8 [(Zero 8)]).

Definition hello_image_item___nanofil_ctor__init_first : item :=
  (IData (a "__nanofil_ctor__init_first") (LInit (a "ctor") (a "none")) 8 [(Sym (a "glibc_init_first#_init_first") 0)]).
