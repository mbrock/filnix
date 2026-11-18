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

Definition hello_image_item_glibc_setlocale'23_nl_category_postload : item :=
  (IData (a "glibc_setlocale#_nl_category_postload") (LRo (a "local")) 8 [(Sym (a "_nl_postload_ctype") 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Zero 8); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0); (Item Wl 0)]).

Definition hello_image_item_glibc_setlocale'23str'2e234 : item :=
  (IData (a "glibc_setlocale#str.234") (LRo (a "local")) 1 [(Item Wb 76); (Item Wb 79); (Item Wb 67); (Item Wb 80); (Item Wb 65); (Item Wb 84); (Item Wb 72); (Item Wb 0)]).

Definition hello_image_item_setlocale : item :=
  (IAlias (a "setlocale") (a "export") (a "__GI_setlocale")).

Definition hello_image_item__nl_C_locobj : item :=
  (IData (a "_nl_C_locobj") (LRo (a "export")) 8 [(Sym (a "_nl_C_LC_CTYPE") 0); (Sym (a "_nl_C_LC_NUMERIC") 0); (Sym (a "_nl_C_LC_TIME") 0); (Sym (a "_nl_C_LC_COLLATE") 0); (Sym (a "_nl_C_LC_MONETARY") 0); (Sym (a "_nl_C_LC_MESSAGES") 0); (Zero 8); (Sym (a "_nl_C_LC_PAPER") 0); (Sym (a "_nl_C_LC_NAME") 0); (Sym (a "_nl_C_LC_ADDRESS") 0); (Sym (a "_nl_C_LC_TELEPHONE") 0); (Sym (a "_nl_C_LC_MEASUREMENT") 0); (Sym (a "_nl_C_LC_IDENTIFICATION") 0); (Sym (a "_nl_C_LC_CTYPE_class") 256); (Sym (a "_nl_C_LC_CTYPE_tolower") 512); (Sym (a "_nl_C_LC_CTYPE_toupper") 512); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0); (Sym (a "_nl_C_name") 0)]).

Definition hello_image_item_malloc : item :=
  (IAlias (a "malloc") (a "export") (a "__GI___libc_malloc")).

Definition hello_image_item_realloc : item :=
  (IAlias (a "realloc") (a "export") (a "__GI___libc_realloc")).

Definition hello_image_item_free : item :=
  (IAlias (a "free") (a "export") (a "__GI___libc_free")).

Definition hello_image_item_calloc : item :=
  (IAlias (a "calloc") (a "weak") (a "__libc_calloc")).

Definition hello_image_item_glibc_malloc'23__always_fail_morecore : item :=
  (IData (a "glibc_malloc#__always_fail_morecore") LLocal 1 [(Item Wb 0)]).

Definition hello_image_item_glibc_malloc'23__tcache_dummy : item :=
  (IData (a "glibc_malloc#__tcache_dummy") (LRo (a "local")) 8 [(Zero 768)]).

Definition hello_image_item_glibc_malloc'23main_arena : item :=
  (IData (a "glibc_malloc#main_arena") LLocal 8 [(Item Ww 0); (Zero 2068); (Sym (a "glibc_malloc#main_arena") 0); (Zero 8); (Item Wl 1); (Zero 16)]).

Definition hello_image_item_glibc_malloc'23mp_ : item :=
  (IData (a "glibc_malloc#mp_") LLocal 8 [(Item Wl 131072); (Item Wl 131072); (Item Wl 131072); (Item Wl 8); (Zero 8); (Item Ww 0); (Zero 28); (Item Ww 65536); (Zero 36); (Item Wl 64); (Item Wl 1041); (Item Wl 16)]).

Definition hello_image_item_glibc_malloc'23perturb_byte : item :=
  (IData (a "glibc_malloc#perturb_byte") LLocal 4 [(Zero 4)]).

Definition hello_image_item_tcache : item :=
  (IData (a "tcache") (LTls (a "local")) 8 [(Sym (a "glibc_malloc#__tcache_dummy") 0)]).

Definition hello_image_item_glibc_malloc'23tcache_key : item :=
  (IData (a "glibc_malloc#tcache_key") LLocal 8 [(Zero 8)]).

Definition hello_image_item_thread_arena : item :=
  (IData (a "thread_arena") (LTls (a "local")) 8 [(Zero 8)]).

Definition hello_image_item_glibc_malloc'23str'2e407 : item :=
  (IData (a "glibc_malloc#str.407") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_malloc'23str'2e408 : item :=
  (IData (a "glibc_malloc#str.408") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_malloc'23str'2e421 : item :=
  (IData (a "glibc_malloc#str.421") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 40); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 117); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 103); (Item Wb 110); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 116); (Item Wb 99); (Item Wb 97); (Item Wb 99); (Item Wb 104); (Item Wb 101); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 117); (Item Wb 110); (Item Wb 107); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_obstack_alloc_failed_handler : item :=
  (IData (a "obstack_alloc_failed_handler") LExport 8 [(Sym (a "glibc_obstack#print_and_abort") 0)]).

Definition hello_image_item_obstack_exit_failure : item :=
  (IData (a "obstack_exit_failure") LExport 4 [(Item Ww 1)]).

Definition hello_image_item_glibc_obstack'23str'2e148 : item :=
  (IData (a "glibc_obstack#str.148") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_obstack'23str'2e149 : item :=
  (IData (a "glibc_obstack#str.149") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 104); (Item Wb 97); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_error : item :=
  (IAlias (a "error") (a "weak") (a "__error")).

Definition hello_image_item_error_message_count : item :=
  (IData (a "error_message_count") LExport 4 [(Zero 4)]).

Definition hello_image_item_error_print_progname : item :=
  (IData (a "error_print_progname") LExport 8 [(Zero 8)]).

Definition hello_image_item_glibc_error'23str'2e252 : item :=
  (IData (a "glibc_error#str.252") (LRo (a "local")) 1 [(Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_error'23str'2e253 : item :=
  (IData (a "glibc_error#str.253") (LRo (a "local")) 4 [(Item Ww 111); (Item Ww 117); (Item Ww 116); (Item Ww 32); (Item Ww 111); (Item Ww 102); (Item Ww 32); (Item Ww 109); (Item Ww 101); (Item Ww 109); (Item Ww 111); (Item Ww 114); (Item Ww 121); (Item Ww 10); (Item Ww 0)]).

Definition hello_image_item_glibc_error'23str'2e254 : item :=
  (IData (a "glibc_error#str.254") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_error'23str'2e255 : item :=
  (IData (a "glibc_error#str.255") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 0)]).

Definition hello_image_item_glibc_getpagesize'23str'2e279 : item :=
  (IData (a "glibc_getpagesize#str.279") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 76); (Item Wb 82); (Item Wb 79); (Item Wb 40); (Item Wb 100); (Item Wb 108); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 41); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_getpagesize'23str'2e280 : item :=
  (IData (a "glibc_getpagesize#str.280") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 118); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 47); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_getpagesize'23str'2e281 : item :=
  (IData (a "glibc_getpagesize#str.281") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_getsysstats'23str'2e311 : item :=
  (IData (a "glibc_getsysstats#str.311") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 99); (Item Wb 112); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 42); (Item Wb 114); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_getsysstats'23str'2e312 : item :=
  (IData (a "glibc_getsysstats#str.312") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 118); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 47); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_getsysstats'23str'2e313 : item :=
  (IData (a "glibc_getsysstats#str.313") (LRo (a "local")) 1 [(Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 95); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_getsysstats'23str'2e314 : item :=
  (IData (a "glibc_getsysstats#str.314") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 47); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_getsysstats'23str'2e315 : item :=
  (IData (a "glibc_getsysstats#str.315") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 112); (Item Wb 117); (Item Wb 0)]).

Definition hello_image_item_glibc_getsysstats'23str'2e316 : item :=
  (IData (a "glibc_getsysstats#str.316") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 47); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 47); (Item Wb 99); (Item Wb 112); (Item Wb 117); (Item Wb 47); (Item Wb 111); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_getsysstats'23str'2e317 : item :=
  (IData (a "glibc_getsysstats#str.317") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 47); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 47); (Item Wb 99); (Item Wb 112); (Item Wb 117); (Item Wb 47); (Item Wb 112); (Item Wb 111); (Item Wb 115); (Item Wb 115); (Item Wb 105); (Item Wb 98); (Item Wb 108); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_program_invocation_name : item :=
  (IAlias (a "program_invocation_name") (a "weak") (a "__progname_full")).

Definition hello_image_item_program_invocation_short_name : item :=
  (IAlias (a "program_invocation_short_name") (a "weak") (a "__progname")).

Definition hello_image_item___progname : item :=
  (IData (a "__progname") LExport 8 [(Sym (a "glibc_init_misc#str.61") 0)]).

Definition hello_image_item___progname_full : item :=
  (IData (a "__progname_full") LExport 8 [(Sym (a "glibc_init_misc#str.61") 0)]).

Definition hello_image_item_glibc_init_misc'23str'2e61 : item :=
  (IData (a "glibc_init_misc#str.61") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition hello_image_item___GI___mmap : item :=
  (IAlias (a "__GI___mmap") (a "export") (a "__GI___mmap64")).

Definition hello_image_item_glibc_mmap64'23str'2e279 : item :=
  (IData (a "glibc_mmap64#str.279") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109); (Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110)] [(Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 10); (Item Wb 9); (Item Wb 0)])).

Definition hello_image_item___munmap : item :=
  (IOutside (a "__munmap") (TApp "func" [(a "__munmap"); (a "export"); (a "data"); (TList []); (TList [(TApp "block" [(a "start"); (TList []); (TList [(TApp "let" [(TApp "tmp" [(a "v0")]); (a "p"); (a "copy"); (TList [(TApp "global" [(a "zsys_munmap")])])]); (TApp "let" [(TApp "tmp" [(a "v1")]); (a "p"); (a "va_args"); (TList [(TApp "const" [(TInt 0)])])]); (TApp "call" [(TApp "result" [(TApp "tmp" [(a "v2")]); (a "p")]); (TApp "global" [(a "zcall")]); (TList [(TApp "arg" [(a "p"); (TApp "tmp" [(a "v0")])]); (TApp "arg" [(a "p"); (TApp "tmp" [(a "v1")])])])])]); (TApp "ret" [(TApp "tmp" [(a "v2")])])])])])).

Definition hello_image_item___GI___munmap : item :=
  (IAlias (a "__GI___munmap") (a "export") (a "__munmap")).

Definition hello_image_item_glibc_setvmaname'23decorate_maps : item :=
  (IData (a "glibc_setvmaname#decorate_maps") LLocal 4 [(Item Ww (-1))]).

Definition hello_image_item_glibc_setvmaname'23str'2e282 : item :=
  (IData (a "glibc_setvmaname#str.282") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109); (Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110)] [(Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 10); (Item Wb 9); (Item Wb 0)])).

Definition hello_image_item___libc_single_threaded_internal : item :=
  (IAlias (a "__libc_single_threaded_internal") (a "export") (a "__libc_single_threaded")).

Definition hello_image_item___libc_single_threaded : item :=
  (IData (a "__libc_single_threaded") LExport 1 [(Zero 1)]).

Definition hello_image_item___sysinfo : item :=
  (IOutside (a "__sysinfo") (TApp "func" [(a "__sysinfo"); (a "export"); (a "data"); (TList []); (TList [(TApp "block" [(a "start"); (TList []); (TList [(TApp "let" [(TApp "tmp" [(a "v0")]); (a "p"); (a "copy"); (TList [(TApp "global" [(a "zsys_sysinfo")])])]); (TApp "let" [(TApp "tmp" [(a "v1")]); (a "p"); (a "va_args"); (TList [(TApp "const" [(TInt 0)])])]); (TApp "call" [(TApp "result" [(TApp "tmp" [(a "v2")]); (a "p")]); (TApp "global" [(a "zcall")]); (TList [(TApp "arg" [(a "p"); (TApp "tmp" [(a "v0")])]); (TApp "arg" [(a "p"); (TApp "tmp" [(a "v1")])])])])]); (TApp "ret" [(TApp "tmp" [(a "v2")])])])])])).

Definition hello_image_item_glibc_futex_internal'23str'2e244 : item :=
  (IData (a "glibc_futex_internal#str.244") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition hello_image_item_glibc_futex_internal'23str'2e245 : item :=
  (IData (a "glibc_futex_internal#str.245") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_futex_internal'23str'2e246 : item :=
  (IData (a "glibc_futex_internal#str.246") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 97); (Item Wb 98); (Item Wb 115); (Item Wb 116); (Item Wb 105); (Item Wb 109); (Item Wb 101); (Item Wb 100); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 105); (Item Wb 116); (Item Wb 54); (Item Wb 52); (Item Wb 0)]).

Definition hello_image_item_glibc_futex_internal'23str'2e247 : item :=
  (IData (a "glibc_futex_internal#str.247") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).

Definition hello_image_item___fork_generation : item :=
  (IData (a "__fork_generation") LExport 8 [(Zero 8)]).

Definition hello_image_item___GI___pthread_once : item :=
  (IAlias (a "__GI___pthread_once") (a "export") (a "___pthread_once")).

Definition hello_image_item_glibc_pthread_rwlock_init'23default_rwlockattr : item :=
  (IData (a "glibc_pthread_rwlock_init#default_rwlockattr") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0)]).

Definition hello_image_item___GI___pthread_rwlock_init : item :=
  (IAlias (a "__GI___pthread_rwlock_init") (a "export") (a "___pthread_rwlock_init")).

Definition hello_image_item___GI___pthread_rwlock_rdlock : item :=
  (IAlias (a "__GI___pthread_rwlock_rdlock") (a "export") (a "___pthread_rwlock_rdlock")).

Definition hello_image_item_glibc_pthread_rwlock_rdlock'23str'2e286 : item :=
  (IData (a "glibc_pthread_rwlock_rdlock#str.286") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_rdlock'23str'2e287 : item :=
  (IData (a "glibc_pthread_rwlock_rdlock#str.287") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 110); (Item Wb 112); (Item Wb 116); (Item Wb 108); (Item Wb 47); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_rdlock'23str'2e288 : item :=
  (IData (a "glibc_pthread_rwlock_rdlock#str.288") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 107); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_rdlock'23str'2e289 : item :=
  (IData (a "glibc_pthread_rwlock_rdlock#str.289") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).

Definition hello_image_item___GI___pthread_rwlock_unlock : item :=
  (IAlias (a "__GI___pthread_rwlock_unlock") (a "export") (a "___pthread_rwlock_unlock")).

Definition hello_image_item_glibc_pthread_rwlock_unlock'23str'2e286 : item :=
  (IData (a "glibc_pthread_rwlock_unlock#str.286") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_unlock'23str'2e287 : item :=
  (IData (a "glibc_pthread_rwlock_unlock#str.287") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 110); (Item Wb 112); (Item Wb 116); (Item Wb 108); (Item Wb 47); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_unlock'23str'2e288 : item :=
  (IData (a "glibc_pthread_rwlock_unlock#str.288") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 107); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_unlock'23str'2e289 : item :=
  (IData (a "glibc_pthread_rwlock_unlock#str.289") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).

Definition hello_image_item___GI___pthread_rwlock_wrlock : item :=
  (IAlias (a "__GI___pthread_rwlock_wrlock") (a "export") (a "___pthread_rwlock_wrlock")).

Definition hello_image_item_glibc_pthread_rwlock_wrlock'23str'2e286 : item :=
  (IData (a "glibc_pthread_rwlock_wrlock#str.286") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_wrlock'23str'2e287 : item :=
  (IData (a "glibc_pthread_rwlock_wrlock#str.287") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 110); (Item Wb 112); (Item Wb 116); (Item Wb 108); (Item Wb 47); (Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 45); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 97); (Item Wb 108); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_wrlock'23str'2e288 : item :=
  (IData (a "glibc_pthread_rwlock_wrlock#str.288") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 117); (Item Wb 116); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 119); (Item Wb 97); (Item Wb 107); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_pthread_rwlock_wrlock'23str'2e289 : item :=
  (IData (a "glibc_pthread_rwlock_wrlock#str.289") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 80); (Item Wb 82); (Item Wb 73); (Item Wb 86); (Item Wb 65); (Item Wb 84); (Item Wb 69); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 118); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 76); (Item Wb 76); (Item Wb 76); (Item Wb 95); (Item Wb 83); (Item Wb 72); (Item Wb 65); (Item Wb 82); (Item Wb 69); (Item Wb 68); (Item Wb 0)]).

Definition hello_image_item_glibc_unwind'23str'2e287 : item :=
  (IData (a "glibc_unwind#str.287") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 37); (Item Wb 100); (Item Wb 58); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition hello_image_item_glibc_unwind'23str'2e288 : item :=
  (IData (a "glibc_unwind#str.288") (LRo (a "local")) 1 [(Item Wb 117); (Item Wb 110); (Item Wb 119); (Item Wb 105); (Item Wb 110); (Item Wb 100); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_unwind'23str'2e289 : item :=
  (IData (a "glibc_unwind#str.289") (LRo (a "local")) 1 [(Item Wb 117); (Item Wb 110); (Item Wb 119); (Item Wb 105); (Item Wb 110); (Item Wb 100); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 111); (Item Wb 112); (Item Wb 0)]).

Definition hello_image_item_glibc_unwind'23str'2e290 : item :=
  (IData (a "glibc_unwind#str.290") (LRo (a "local")) 1 [(Item Wb 33); (Item Wb 99); (Item Wb 117); (Item Wb 114); (Item Wb 112); (Item Wb 0)]).

Definition hello_image_item_glibc_unwind'23str'2e291 : item :=
  (IData (a "glibc_unwind#str.291") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 65); (Item Wb 84); (Item Wb 65); (Item Wb 76); (Item Wb 58); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 99); (Item Wb 101); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 116); (Item Wb 104); (Item Wb 114); (Item Wb 111); (Item Wb 119); (Item Wb 110); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item__exit : item :=
  (IAlias (a "_exit") (a "export") (a "__GI__exit")).

Definition hello_image_item___environ : item :=
  (IData (a "__environ") LExport 8 [(Item Wl 0)]).

Definition hello_image_item___environ_counter : item :=
  (IData (a "__environ_counter") LExport 8 [(Zero 8)]).

Definition hello_image_item_glibc_getopt'23getopt_data : item :=
  (IData (a "glibc_getopt#getopt_data") LLocal 8 [(Zero 56)]).

Definition hello_image_item_optarg : item :=
  (IData (a "optarg") LExport 8 [(Zero 8)]).

Definition hello_image_item_opterr : item :=
  (IData (a "opterr") LExport 4 [(Item Ww 1)]).

Definition hello_image_item_optind : item :=
  (IData (a "optind") LExport 4 [(Item Ww 1)]).

Definition hello_image_item_optopt : item :=
  (IData (a "optopt") LExport 4 [(Item Ww 63)]).

Definition hello_image_item_glibc_getopt'23str'2e138 : item :=
  (IData (a "glibc_getopt#str.138") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 109); (Item Wb 98); (Item Wb 105); (Item Wb 103); (Item Wb 117); (Item Wb 111); (Item Wb 117); (Item Wb 115); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e139 : item :=
  (IData (a "glibc_getopt#str.139") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 32); (Item Wb 105); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 109); (Item Wb 98); (Item Wb 105); (Item Wb 103); (Item Wb 117); (Item Wb 111); (Item Wb 117); (Item Wb 115); (Item Wb 59); (Item Wb 32); (Item Wb 112); (Item Wb 111); (Item Wb 115); (Item Wb 115); (Item Wb 105); (Item Wb 98); (Item Wb 105); (Item Wb 108); (Item Wb 105); (Item Wb 116); (Item Wb 105); (Item Wb 101); (Item Wb 115); (Item Wb 58); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e140 : item :=
  (IData (a "glibc_getopt#str.140") (LRo (a "local")) 1 [(Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e141 : item :=
  (IData (a "glibc_getopt#str.141") (LRo (a "local")) 1 [(Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e142 : item :=
  (IData (a "glibc_getopt#str.142") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 117); (Item Wb 110); (Item Wb 114); (Item Wb 101); (Item Wb 99); (Item Wb 111); (Item Wb 103); (Item Wb 110); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e143 : item :=
  (IData (a "glibc_getopt#str.143") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 32); (Item Wb 100); (Item Wb 111); (Item Wb 101); (Item Wb 115); (Item Wb 110); (Item Wb 39); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e144 : item :=
  (IData (a "glibc_getopt#str.144") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 115); (Item Wb 39); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e145 : item :=
  (IData (a "glibc_getopt#str.145") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 79); (Item Wb 83); (Item Wb 73); (Item Wb 88); (Item Wb 76); (Item Wb 89); (Item Wb 95); (Item Wb 67); (Item Wb 79); (Item Wb 82); (Item Wb 82); (Item Wb 69); (Item Wb 67); (Item Wb 84); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e146 : item :=
  (IData (a "glibc_getopt#str.146") (LRo (a "local")) 1 [(Item Wb 45); (Item Wb 45); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e147 : item :=
  (IData (a "glibc_getopt#str.147") (LRo (a "local")) 1 [(Item Wb 45); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e148 : item :=
  (IData (a "glibc_getopt#str.148") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 99); (Item Wb 39); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e149 : item :=
  (IData (a "glibc_getopt#str.149") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 58); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 110); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 45); (Item Wb 45); (Item Wb 32); (Item Wb 39); (Item Wb 37); (Item Wb 99); (Item Wb 39); (Item Wb 10); (Item Wb 0)]).

Definition hello_image_item_glibc_getopt'23str'2e150 : item :=
  (IData (a "glibc_getopt#str.150") (LRo (a "local")) 1 [(Item Wb 45); (Item Wb 87); (Item Wb 32); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e302 : item :=
  (IData (a "glibc_sysconf#str.302") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 105); (Item Wb 110); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 99); (Item Wb 107); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e303 : item :=
  (IData (a "glibc_sysconf#str.303") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 118); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 102); (Item Wb 45); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 115); (Item Wb 116); (Item Wb 107); (Item Wb 115); (Item Wb 122); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e304 : item :=
  (IData (a "glibc_sysconf#str.304") (LRo (a "local")) 1 [(Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 102); (Item Wb 95); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 115); (Item Wb 116); (Item Wb 107); (Item Wb 115); (Item Wb 122); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e305 : item :=
  (IData (a "glibc_sysconf#str.305") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 47); (Item Wb 107); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 101); (Item Wb 108); (Item Wb 47); (Item Wb 110); (Item Wb 103); (Item Wb 114); (Item Wb 111); (Item Wb 117); (Item Wb 112); (Item Wb 115); (Item Wb 95); (Item Wb 109); (Item Wb 97); (Item Wb 120); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e306 : item :=
  (IData (a "glibc_sysconf#str.306") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 47); (Item Wb 107); (Item Wb 101); (Item Wb 114); (Item Wb 110); (Item Wb 101); (Item Wb 108); (Item Wb 47); (Item Wb 114); (Item Wb 116); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 45); (Item Wb 109); (Item Wb 97); (Item Wb 120); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e307 : item :=
  (IData (a "glibc_sysconf#str.307") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 76); (Item Wb 82); (Item Wb 79); (Item Wb 40); (Item Wb 100); (Item Wb 108); (Item Wb 95); (Item Wb 109); (Item Wb 105); (Item Wb 110); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 99); (Item Wb 107); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 41); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e308 : item :=
  (IData (a "glibc_sysconf#str.308") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 118); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 47); (Item Wb 120); (Item Wb 56); (Item Wb 54); (Item Wb 47); (Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 102); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e309 : item :=
  (IData (a "glibc_sysconf#str.309") (LRo (a "local")) 1 [(Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 95); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 102); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e348 : item :=
  (IData (a "glibc_sysconf#str.348") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 76); (Item Wb 80); (Item Wb 51); (Item Wb 50); (Item Wb 95); (Item Wb 79); (Item Wb 70); (Item Wb 70); (Item Wb 51); (Item Wb 50); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e349 : item :=
  (IData (a "glibc_sysconf#str.349") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 76); (Item Wb 80); (Item Wb 51); (Item Wb 50); (Item Wb 95); (Item Wb 79); (Item Wb 70); (Item Wb 70); (Item Wb 66); (Item Wb 73); (Item Wb 71); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e350 : item :=
  (IData (a "glibc_sysconf#str.350") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 69); (Item Wb 84); (Item Wb 67); (Item Wb 79); (Item Wb 78); (Item Wb 70); (Item Wb 95); (Item Wb 68); (Item Wb 73); (Item Wb 82); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e351 : item :=
  (IData (a "glibc_sysconf#str.351") (LRo (a "local")) 1 (app [(Item Wb 47); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 101); (Item Wb 47); (Item Wb 55); (Item Wb 104); (Item Wb 104); (Item Wb 52); (Item Wb 53); (Item Wb 99); (Item Wb 118); (Item Wb 119); (Item Wb 122); (Item Wb 114); (Item Wb 113); (Item Wb 121); (Item Wb 113); (Item Wb 118); (Item Wb 112); (Item Wb 107); (Item Wb 110); (Item Wb 110); (Item Wb 108); (Item Wb 106); (Item Wb 56); (Item Wb 50); (Item Wb 118); (Item Wb 114); (Item Wb 113); (Item Wb 100); (Item Wb 109); (Item Wb 103)] [(Item Wb 54); (Item Wb 107); (Item Wb 120); (Item Wb 119); (Item Wb 45); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 99); (Item Wb 45); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 45); (Item Wb 112); (Item Wb 112); (Item Wb 45); (Item Wb 50); (Item Wb 46); (Item Wb 52); (Item Wb 52); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 101); (Item Wb 120); (Item Wb 101); (Item Wb 99); (Item Wb 47); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 102); (Item Wb 0)])).

Definition hello_image_item_glibc_sysconf'23str'2e353 : item :=
  (IData (a "glibc_sysconf#str.353") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 80); (Item Wb 79); (Item Wb 83); (Item Wb 73); (Item Wb 88); (Item Wb 95); (Item Wb 86); (Item Wb 54); (Item Wb 95); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e354 : item :=
  (IData (a "glibc_sysconf#str.354") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 116); (Item Wb 104); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 99); (Item Wb 107); (Item Wb 95); (Item Wb 109); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e355 : item :=
  (IData (a "glibc_sysconf#str.355") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 118); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 102); (Item Wb 45); (Item Wb 112); (Item Wb 116); (Item Wb 104); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 99); (Item Wb 107); (Item Wb 95); (Item Wb 109); (Item Wb 105); (Item Wb 110); (Item Wb 46); (Item Wb 104); (Item Wb 0)]).

Definition hello_image_item_glibc_sysconf'23str'2e356 : item :=
  (IData (a "glibc_sysconf#str.356") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 104); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 99); (Item Wb 107); (Item Wb 95); (Item Wb 109); (Item Wb 105); (Item Wb 110); (Item Wb 0)]).

Definition hello_image_item___GI___getrlimit : item :=
  (IAlias (a "__GI___getrlimit") (a "export") (a "__GI___getrlimit64")).

Definition hello_image_item___libc_longjmp : item :=
  (IAlias (a "__libc_longjmp") (a "export") (a "__libc_siglongjmp")).

Definition hello_image_item___GI___asprintf : item :=
  (IAlias (a "__GI___asprintf") (a "export") (a "___asprintf")).

Definition hello_image_item__sys_errlist_internal : item :=
  (IData (a "_sys_errlist_internal") (LRo (a "export")) 8 (app (app [(Sym (a "glibc_errlist_data_gen#str.247") 0); (Sym (a "glibc_errlist_data_gen#str.248") 0); (Sym (a "glibc_errlist_data_gen#str.249") 0); (Sym (a "glibc_errlist_data_gen#str.250") 0); (Sym (a "glibc_errlist_data_gen#str.251") 0); (Sym (a "glibc_errlist_data_gen#str.252") 0); (Sym (a "glibc_errlist_data_gen#str.253") 0); (Sym (a "glibc_errlist_data_gen#str.254") 0); (Sym (a "glibc_errlist_data_gen#str.255") 0); (Sym (a "glibc_errlist_data_gen#str.256") 0); (Sym (a "glibc_errlist_data_gen#str.257") 0); (Sym (a "glibc_errlist_data_gen#str.282") 0); (Sym (a "glibc_errlist_data_gen#str.259") 0); (Sym (a "glibc_errlist_data_gen#str.260") 0); (Sym (a "glibc_errlist_data_gen#str.261") 0); (Sym (a "glibc_errlist_data_gen#str.262") 0); (Sym (a "glibc_errlist_data_gen#str.263") 0); (Sym (a "glibc_errlist_data_gen#str.264") 0); (Sym (a "glibc_errlist_data_gen#str.265") 0); (Sym (a "glibc_errlist_data_gen#str.266") 0); (Sym (a "glibc_errlist_data_gen#str.267") 0); (Sym (a "glibc_errlist_data_gen#str.268") 0); (Sym (a "glibc_errlist_data_gen#str.269") 0); (Sym (a "glibc_errlist_data_gen#str.271") 0); (Sym (a "glibc_errlist_data_gen#str.270") 0); (Sym (a "glibc_errlist_data_gen#str.272") 0); (Sym (a "glibc_errlist_data_gen#str.273") 0); (Sym (a "glibc_errlist_data_gen#str.274") 0); (Sym (a "glibc_errlist_data_gen#str.275") 0); (Sym (a "glibc_errlist_data_gen#str.276") 0); (Sym (a "glibc_errlist_data_gen#str.277") 0); (Sym (a "glibc_errlist_data_gen#str.278") 0); (Sym (a "glibc_errlist_data_gen#str.279") 0)] [(Sym (a "glibc_errlist_data_gen#str.280") 0); (Sym (a "glibc_errlist_data_gen#str.281") 0); (Sym (a "glibc_errlist_data_gen#str.258") 0); (Sym (a "glibc_errlist_data_gen#str.310") 0); (Sym (a "glibc_errlist_data_gen#str.318") 0); (Sym (a "glibc_errlist_data_gen#str.319") 0); (Sym (a "glibc_errlist_data_gen#str.313") 0); (Sym (a "glibc_errlist_data_gen#str.309") 0); (Zero 8); (Sym (a "glibc_errlist_data_gen#str.326") 0); (Sym (a "glibc_errlist_data_gen#str.322") 0); (Sym (a "glibc_errlist_data_gen#str.336") 0); (Sym (a "glibc_errlist_data_gen#str.337") 0); (Sym (a "glibc_errlist_data_gen#str.338") 0); (Sym (a "glibc_errlist_data_gen#str.339") 0); (Sym (a "glibc_errlist_data_gen#str.340") 0); (Sym (a "glibc_errlist_data_gen#str.341") 0); (Sym (a "glibc_errlist_data_gen#str.342") 0); (Sym (a "glibc_errlist_data_gen#str.343") 0); (Sym (a "glibc_errlist_data_gen#str.344") 0); (Sym (a "glibc_errlist_data_gen#str.345") 0); (Sym (a "glibc_errlist_data_gen#str.346") 0); (Sym (a "glibc_errlist_data_gen#str.347") 0); (Sym (a "glibc_errlist_data_gen#str.348") 0); (Sym (a "glibc_errlist_data_gen#str.349") 0); (Zero 8); (Sym (a "glibc_errlist_data_gen#str.350") 0); (Sym (a "glibc_errlist_data_gen#str.328") 0); (Sym (a "glibc_errlist_data_gen#str.324") 0); (Sym (a "glibc_errlist_data_gen#str.331") 0); (Sym (a "glibc_errlist_data_gen#str.327") 0); (Sym (a "glibc_errlist_data_gen#str.351") 0); (Sym (a "glibc_errlist_data_gen#str.352") 0); (Sym (a "glibc_errlist_data_gen#str.317") 0)]) (app [(Sym (a "glibc_errlist_data_gen#str.325") 0); (Sym (a "glibc_errlist_data_gen#str.353") 0); (Sym (a "glibc_errlist_data_gen#str.354") 0); (Sym (a "glibc_errlist_data_gen#str.355") 0); (Sym (a "glibc_errlist_data_gen#str.330") 0); (Sym (a "glibc_errlist_data_gen#str.323") 0); (Sym (a "glibc_errlist_data_gen#str.356") 0); (Sym (a "glibc_errlist_data_gen#str.321") 0); (Sym (a "glibc_errlist_data_gen#str.329") 0); (Sym (a "glibc_errlist_data_gen#str.357") 0); (Sym (a "glibc_errlist_data_gen#str.358") 0); (Sym (a "glibc_errlist_data_gen#str.359") 0); (Sym (a "glibc_errlist_data_gen#str.360") 0); (Sym (a "glibc_errlist_data_gen#str.361") 0); (Sym (a "glibc_errlist_data_gen#str.362") 0); (Sym (a "glibc_errlist_data_gen#str.363") 0); (Sym (a "glibc_errlist_data_gen#str.364") 0); (Sym (a "glibc_errlist_data_gen#str.320") 0); (Sym (a "glibc_errlist_data_gen#str.335") 0); (Sym (a "glibc_errlist_data_gen#str.365") 0); (Sym (a "glibc_errlist_data_gen#str.314") 0); (Sym (a "glibc_errlist_data_gen#str.285") 0); (Sym (a "glibc_errlist_data_gen#str.304") 0); (Sym (a "glibc_errlist_data_gen#str.286") 0); (Sym (a "glibc_errlist_data_gen#str.287") 0); (Sym (a "glibc_errlist_data_gen#str.288") 0); (Sym (a "glibc_errlist_data_gen#str.289") 0); (Sym (a "glibc_errlist_data_gen#str.290") 0); (Sym (a "glibc_errlist_data_gen#str.291") 0); (Sym (a "glibc_errlist_data_gen#str.292") 0); (Sym (a "glibc_errlist_data_gen#str.293") 0); (Sym (a "glibc_errlist_data_gen#str.294") 0); (Sym (a "glibc_errlist_data_gen#str.295") 0)] [(Sym (a "glibc_errlist_data_gen#str.296") 0); (Sym (a "glibc_errlist_data_gen#str.297") 0); (Sym (a "glibc_errlist_data_gen#str.298") 0); (Sym (a "glibc_errlist_data_gen#str.299") 0); (Sym (a "glibc_errlist_data_gen#str.300") 0); (Sym (a "glibc_errlist_data_gen#str.301") 0); (Sym (a "glibc_errlist_data_gen#str.302") 0); (Sym (a "glibc_errlist_data_gen#str.303") 0); (Sym (a "glibc_errlist_data_gen#str.305") 0); (Sym (a "glibc_errlist_data_gen#str.306") 0); (Sym (a "glibc_errlist_data_gen#str.307") 0); (Sym (a "glibc_errlist_data_gen#str.308") 0); (Sym (a "glibc_errlist_data_gen#str.311") 0); (Sym (a "glibc_errlist_data_gen#str.312") 0); (Sym (a "glibc_errlist_data_gen#str.284") 0); (Sym (a "glibc_errlist_data_gen#str.283") 0); (Sym (a "glibc_errlist_data_gen#str.316") 0); (Sym (a "glibc_errlist_data_gen#str.366") 0); (Sym (a "glibc_errlist_data_gen#str.367") 0); (Sym (a "glibc_errlist_data_gen#str.368") 0); (Sym (a "glibc_errlist_data_gen#str.369") 0); (Sym (a "glibc_errlist_data_gen#str.370") 0); (Sym (a "glibc_errlist_data_gen#str.315") 0); (Sym (a "glibc_errlist_data_gen#str.371") 0); (Sym (a "glibc_errlist_data_gen#str.372") 0); (Sym (a "glibc_errlist_data_gen#str.332") 0); (Sym (a "glibc_errlist_data_gen#str.373") 0); (Sym (a "glibc_errlist_data_gen#str.374") 0); (Sym (a "glibc_errlist_data_gen#str.375") 0); (Sym (a "glibc_errlist_data_gen#str.376") 0); (Sym (a "glibc_errlist_data_gen#str.333") 0); (Sym (a "glibc_errlist_data_gen#str.334") 0); (Sym (a "glibc_errlist_data_gen#str.377") 0); (Sym (a "glibc_errlist_data_gen#str.378") 0)]))).

Definition hello_image_item__sys_errlist_internal_len : item :=
  (IData (a "_sys_errlist_internal_len") (LRo (a "export")) 8 [(Item Wl 134)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e247 : item :=
  (IData (a "glibc_errlist_data_gen#str.247") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 117); (Item Wb 99); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e248 : item :=
  (IData (a "glibc_errlist_data_gen#str.248") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 97); (Item Wb 116); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 112); (Item Wb 101); (Item Wb 114); (Item Wb 109); (Item Wb 105); (Item Wb 116); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e249 : item :=
  (IData (a "glibc_errlist_data_gen#str.249") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 99); (Item Wb 104); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e250 : item :=
  (IData (a "glibc_errlist_data_gen#str.250") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 99); (Item Wb 104); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e251 : item :=
  (IData (a "glibc_errlist_data_gen#str.251") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 117); (Item Wb 112); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 32); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e252 : item :=
  (IData (a "glibc_errlist_data_gen#str.252") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 47); (Item Wb 111); (Item Wb 117); (Item Wb 116); (Item Wb 112); (Item Wb 117); (Item Wb 116); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e253 : item :=
  (IData (a "glibc_errlist_data_gen#str.253") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 99); (Item Wb 104); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 97); (Item Wb 100); (Item Wb 100); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e254 : item :=
  (IData (a "glibc_errlist_data_gen#str.254") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 115); (Item Wb 116); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 108); (Item Wb 111); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e255 : item :=
  (IData (a "glibc_errlist_data_gen#str.255") (LRo (a "local")) 1 [(Item Wb 69); (Item Wb 120); (Item Wb 101); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 109); (Item Wb 97); (Item Wb 116); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e256 : item :=
  (IData (a "glibc_errlist_data_gen#str.256") (LRo (a "local")) 1 [(Item Wb 66); (Item Wb 97); (Item Wb 100); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 115); (Item Wb 99); (Item Wb 114); (Item Wb 105); (Item Wb 112); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e257 : item :=
  (IData (a "glibc_errlist_data_gen#str.257") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 99); (Item Wb 104); (Item Wb 105); (Item Wb 108); (Item Wb 100); (Item Wb 32); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 99); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 101); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e258 : item :=
  (IData (a "glibc_errlist_data_gen#str.258") (LRo (a "local")) 1 [(Item Wb 82); (Item Wb 101); (Item Wb 115); (Item Wb 111); (Item Wb 117); (Item Wb 114); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 107); (Item Wb 32); (Item Wb 97); (Item Wb 118); (Item Wb 111); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e259 : item :=
  (IData (a "glibc_errlist_data_gen#str.259") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 109); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e260 : item :=
  (IData (a "glibc_errlist_data_gen#str.260") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 101); (Item Wb 114); (Item Wb 109); (Item Wb 105); (Item Wb 115); (Item Wb 115); (Item Wb 105); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 110); (Item Wb 105); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e261 : item :=
  (IData (a "glibc_errlist_data_gen#str.261") (LRo (a "local")) 1 [(Item Wb 66); (Item Wb 97); (Item Wb 100); (Item Wb 32); (Item Wb 97); (Item Wb 100); (Item Wb 100); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e262 : item :=
  (IData (a "glibc_errlist_data_gen#str.262") (LRo (a "local")) 1 [(Item Wb 66); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 107); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 113); (Item Wb 117); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e263 : item :=
  (IData (a "glibc_errlist_data_gen#str.263") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 114); (Item Wb 101); (Item Wb 115); (Item Wb 111); (Item Wb 117); (Item Wb 114); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 115); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e264 : item :=
  (IData (a "glibc_errlist_data_gen#str.264") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 105); (Item Wb 115); (Item Wb 116); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e265 : item :=
  (IData (a "glibc_errlist_data_gen#str.265") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 99); (Item Wb 114); (Item Wb 111); (Item Wb 115); (Item Wb 115); (Item Wb 45); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 107); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e266 : item :=
  (IData (a "glibc_errlist_data_gen#str.266") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 115); (Item Wb 117); (Item Wb 99); (Item Wb 104); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e267 : item :=
  (IData (a "glibc_errlist_data_gen#str.267") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e268 : item :=
  (IData (a "glibc_errlist_data_gen#str.268") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 115); (Item Wb 32); (Item Wb 97); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 114); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e269 : item :=
  (IData (a "glibc_errlist_data_gen#str.269") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 118); (Item Wb 97); (Item Wb 108); (Item Wb 105); (Item Wb 100); (Item Wb 32); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 117); (Item Wb 109); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e270 : item :=
  (IData (a "glibc_errlist_data_gen#str.270") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 97); (Item Wb 110); (Item Wb 121); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 115); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e271 : item :=
  (IData (a "glibc_errlist_data_gen#str.271") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 109); (Item Wb 97); (Item Wb 110); (Item Wb 121); (Item Wb 32); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 110); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 115); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e272 : item :=
  (IData (a "glibc_errlist_data_gen#str.272") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 110); (Item Wb 97); (Item Wb 112); (Item Wb 112); (Item Wb 114); (Item Wb 111); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 111); (Item Wb 99); (Item Wb 116); (Item Wb 108); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e273 : item :=
  (IData (a "glibc_errlist_data_gen#str.273") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 98); (Item Wb 117); (Item Wb 115); (Item Wb 121); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e274 : item :=
  (IData (a "glibc_errlist_data_gen#str.274") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 111); (Item Wb 32); (Item Wb 108); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 101); (Item Wb 0)]).

Definition hello_image_item_glibc_errlist_data_gen'23str'2e275 : item :=
  (IData (a "glibc_errlist_data_gen#str.275") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 32); (Item Wb 115); (Item Wb 112); (Item Wb 97); (Item Wb 99); (Item Wb 101); (Item Wb 32); (Item Wb 108); (Item Wb 101); (Item Wb 102); (Item Wb 116); (Item Wb 32); (Item Wb 111); (Item Wb 110); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 118); (Item Wb 105); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).
