(** This file defines checked IR from glibc’s `intl/plural.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation Unit_intl_plural_os_Blocks_5f5f676574746578747061727365_1 Unit_intl_plural_os_Blocks_5f5f676574746578747061727365_2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___gettext_free_exp : func :=
  ir_fn{ "export" "__gettext_free_exp"(P %"v0") -> RVoid {
  @"start":
    %"v6" : L = Ptoi %"v0";
    %"v7" : L = Ptoi #0;
    %"v8" : W = (Cmp Eq L) %"v6", %"v7"
    => br %"v8" ? "L2" : "L4";
  @"L2":
    => ret void;
  @"L4":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v31" : W = (Cmp Eq W) %"v11", #3
    => br %"v31" ? "L14" : "L32";
  @"L14":
    %"v16" = %"v0" +p #8;
    %"v17" = %"v16" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v17";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call void $"__gettext_free_exp"(P %"v18")
    => goto "L19";
  @"L19":
    %"v21" = %"v0" +p #8;
    %"v22" = %"v21" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call void $"__gettext_free_exp"(P %"v23")
    => goto "L24";
  @"L24":
    %"v26" = %"v0" +p #8;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v26";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call void $"__gettext_free_exp"(P %"v28")
    => goto "L13";
  @"L32":
    %"v33" : W = (Cmp Eq W) %"v11", #2
    => br %"v33" ? poll "L19" : "L34";
  @"L34":
    %"v35" : W = (Cmp Eq W) %"v11", #1
    => br %"v35" ? poll "L24" : "L13";
  @"L13":
    call void $"free"(P %"v0")
    => ret void
} }.

Definition fn___gettextparse : func :=
  ir_fn{ "export" "__gettextparse"(P %"v0") -> (RClass W) blocks (fn___gettextparse'blocks1 ++ fn___gettextparse'blocks2) }.

Definition item_glibc_plural'23__gettextparse'2eyyval_default'2e125 : item :=
  (IData (a "glibc_plural#__gettextparse.yyval_default.125") LLocal 8 [(Zero 8)]).

Definition item_glibc_plural'23str'2e124 : item :=
  (IData (a "glibc_plural#str.124") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 101); (Item Wb 108); (Item Wb 101); (Item Wb 116); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition item_glibc_plural'23str'2e126 : item :=
  (IData (a "glibc_plural#str.126") (LRo (a "local")) 1 [(Item Wb 115); (Item Wb 121); (Item Wb 110); (Item Wb 116); (Item Wb 97); (Item Wb 120); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_plural'23str'2e127 : item :=
  (IData (a "glibc_plural#str.127") (LRo (a "local")) 1 [(Item Wb 69); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 58); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 114); (Item Wb 100); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition item_glibc_plural'23str'2e128 : item :=
  (IData (a "glibc_plural#str.128") (LRo (a "local")) 1 [(Item Wb 69); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 58); (Item Wb 32); (Item Wb 112); (Item Wb 111); (Item Wb 112); (Item Wb 112); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition item_glibc_plural'23str'2e129 : item :=
  (IData (a "glibc_plural#str.129") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 104); (Item Wb 97); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_plural'23str'2e130 : item :=
  (IData (a "glibc_plural#str.130") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 108); (Item Wb 101); (Item Wb 97); (Item Wb 110); (Item Wb 117); (Item Wb 112); (Item Wb 58); (Item Wb 32); (Item Wb 100); (Item Wb 105); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 114); (Item Wb 100); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 32); (Item Wb 108); (Item Wb 111); (Item Wb 111); (Item Wb 107); (Item Wb 97); (Item Wb 104); (Item Wb 101); (Item Wb 97); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_plural'23str'2e131 : item :=
  (IData (a "glibc_plural#str.131") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 108); (Item Wb 101); (Item Wb 97); (Item Wb 110); (Item Wb 117); (Item Wb 112); (Item Wb 58); (Item Wb 32); (Item Wb 112); (Item Wb 111); (Item Wb 112); (Item Wb 112); (Item Wb 105); (Item Wb 110); (Item Wb 103); (Item Wb 0)]).

Definition item_glibc_plural'23yycheck : item :=
  (IData (a "glibc_plural#yycheck") (LRo (a "local")) 1 [(Item Wb 1); (Item Wb 0); (Item Wb 5); (Item Wb 4); (Item Wb 7); (Item Wb 8); (Item Wb 9); (Item Wb 10); (Item Wb 10); (Item Wb 10); (Item Wb 11); (Item Wb 12); (Item Wb 13); (Item Wb 14); (Item Wb 15); (Item Wb 16); (Item Wb 3); (Item Wb 4); (Item Wb 5); (Item Wb (-1)); (Item Wb 7); (Item Wb 8); (Item Wb 9); (Item Wb 10); (Item Wb 25); (Item Wb 3); (Item Wb 4); (Item Wb 5); (Item Wb 15); (Item Wb 7); (Item Wb 8); (Item Wb 9); (Item Wb 10); (Item Wb 6); (Item Wb 12); (Item Wb 9); (Item Wb 10); (Item Wb (-1)); (Item Wb 11); (Item Wb (-1)); (Item Wb 13); (Item Wb 14); (Item Wb 3); (Item Wb 4); (Item Wb 5); (Item Wb (-1)); (Item Wb 7); (Item Wb 8); (Item Wb 9); (Item Wb 10); (Item Wb 7); (Item Wb 8); (Item Wb 9); (Item Wb 10); (Item Wb 8); (Item Wb 9); (Item Wb 10)]).

Definition item_glibc_plural'23yydefact : item :=
  (IData (a "glibc_plural#yydefact") (LRo (a "local")) 1 [(Str [0; 0; 12; 11; 0; 0; 2; 10; 0; 1; 0; 0; 0; 0; 0; 0; 0; 13; 0; 4; 5; 6; 7; 8; 9; 0; 3])]).

Definition item_glibc_plural'23yydefgoto : item :=
  (IData (a "glibc_plural#yydefgoto") (LRo (a "local")) 1 [(Str [0; 5; 6])]).

Definition item_glibc_plural'23yypact : item :=
  (IData (a "glibc_plural#yypact") (LRo (a "local")) 1 [(Item Wb 27); (Item Wb 27); (Item Wb (-4)); (Item Wb (-4)); (Item Wb 27); (Item Wb 1); (Item Wb 39); (Item Wb (-4)); (Item Wb 13); (Item Wb (-4)); (Item Wb 27); (Item Wb 27); (Item Wb 27); (Item Wb 27); (Item Wb 27); (Item Wb 27); (Item Wb 27); (Item Wb (-4)); (Item Wb 22); (Item Wb (-3)); (Item Wb 43); (Item Wb 46); (Item Wb 26); (Item Wb (-2)); (Item Wb (-4)); (Item Wb 27); (Item Wb 39)]).

Definition item_glibc_plural'23yypgoto : item :=
  (IData (a "glibc_plural#yypgoto") (LRo (a "local")) 1 [(Item Wb (-4)); (Item Wb (-4)); (Item Wb (-1))]).

Definition item_glibc_plural'23yyr1 : item :=
  (IData (a "glibc_plural#yyr1") (LRo (a "local")) 1 [(Str [0; 16; 17; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18])]).

Definition item_glibc_plural'23yyr2 : item :=
  (IData (a "glibc_plural#yyr2") (LRo (a "local")) 1 [(Str [0; 2; 1; 5; 3; 3; 3; 3; 3; 3; 2; 1; 1; 3])]).

Definition item_glibc_plural'23yystos : item :=
  (IData (a "glibc_plural#yystos") (LRo (a "local")) 1 [(Str [0; 6; 11; 13; 14; 17; 18; 18; 18; 0; 3; 4; 5; 7; 8; 9; 10; 15; 18; 18; 18; 18; 18; 18; 18; 12; 18])]).

Definition item_glibc_plural'23yytable : item :=
  (IData (a "glibc_plural#yytable") (LRo (a "local")) 1 [(Str [7; 9; 12; 8; 13; 14; 15; 16; 16; 18; 19; 20; 21; 22; 23; 24; 10; 11; 12; 0; 13; 14; 15; 16; 26; 10; 11; 12; 17; 13; 14; 15; 16; 1; 25; 15; 16; 0; 2; 0; 3; 4; 10; 11; 12; 0; 13; 14; 15; 16; 13; 14; 15; 16; 14; 15; 16])]).

Definition item_glibc_plural'23yytranslate : item :=
  (IData (a "glibc_plural#yytranslate") (LRo (a "local")) 1 [(Str (app (app (app [0; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2] [2; 6; 2; 2; 2; 2; 5; 2; 14; 15; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 12; 2; 2; 2; 2; 3; 2]) (app [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2] [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 13; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 4; 2; 2; 2; 2; 2; 2])) (app (app [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2] [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]) (app [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2] [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 1; 2; 7; 8; 9; 10; 11]))))]).
