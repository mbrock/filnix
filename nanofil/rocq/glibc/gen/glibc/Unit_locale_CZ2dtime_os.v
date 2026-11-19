(** This file defines checked IR from glibc’s `locale/C-time.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item__nl_C_LC_TIME : item :=
  (IData (a "_nl_C_LC_TIME") (LRo (a "export")) 8 (app (app [(Sym (a "_nl_C_name") 0); (Item Wl 0); (Item Wl 0); (Item Ww 0); (Zero 4); (Item Wl 0); (Item Ww 4294967295); (Item Ww 0); (Item Ww 159); (Zero 4); (Sym (a "glibc_C_time#str.40") 0); (Sym (a "glibc_C_time#str.41") 0); (Sym (a "glibc_C_time#str.42") 0); (Sym (a "glibc_C_time#str.43") 0); (Sym (a "glibc_C_time#str.44") 0); (Sym (a "glibc_C_time#str.45") 0); (Sym (a "glibc_C_time#str.46") 0); (Sym (a "glibc_C_time#str.47") 0); (Sym (a "glibc_C_time#str.48") 0); (Sym (a "glibc_C_time#str.49") 0); (Sym (a "glibc_C_time#str.50") 0); (Sym (a "glibc_C_time#str.51") 0); (Sym (a "glibc_C_time#str.52") 0); (Sym (a "glibc_C_time#str.53") 0); (Sym (a "glibc_C_time#str.54") 0); (Sym (a "glibc_C_time#str.55") 0); (Sym (a "glibc_C_time#str.56") 0); (Sym (a "glibc_C_time#str.57") 0); (Sym (a "glibc_C_time#str.58") 0); (Sym (a "glibc_C_time#str.59") 0); (Sym (a "glibc_C_time#str.60") 0); (Sym (a "glibc_C_time#str.61") 0); (Sym (a "glibc_C_time#str.62") 0); (Sym (a "glibc_C_time#str.63") 0); (Sym (a "glibc_C_time#str.64") 0); (Sym (a "glibc_C_time#str.65") 0); (Sym (a "glibc_C_time#str.66") 0); (Sym (a "glibc_C_time#str.67") 0); (Sym (a "glibc_C_time#str.68") 0); (Sym (a "glibc_C_time#str.69") 0); (Sym (a "glibc_C_time#str.58") 0); (Sym (a "glibc_C_time#str.70") 0)] [(Sym (a "glibc_C_time#str.71") 0); (Sym (a "glibc_C_time#str.72") 0); (Sym (a "glibc_C_time#str.73") 0); (Sym (a "glibc_C_time#str.74") 0); (Sym (a "glibc_C_time#str.75") 0); (Sym (a "glibc_C_time#str.76") 0); (Sym (a "glibc_C_time#str.77") 0); (Sym (a "glibc_C_time#str.78") 0); (Sym (a "glibc_C_time#str.79") 0); (Sym (a "glibc_C_time#str.80") 0); (Sym (a "glibc_C_time#str.81") 0); (Sym (a "glibc_C_time#str.82") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.83") 0); (Item Ww 0); (Zero 4); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.84") 0); (Sym (a "glibc_C_time#str.85") 0); (Sym (a "glibc_C_time#str.86") 0); (Sym (a "glibc_C_time#str.87") 0); (Sym (a "glibc_C_time#str.88") 0); (Sym (a "glibc_C_time#str.89") 0); (Sym (a "glibc_C_time#str.90") 0); (Sym (a "glibc_C_time#str.91") 0); (Sym (a "glibc_C_time#str.92") 0); (Sym (a "glibc_C_time#str.93") 0); (Sym (a "glibc_C_time#str.94") 0); (Sym (a "glibc_C_time#str.95") 0); (Sym (a "glibc_C_time#str.96") 0); (Sym (a "glibc_C_time#str.97") 0); (Sym (a "glibc_C_time#str.98") 0); (Sym (a "glibc_C_time#str.99") 0); (Sym (a "glibc_C_time#str.100") 0); (Sym (a "glibc_C_time#str.101") 0); (Sym (a "glibc_C_time#str.102") 0); (Sym (a "glibc_C_time#str.103") 0); (Sym (a "glibc_C_time#str.104") 0); (Sym (a "glibc_C_time#str.105") 0)]) (app [(Sym (a "glibc_C_time#str.106") 0); (Sym (a "glibc_C_time#str.107") 0); (Sym (a "glibc_C_time#str.108") 0); (Sym (a "glibc_C_time#str.109") 0); (Sym (a "glibc_C_time#str.110") 0); (Sym (a "glibc_C_time#str.111") 0); (Sym (a "glibc_C_time#str.112") 0); (Sym (a "glibc_C_time#str.113") 0); (Sym (a "glibc_C_time#str.102") 0); (Sym (a "glibc_C_time#str.114") 0); (Sym (a "glibc_C_time#str.115") 0); (Sym (a "glibc_C_time#str.116") 0); (Sym (a "glibc_C_time#str.117") 0); (Sym (a "glibc_C_time#str.118") 0); (Sym (a "glibc_C_time#str.119") 0); (Sym (a "glibc_C_time#str.120") 0); (Sym (a "glibc_C_time#str.121") 0); (Sym (a "glibc_C_time#str.122") 0); (Sym (a "glibc_C_time#str.123") 0); (Sym (a "glibc_C_time#str.124") 0); (Sym (a "glibc_C_time#str.125") 0); (Sym (a "glibc_C_time#str.126") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.127") 0); (Sym (a "glibc_C_time#str.128") 0); (Item Ww 19971130); (Zero 4); (Sym (a "glibc_C_time#str.129") 0); (Sym (a "glibc_C_time#str.130") 0); (Sym (a "glibc_C_time#str.131") 0); (Sym (a "glibc_C_time#str.130") 0); (Sym (a "glibc_C_time#str.83") 0); (Sym (a "glibc_C_time#str.132") 0); (Sym (a "glibc_C_time#str.133") 0); (Sym (a "_nl_C_codeset") 0); (Sym (a "glibc_C_time#str.66") 0); (Sym (a "glibc_C_time#str.67") 0); (Sym (a "glibc_C_time#str.68") 0); (Sym (a "glibc_C_time#str.69") 0); (Sym (a "glibc_C_time#str.58") 0)] [(Sym (a "glibc_C_time#str.70") 0); (Sym (a "glibc_C_time#str.71") 0); (Sym (a "glibc_C_time#str.72") 0); (Sym (a "glibc_C_time#str.73") 0); (Sym (a "glibc_C_time#str.74") 0); (Sym (a "glibc_C_time#str.75") 0); (Sym (a "glibc_C_time#str.76") 0); (Sym (a "glibc_C_time#str.110") 0); (Sym (a "glibc_C_time#str.111") 0); (Sym (a "glibc_C_time#str.112") 0); (Sym (a "glibc_C_time#str.113") 0); (Sym (a "glibc_C_time#str.102") 0); (Sym (a "glibc_C_time#str.114") 0); (Sym (a "glibc_C_time#str.115") 0); (Sym (a "glibc_C_time#str.116") 0); (Sym (a "glibc_C_time#str.117") 0); (Sym (a "glibc_C_time#str.118") 0); (Sym (a "glibc_C_time#str.119") 0); (Sym (a "glibc_C_time#str.120") 0); (Sym (a "glibc_C_time#str.54") 0); (Sym (a "glibc_C_time#str.55") 0); (Sym (a "glibc_C_time#str.56") 0); (Sym (a "glibc_C_time#str.57") 0); (Sym (a "glibc_C_time#str.58") 0); (Sym (a "glibc_C_time#str.59") 0); (Sym (a "glibc_C_time#str.60") 0); (Sym (a "glibc_C_time#str.61") 0); (Sym (a "glibc_C_time#str.62") 0); (Sym (a "glibc_C_time#str.63") 0); (Sym (a "glibc_C_time#str.64") 0); (Sym (a "glibc_C_time#str.65") 0); (Sym (a "glibc_C_time#str.98") 0); (Sym (a "glibc_C_time#str.99") 0); (Sym (a "glibc_C_time#str.100") 0); (Sym (a "glibc_C_time#str.101") 0); (Sym (a "glibc_C_time#str.102") 0); (Sym (a "glibc_C_time#str.103") 0); (Sym (a "glibc_C_time#str.104") 0); (Sym (a "glibc_C_time#str.105") 0); (Sym (a "glibc_C_time#str.106") 0); (Sym (a "glibc_C_time#str.107") 0); (Sym (a "glibc_C_time#str.108") 0); (Sym (a "glibc_C_time#str.109") 0)]))).

Definition item_glibc_C_time'23str'2e100 : item :=
  (IData (a "glibc_C_time#str.100") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 97); (Item Ww 114); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e101 : item :=
  (IData (a "glibc_C_time#str.101") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 112); (Item Ww 114); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e102 : item :=
  (IData (a "glibc_C_time#str.102") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e103 : item :=
  (IData (a "glibc_C_time#str.103") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 117); (Item Ww 110); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e104 : item :=
  (IData (a "glibc_C_time#str.104") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 117); (Item Ww 108); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e105 : item :=
  (IData (a "glibc_C_time#str.105") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 117); (Item Ww 103); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e106 : item :=
  (IData (a "glibc_C_time#str.106") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 101); (Item Ww 112); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e107 : item :=
  (IData (a "glibc_C_time#str.107") (LRo (a "local")) 4 [(Item Ww 79); (Item Ww 99); (Item Ww 116); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e108 : item :=
  (IData (a "glibc_C_time#str.108") (LRo (a "local")) 4 [(Item Ww 78); (Item Ww 111); (Item Ww 118); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e109 : item :=
  (IData (a "glibc_C_time#str.109") (LRo (a "local")) 4 [(Item Ww 68); (Item Ww 101); (Item Ww 99); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e110 : item :=
  (IData (a "glibc_C_time#str.110") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 97); (Item Ww 110); (Item Ww 117); (Item Ww 97); (Item Ww 114); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e111 : item :=
  (IData (a "glibc_C_time#str.111") (LRo (a "local")) 4 [(Item Ww 70); (Item Ww 101); (Item Ww 98); (Item Ww 114); (Item Ww 117); (Item Ww 97); (Item Ww 114); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e112 : item :=
  (IData (a "glibc_C_time#str.112") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 97); (Item Ww 114); (Item Ww 99); (Item Ww 104); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e113 : item :=
  (IData (a "glibc_C_time#str.113") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 112); (Item Ww 114); (Item Ww 105); (Item Ww 108); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e114 : item :=
  (IData (a "glibc_C_time#str.114") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 117); (Item Ww 110); (Item Ww 101); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e115 : item :=
  (IData (a "glibc_C_time#str.115") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 117); (Item Ww 108); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e116 : item :=
  (IData (a "glibc_C_time#str.116") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 117); (Item Ww 103); (Item Ww 117); (Item Ww 115); (Item Ww 116); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e117 : item :=
  (IData (a "glibc_C_time#str.117") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 101); (Item Ww 112); (Item Ww 116); (Item Ww 101); (Item Ww 109); (Item Ww 98); (Item Ww 101); (Item Ww 114); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e118 : item :=
  (IData (a "glibc_C_time#str.118") (LRo (a "local")) 4 [(Item Ww 79); (Item Ww 99); (Item Ww 116); (Item Ww 111); (Item Ww 98); (Item Ww 101); (Item Ww 114); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e119 : item :=
  (IData (a "glibc_C_time#str.119") (LRo (a "local")) 4 [(Item Ww 78); (Item Ww 111); (Item Ww 118); (Item Ww 101); (Item Ww 109); (Item Ww 98); (Item Ww 101); (Item Ww 114); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e120 : item :=
  (IData (a "glibc_C_time#str.120") (LRo (a "local")) 4 [(Item Ww 68); (Item Ww 101); (Item Ww 99); (Item Ww 101); (Item Ww 109); (Item Ww 98); (Item Ww 101); (Item Ww 114); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e121 : item :=
  (IData (a "glibc_C_time#str.121") (LRo (a "local")) 4 [(Item Ww 65); (Item Ww 77); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e122 : item :=
  (IData (a "glibc_C_time#str.122") (LRo (a "local")) 4 [(Item Ww 80); (Item Ww 77); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e123 : item :=
  (IData (a "glibc_C_time#str.123") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 97); (Item Ww 32); (Item Ww 37); (Item Ww 98); (Item Ww 32); (Item Ww 37); (Item Ww 101); (Item Ww 32); (Item Ww 37); (Item Ww 72); (Item Ww 58); (Item Ww 37); (Item Ww 77); (Item Ww 58); (Item Ww 37); (Item Ww 83); (Item Ww 32); (Item Ww 37); (Item Ww 89); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e124 : item :=
  (IData (a "glibc_C_time#str.124") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 109); (Item Ww 47); (Item Ww 37); (Item Ww 100); (Item Ww 47); (Item Ww 37); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e125 : item :=
  (IData (a "glibc_C_time#str.125") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 72); (Item Ww 58); (Item Ww 37); (Item Ww 77); (Item Ww 58); (Item Ww 37); (Item Ww 83); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e126 : item :=
  (IData (a "glibc_C_time#str.126") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 73); (Item Ww 58); (Item Ww 37); (Item Ww 77); (Item Ww 58); (Item Ww 37); (Item Ww 83); (Item Ww 32); (Item Ww 37); (Item Ww 112); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e127 : item :=
  (IData (a "glibc_C_time#str.127") (LRo (a "local")) 4 [(Item Ww 0)]).

Definition item_glibc_C_time'23str'2e128 : item :=
  (IData (a "glibc_C_time#str.128") (LRo (a "local")) 1 [(Item Wb 7); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e129 : item :=
  (IData (a "glibc_C_time#str.129") (LRo (a "local")) 1 [(Item Wb 4); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e130 : item :=
  (IData (a "glibc_C_time#str.130") (LRo (a "local")) 1 [(Item Wb 1); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e131 : item :=
  (IData (a "glibc_C_time#str.131") (LRo (a "local")) 1 [(Item Wb 2); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e132 : item :=
  (IData (a "glibc_C_time#str.132") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 97); (Item Wb 32); (Item Wb 37); (Item Wb 98); (Item Wb 32); (Item Wb 37); (Item Wb 101); (Item Wb 32); (Item Wb 37); (Item Wb 72); (Item Wb 58); (Item Wb 37); (Item Wb 77); (Item Wb 58); (Item Wb 37); (Item Wb 83); (Item Wb 32); (Item Wb 37); (Item Wb 90); (Item Wb 32); (Item Wb 37); (Item Wb 89); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e133 : item :=
  (IData (a "glibc_C_time#str.133") (LRo (a "local")) 4 [(Item Ww 37); (Item Ww 97); (Item Ww 32); (Item Ww 37); (Item Ww 98); (Item Ww 32); (Item Ww 37); (Item Ww 101); (Item Ww 32); (Item Ww 37); (Item Ww 72); (Item Ww 58); (Item Ww 37); (Item Ww 77); (Item Ww 58); (Item Ww 37); (Item Ww 83); (Item Ww 32); (Item Ww 37); (Item Ww 90); (Item Ww 32); (Item Ww 37); (Item Ww 89); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e40 : item :=
  (IData (a "glibc_C_time#str.40") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 117); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e41 : item :=
  (IData (a "glibc_C_time#str.41") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 111); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e42 : item :=
  (IData (a "glibc_C_time#str.42") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 117); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e43 : item :=
  (IData (a "glibc_C_time#str.43") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e44 : item :=
  (IData (a "glibc_C_time#str.44") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 104); (Item Wb 117); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e45 : item :=
  (IData (a "glibc_C_time#str.45") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 114); (Item Wb 105); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e46 : item :=
  (IData (a "glibc_C_time#str.46") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 97); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e47 : item :=
  (IData (a "glibc_C_time#str.47") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 117); (Item Wb 110); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e48 : item :=
  (IData (a "glibc_C_time#str.48") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 111); (Item Wb 110); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e49 : item :=
  (IData (a "glibc_C_time#str.49") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 117); (Item Wb 101); (Item Wb 115); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e50 : item :=
  (IData (a "glibc_C_time#str.50") (LRo (a "local")) 1 [(Item Wb 87); (Item Wb 101); (Item Wb 100); (Item Wb 110); (Item Wb 101); (Item Wb 115); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e51 : item :=
  (IData (a "glibc_C_time#str.51") (LRo (a "local")) 1 [(Item Wb 84); (Item Wb 104); (Item Wb 117); (Item Wb 114); (Item Wb 115); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e52 : item :=
  (IData (a "glibc_C_time#str.52") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 114); (Item Wb 105); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e53 : item :=
  (IData (a "glibc_C_time#str.53") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 97); (Item Wb 116); (Item Wb 117); (Item Wb 114); (Item Wb 100); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e54 : item :=
  (IData (a "glibc_C_time#str.54") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 97); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e55 : item :=
  (IData (a "glibc_C_time#str.55") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 101); (Item Wb 98); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e56 : item :=
  (IData (a "glibc_C_time#str.56") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 97); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e57 : item :=
  (IData (a "glibc_C_time#str.57") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 112); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e58 : item :=
  (IData (a "glibc_C_time#str.58") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 97); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e59 : item :=
  (IData (a "glibc_C_time#str.59") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 117); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e60 : item :=
  (IData (a "glibc_C_time#str.60") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 117); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e61 : item :=
  (IData (a "glibc_C_time#str.61") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 117); (Item Wb 103); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e62 : item :=
  (IData (a "glibc_C_time#str.62") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 101); (Item Wb 112); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e63 : item :=
  (IData (a "glibc_C_time#str.63") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 99); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e64 : item :=
  (IData (a "glibc_C_time#str.64") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 118); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e65 : item :=
  (IData (a "glibc_C_time#str.65") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 101); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e66 : item :=
  (IData (a "glibc_C_time#str.66") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 97); (Item Wb 110); (Item Wb 117); (Item Wb 97); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e67 : item :=
  (IData (a "glibc_C_time#str.67") (LRo (a "local")) 1 [(Item Wb 70); (Item Wb 101); (Item Wb 98); (Item Wb 114); (Item Wb 117); (Item Wb 97); (Item Wb 114); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e68 : item :=
  (IData (a "glibc_C_time#str.68") (LRo (a "local")) 1 [(Item Wb 77); (Item Wb 97); (Item Wb 114); (Item Wb 99); (Item Wb 104); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e69 : item :=
  (IData (a "glibc_C_time#str.69") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e70 : item :=
  (IData (a "glibc_C_time#str.70") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 117); (Item Wb 110); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e71 : item :=
  (IData (a "glibc_C_time#str.71") (LRo (a "local")) 1 [(Item Wb 74); (Item Wb 117); (Item Wb 108); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e72 : item :=
  (IData (a "glibc_C_time#str.72") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 117); (Item Wb 103); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e73 : item :=
  (IData (a "glibc_C_time#str.73") (LRo (a "local")) 1 [(Item Wb 83); (Item Wb 101); (Item Wb 112); (Item Wb 116); (Item Wb 101); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e74 : item :=
  (IData (a "glibc_C_time#str.74") (LRo (a "local")) 1 [(Item Wb 79); (Item Wb 99); (Item Wb 116); (Item Wb 111); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e75 : item :=
  (IData (a "glibc_C_time#str.75") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 111); (Item Wb 118); (Item Wb 101); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e76 : item :=
  (IData (a "glibc_C_time#str.76") (LRo (a "local")) 1 [(Item Wb 68); (Item Wb 101); (Item Wb 99); (Item Wb 101); (Item Wb 109); (Item Wb 98); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e77 : item :=
  (IData (a "glibc_C_time#str.77") (LRo (a "local")) 1 [(Item Wb 65); (Item Wb 77); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e78 : item :=
  (IData (a "glibc_C_time#str.78") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 77); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e79 : item :=
  (IData (a "glibc_C_time#str.79") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 97); (Item Wb 32); (Item Wb 37); (Item Wb 98); (Item Wb 32); (Item Wb 37); (Item Wb 101); (Item Wb 32); (Item Wb 37); (Item Wb 72); (Item Wb 58); (Item Wb 37); (Item Wb 77); (Item Wb 58); (Item Wb 37); (Item Wb 83); (Item Wb 32); (Item Wb 37); (Item Wb 89); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e80 : item :=
  (IData (a "glibc_C_time#str.80") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 109); (Item Wb 47); (Item Wb 37); (Item Wb 100); (Item Wb 47); (Item Wb 37); (Item Wb 121); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e81 : item :=
  (IData (a "glibc_C_time#str.81") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 72); (Item Wb 58); (Item Wb 37); (Item Wb 77); (Item Wb 58); (Item Wb 37); (Item Wb 83); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e82 : item :=
  (IData (a "glibc_C_time#str.82") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 73); (Item Wb 58); (Item Wb 37); (Item Wb 77); (Item Wb 58); (Item Wb 37); (Item Wb 83); (Item Wb 32); (Item Wb 37); (Item Wb 112); (Item Wb 0)]).

Definition item_glibc_C_time'23str'2e83 : item :=
  (IData (a "glibc_C_time#str.83") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition item_glibc_C_time'23str'2e84 : item :=
  (IData (a "glibc_C_time#str.84") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 117); (Item Ww 110); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e85 : item :=
  (IData (a "glibc_C_time#str.85") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 111); (Item Ww 110); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e86 : item :=
  (IData (a "glibc_C_time#str.86") (LRo (a "local")) 4 [(Item Ww 84); (Item Ww 117); (Item Ww 101); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e87 : item :=
  (IData (a "glibc_C_time#str.87") (LRo (a "local")) 4 [(Item Ww 87); (Item Ww 101); (Item Ww 100); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e88 : item :=
  (IData (a "glibc_C_time#str.88") (LRo (a "local")) 4 [(Item Ww 84); (Item Ww 104); (Item Ww 117); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e89 : item :=
  (IData (a "glibc_C_time#str.89") (LRo (a "local")) 4 [(Item Ww 70); (Item Ww 114); (Item Ww 105); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e90 : item :=
  (IData (a "glibc_C_time#str.90") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 97); (Item Ww 116); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e91 : item :=
  (IData (a "glibc_C_time#str.91") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 117); (Item Ww 110); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e92 : item :=
  (IData (a "glibc_C_time#str.92") (LRo (a "local")) 4 [(Item Ww 77); (Item Ww 111); (Item Ww 110); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e93 : item :=
  (IData (a "glibc_C_time#str.93") (LRo (a "local")) 4 [(Item Ww 84); (Item Ww 117); (Item Ww 101); (Item Ww 115); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e94 : item :=
  (IData (a "glibc_C_time#str.94") (LRo (a "local")) 4 [(Item Ww 87); (Item Ww 101); (Item Ww 100); (Item Ww 110); (Item Ww 101); (Item Ww 115); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e95 : item :=
  (IData (a "glibc_C_time#str.95") (LRo (a "local")) 4 [(Item Ww 84); (Item Ww 104); (Item Ww 117); (Item Ww 114); (Item Ww 115); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e96 : item :=
  (IData (a "glibc_C_time#str.96") (LRo (a "local")) 4 [(Item Ww 70); (Item Ww 114); (Item Ww 105); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e97 : item :=
  (IData (a "glibc_C_time#str.97") (LRo (a "local")) 4 [(Item Ww 83); (Item Ww 97); (Item Ww 116); (Item Ww 117); (Item Ww 114); (Item Ww 100); (Item Ww 97); (Item Ww 121); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e98 : item :=
  (IData (a "glibc_C_time#str.98") (LRo (a "local")) 4 [(Item Ww 74); (Item Ww 97); (Item Ww 110); (Item Ww 0)]).

Definition item_glibc_C_time'23str'2e99 : item :=
  (IData (a "glibc_C_time#str.99") (LRo (a "local")) 4 [(Item Ww 70); (Item Ww 101); (Item Ww 98); (Item Ww 0)]).
