(** This file defines checked IR from glibc’s `string/strcasecmp_l.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___GI___strcasecmp_l : func :=
  ir_fn{ "export" "__GI___strcasecmp_l"(P %"v0", P %"v2", P %"v4") -> (RClass W) {
  @"start":
    %"v16" : L = Ptoi %"v0";
    %"v17" : L = Ptoi %"v2";
    %"v18" : W = (Cmp Eq L) %"v16", %"v17"
    => br %"v18" ? "L11" : "L20";
  @"L11":
    => ret #0;
  @"L20" [%"pr.2" : P = phi("start" => %"v2", "L21" => %"v113"); %"pr.1" : P = phi("start" => %"v0", "L21" => %"v126")]:
    %"v61" = %"v4" +p #112;
    %"chk0" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v64" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v65" : L = (Ext Sw) %"v64";
    %"v66" : L = Shl %"v65", #2;
    %"v67" = %"v62" +p %"v66";
    %"chk2" : A = (Check 0 4 Read 1) %"v67";
    %"v68" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v110" = %"v4" +p #112;
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v113" = %"pr.2" +p #1;
    %"chk4" : A = (Check 0 1 Read 1) %"pr.2";
    %"v114" : W = (RawLoad (LdNarrow Ub) 0) %"chk4";
    %"v115" : L = (Ext Sw) %"v114";
    %"v116" : L = Shl %"v115", #2;
    %"v117" = %"v111" +p %"v116";
    %"chk5" : A = (Check 0 4 Read 1) %"v117";
    %"v118" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v120" : W = Sub %"v68", %"v118";
    %"v121" : W = (Cmp Eq W) %"v120", #0
    => br %"v121" ? "L21" : "L22";
  @"L21":
    %"v126" = %"pr.1" +p #1;
    %"v127" : W = (RawLoad (LdNarrow Ub) 0) %"chk1";
    %"v128" : W = (Cmp Eq W) %"v127", #0
    => br %"v128" ? "L22" : poll "L20";
  @"L22":
    => ret %"v120"
} }.
