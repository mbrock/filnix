(** This file defines checked IR from glibc’s `intl/plural-exp.os` object.
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

Definition fn___gettext_extract_plural : func :=
  ir_fn{ "export" "__gettext_extract_plural"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v38" : P = (Alloc 8) #8;
    %"v40" : P = (Alloc 8) #16;
    %"v10" : L = Ptoi %"v0";
    %"v11" : L = Ptoi #0;
    %"v12" : W = (Cmp Ne L) %"v10", %"v11"
    => br %"v12" ? "L6" : "L36";
  @"L6":
    %"v16" : P = Copy $"glibc_plural_exp#str.134";
    call %"v17" : P = $"__GI_strstr"(P %"v0", P %"v16");
    %"v19" : P = Copy $"glibc_plural_exp#str.135";
    call %"v20" : P = $"__GI_strstr"(P %"v0", P %"v19");
    %"v25" : L = Ptoi %"v17";
    %"v27" : W = (Cmp Eq L) %"v25", %"v11"
    => br %"v27" ? "L29" : "L28";
  @"L28":
    %"v31" : L = Ptoi %"v20";
    %"v33" : W = (Cmp Eq L) %"v31", %"v11"
    => goto "L29";
  @"L29" [%"v35" : W = phi("L6" => #1, "L28" => %"v33")]:
    => br %"v35" ? "L36" : "L22";
  @"L22":
    %"v42" = %"v20" +p #9
    => goto "L43";
  @"L43" [%"pr.1" : P = phi("L22" => %"v42", "L44" => %"v64")]:
    %"chk0" : A = (Check 0 1 Read 1) %"pr.1";
    %"v47" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v48" : W = (Cmp Ne W) %"v47", #0
    => br %"v48" ? "iw_1.start" : "L50";
  @"iw_1.start":
    %"iw_1.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v0";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Renew 0 1 Read 1) %"chk0", %"pr.1";
    %"v54" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v55" : W = (Ext Ub) %"v54";
    %"v56" : L = (Ext Sw) %"v55";
    %"v57" : L = Shl %"v56", #1;
    %"v58" = %"v52" +p %"v57";
    %"chk3" : A = (Check 0 2 Read 1) %"v58";
    %"v59" : W = (RawLoad (LdNarrow Uh) 0) %"chk3";
    %"v60" : W = And %"v59", #8192;
    %"v61" : W = (Cmp Ne W) %"v60", #0
    => goto "L50";
  @"L50" [%"v62" : W = phi("L43" => #0, "iw_1.start" => %"v61")]:
    => br %"v62" ? "L44" : "L45";
  @"L44":
    %"v64" = %"pr.1" +p #1
    => goto poll "L43";
  @"L45":
    %"chk4" : A = (Renew 0 1 Read 1) %"chk0", %"pr.1";
    %"v69" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v70" : W = (Cmp Sge W) %"v69", #48
    => br %"v70" ? "L71" : "L72";
  @"L71":
    %"v74" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v75" : W = (Cmp Sle W) %"v74", #57
    => goto "L72";
  @"L72" [%"v77" : W = phi("L45" => #0, "L71" => %"v75")]:
    => br %"v77" ? "L67" : "L36";
  @"L67":
    call %"v81" : L = $"__GI___isoc23_strtoul"(P %"pr.1", P %"v38", W #10);
    %"chk6" : A = (Check 0 8 Read 8) %"v38";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v87" : L = Ptoi %"pr.1";
    %"v88" : L = Ptoi %"v86";
    %"v89" : W = (Cmp Eq L) %"v87", %"v88"
    => br %"v89" ? "L36" : "L84";
  @"L84":
    %"chk7" : A = (Check 0 8 Write 1) %"v4";
    store Wl [%"chk7" + 0] <- %"v81";
    %"v94" = %"v17" +p #7;
    %"chk8" : A = (Check 0 8 Write 8) %"v40";
    store.ptr [%"chk8" + 0] <- %"v94";
    call %"v99" : W = $"__gettextparse"(P %"v40");
    %"v100" : W = (Cmp Ne W) %"v99", #0
    => br %"v100" ? "L36" : "L98";
  @"L98":
    %"v103" = %"v40" +p #8;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk8", %"v103";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk10" + 0] <- %"v104"
    => goto "L8";
  @"L36":
    %"v106" : P = Copy $"__gettext_germanic_plural";
    %"chk11" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk11" + 0] <- %"v106";
    %"chk12" : A = (Check 0 8 Write 1) %"v4";
    store Wl [%"chk12" + 0] <- #2
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition item___gettext_germanic_plural : item :=
  (IData (a "__gettext_germanic_plural") (LRo (a "export")) 8 [(Item Ww 2); (Item Ww 13); (Sym (a "glibc_plural_exp#plvar") 0); (Sym (a "glibc_plural_exp#plone") 0); (Zero 8)]).

Definition item_glibc_plural_exp'23plone : item :=
  (IData (a "glibc_plural_exp#plone") (LRo (a "local")) 8 [(Item Ww 0); (Item Ww 1); (Item Wl 1); (Zero 16)]).

Definition item_glibc_plural_exp'23plvar : item :=
  (IData (a "glibc_plural_exp#plvar") (LRo (a "local")) 8 [(Item Ww 0); (Item Ww 0); (Zero 24)]).

Definition item_glibc_plural_exp'23str'2e134 : item :=
  (IData (a "glibc_plural_exp#str.134") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 108); (Item Wb 117); (Item Wb 114); (Item Wb 97); (Item Wb 108); (Item Wb 61); (Item Wb 0)]).

Definition item_glibc_plural_exp'23str'2e135 : item :=
  (IData (a "glibc_plural_exp#str.135") (LRo (a "local")) 1 [(Item Wb 110); (Item Wb 112); (Item Wb 108); (Item Wb 117); (Item Wb 114); (Item Wb 97); (Item Wb 108); (Item Wb 115); (Item Wb 61); (Item Wb 0)]).
