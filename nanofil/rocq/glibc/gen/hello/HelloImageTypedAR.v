(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn_glibc_l10nflist'23argz_count__ : func :=
  ir_fn{ "local" "glibc_l10nflist#argz_count__"(P %"v0", L %"v2") -> (RClass L) {
  @"start":
    => goto "L5";
  @"L5" [%"pr.3" : L = phi("L6" => %"v22", "start" => #0); %"pr.2" : L = phi("L6" => %"v20", "start" => %"v2"); %"pr.1" : P = phi("L6" => %"v16", "start" => %"v0")]:
    %"v9" : W = (Cmp Ugt L) %"pr.2", #0
    => br %"v9" ? "L6" : "L7";
  @"L6":
    call %"v12" : L = $"__GI_strlen"(P %"pr.1");
    %"v15" : L = Add %"v12", #1;
    %"v16" = %"pr.1" +p %"v15";
    %"v20" : L = Sub %"pr.2", %"v15";
    %"v22" : L = Add %"pr.3", #1
    => goto poll "L5";
  @"L7":
    => ret %"pr.3"
} }.

Definition hello_image_fn_glibc_l10nflist'23argz_stringify__ : func :=
  ir_fn{ "local" "glibc_l10nflist#argz_stringify__"(P %"v0", L %"v2", W %"v4") -> RVoid {
  @"start":
    => goto "L6";
  @"L6" [%"pr.3" : L = phi("start" => %"v2", "L21" => %"v20", "L7" => %"v20"); %"pr.2" : P = phi("start" => %"v0", "L21" => %"v27", "L7" => %"v16")]:
    %"v10" : W = (Cmp Ugt L) %"pr.3", #0
    => br %"v10" ? "L7" : "L8";
  @"L7":
    call %"v13" : L = $"__GI_strlen"(P %"pr.2");
    %"v16" = %"pr.2" +p %"v13";
    %"v19" : L = Add %"v13", #1;
    %"v20" : L = Sub %"pr.3", %"v19";
    %"v25" : W = (Cmp Ugt L) %"v20", #0
    => br %"v25" ? "L21" : poll "L6";
  @"L21":
    %"v27" = %"v16" +p #1;
    %"v29" : W = (Ext Sb) %"v4";
    %"chk0" : A = (Check 0 1 Write 1) %"v16";
    store Wb [%"chk0" + 0] <- %"v29"
    => goto poll "L6";
  @"L8":
    => ret void
} }.

Definition hello_image_fn___argz_add_sep : func :=
  ir_fn{ "export" "__argz_add_sep"(P %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    call %"v10" : L = $"__GI_strlen"(P %"v4");
    %"v11" : L = Add %"v10", #1;
    %"v16" : W = (Cmp Ugt L) %"v11", #1
    => br %"v16" ? "L12" : "L14";
  @"L12":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 1) %"v2";
    %"v23" : L = (RawLoad LdL 0) %"chk1";
    %"v25" : L = Add %"v23", %"v11";
    call %"v26" : P = $"realloc"(P %"v21", L %"v25");
    %"v31" : L = Ptoi %"v26";
    %"v32" : L = Ptoi #0;
    %"v33" : W = (Cmp Eq L) %"v31", %"v32"
    => br %"v33" ? "L27" : "L29";
  @"L27":
    => ret #12;
  @"L29":
    %"chk2" : A = (Renew 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk2" + 0] <- %"v26";
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Read 1) %"chk1", %"v2";
    %"v40" : L = (RawLoad LdL 0) %"chk4";
    %"v41" = %"v38" +p %"v40"
    => goto "L43";
  @"L43" [%"pr.5" : P = phi("L29" => %"v41", "L48" => %"pr.6"); %"pr.4" : P = phi("L29" => %"v4", "L48" => %"v81"); %"pr.1" : L = phi("L29" => %"v11", "L48" => %"pr.2")]:
    %"chk5" : A = (Check 0 1 Read 1) %"pr.4";
    %"v50" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v52" : W = (Cmp Eq W) %"v50", %"v6"
    => br %"v52" ? "L46" : "L47";
  @"L46":
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v59" : L = Ptoi %"pr.5";
    %"v60" : L = Ptoi %"v58";
    %"v61" : W = (Cmp Ugt L) %"v59", %"v60"
    => br %"v61" ? "L62" : "L63";
  @"L62":
    %"v67" = %"pr.5" +p #18446744073709551615;
    %"chk7" : A = (Check 0 1 Read 1) %"v67";
    %"v68" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"v69" : W = (Cmp Ne W) %"v68", #0
    => goto "L63";
  @"L63" [%"v71" : W = phi("L46" => #0, "L62" => %"v69")]:
    => br %"v71" ? "L53" : "L54";
  @"L53":
    %"v73" = %"pr.5" +p #1;
    %"chk8" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk8" + 0] <- #0
    => goto "L48";
  @"L54":
    %"v75" : L = Sub %"pr.1", #1
    => goto "L48";
  @"L47":
    %"v77" = %"pr.5" +p #1;
    %"v79" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"chk10" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk10" + 0] <- %"v79"
    => goto "L48";
  @"L48" [%"pr.6" : P = phi("L47" => %"v77", "L53" => %"v73", "L54" => %"pr.5"); %"pr.2" : L = phi("L47" => %"pr.1", "L53" => %"pr.1", "L54" => %"v75")]:
    %"v81" = %"pr.4" +p #1;
    %"v82" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v83" : W = (Cmp Ne W) %"v82", #0
    => br %"v83" ? poll "L43" : "L45";
  @"L45":
    %"chk12" : A = (Renew 0 8 Read 1) %"chk1", %"v2";
    %"v85" : L = (RawLoad LdL 0) %"chk12";
    %"v87" : L = Add %"v85", %"pr.2";
    %"chk13" : A = (Renew 0 8 Write 1) %"chk1", %"v2";
    store Wl [%"chk13" + 0] <- %"v87"
    => goto "L14";
  @"L14":
    => ret #0
} }.

Definition hello_image_fn___argz_create_sep : func :=
  ir_fn{ "export" "__argz_create_sep"(P %"v0", W %"v2", P %"v4", P %"v6") -> (RClass W) {
  @"start":
    call %"v10" : L = $"__GI_strlen"(P %"v0");
    %"v11" : L = Add %"v10", #1;
    %"v16" : W = (Cmp Ugt L) %"v11", #1
    => br %"v16" ? "L12" : "L13";
  @"L12":
    call %"v21" : P = $"malloc"(L %"v11");
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- %"v21";
    %"chk1" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v27" : L = Ptoi %"v26";
    %"v28" : L = Ptoi #0;
    %"v29" : W = (Cmp Eq L) %"v27", %"v28"
    => br %"v29" ? "L22" : "L24";
  @"L22":
    => ret #12;
  @"L24":
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L34";
  @"L34" [%"pr.5" : P = phi("L24" => %"v33", "L39" => %"pr.6"); %"pr.4" : P = phi("L24" => %"v0", "L39" => %"v72"); %"pr.1" : L = phi("L24" => %"v11", "L39" => %"pr.2")]:
    %"chk3" : A = (Check 0 1 Read 1) %"pr.4";
    %"v41" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v43" : W = (Cmp Eq W) %"v41", %"v2"
    => br %"v43" ? "L37" : "L38";
  @"L37":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v50" : L = Ptoi %"pr.5";
    %"v51" : L = Ptoi %"v49";
    %"v52" : W = (Cmp Ugt L) %"v50", %"v51"
    => br %"v52" ? "L53" : "L54";
  @"L53":
    %"v58" = %"pr.5" +p #18446744073709551615;
    %"chk5" : A = (Check 0 1 Read 1) %"v58";
    %"v59" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v60" : W = (Cmp Ne W) %"v59", #0
    => goto "L54";
  @"L54" [%"v62" : W = phi("L37" => #0, "L53" => %"v60")]:
    => br %"v62" ? "L44" : "L45";
  @"L44":
    %"v64" = %"pr.5" +p #1;
    %"chk6" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk6" + 0] <- #0
    => goto "L39";
  @"L45":
    %"v66" : L = Sub %"pr.1", #1
    => goto "L39";
  @"L38":
    %"v68" = %"pr.5" +p #1;
    %"v70" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"chk8" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk8" + 0] <- %"v70"
    => goto "L39";
  @"L39" [%"pr.6" : P = phi("L38" => %"v68", "L44" => %"v64", "L45" => %"pr.5"); %"pr.2" : L = phi("L38" => %"pr.1", "L44" => %"pr.1", "L45" => %"v66")]:
    %"v72" = %"pr.4" +p #1;
    %"v73" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v74" : W = (Cmp Ne W) %"v73", #0
    => br %"v74" ? poll "L34" : "L36";
  @"L36":
    %"v79" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v79" ? "L75" : "L77";
  @"L75":
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk10";
    call void $"free"(P %"v81");
    %"chk11" : A = (Renew 0 8 Write 8) %"chk0", %"v4";
    store.ptr [%"chk11" + 0] <- #0;
    %"chk12" : A = (Check 0 8 Write 1) %"v6";
    store Wl [%"chk12" + 0] <- #0
    => goto "L77";
  @"L77":
    %"chk13" : A = (Check 0 8 Write 1) %"v6";
    store Wl [%"chk13" + 0] <- %"pr.2"
    => goto "L14";
  @"L13":
    %"chk14" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk14" + 0] <- #0;
    %"chk15" : A = (Check 0 8 Write 1) %"v6";
    store Wl [%"chk15" + 0] <- #0
    => goto "L14";
  @"L14":
    => ret #0
} }.

Definition hello_image_fn___GI___argz_next : func :=
  ir_fn{ "export" "__GI___argz_next"(P %"v0", L %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v10" : L = Ptoi %"v4";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L6" : "L7";
  @"L6":
    %"v18" = %"v0" +p %"v2";
    %"v20" : L = Ptoi %"v18";
    %"v21" : W = (Cmp Ult L) %"v10", %"v20"
    => br %"v21" ? "L12" : "L14";
  @"L12":
    call %"v23" : P = $"__GI_strchr"(P %"v4", W #0);
    %"v24" = %"v23" +p #1
    => goto "L14";
  @"L14" [%"pr.1" : P = phi("L12" => %"v24", "L6" => %"v4")]:
    %"v32" : L = Ptoi %"pr.1";
    %"v34" : W = (Cmp Uge L) %"v32", %"v20"
    => br %"v34" ? "L27" : "L26";
  @"L26":
    => goto "L27";
  @"L27" [%"v36" : P = phi("L26" => %"pr.1", "L14" => #0)]:
    => ret %"v36";
  @"L7":
    %"v42" : W = (Cmp Ugt L) %"v2", #0
    => br %"v42" ? "L38" : "L39";
  @"L38":
    => ret %"v0";
  @"L39":
    => ret #0
} }.
