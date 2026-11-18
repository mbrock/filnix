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

Definition hello_image_fn__IO_default_setbuf : func :=
  ir_fn{ "export" "_IO_default_setbuf"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v10" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v11";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v13" = %"v11" +p #96;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v14";
    rawcall %"v16" : W = %"chk2"(P %"v0");
    %"v18" : W = (Cmp Eq W) %"v16", #4294967295
    => br %"v18" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"v24" : L = Ptoi %"v2";
    %"v25" : L = Ptoi #0;
    %"v26" : W = (Cmp Eq L) %"v24", %"v25"
    => br %"v26" ? "L28" : "L27";
  @"L27":
    %"v30" : W = (Cmp Eq L) %"v4", #0
    => goto "L28";
  @"L28" [%"v32" : W = phi("L8" => #1, "L27" => %"v30")]:
    => br %"v32" ? "L20" : "L21";
  @"L20":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v35" : W = Or %"v34", #2;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk4" + 0] <- %"v35";
    %"v38" = %"v0" +p #131;
    %"v41" = %"v38" +p #1;
    call void $"__GI__IO_setb"(P %"v0", P %"v38", P %"v41", W #0)
    => goto "L22";
  @"L21":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v43" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v45" : W = And %"v43", #4294967293;
    %"chk6" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk6" + 0] <- %"v45";
    %"v50" = %"v2" +p %"v4";
    call void $"__GI__IO_setb"(P %"v0", P %"v2", P %"v50", W #0)
    => goto "L22";
  @"L22":
    %"v52" = %"v0" +p #32;
    %"v54" = %"v0" +p #40;
    %"v56" = %"v0" +p #48;
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v56";
    store.ptr [%"chk7" + 0] <- #0;
    %"chk8" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v54";
    store.ptr [%"chk8" + 0] <- #0;
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v52";
    store.ptr [%"chk9" + 0] <- #0;
    %"v58" = %"v0" +p #24;
    %"v60" = %"v0" +p #8;
    %"v62" = %"v0" +p #16;
    %"chk10" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v62";
    store.ptr [%"chk10" + 0] <- #0;
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v60";
    store.ptr [%"chk11" + 0] <- #0;
    %"chk12" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v58";
    store.ptr [%"chk12" + 0] <- #0
    => ret %"v0"
} }.

Definition hello_image_fn__IO_default_seekpos : func :=
  ir_fn{ "export" "_IO_default_seekpos"(P %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v7" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v8";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v10" = %"v8" +p #72;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v11";
    rawcall %"v15" : L = %"chk2"(P %"v0", L %"v2", W #0, W %"v4")
    => ret %"v15"
} }.

Definition hello_image_fn___GI__IO_default_doallocate : func :=
  ir_fn{ "export" "__GI__IO_default_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    call %"v3" : P = $"malloc"(L #8192);
    %"v8" : L = Ptoi %"v3";
    %"v9" : L = Ptoi #0;
    %"v10" : W = (Cmp Eq L) %"v8", %"v9"
    => br %"v10" ? "L4" : "L6";
  @"L4":
    => ret #4294967295;
  @"L6":
    %"v18" = %"v3" +p #8192;
    call void $"__GI__IO_setb"(P %"v0", P %"v3", P %"v18", W #1)
    => ret #1
} }.

Definition hello_image_fn__IO_old_init : func :=
  ir_fn{ "export" "_IO_old_init"(P %"v0", W %"v2") -> RVoid {
  @"start":
    alloca "v72" 16;
    %"v6" : W = Or %"v2", #4222418944;
    %"chk0" : A = (Check 0 4 Write 1) %"v0";
    store Ww [%"chk0" + 0] <- %"v6";
    %"v8" = %"v0" +p #116;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v10" : W = And %"v9", #4278190080;
    store Ww [%"chk1" + 0] <- %"v10";
    %"v18" : P = Copy $"glibc_genops#stdio_needs_locking";
    %"chk3" : A = (Check 0 4 Read 1) %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk3"
    => br %"v19" ? "L15" : "L17";
  @"L15":
    %"v21" = %"v0" +p #116;
    %"chk4" : A = (Renew 0 4 Read 1) %"chk1", %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v23" : W = Shl %"v22", #8;
    %"v24" : W = Sar %"v23", #8;
    %"v25" : W = Or %"v24", #128;
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v27" : W = And %"v26", #4278190080;
    %"v28" : W = And %"v25", #16777215;
    %"v29" : W = Or %"v27", %"v28";
    %"chk6" : A = (Renew 0 4 Write 1) %"chk1", %"v21";
    store Ww [%"chk6" + 0] <- %"v29"
    => goto "L17";
  @"L17":
    %"v33" = %"v0" +p #56;
    %"chk7" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v33";
    store.ptr [%"chk7" + 0] <- #0;
    %"v35" = %"v0" +p #64;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v35";
    store.ptr [%"chk8" + 0] <- #0;
    %"v37" = %"v0" +p #24;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v37";
    store.ptr [%"chk9" + 0] <- #0;
    %"v39" = %"v0" +p #8;
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v39";
    store.ptr [%"chk10" + 0] <- #0;
    %"v41" = %"v0" +p #16;
    %"chk11" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v41";
    store.ptr [%"chk11" + 0] <- #0;
    %"v43" = %"v0" +p #32;
    %"chk12" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v43";
    store.ptr [%"chk12" + 0] <- #0;
    %"v45" = %"v0" +p #40;
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v45";
    store.ptr [%"chk13" + 0] <- #0;
    %"v47" = %"v0" +p #48;
    %"chk14" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v47";
    store.ptr [%"chk14" + 0] <- #0;
    %"v49" = %"v0" +p #104;
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v49";
    store.ptr [%"chk15" + 0] <- #0;
    %"v51" = %"v0" +p #72;
    %"chk16" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v51";
    store.ptr [%"chk16" + 0] <- #0;
    %"v53" = %"v0" +p #80;
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v53";
    store.ptr [%"chk17" + 0] <- #0;
    %"v55" = %"v0" +p #88;
    %"chk18" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v55";
    store.ptr [%"chk18" + 0] <- #0;
    %"v57" = %"v0" +p #96;
    %"chk19" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v57";
    store.ptr [%"chk19" + 0] <- #0;
    %"v59" = %"v0" +p #128;
    %"chk20" : A = (HalfCheck Upper 0 2 Write 1) %"chk0", %"v59";
    store Wh [%"chk20" + 0] <- #0;
    %"v64" = %"v0" +p #136;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v66" : L = Ptoi %"v65";
    %"v67" : L = Ptoi #0;
    %"v68" : W = (Cmp Ne L) %"v66", %"v67"
    => br %"v68" ? "L60" : "L62";
  @"L60":
    %"v70" = %"v0" +p #136;
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk23" : A = (CheckLocal (a "v72") 0 8 Write 1);
    store Wl [%"chk23" + 0] <- #0;
    %"chk24" : A = (CheckLocal (a "v72") 8 8 Write 1);
    store Wl [%"chk24" + 0] <- #0;
    %"chk25" : A = (CheckLocal (a "v72") 0 4 Write 1);
    store Ww [%"chk25" + 0] <- #0;
    %"chk26" : A = (CheckLocal (a "v72") 4 4 Write 1);
    store Ww [%"chk26" + 0] <- #0;
    %"chk27" : A = (CheckLocal (a "v72") 8 8 Write 8);
    (RawStorePointer 0 (Const 0) (t "chk27") [LowerWrite; AddressWrite]);
    %"chk28" : A = (CheckLocal (a "v72") 0 8 Read 1);
    %"v76" : L = (RawLoad LdL 0) %"chk28";
    %"chk29" : A = (Check 0 8 Write 1) %"v71";
    store Wl [%"chk29" + 0] <- %"v76";
    %"v78" = %"v71" +p #8;
    %"chk30" : A = (CheckLocal (a "v72") 8 8 Read 8);
    %"v79" : P = (RawLoadPointer 0 local_load_effects) %"chk30";
    %"chk31" : A = (HalfCheck Upper 0 8 Write 8) %"chk29", %"v78";
    store.ptr [%"chk31" + 0] <- %"v79"
    => goto "L62";
  @"L62":
    => ret void
} }.

Definition hello_image_fn__IO_no_init : func :=
  ir_fn{ "export" "_IO_no_init"(P %"v0", W %"v2", W %"v4", P %"v6", P %"v8") -> RVoid {
  @"start":
    call void $"_IO_old_init"(P %"v0", W %"v2");
    %"v13" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk0" + 0] <- %"v4";
    %"v19" : W = (Cmp Sge W) %"v4", #0
    => br %"v19" ? "L15" : "L16";
  @"L15":
    %"v21" = %"v0" +p #160;
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v21";
    store.ptr [%"chk1" + 0] <- %"v6";
    %"chk2" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v26" = %"v25" +p #48;
    %"chk3" : A = (Check 0 8 Write 8) %"v26";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v30" = %"v29" +p #56;
    %"chk5" : A = (Check 0 8 Write 8) %"v30";
    store.ptr [%"chk5" + 0] <- #0;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v34" = %"v33" +p #16;
    %"chk7" : A = (Check 0 8 Write 8) %"v34";
    store.ptr [%"chk7" + 0] <- #0;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Write 8) %"v37";
    store.ptr [%"chk9" + 0] <- #0;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v41" = %"v40" +p #8;
    %"chk11" : A = (Check 0 8 Write 8) %"v41";
    store.ptr [%"chk11" + 0] <- #0;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v45" = %"v44" +p #24;
    %"chk13" : A = (Check 0 8 Write 8) %"v45";
    store.ptr [%"chk13" + 0] <- #0;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v49" = %"v48" +p #32;
    %"chk15" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk15" + 0] <- #0;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v53" = %"v52" +p #40;
    %"chk17" : A = (Check 0 8 Write 8) %"v53";
    store.ptr [%"chk17" + 0] <- #0;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v57" = %"v56" +p #64;
    %"chk19" : A = (Check 0 8 Write 8) %"v57";
    store.ptr [%"chk19" + 0] <- #0;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v61" = %"v60" +p #72;
    %"chk21" : A = (Check 0 8 Write 8) %"v61";
    store.ptr [%"chk21" + 0] <- #0;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v65" = %"v64" +p #80;
    %"chk23" : A = (Check 0 8 Write 8) %"v65";
    store.ptr [%"chk23" + 0] <- #0;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk1", %"v21";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v69" = %"v68" +p #224;
    %"chk25" : A = (Check 0 8 Write 8) %"v69";
    store.ptr [%"chk25" + 0] <- %"v8"
    => goto "L17";
  @"L16":
    %"v72" = %"v0" +p #160;
    (Flight (a "v74") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk26" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v72";
    store.ptr [%"chk26" + 0] <- %"v74"
    => goto "L17";
  @"L17":
    %"v76" = %"v0" +p #168;
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v76";
    store.ptr [%"chk27" + 0] <- #0;
    %"v78" = %"v0" +p #200;
    %"chk28" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v78";
    store Wl [%"chk28" + 0] <- #0
    => ret void
} }.

Definition hello_image_fn__IO_default_sync : func :=
  ir_fn{ "export" "_IO_default_sync"(P %"v0") -> (RClass W) {
  @"start":
    => ret #0
} }.

Definition hello_image_fn___GI__IO_default_finish : func :=
  ir_fn{ "export" "__GI__IO_default_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v9" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" : L = Ptoi %"v10";
    %"v12" : W = (Cmp Ne L) %"v11", #0
    => br %"v12" ? "L13" : "L14";
  @"L13":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v17" : W = And %"v16", #1;
    %"v18" : W = (Cmp Eq W) %"v17", #0
    => goto "L14";
  @"L14" [%"v20" : W = phi("start" => #0, "L13" => %"v18")]:
    => br %"v20" ? "L5" : "L7";
  @"L5":
    %"v22" = %"v0" +p #56;
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"free"(P %"v23");
    %"v27" = %"v0" +p #64;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v27";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk0", %"v22";
    store.ptr [%"chk4" + 0] <- #0
    => goto "L7";
  @"L7":
    %"v29" = %"v0" +p #96;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5"
    => goto "L31";
  @"L31" [%"pr.1" : P = phi("L32" => %"v42", "L7" => %"v30")]:
    %"v36" : L = Ptoi %"pr.1";
    %"v37" : L = Ptoi #0;
    %"v38" : W = (Cmp Ne L) %"v36", %"v37"
    => br %"v38" ? "L32" : "L34";
  @"L32":
    %"v40" = %"pr.1" +p #8;
    %"chk6" : A = (Check 0 8 Write 8) %"v40";
    store.ptr [%"chk6" + 0] <- #0;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk6", %"pr.1";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk7"
    => goto poll "L31";
  @"L34":
    %"v47" = %"v0" +p #80;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v49" : L = Ptoi %"v48";
    %"v51" : W = (Cmp Ne L) %"v49", %"v37"
    => br %"v51" ? "L43" : "L45";
  @"L43":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L45";
  @"L45":
    call void $"__GI__IO_un_link"(P %"v0");
    %"v58" = %"v0" +p #136;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v60" : L = Ptoi %"v59";
    %"v62" : W = (Cmp Ne L) %"v60", %"v37"
    => br %"v62" ? "L56" : "L55";
  @"L55":
    => goto "L56";
  @"L56":
    => ret void
} }.

Definition hello_image_fn___GI__IO_sputbackc : func :=
  ir_fn{ "export" "__GI__IO_sputbackc"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v9" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v12" = %"v0" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v14" : L = Ptoi %"v10";
    %"v15" : L = Ptoi %"v13";
    %"v16" : W = (Cmp Ugt L) %"v14", %"v15"
    => br %"v16" ? "L17" : "L18";
  @"L17":
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v21" : W = And %"v20", #256;
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => goto "L18";
  @"L18" [%"v24" : W = phi("start" => #0, "L17" => %"v22")]:
    => br %"v24" ? "L25" : "L26";
  @"L25":
    %"v28" = %"v0" +p #8;
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v32" = %"v29" +p #18446744073709551615;
    %"chk4" : A = (Check 0 1 Read 1) %"v32";
    %"v33" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v34" : W = (Ext Ub) %"v33";
    %"v36" : W = (Ext Ub) %"v2";
    %"v37" : W = (Cmp Eq W) %"v34", %"v36"
    => goto "L26";
  @"L26" [%"v39" : W = phi("L18" => #0, "L25" => %"v37")]:
    => br %"v39" ? "L5" : "L6";
  @"L5":
    %"v41" = %"v0" +p #8;
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk0";
    (Flight (a "v43") Sub [(FAddress (t "v42")); (FValue (Const 1))] (LowerOf (t "v42")));
    %"chk6" : A = (Renew 0 8 Write 8) %"chk0", %"v41";
    store.ptr [%"chk6" + 0] <- %"v43";
    %"v45" : W = (Ext Ub) %"v2"
    => goto "L7";
  @"L6":
    %"v47" = %"v0" +p #216;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v4" : L = Ptoi %"v48";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v50" = %"v48" +p #48;
    %"chk8" : A = (Check 0 8 Read 8) %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : F = CheckFunction %"v51";
    rawcall %"v54" : W = %"chk9"(P %"v0", W %"v2")
    => goto "L7";
  @"L7" [%"pr.1" : W = phi("L5" => %"v45", "iw_1.join" => %"v54")]:
    %"v60" : W = (Cmp Ne W) %"pr.1", #4294967295
    => br %"v60" ? "L55" : "L57";
  @"L55":
    %"chk10" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v64" : W = And %"v62", #4294967279;
    %"chk11" : A = (Renew 0 4 Write 1) %"chk10", %"v0";
    store Ww [%"chk11" + 0] <- %"v64"
    => goto "L57";
  @"L57":
    => ret %"pr.1"
} }.

Definition hello_image_fn___GI__IO_adjust_column : func :=
  ir_fn{ "export" "__GI__IO_adjust_column"(W %"v0", P %"v2", W %"v4") -> (RClass W) {
  @"start":
    %"v9" : L = (Ext Sw) %"v4";
    %"v10" = %"v2" +p %"v9"
    => goto "L11";
  @"L11" [%"pr.1" : P = phi("start" => %"v10", "L12" => %"v23")]:
    %"v16" : L = Ptoi %"pr.1";
    %"v17" : L = Ptoi %"v2";
    %"v18" : W = (Cmp Ugt L) %"v16", %"v17"
    => br %"v18" ? "L12" : "L13";
  @"L12":
    (Flight (a "v23") Sub [(FAddress (t "pr.1")); (FValue (Const 1))] (LowerOf (t "pr.1")));
    %"chk0" : A = (Check 0 1 Read 1) %"v23";
    %"v24" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v25" : W = (Cmp Eq W) %"v24", #10
    => br %"v25" ? "L19" : poll "L11";
  @"L19":
    %"v31" : L = Ptoi %"v10";
    %"v32" : L = Ptoi %"v23";
    %"v33" : L = Sub %"v31", %"v32";
    %"v34" : L = Sub %"v33", #1
    => ret %"v34";
  @"L13":
    %"v38" : W = Add %"v0", %"v4"
    => ret %"v38"
} }.

Definition hello_image_fn___GI__IO_flush_all : func :=
  ir_fn{ "export" "__GI__IO_flush_all"() -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v3" : P = (Alloc 8) #32;
    %"v5" : P = Copy $"glibc_genops#flush_cleanup";
    %"v6" = %"v3" +p #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v6";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v3";
    store.ptr [%"chk1" + 0] <- %"v5";
    call void $"__GI___libc_cleanup_push_defer"(P %"v3");
    call %"v17" : P = $"zthread_self_cookie"();
    %"v21" : P = Copy $"__libc_single_threaded_internal";
    %"chk2" : A = (Check 0 1 Read 1) %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v23" : W = (Cmp Ne W) %"v22", #0
    => br %"v23" ? "L24" : "L25" };
  ir_blk{ @"L24":
    %"v26" : P = Copy $"glibc_genops#list_all_lock";
    %"v27" = %"v26" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v29" : L = Ptoi %"v28";
    %"v30" : L = Ptoi #0;
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => goto "L25" };
  ir_blk{ @"L25" [%"v33" : W = phi("start" => #0, "L24" => %"v31")]:
    => br %"v33" ? "L18" : "L19" };
  ir_blk{ @"L18":
    %"v34" : P = Copy $"glibc_genops#list_all_lock";
    %"chk4" : A = (Check 0 4 Write 1) %"v34";
    store Ww [%"chk4" + 0] <- #1;
    %"v35" : P = Copy $"glibc_genops#list_all_lock";
    %"v36" = %"v35" +p #8;
    %"chk5" : A = (Check 0 8 Write 8) %"v36";
    store.ptr [%"chk5" + 0] <- %"v17"
    => goto "L15" };
  ir_blk{ @"L19":
    %"v41" : P = Copy $"glibc_genops#list_all_lock";
    %"v42" = %"v41" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v45" : L = Ptoi %"v43";
    %"v46" : L = Ptoi %"v17";
    %"v47" : W = (Cmp Ne L) %"v45", %"v46"
    => br %"v47" ? "L38" : "L39" };
  ir_blk{ @"L38":
    %"v49" : P = Copy $"glibc_genops#list_all_lock";
    %"chk7" : A = (Check 0 4 Write 4) %"v49";
    %"v56" : W = (RawCas (CasNarrow Sw) 0) %"chk7", #0, #1;
    %"v57" : W = (Cmp Eq W) %"v56", #0
    => br %"v57" ? "L59" : "L58" };
  ir_blk{ @"L58":
    => goto "L59" };
  ir_blk{ @"L59":
    %"v60" : W = (Cmp Ne W) %"v56", #0
    => br %"v60" ? "L63" : "L52" };
  ir_blk{ @"L63":
    call void $"__GI___lll_lock_wait_private"(P %"v49")
    => goto "L52" };
  ir_blk{ @"L52":
    %"v73" : P = Copy $"glibc_genops#list_all_lock";
    %"v74" = %"v73" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"v74";
    store.ptr [%"chk8" + 0] <- %"v17"
    => goto "L15" };
  ir_blk{ @"L39":
    %"v76" : P = Copy $"glibc_genops#list_all_lock";
    %"v77" = %"v76" +p #4;
    %"chk9" : A = (Check 0 4 Read 1) %"v77";
    %"v78" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v79" : W = Add %"v78", #1;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk9", %"v77";
    store Ww [%"chk10" + 0] <- %"v79"
    => goto "L15" };
  ir_blk{ @"L15":
    %"v80" : P = Copy $"__GI__IO_list_all";
    %"chk11" : A = (Check 0 8 Read 8) %"v80";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto "L82" };
  ir_blk{ @"L82" [%"pr.5" : P = phi("L15" => %"v81", "L329" => %"v413"); %"pr.4" : W = phi("L15" => #0, "L329" => %"pr.1")]:
    %"v87" : L = Ptoi %"pr.5";
    %"v88" : L = Ptoi #0;
    %"v89" : W = (Cmp Ne L) %"v87", %"v88"
    => br %"v89" ? "L83" : "L414" };
  ir_blk{ @"L83":
    %"v90" : P = Copy $"glibc_genops#run_fp";
    %"chk12" : A = (Check 0 8 Write 8) %"v90";
    store.ptr [%"chk12" + 0] <- %"pr.5";
    %"chk13" : A = (Check 0 4 Read 1) %"pr.5";
    %"v96" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v97" : W = And %"v96", #32768;
    %"v98" : W = (Cmp Eq W) %"v97", #0
    => br %"v98" ? "L99" : "L94" };
  ir_blk{ @"L99":
    call %"v103" : P = $"zthread_self_cookie"();
    %"v107" : P = Copy $"__libc_single_threaded_internal";
    %"chk14" : A = (Check 0 1 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v109" : W = (Cmp Ne W) %"v108", #0
    => br %"v109" ? "L110" : "L111" };
  ir_blk{ @"L110":
    %"v113" = %"pr.5" +p #136;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v115" = %"v114" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"v115";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v117" : L = Ptoi %"v116";
    %"v119" : W = (Cmp Eq L) %"v117", %"v88"
    => goto "L111" };
  ir_blk{ @"L111" [%"v121" : W = phi("L99" => #0, "L110" => %"v119")]:
    => br %"v121" ? "L104" : "L105" };
  ir_blk{ @"L104":
    %"v123" = %"pr.5" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v123";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Write 1) %"v124";
    store Ww [%"chk18" + 0] <- #1;
    %"v127" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v128" = %"v127" +p #8;
    %"chk20" : A = (Check 0 8 Write 8) %"v128";
    store.ptr [%"chk20" + 0] <- %"v103"
    => goto "L94" };
  ir_blk{ @"L105":
    %"v134" = %"pr.5" +p #136;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v136" = %"v135" +p #8;
    %"chk22" : A = (Check 0 8 Read 8) %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v139" : L = Ptoi %"v137";
    %"v140" : L = Ptoi %"v103";
    %"v141" : W = (Cmp Ne L) %"v139", %"v140"
    => br %"v141" ? "L130" : "L131" };
  ir_blk{ @"L130":
    %"v144" = %"pr.5" +p #136;
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 4 Write 4) %"v145";
    %"v152" : W = (RawCas (CasNarrow Sw) 0) %"chk24", #0, #1;
    %"v153" : W = (Cmp Eq W) %"v152", #0
    => br %"v153" ? "L155" : "L154" };
  ir_blk{ @"L154":
    => goto "L155" };
  ir_blk{ @"L155":
    %"v156" : W = (Cmp Ne W) %"v152", #0
    => br %"v156" ? "L159" : "L148" };
  ir_blk{ @"L159":
    call void $"__GI___lll_lock_wait_private"(P %"v145")
    => goto "L148" };
  ir_blk{ @"L148":
    %"v170" = %"pr.5" +p #136;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk21", %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v172" = %"v171" +p #8;
    %"chk26" : A = (Check 0 8 Write 8) %"v172";
    store.ptr [%"chk26" + 0] <- %"v103"
    => goto "L94" };
  ir_blk{ @"L131":
    %"v175" = %"pr.5" +p #136;
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v177" = %"v176" +p #4;
    %"chk28" : A = (Check 0 4 Read 1) %"v177";
    %"v178" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v179" : W = Add %"v178", #1;
    %"chk29" : A = (Renew 0 4 Write 1) %"chk28", %"v177";
    store Ww [%"chk29" + 0] <- %"v179"
    => goto "L94" };
  ir_blk{ @"L94":
    %"v184" = %"pr.5" +p #116;
    %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk13", %"v184";
    %"v185" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v186" : W = Shl %"v185", #8;
    %"v187" : W = Sar %"v186", #8;
    %"v188" : W = And %"v187", #32;
    %"v189" : W = (Cmp Eq W) %"v188", #0
    => br %"v189" ? "L180" : "L182" };
  ir_blk{ @"L180":
    %"v194" = %"pr.5" +p #192;
    %"chk31" : A = (HalfCheck Upper 0 4 Read 1) %"chk13", %"v194";
    %"v195" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v196" : W = (Cmp Sle W) %"v195", #0
    => br %"v196" ? "L197" : "L198" };
  ir_blk{ @"L197":
    %"v200" = %"pr.5" +p #40;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v200";
    %"v201" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v203" = %"pr.5" +p #32;
    %"chk33" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v203";
    %"v204" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v205" : L = Ptoi %"v201";
    %"v206" : L = Ptoi %"v204";
    %"v207" : W = (Cmp Ugt L) %"v205", %"v206"
    => goto "L198" };
  ir_blk{ @"L198" [%"v209" : W = phi("L180" => #0, "L197" => %"v207")]:
    => br %"v209" ? "L211" : "L213" };
  ir_blk{ @"L213":
    %"v216" = %"pr.5" +p #192;
    %"v217" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v218" : W = (Cmp Sgt W) %"v217", #0
    => br %"v218" ? "L221" : "L211" };
  ir_blk{ @"L221":
    %"v224" = %"pr.5" +p #160;
    %"chk35" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v224";
    %"v225" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v226" = %"v225" +p #32;
    %"chk36" : A = (Check 0 8 Read 8) %"v226";
    %"v227" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v230" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v231" = %"v230" +p #24;
    %"chk38" : A = (Check 0 8 Read 8) %"v231";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v233" : L = Ptoi %"v227";
    %"v234" : L = Ptoi %"v232";
    %"v235" : W = (Cmp Ugt L) %"v233", %"v234"
    => goto "L211" };
  ir_blk{ @"L211" [%"v239" : W = phi("L198" => #1, "L213" => #0, "L221" => %"v235")]:
    => br %"v239" ? "L240" : "L241" };
  ir_blk{ @"L240":
    %"v243" = %"pr.5" +p #216;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v243";
    %"v244" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"iw_1.v4" : L = Ptoi %"v244";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join" };
  ir_blk{ @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join":
    %"v246" = %"v244" +p #24;
    %"chk40" : A = (Check 0 8 Read 8) %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : F = CheckFunction %"v247";
    rawcall %"v250" : W = %"chk41"(P %"pr.5", W #4294967295);
    %"v252" : W = (Cmp Eq W) %"v250", #4294967295
    => goto "L241" };
  ir_blk{ @"L241" [%"v254" : W = phi("L211" => #0, "iw_1.join" => %"v252")]:
    => br %"v254" ? "L192" : "L191" }] [ir_blk{ @"L191":
    => goto "L192" };
  ir_blk{ @"L192" [%"pr.2" : W = phi("L191" => %"pr.4", "L241" => #4294967295)]:
    %"v260" = %"pr.5" +p #112;
    %"chk42" : A = (HalfCheck Upper 0 4 Read 1) %"chk13", %"v260";
    %"v261" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v262" : W = (Cmp Sge W) %"v261", #0
    => br %"v262" ? "L263" : "L264" };
  ir_blk{ @"L263":
    %"v266" = %"pr.5" +p #192;
    %"chk43" : A = (Renew 0 4 Read 1) %"chk31", %"v266";
    %"v267" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v268" : W = (Cmp Sle W) %"v267", #0
    => br %"v268" ? "L269" : "L270" };
  ir_blk{ @"L269":
    %"v272" = %"pr.5" +p #8;
    %"chk44" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v272";
    %"v273" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v275" = %"pr.5" +p #16;
    %"v276" : P = (RawLoadPointer 8 load_effects) %"chk44";
    %"v277" : L = Ptoi %"v273";
    %"v278" : L = Ptoi %"v276";
    %"v279" : W = (Cmp Ult L) %"v277", %"v278"
    => goto "L270" };
  ir_blk{ @"L270" [%"v281" : W = phi("L263" => #0, "L269" => %"v279")]:
    => br %"v281" ? "L264" : "L285" };
  ir_blk{ @"L285":
    %"v288" = %"pr.5" +p #192;
    %"v289" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v290" : W = (Cmp Sgt W) %"v289", #0
    => br %"v290" ? "L293" : "L264" };
  ir_blk{ @"L293":
    %"v296" = %"pr.5" +p #160;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v296";
    %"v297" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"chk48" : A = (Check 0 8 Read 8) %"v297";
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v301" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v302" = %"v301" +p #8;
    %"chk50" : A = (Check 0 8 Read 8) %"v302";
    %"v303" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v304" : L = Ptoi %"v298";
    %"v305" : L = Ptoi %"v303";
    %"v306" : W = (Cmp Ult L) %"v304", %"v305"
    => goto "L264" };
  ir_blk{ @"L264" [%"v312" : W = phi("L192" => #0, "L270" => #1, "L285" => #0, "L293" => %"v306")]:
    => br %"v312" ? "L313" : "L314" };
  ir_blk{ @"L313":
    %"v316" = %"pr.5" +p #216;
    %"chk51" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v316";
    %"v317" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"iw_2.v4" : L = Ptoi %"v317";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join" };
  ir_blk{ @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join":
    %"v319" = %"v317" +p #96;
    %"chk52" : A = (Check 0 8 Read 8) %"v319";
    %"v320" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"chk53" : F = CheckFunction %"v320";
    rawcall %"v322" : W = %"chk53"(P %"pr.5");
    %"v323" : W = (Cmp Ne W) %"v322", #0
    => goto "L314" };
  ir_blk{ @"L314" [%"v325" : W = phi("L264" => #0, "iw_2.join" => %"v323")]:
    => br %"v325" ? "L182" : "L257" };
  ir_blk{ @"L257":
    => goto "L182" };
  ir_blk{ @"L182" [%"pr.1" : W = phi("L257" => %"pr.2", "L314" => #4294967295, "L94" => %"pr.4")]:
    %"chk54" : A = (Renew 0 4 Read 1) %"chk13", %"pr.5";
    %"v331" : W = (RawLoad (LdNarrow Sw) 0) %"chk54";
    %"v332" : W = And %"v331", #32768;
    %"v333" : W = (Cmp Eq W) %"v332", #0
    => br %"v333" ? "L334" : "L329" };
  ir_blk{ @"L334":
    %"v340" : P = Copy $"__libc_single_threaded_internal";
    %"chk55" : A = (Check 0 1 Read 1) %"v340";
    %"v341" : W = (RawLoad (LdNarrow Sb) 0) %"chk55";
    %"v342" : W = (Cmp Ne W) %"v341", #0
    => br %"v342" ? "L343" : "L344" };
  ir_blk{ @"L343":
    %"v346" = %"pr.5" +p #136;
    %"chk56" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v346";
    %"v347" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v348" = %"v347" +p #4;
    %"chk57" : A = (Check 0 4 Read 1) %"v348";
    %"v349" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v350" : W = (Cmp Eq W) %"v349", #0
    => goto "L344" };
  ir_blk{ @"L344" [%"v352" : W = phi("L334" => #0, "L343" => %"v350")]:
    => br %"v352" ? "L337" : "L338" };
  ir_blk{ @"L337":
    %"v354" = %"pr.5" +p #136;
    %"chk58" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v354";
    %"v355" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v356" = %"v355" +p #8;
    %"chk59" : A = (Check 0 8 Write 8) %"v356";
    store.ptr [%"chk59" + 0] <- #0;
    %"chk60" : A = (Renew 0 8 Read 8) %"chk58", %"v354";
    %"v359" : P = (RawLoadPointer 0 load_effects) %"chk60";
    %"chk61" : A = (Check 0 4 Write 1) %"v359";
    store Ww [%"chk61" + 0] <- #0
    => goto "L329" };
  ir_blk{ @"L338":
    %"v364" = %"pr.5" +p #136;
    %"chk62" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v364";
    %"v365" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v366" = %"v365" +p #4;
    %"chk63" : A = (Check 0 4 Read 1) %"v366";
    %"v367" : W = (RawLoad (LdNarrow Sw) 0) %"chk63";
    %"v368" : W = (Cmp Eq W) %"v367", #0
    => br %"v368" ? "L360" : "L361" };
  ir_blk{ @"L360":
    %"v370" = %"pr.5" +p #136;
    %"v371" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v372" = %"v371" +p #8;
    %"chk65" : A = (Check 0 8 Write 8) %"v372";
    store.ptr [%"chk65" + 0] <- #0;
    %"chk66" : A = (Renew 0 8 Read 8) %"chk62", %"v370";
    %"v376" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"chk67" : A = (Check 0 4 Read 1) %"v376";
    %"v380" : W = (RawLoad (LdNarrow Sw) 0) %"chk67"
    => goto "L381" };
  ir_blk{ @"L381" [%"v383" : W = phi("L360" => %"v380", "L381" => %"v384")]:
    %"chk68" : A = (HalfCheck Lower 0 4 Write 4) %"chk67", %"v376";
    %"v384" : W = (RawCas (CasNarrow Sw) 0) %"chk68", %"v383", #0;
    %"v385" : W = (Cmp Eq W) %"v384", %"v383"
    => br %"v385" ? "L382" : poll "L381" };
  ir_blk{ @"L382":
    %"v390" : W = (Cmp Sgt W) %"v383", #1
    => br %"v390" ? "L393" : "L329" };
  ir_blk{ @"L393":
    call void $"__GI___lll_lock_wake_private"(P %"v376")
    => goto "L329" };
  ir_blk{ @"L361":
    %"v405" = %"pr.5" +p #136;
    %"v406" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v407" = %"v406" +p #4;
    %"chk70" : A = (Check 0 4 Read 1) %"v407";
    %"v408" : W = (RawLoad (LdNarrow Sw) 0) %"chk70";
    %"v409" : W = Sub %"v408", #1;
    %"chk71" : A = (Renew 0 4 Write 1) %"chk70", %"v407";
    store Ww [%"chk71" + 0] <- %"v409"
    => goto "L329" };
  ir_blk{ @"L329":
    %"v410" : P = Copy $"glibc_genops#run_fp";
    %"chk72" : A = (Check 0 8 Write 8) %"v410";
    store.ptr [%"chk72" + 0] <- #0;
    %"v412" = %"pr.5" +p #104;
    %"chk73" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"v412";
    %"v413" : P = (RawLoadPointer 0 load_effects) %"chk73"
    => goto poll "L82" };
  ir_blk{ @"L414":
    %"v420" : P = Copy $"__libc_single_threaded_internal";
    %"chk74" : A = (Check 0 1 Read 1) %"v420";
    %"v421" : W = (RawLoad (LdNarrow Sb) 0) %"chk74";
    %"v422" : W = (Cmp Ne W) %"v421", #0
    => br %"v422" ? "L423" : "L424" };
  ir_blk{ @"L423":
    %"v425" : P = Copy $"glibc_genops#list_all_lock";
    %"v426" = %"v425" +p #4;
    %"chk75" : A = (Check 0 4 Read 1) %"v426";
    %"v427" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"v428" : W = (Cmp Eq W) %"v427", #0
    => goto "L424" };
  ir_blk{ @"L424" [%"v430" : W = phi("L414" => #0, "L423" => %"v428")]:
    => br %"v430" ? "L417" : "L418" };
  ir_blk{ @"L417":
    %"v431" : P = Copy $"glibc_genops#list_all_lock";
    %"v432" = %"v431" +p #8;
    %"chk76" : A = (Check 0 8 Write 8) %"v432";
    store.ptr [%"chk76" + 0] <- #0;
    %"v433" : P = Copy $"glibc_genops#list_all_lock";
    %"chk77" : A = (Check 0 4 Write 1) %"v433";
    store Ww [%"chk77" + 0] <- #0
    => goto "L476" };
  ir_blk{ @"L418":
    %"v437" : P = Copy $"glibc_genops#list_all_lock";
    %"v438" = %"v437" +p #4;
    %"chk78" : A = (Check 0 4 Read 1) %"v438";
    %"v439" : W = (RawLoad (LdNarrow Sw) 0) %"chk78";
    %"v440" : W = (Cmp Eq W) %"v439", #0
    => br %"v440" ? "L434" : "L435" };
  ir_blk{ @"L434":
    %"v441" : P = Copy $"glibc_genops#list_all_lock";
    %"v442" = %"v441" +p #8;
    %"chk79" : A = (Check 0 8 Write 8) %"v442";
    store.ptr [%"chk79" + 0] <- #0;
    %"v444" : P = Copy $"glibc_genops#list_all_lock";
    %"chk80" : A = (Check 0 4 Read 1) %"v444";
    %"v448" : W = (RawLoad (LdNarrow Sw) 0) %"chk80"
    => goto "L449" };
  ir_blk{ @"L449" [%"v451" : W = phi("L434" => %"v448", "L449" => %"v452")]:
    %"chk81" : A = (HalfCheck Lower 0 4 Write 4) %"chk80", %"v444";
    %"v452" : W = (RawCas (CasNarrow Sw) 0) %"chk81", %"v451", #0;
    %"v453" : W = (Cmp Eq W) %"v452", %"v451"
    => br %"v453" ? "L450" : poll "L449" };
  ir_blk{ @"L450":
    %"v458" : W = (Cmp Sgt W) %"v451", #1
    => br %"v458" ? "L461" : "L476" };
  ir_blk{ @"L461":
    call void $"__GI___lll_lock_wake_private"(P %"v444")
    => goto "L476" };
  ir_blk{ @"L435":
    %"v472" : P = Copy $"glibc_genops#list_all_lock";
    %"v473" = %"v472" +p #4;
    %"chk82" : A = (Check 0 4 Read 1) %"v473";
    %"v474" : W = (RawLoad (LdNarrow Sw) 0) %"chk82";
    %"v475" : W = Sub %"v474", #1;
    %"chk83" : A = (Renew 0 4 Write 1) %"chk82", %"v473";
    store Ww [%"chk83" + 0] <- %"v475"
    => goto "L476" };
  ir_blk{ @"L476":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v3")
    => ret %"pr.4" }])) }.

Definition hello_image_fn__IO_cleanup : func :=
  ir_fn{ "export" "_IO_cleanup"() -> (RClass W) blocks ((app [ir_blk{ @"start":
    call %"v1" : W = $"__GI__IO_flush_all"();
    %"iw_1.v2" : P = (Alloc 8) #32;
    %"iw_1.v4" : P = Copy $"glibc_genops#flush_cleanup";
    %"iw_1.v5" = %"iw_1.v2" +p #8;
    %"chk0" : A = (Check 0 8 Write 8) %"iw_1.v5";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"iw_1.v2";
    store.ptr [%"chk1" + 0] <- %"iw_1.v4";
    call void $"__GI___libc_cleanup_push_defer"(P %"iw_1.v2");
    call %"iw_1.v16" : P = $"zthread_self_cookie"();
    %"iw_1.v20" : P = Copy $"__libc_single_threaded_internal";
    %"chk2" : A = (Check 0 1 Read 1) %"iw_1.v20";
    %"iw_1.v21" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"iw_1.v22" : W = (Cmp Ne W) %"iw_1.v21", #0
    => br %"iw_1.v22" ? "iw_1.L23" : "iw_1.L24" };
  ir_blk{ @"iw_1.L23":
    %"iw_1.v25" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v26" = %"iw_1.v25" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v26";
    %"iw_1.v27" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v28" : L = Ptoi %"iw_1.v27";
    %"iw_1.v29" : L = Ptoi #0;
    %"iw_1.v30" : W = (Cmp Eq L) %"iw_1.v28", %"iw_1.v29"
    => goto "iw_1.L24" };
  ir_blk{ @"iw_1.L24" [%"iw_1.v32" : W = phi("start" => #0, "iw_1.L23" => %"iw_1.v30")]:
    => br %"iw_1.v32" ? "iw_1.L17" : "iw_1.L18" };
  ir_blk{ @"iw_1.L17":
    %"iw_1.v33" : P = Copy $"glibc_genops#list_all_lock";
    %"chk4" : A = (Check 0 4 Write 1) %"iw_1.v33";
    store Ww [%"chk4" + 0] <- #1;
    %"iw_1.v34" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v35" = %"iw_1.v34" +p #8;
    %"chk5" : A = (Check 0 8 Write 8) %"iw_1.v35";
    store.ptr [%"chk5" + 0] <- %"iw_1.v16"
    => goto "iw_1.L14" };
  ir_blk{ @"iw_1.L18":
    %"iw_1.v40" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v41" = %"iw_1.v40" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v41";
    %"iw_1.v42" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v44" : L = Ptoi %"iw_1.v42";
    %"iw_1.v45" : L = Ptoi %"iw_1.v16";
    %"iw_1.v46" : W = (Cmp Ne L) %"iw_1.v44", %"iw_1.v45"
    => br %"iw_1.v46" ? "iw_1.L37" : "iw_1.L38" };
  ir_blk{ @"iw_1.L37":
    %"iw_1.v48" : P = Copy $"glibc_genops#list_all_lock";
    %"chk7" : A = (Check 0 4 Write 4) %"iw_1.v48";
    %"iw_1.v55" : W = (RawCas (CasNarrow Sw) 0) %"chk7", #0, #1;
    %"iw_1.v56" : W = (Cmp Eq W) %"iw_1.v55", #0
    => br %"iw_1.v56" ? "iw_1.L58" : "iw_1.L57" };
  ir_blk{ @"iw_1.L57":
    => goto "iw_1.L58" };
  ir_blk{ @"iw_1.L58":
    %"iw_1.v59" : W = (Cmp Ne W) %"iw_1.v55", #0
    => br %"iw_1.v59" ? "iw_1.L62" : "iw_1.L51" };
  ir_blk{ @"iw_1.L62":
    call void $"__GI___lll_lock_wait_private"(P %"iw_1.v48")
    => goto "iw_1.L51" };
  ir_blk{ @"iw_1.L51":
    %"iw_1.v72" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v73" = %"iw_1.v72" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"iw_1.v73";
    store.ptr [%"chk8" + 0] <- %"iw_1.v16"
    => goto "iw_1.L14" };
  ir_blk{ @"iw_1.L38":
    %"iw_1.v75" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v76" = %"iw_1.v75" +p #4;
    %"chk9" : A = (Check 0 4 Read 1) %"iw_1.v76";
    %"iw_1.v77" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"iw_1.v78" : W = Add %"iw_1.v77", #1;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk9", %"iw_1.v76";
    store Ww [%"chk10" + 0] <- %"iw_1.v78"
    => goto "iw_1.L14" };
  ir_blk{ @"iw_1.L14":
    %"iw_1.v79" : P = Copy $"__GI__IO_list_all";
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v79";
    %"iw_1.v80" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto "iw_1.L81" };
  ir_blk{ @"iw_1.L81" [%"iw_1.pr.1" : P = phi("iw_1.L14" => %"iw_1.v80", "iw_1.L301" => %"iw_1.v385")]:
    %"iw_1.v86" : L = Ptoi %"iw_1.pr.1";
    %"iw_1.v87" : W = (Cmp Ne L) %"iw_1.v86", #0
    => br %"iw_1.v87" ? "iw_1.L82" : "iw_1.L386" };
  ir_blk{ @"iw_1.L82":
    %"iw_1.v89" : P = Copy $"glibc_genops#run_fp";
    %"chk12" : A = (Check 0 8 Write 8) %"iw_1.v89";
    store.ptr [%"chk12" + 0] <- %"iw_1.pr.1";
    %"chk13" : A = (Check 0 4 Read 1) %"iw_1.pr.1";
    %"iw_1.v95" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"iw_1.v96" : W = And %"iw_1.v95", #32768;
    %"iw_1.v97" : W = (Cmp Eq W) %"iw_1.v96", #0
    => br %"iw_1.v97" ? "iw_1.L98" : "iw_1.L93" };
  ir_blk{ @"iw_1.L98":
    call %"iw_1.v102" : P = $"zthread_self_cookie"();
    %"iw_1.v106" : P = Copy $"__libc_single_threaded_internal";
    %"chk14" : A = (Check 0 1 Read 1) %"iw_1.v106";
    %"iw_1.v107" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_1.v108" : W = (Cmp Ne W) %"iw_1.v107", #0
    => br %"iw_1.v108" ? "iw_1.L109" : "iw_1.L110" };
  ir_blk{ @"iw_1.L109":
    %"iw_1.v112" = %"iw_1.pr.1" +p #136;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v112";
    %"iw_1.v113" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_1.v114" = %"iw_1.v113" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"iw_1.v114";
    %"iw_1.v115" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_1.v116" : L = Ptoi %"iw_1.v115";
    %"iw_1.v117" : L = Ptoi #0;
    %"iw_1.v118" : W = (Cmp Eq L) %"iw_1.v116", %"iw_1.v117"
    => goto "iw_1.L110" };
  ir_blk{ @"iw_1.L110" [%"iw_1.v120" : W = phi("iw_1.L98" => #0, "iw_1.L109" => %"iw_1.v118")]:
    => br %"iw_1.v120" ? "iw_1.L103" : "iw_1.L104" };
  ir_blk{ @"iw_1.L103":
    %"iw_1.v122" = %"iw_1.pr.1" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v122";
    %"iw_1.v123" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Write 1) %"iw_1.v123";
    store Ww [%"chk18" + 0] <- #1;
    %"iw_1.v126" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_1.v127" = %"iw_1.v126" +p #8;
    %"chk20" : A = (Check 0 8 Write 8) %"iw_1.v127";
    store.ptr [%"chk20" + 0] <- %"iw_1.v102"
    => goto "iw_1.L93" };
  ir_blk{ @"iw_1.L104":
    %"iw_1.v133" = %"iw_1.pr.1" +p #136;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v133";
    %"iw_1.v134" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_1.v135" = %"iw_1.v134" +p #8;
    %"chk22" : A = (Check 0 8 Read 8) %"iw_1.v135";
    %"iw_1.v136" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_1.v138" : L = Ptoi %"iw_1.v136";
    %"iw_1.v139" : L = Ptoi %"iw_1.v102";
    %"iw_1.v140" : W = (Cmp Ne L) %"iw_1.v138", %"iw_1.v139"
    => br %"iw_1.v140" ? "iw_1.L129" : "iw_1.L130" };
  ir_blk{ @"iw_1.L129":
    %"iw_1.v143" = %"iw_1.pr.1" +p #136;
    %"iw_1.v144" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 4 Write 4) %"iw_1.v144";
    %"iw_1.v151" : W = (RawCas (CasNarrow Sw) 0) %"chk24", #0, #1;
    %"iw_1.v152" : W = (Cmp Eq W) %"iw_1.v151", #0
    => br %"iw_1.v152" ? "iw_1.L154" : "iw_1.L153" };
  ir_blk{ @"iw_1.L153":
    => goto "iw_1.L154" };
  ir_blk{ @"iw_1.L154":
    %"iw_1.v155" : W = (Cmp Ne W) %"iw_1.v151", #0
    => br %"iw_1.v155" ? "iw_1.L158" : "iw_1.L147" };
  ir_blk{ @"iw_1.L158":
    call void $"__GI___lll_lock_wait_private"(P %"iw_1.v144")
    => goto "iw_1.L147" };
  ir_blk{ @"iw_1.L147":
    %"iw_1.v169" = %"iw_1.pr.1" +p #136;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk21", %"iw_1.v169";
    %"iw_1.v170" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_1.v171" = %"iw_1.v170" +p #8;
    %"chk26" : A = (Check 0 8 Write 8) %"iw_1.v171";
    store.ptr [%"chk26" + 0] <- %"iw_1.v102"
    => goto "iw_1.L93" };
  ir_blk{ @"iw_1.L130":
    %"iw_1.v174" = %"iw_1.pr.1" +p #136;
    %"iw_1.v175" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_1.v176" = %"iw_1.v175" +p #4;
    %"chk28" : A = (Check 0 4 Read 1) %"iw_1.v176";
    %"iw_1.v177" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"iw_1.v178" : W = Add %"iw_1.v177", #1;
    %"chk29" : A = (Renew 0 4 Write 1) %"chk28", %"iw_1.v176";
    store Ww [%"chk29" + 0] <- %"iw_1.v178"
    => goto "iw_1.L93" };
  ir_blk{ @"iw_1.L93":
    %"iw_1.v183" = %"iw_1.pr.1" +p #80;
    %"chk30" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v183";
    %"iw_1.v184" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_1.v185" : L = Ptoi %"iw_1.v184";
    %"iw_1.v186" : L = Ptoi #0;
    %"iw_1.v187" : W = (Cmp Ne L) %"iw_1.v185", %"iw_1.v186"
    => br %"iw_1.v187" ? "iw_1.L179" : "iw_1.L194" };
  ir_blk{ @"iw_1.L179":
    call void $"__GI__IO_free_backup_area"(P %"iw_1.pr.1")
    => goto "iw_1.L194" };
  ir_blk{ @"iw_1.L194":
    %"iw_1.v197" = %"iw_1.pr.1" +p #192;
    %"chk31" : A = (HalfCheck Upper 0 4 Read 1) %"chk13", %"iw_1.v197";
    %"iw_1.v198" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"iw_1.v199" : W = (Cmp Sgt W) %"iw_1.v198", #0
    => br %"iw_1.v199" ? "iw_1.L202" : "iw_1.L203" };
  ir_blk{ @"iw_1.L202":
    %"iw_1.v205" = %"iw_1.pr.1" +p #160;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v205";
    %"iw_1.v206" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"iw_1.v207" = %"iw_1.v206" +p #72;
    %"chk33" : A = (Check 0 8 Read 8) %"iw_1.v207";
    %"iw_1.v208" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"iw_1.v209" : L = Ptoi %"iw_1.v208";
    %"iw_1.v211" : W = (Cmp Ne L) %"iw_1.v209", %"iw_1.v186"
    => goto "iw_1.L203" };
  ir_blk{ @"iw_1.L203" [%"iw_1.v213" : W = phi("iw_1.L194" => #0, "iw_1.L202" => %"iw_1.v211")]:
    => br %"iw_1.v213" ? "iw_1.L189" : "iw_1.L191" };
  ir_blk{ @"iw_1.L189":
    call void $"__GI__IO_free_wbackup_area"(P %"iw_1.pr.1")
    => goto "iw_1.L191" };
  ir_blk{ @"iw_1.L191":
    %"chk34" : A = (Renew 0 4 Read 1) %"chk13", %"iw_1.pr.1";
    %"iw_1.v219" : W = (RawLoad (LdNarrow Sw) 0) %"chk34";
    %"iw_1.v220" : W = And %"iw_1.v219", #2;
    %"iw_1.v221" : W = (Cmp Eq W) %"iw_1.v220", #0
    => br %"iw_1.v221" ? "iw_1.L225" : "iw_1.L223" }] [ir_blk{ @"iw_1.L225":
    %"iw_1.v228" = %"iw_1.pr.1" +p #192;
    %"chk35" : A = (Renew 0 4 Read 1) %"chk31", %"iw_1.v228";
    %"iw_1.v229" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"iw_1.v230" : W = (Cmp Ne W) %"iw_1.v229", #0
    => goto "iw_1.L223" };
  ir_blk{ @"iw_1.L223" [%"iw_1.v234" : W = phi("iw_1.L191" => #0, "iw_1.L225" => %"iw_1.v230")]:
    => br %"iw_1.v234" ? "iw_1.L240" : "iw_1.L291" };
  ir_blk{ @"iw_1.L240":
    %"iw_1.v242" : P = Copy $"glibc_genops#dealloc_buffers";
    %"chk36" : A = (Check 0 1 Read 1) %"iw_1.v242";
    %"iw_1.v243" : W = (RawLoad (LdNarrow Ub) 0) %"chk36";
    %"iw_1.v244" : W = (Cmp Eq W) %"iw_1.v243", #0
    => br %"iw_1.v244" ? "iw_1.L247" : "iw_1.L248" };
  ir_blk{ @"iw_1.L247":
    %"chk37" : A = (Renew 0 4 Read 1) %"chk13", %"iw_1.pr.1";
    %"iw_1.v250" : W = (RawLoad (LdNarrow Sw) 0) %"chk37";
    %"iw_1.v251" : W = And %"iw_1.v250", #1;
    %"iw_1.v252" : W = (Cmp Eq W) %"iw_1.v251", #0
    => goto "iw_1.L248" };
  ir_blk{ @"iw_1.L248" [%"iw_1.v254" : W = phi("iw_1.L240" => #0, "iw_1.L247" => %"iw_1.v252")]:
    => br %"iw_1.v254" ? "iw_1.L235" : "iw_1.L237" };
  ir_blk{ @"iw_1.L235":
    %"chk38" : A = (Renew 0 4 Read 1) %"chk13", %"iw_1.pr.1";
    %"iw_1.v256" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"iw_1.v257" : W = Or %"iw_1.v256", #1;
    %"chk39" : A = (Renew 0 4 Write 1) %"chk13", %"iw_1.pr.1";
    store Ww [%"chk39" + 0] <- %"iw_1.v257";
    %"iw_1.v259" = %"iw_1.pr.1" +p #168;
    %"iw_1.v260" : P = Copy $"glibc_genops#freeres_list";
    %"chk40" : A = (Check 0 8 Read 8) %"iw_1.v260";
    %"iw_1.v261" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : A = (HalfCheck Upper 0 8 Write 8) %"chk13", %"iw_1.v259";
    store.ptr [%"chk41" + 0] <- %"iw_1.v261";
    %"iw_1.v262" : P = Copy $"glibc_genops#freeres_list";
    %"chk42" : A = (Check 0 8 Write 8) %"iw_1.v262";
    store.ptr [%"chk42" + 0] <- %"iw_1.pr.1";
    %"iw_1.v265" = %"iw_1.pr.1" +p #176;
    %"iw_1.v267" = %"iw_1.pr.1" +p #56;
    %"chk43" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v267";
    %"iw_1.v268" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"chk44" : A = (HalfCheck Upper 0 8 Write 8) %"chk13", %"iw_1.v265";
    store.ptr [%"chk44" + 0] <- %"iw_1.v268"
    => goto "iw_1.L237" };
  ir_blk{ @"iw_1.L237":
    %"iw_1.v270" = %"iw_1.pr.1" +p #216;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v270";
    %"iw_1.v271" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"iw_1.iw_1.v4" : L = Ptoi %"iw_1.v271";
    %"iw_1.iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_1.v8" : L = Ptoi %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v9" : L = Sub %"iw_1.iw_1.v4", %"iw_1.iw_1.v8";
    %"iw_1.iw_1.v15" : W = (Cmp Uge L) %"iw_1.iw_1.v9", #2352
    => br %"iw_1.iw_1.v15" ? "iw_1.iw_1.L10" : "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.join":
    %"iw_1.v273" = %"iw_1.v271" +p #88;
    %"chk46" : A = (Check 0 8 Read 8) %"iw_1.v273";
    %"iw_1.v274" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"chk47" : F = CheckFunction %"iw_1.v274";
    rawcall %"iw_1.v276" : P = %"chk47"(P %"iw_1.pr.1", P #0, L #0);
    %"iw_1.v285" = %"iw_1.pr.1" +p #192;
    %"chk48" : A = (Renew 0 4 Read 1) %"chk31", %"iw_1.v285";
    %"iw_1.v286" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"iw_1.v287" : W = (Cmp Sgt W) %"iw_1.v286", #0
    => br %"iw_1.v287" ? "iw_1.L277" : "iw_1.L291" };
  ir_blk{ @"iw_1.L277":
    call void $"__GI__IO_wsetb"(P %"iw_1.pr.1", P #0, P #0, W #0)
    => goto "iw_1.L291" };
  ir_blk{ @"iw_1.L291":
    %"iw_1.v297" = %"iw_1.pr.1" +p #192;
    %"chk49" : A = (Renew 0 4 Write 1) %"chk31", %"iw_1.v297";
    store Ww [%"chk49" + 0] <- #4294967295;
    %"chk50" : A = (Renew 0 4 Read 1) %"chk13", %"iw_1.pr.1";
    %"iw_1.v303" : W = (RawLoad (LdNarrow Sw) 0) %"chk50";
    %"iw_1.v304" : W = And %"iw_1.v303", #32768;
    %"iw_1.v305" : W = (Cmp Eq W) %"iw_1.v304", #0
    => br %"iw_1.v305" ? "iw_1.L306" : "iw_1.L301" };
  ir_blk{ @"iw_1.L306":
    %"iw_1.v312" : P = Copy $"__libc_single_threaded_internal";
    %"chk51" : A = (Check 0 1 Read 1) %"iw_1.v312";
    %"iw_1.v313" : W = (RawLoad (LdNarrow Sb) 0) %"chk51";
    %"iw_1.v314" : W = (Cmp Ne W) %"iw_1.v313", #0
    => br %"iw_1.v314" ? "iw_1.L315" : "iw_1.L316" };
  ir_blk{ @"iw_1.L315":
    %"iw_1.v318" = %"iw_1.pr.1" +p #136;
    %"chk52" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v318";
    %"iw_1.v319" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"iw_1.v320" = %"iw_1.v319" +p #4;
    %"chk53" : A = (Check 0 4 Read 1) %"iw_1.v320";
    %"iw_1.v321" : W = (RawLoad (LdNarrow Sw) 0) %"chk53";
    %"iw_1.v322" : W = (Cmp Eq W) %"iw_1.v321", #0
    => goto "iw_1.L316" };
  ir_blk{ @"iw_1.L316" [%"iw_1.v324" : W = phi("iw_1.L306" => #0, "iw_1.L315" => %"iw_1.v322")]:
    => br %"iw_1.v324" ? "iw_1.L309" : "iw_1.L310" };
  ir_blk{ @"iw_1.L309":
    %"iw_1.v326" = %"iw_1.pr.1" +p #136;
    %"chk54" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v326";
    %"iw_1.v327" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"iw_1.v328" = %"iw_1.v327" +p #8;
    %"chk55" : A = (Check 0 8 Write 8) %"iw_1.v328";
    store.ptr [%"chk55" + 0] <- #0;
    %"chk56" : A = (Renew 0 8 Read 8) %"chk54", %"iw_1.v326";
    %"iw_1.v331" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"chk57" : A = (Check 0 4 Write 1) %"iw_1.v331";
    store Ww [%"chk57" + 0] <- #0
    => goto "iw_1.L301" };
  ir_blk{ @"iw_1.L310":
    %"iw_1.v336" = %"iw_1.pr.1" +p #136;
    %"chk58" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v336";
    %"iw_1.v337" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"iw_1.v338" = %"iw_1.v337" +p #4;
    %"chk59" : A = (Check 0 4 Read 1) %"iw_1.v338";
    %"iw_1.v339" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"iw_1.v340" : W = (Cmp Eq W) %"iw_1.v339", #0
    => br %"iw_1.v340" ? "iw_1.L332" : "iw_1.L333" };
  ir_blk{ @"iw_1.L332":
    %"iw_1.v342" = %"iw_1.pr.1" +p #136;
    %"iw_1.v343" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"iw_1.v344" = %"iw_1.v343" +p #8;
    %"chk61" : A = (Check 0 8 Write 8) %"iw_1.v344";
    store.ptr [%"chk61" + 0] <- #0;
    %"chk62" : A = (Renew 0 8 Read 8) %"chk58", %"iw_1.v342";
    %"iw_1.v348" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"chk63" : A = (Check 0 4 Read 1) %"iw_1.v348";
    %"iw_1.v352" : W = (RawLoad (LdNarrow Sw) 0) %"chk63"
    => goto "iw_1.L353" };
  ir_blk{ @"iw_1.L353" [%"iw_1.v355" : W = phi("iw_1.L332" => %"iw_1.v352", "iw_1.L353" => %"iw_1.v356")]:
    %"chk64" : A = (HalfCheck Lower 0 4 Write 4) %"chk63", %"iw_1.v348";
    %"iw_1.v356" : W = (RawCas (CasNarrow Sw) 0) %"chk64", %"iw_1.v355", #0;
    %"iw_1.v357" : W = (Cmp Eq W) %"iw_1.v356", %"iw_1.v355"
    => br %"iw_1.v357" ? "iw_1.L354" : poll "iw_1.L353" };
  ir_blk{ @"iw_1.L354":
    %"iw_1.v362" : W = (Cmp Sgt W) %"iw_1.v355", #1
    => br %"iw_1.v362" ? "iw_1.L365" : "iw_1.L301" };
  ir_blk{ @"iw_1.L365":
    call void $"__GI___lll_lock_wake_private"(P %"iw_1.v348")
    => goto "iw_1.L301" };
  ir_blk{ @"iw_1.L333":
    %"iw_1.v377" = %"iw_1.pr.1" +p #136;
    %"iw_1.v378" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"iw_1.v379" = %"iw_1.v378" +p #4;
    %"chk66" : A = (Check 0 4 Read 1) %"iw_1.v379";
    %"iw_1.v380" : W = (RawLoad (LdNarrow Sw) 0) %"chk66";
    %"iw_1.v381" : W = Sub %"iw_1.v380", #1;
    %"chk67" : A = (Renew 0 4 Write 1) %"chk66", %"iw_1.v379";
    store Ww [%"chk67" + 0] <- %"iw_1.v381"
    => goto "iw_1.L301" };
  ir_blk{ @"iw_1.L301":
    %"iw_1.v382" : P = Copy $"glibc_genops#run_fp";
    %"chk68" : A = (Check 0 8 Write 8) %"iw_1.v382";
    store.ptr [%"chk68" + 0] <- #0;
    %"iw_1.v384" = %"iw_1.pr.1" +p #104;
    %"chk69" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v384";
    %"iw_1.v385" : P = (RawLoadPointer 0 load_effects) %"chk69"
    => goto poll "iw_1.L81" };
  ir_blk{ @"iw_1.L386":
    %"iw_1.v392" : P = Copy $"__libc_single_threaded_internal";
    %"chk70" : A = (Check 0 1 Read 1) %"iw_1.v392";
    %"iw_1.v393" : W = (RawLoad (LdNarrow Sb) 0) %"chk70";
    %"iw_1.v394" : W = (Cmp Ne W) %"iw_1.v393", #0
    => br %"iw_1.v394" ? "iw_1.L395" : "iw_1.L396" };
  ir_blk{ @"iw_1.L395":
    %"iw_1.v397" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v398" = %"iw_1.v397" +p #4;
    %"chk71" : A = (Check 0 4 Read 1) %"iw_1.v398";
    %"iw_1.v399" : W = (RawLoad (LdNarrow Sw) 0) %"chk71";
    %"iw_1.v400" : W = (Cmp Eq W) %"iw_1.v399", #0
    => goto "iw_1.L396" };
  ir_blk{ @"iw_1.L396" [%"iw_1.v402" : W = phi("iw_1.L386" => #0, "iw_1.L395" => %"iw_1.v400")]:
    => br %"iw_1.v402" ? "iw_1.L389" : "iw_1.L390" };
  ir_blk{ @"iw_1.L389":
    %"iw_1.v403" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v404" = %"iw_1.v403" +p #8;
    %"chk72" : A = (Check 0 8 Write 8) %"iw_1.v404";
    store.ptr [%"chk72" + 0] <- #0;
    %"iw_1.v405" : P = Copy $"glibc_genops#list_all_lock";
    %"chk73" : A = (Check 0 4 Write 1) %"iw_1.v405";
    store Ww [%"chk73" + 0] <- #0
    => goto "iw_1.L448" };
  ir_blk{ @"iw_1.L390":
    %"iw_1.v409" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v410" = %"iw_1.v409" +p #4;
    %"chk74" : A = (Check 0 4 Read 1) %"iw_1.v410";
    %"iw_1.v411" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"iw_1.v412" : W = (Cmp Eq W) %"iw_1.v411", #0
    => br %"iw_1.v412" ? "iw_1.L406" : "iw_1.L407" };
  ir_blk{ @"iw_1.L406":
    %"iw_1.v413" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v414" = %"iw_1.v413" +p #8;
    %"chk75" : A = (Check 0 8 Write 8) %"iw_1.v414";
    store.ptr [%"chk75" + 0] <- #0;
    %"iw_1.v416" : P = Copy $"glibc_genops#list_all_lock";
    %"chk76" : A = (Check 0 4 Read 1) %"iw_1.v416";
    %"iw_1.v420" : W = (RawLoad (LdNarrow Sw) 0) %"chk76"
    => goto "iw_1.L421" };
  ir_blk{ @"iw_1.L421" [%"iw_1.v423" : W = phi("iw_1.L406" => %"iw_1.v420", "iw_1.L421" => %"iw_1.v424")]:
    %"chk77" : A = (HalfCheck Lower 0 4 Write 4) %"chk76", %"iw_1.v416";
    %"iw_1.v424" : W = (RawCas (CasNarrow Sw) 0) %"chk77", %"iw_1.v423", #0;
    %"iw_1.v425" : W = (Cmp Eq W) %"iw_1.v424", %"iw_1.v423"
    => br %"iw_1.v425" ? "iw_1.L422" : poll "iw_1.L421" };
  ir_blk{ @"iw_1.L422":
    %"iw_1.v430" : W = (Cmp Sgt W) %"iw_1.v423", #1
    => br %"iw_1.v430" ? "iw_1.L433" : "iw_1.L448" };
  ir_blk{ @"iw_1.L433":
    call void $"__GI___lll_lock_wake_private"(P %"iw_1.v416")
    => goto "iw_1.L448" };
  ir_blk{ @"iw_1.L407":
    %"iw_1.v444" : P = Copy $"glibc_genops#list_all_lock";
    %"iw_1.v445" = %"iw_1.v444" +p #4;
    %"chk78" : A = (Check 0 4 Read 1) %"iw_1.v445";
    %"iw_1.v446" : W = (RawLoad (LdNarrow Sw) 0) %"chk78";
    %"iw_1.v447" : W = Sub %"iw_1.v446", #1;
    %"chk79" : A = (Renew 0 4 Write 1) %"chk78", %"iw_1.v445";
    store Ww [%"chk79" + 0] <- %"iw_1.v447"
    => goto "iw_1.L448" };
  ir_blk{ @"iw_1.L448":
    call void $"__GI___libc_cleanup_pop_restore"(P %"iw_1.v2")
    => ret %"v1" }])) }.

Definition hello_image_fn___GI__IO_unsave_markers : func :=
  ir_fn{ "export" "__GI__IO_unsave_markers"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #96;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" : L = Ptoi %"v5";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L6" : "L8";
  @"L6":
    %"v13" = %"v0" +p #96;
    %"chk1" : A = (Renew 0 8 Write 8) %"chk0", %"v13";
    store.ptr [%"chk1" + 0] <- #0
    => goto "L8";
  @"L8":
    %"v18" = %"v0" +p #80;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v20" : L = Ptoi %"v19";
    %"v21" : L = Ptoi #0;
    %"v22" : W = (Cmp Ne L) %"v20", %"v21"
    => br %"v22" ? "L14" : "L16";
  @"L14":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "L16";
  @"L16":
    => ret void
} }.
