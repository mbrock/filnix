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

Definition hello_image_fn_proper_name : func :=
  ir_fn{ "export" "proper_name"(P %"v0") -> (RClass P) {
  @"start":
    => ret %"v0"
} }.

Definition hello_image_fn___printf_buffer_flush_dprintf : func :=
  ir_fn{ "export" "__printf_buffer_flush_dprintf"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #44;
    %"v7" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L9";
  @"L9" [%"pr.1" : P = phi("L45" => %"v52", "start" => %"v4")]:
    %"v14" : L = Ptoi %"pr.1";
    %"v15" : L = Ptoi %"v8";
    %"v16" : W = (Cmp Ult L) %"v14", %"v15"
    => br %"v16" ? "L19" : "L11";
  @"L19":
    %"v23" = %"v0" +p #40;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v23";
    %"v24" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v30" : L = Sub %"v15", %"v14";
    call %"v31" : L = $"__GI_write"(W %"v24", P %"pr.1", L %"v30");
    %"v34" : W = (Cmp Eq L) %"v31", #18446744073709551615
    => br %"v34" ? "L35" : "L36";
  @"L35":
    %"v37" : P = Copy $"__libc_errno";
    %"chk2" : A = (Check 0 4 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v39" : W = (Cmp Eq W) %"v38", #4
    => goto "L36";
  @"L36" [%"v41" : W = phi("L19" => #0, "L35" => %"v39")]:
    => br %"v41" ? poll "L19" : "L21";
  @"L21":
    %"v47" : W = (Cmp Slt L) %"v31", #0
    => br %"v47" ? "iw_1.start" : "L45";
  @"iw_1.start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk3" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v3";
    store Ww [%"chk3" + 0] <- #0
    => ret void;
  @"L45":
    %"v52" = %"pr.1" +p %"v31"
    => goto poll "L9";
  @"L11":
    %"v54" = %"v0" +p #24;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v54";
    %"v55" : L = (RawLoad LdL 0) %"chk4";
    %"v57" = %"v0" +p #8;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v57";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v61" : L = Ptoi %"v58";
    %"v62" : L = Ptoi %"v60";
    %"v63" : L = Sub %"v61", %"v62";
    %"v64" : L = Add %"v55", %"v63";
    %"chk7" : A = (Renew 0 8 Write 1) %"chk4", %"v54";
    store Wl [%"chk7" + 0] <- %"v64";
    %"v68" = %"v0" +p #44;
    %"chk8" : A = (Renew 0 8 Write 8) %"chk0", %"v57";
    store.ptr [%"chk8" + 0] <- %"v68"
    => ret void
} }.

Definition hello_image_fn___printf_buffer_flush_obstack : func :=
  ir_fn{ "export" "__printf_buffer_flush_obstack"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 1) %"v3";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v6" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v10" : L = Ptoi %"v7";
    %"v11" : L = Ptoi %"v9";
    %"v12" : L = Sub %"v10", %"v11";
    %"v13" : L = Add %"v4", %"v12";
    %"chk3" : A = (Renew 0 8 Write 1) %"chk0", %"v3";
    store Wl [%"chk3" + 0] <- %"v13";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v21" = %"v0" +p #48;
    %"v22" = %"v21" +p #1;
    %"v23" : L = Ptoi %"v19";
    %"v24" : L = Ptoi %"v22";
    %"v25" : W = (Cmp Eq L) %"v23", %"v24"
    => br %"v25" ? "L14" : "L15";
  @"L14":
    %"v28" = %"v0" +p #40;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v34" = %"v29" +p #24;
    %"chk6" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v36" = %"v35" +p #1;
    %"v38" = %"v29" +p #32;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk6", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v40" : L = Ptoi %"v36";
    %"v41" : L = Ptoi %"v39";
    %"v42" : W = (Cmp Ugt L) %"v40", %"v41"
    => br %"v42" ? "L30" : "L32";
  @"L30":
    call void $"__GI__obstack_newchunk"(P %"v29", W #1)
    => goto "L32";
  @"L32":
    %"v45" = %"v29" +p #24;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk6", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v47" = %"v46" +p #1;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk6", %"v45";
    store.ptr [%"chk9" + 0] <- %"v47";
    %"v49" = %"v0" +p #48;
    %"chk10" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v49";
    %"v50" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"chk11" : A = (Check 0 1 Write 1) %"v46";
    store Wb [%"chk11" + 0] <- %"v50";
    %"v53" = %"v0" +p #40;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk5", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v55" = %"v54" +p #24;
    %"chk13" : A = (Check 0 8 Read 8) %"v55";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk14" + 0] <- %"v56";
    %"v58" = %"v0" +p #8;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk2", %"v0";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk1", %"v58";
    store.ptr [%"chk16" + 0] <- %"v60";
    %"chk17" : A = (Renew 0 8 Read 8) %"chk5", %"v53";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v67" = %"v65" +p #32;
    %"chk18" : A = (Check 0 8 Read 8) %"v67";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v70" = %"v65" +p #24;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk18", %"v70";
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v72" : L = Ptoi %"v68";
    %"v73" : L = Ptoi %"v71";
    %"v74" : L = Sub %"v72", %"v73";
    %"v75" : L = (Ext Uw) %"v74";
    %"v77" = %"v0" +p #16;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk1", %"v58";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v82" = %"v80" +p %"v75";
    %"chk21" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v77";
    store.ptr [%"chk21" + 0] <- %"v82";
    %"chk22" : A = (Renew 0 8 Read 8) %"chk5", %"v53";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v86" = %"v85" +p #24;
    %"chk23" : A = (Check 0 8 Read 8) %"v86";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v89" = %"v87" +p %"v75";
    %"chk24" : A = (Renew 0 8 Write 8) %"chk23", %"v86";
    store.ptr [%"chk24" + 0] <- %"v89"
    => goto "L16";
  @"L15":
    %"v92" = %"v0" +p #48;
    %"chk25" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk25" + 0] <- %"v92";
    %"v94" = %"v0" +p #8;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk1", %"v94";
    store.ptr [%"chk26" + 0] <- %"v92";
    %"v98" = %"v0" +p #16;
    %"v101" = %"v92" +p #1;
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v98";
    store.ptr [%"chk27" + 0] <- %"v101"
    => goto "L16";
  @"L16":
    => ret void
} }.

Definition hello_image_fn___printf_buffer_flush_asprintf : func :=
  ir_fn{ "export" "__printf_buffer_flush_asprintf"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v8" : L = Ptoi %"v5";
    %"v9" : L = Ptoi %"v7";
    %"v10" : L = Sub %"v8", %"v9";
    %"v15" : W = (Cmp Uge L) %"v10", #2147483647
    => br %"v15" ? "L11" : "L13";
  @"L11":
    %"v16" : P = Copy $"__libc_errno";
    %"chk2" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk2" + 0] <- #75;
    %"iw_1.v3" = %"v0" +p #32;
    %"chk3" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v3";
    store Ww [%"chk3" + 0] <- #0
    => ret void;
  @"L13":
    %"v21" = %"v0" +p #16;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" : L = Ptoi %"v22";
    %"v26" : L = Ptoi %"v24";
    %"v27" : L = Sub %"v25", %"v26";
    %"v31" : L = Shr %"v27", #1;
    %"v32" : L = Add %"v27", %"v31";
    %"v33" : L = Add %"v32", #16;
    %"v34" : L = Sub %"v33", #1;
    %"v36" : L = And %"v34", #18446744073709551600;
    %"v37" : L = Or %"v36", #8;
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v45" = %"v0" +p #40;
    %"v46" : L = Ptoi %"v43";
    %"v47" : L = Ptoi %"v45";
    %"v48" : W = (Cmp Eq L) %"v46", %"v47"
    => br %"v48" ? "L39" : "L40";
  @"L39":
    call %"v50" : P = $"malloc"(L %"v37");
    %"v55" : L = Ptoi %"v50";
    %"v56" : L = Ptoi #0;
    %"v57" : W = (Cmp Eq L) %"v55", %"v56"
    => br %"v57" ? "iw_2.start" : "L53";
  @"iw_2.start":
    %"iw_2.v3" = %"v0" +p #32;
    %"chk7" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_2.v3";
    store Ww [%"chk7" + 0] <- #0
    => ret void;
  @"L53":
    %"v62" = %"v0" +p #40;
    call %"v64" : P = $"__GI_memcpy"(P %"v50", P %"v62", L %"v10")
    => goto "L41";
  @"L40":
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v68" : P = $"realloc"(P %"v66", L %"v37");
    %"v73" : L = Ptoi %"v68";
    %"v74" : L = Ptoi #0;
    %"v75" : W = (Cmp Eq L) %"v73", %"v74"
    => br %"v75" ? "iw_3.start" : "L41";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk9" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_3.v3";
    store Ww [%"chk9" + 0] <- #0
    => ret void;
  @"L41" [%"pr.1" : P = phi("L53" => %"v50", "L40" => %"v68")]:
    %"chk10" : A = (Renew 0 8 Write 8) %"chk1", %"v0";
    store.ptr [%"chk10" + 0] <- %"pr.1";
    %"v81" = %"v0" +p #8;
    %"v84" = %"pr.1" +p %"v10";
    %"chk11" : A = (Renew 0 8 Write 8) %"chk0", %"v81";
    store.ptr [%"chk11" + 0] <- %"v84";
    %"v86" = %"v0" +p #16;
    %"v89" = %"pr.1" +p %"v37";
    %"chk12" : A = (Renew 0 8 Write 8) %"chk4", %"v86";
    store.ptr [%"chk12" + 0] <- %"v89"
    => ret void
} }.

Definition hello_image_fn___printf_buffer_flush_snprintf : func :=
  ir_fn{ "export" "__printf_buffer_flush_snprintf"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 1) %"v3";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v6" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v10" : L = Ptoi %"v7";
    %"v11" : L = Ptoi %"v9";
    %"v12" : L = Sub %"v10", %"v11";
    %"v13" : L = Add %"v4", %"v12";
    %"chk3" : A = (Renew 0 8 Write 1) %"chk0", %"v3";
    store Wl [%"chk3" + 0] <- %"v13";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v20" = %"v0" +p #40;
    %"v21" : L = Ptoi %"v18";
    %"v22" : L = Ptoi %"v20";
    %"v23" : W = (Cmp Ne L) %"v21", %"v22"
    => br %"v23" ? "L14" : "L16";
  @"L14":
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v30" = %"v0" +p #16;
    %"v31" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v32" : L = Ptoi %"v28";
    %"v33" : L = Ptoi %"v31";
    %"v34" : W = (Cmp Ne L) %"v32", %"v33"
    => br %"v34" ? "L24" : "L26";
  @"L24":
    %"v36" = %"v0" +p #16;
    %"v37" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v40" = %"v37" +p #18446744073709551615;
    %"chk8" : A = (Check 0 1 Write 1) %"v40";
    store Wb [%"chk8" + 0] <- #0
    => goto "L26";
  @"L26":
    %"v43" = %"v0" +p #40;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk9" + 0] <- %"v43";
    %"v45" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Write 8) %"chk1", %"v45";
    store.ptr [%"chk10" + 0] <- %"v43";
    %"v49" = %"v0" +p #16;
    %"v55" = %"v43" +p #128;
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v49";
    store.ptr [%"chk11" + 0] <- %"v55"
    => goto "L16";
  @"L16":
    %"v58" = %"v0" +p #40;
    %"chk12" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk12" + 0] <- %"v58";
    %"v60" = %"v0" +p #8;
    %"chk13" : A = (Renew 0 8 Write 8) %"chk1", %"v60";
    store.ptr [%"chk13" + 0] <- %"v58"
    => ret void
} }.

Definition hello_image_fn___printf_buffer_snprintf_init : func :=
  ir_fn{ "export" "__printf_buffer_snprintf_init"(P %"v0", P %"v2", L %"v4") -> RVoid {
  @"start":
    %"iw_1.v12" = %"v2" +p %"v4";
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v2";
    %"iw_1.iw_1.v11" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v2";
    %"iw_1.iw_1.v14" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v12";
    %"iw_1.iw_1.v17" = %"v0" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.iw_1.v17";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.iw_1.v19" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.iw_1.v19";
    store Ww [%"chk4" + 0] <- #2;
    %"v13" : W = (Cmp Ugt L) %"v4", #0
    => br %"v13" ? "L9" : "L11";
  @"L9":
    %"chk5" : A = (Check 0 1 Write 1) %"v2";
    store Wb [%"chk5" + 0] <- #0
    => goto "L11";
  @"L11":
    => ret void
} }.

Definition hello_image_fn___printf_buffer_snprintf_done : func :=
  ir_fn{ "export" "__printf_buffer_snprintf_done"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : W = (Cmp Ult L) %"v11", %"v12"
    => br %"v13" ? "L2" : "L3";
  @"L2":
    %"v15" = %"v0" +p #8;
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk3" : A = (Check 0 1 Write 1) %"v16";
    store Wb [%"chk3" + 0] <- #0
    => goto "L4";
  @"L3":
    %"v21" = %"v0" +p #8;
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v25" : L = Ptoi %"v22";
    %"v26" : L = Ptoi %"v24";
    %"v27" : W = (Cmp Ugt L) %"v25", %"v26"
    => br %"v27" ? "L17" : "L4";
  @"L17":
    %"v29" = %"v0" +p #8;
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v33" = %"v30" +p #18446744073709551615;
    %"chk7" : A = (Check 0 1 Write 1) %"v33";
    store Wb [%"chk7" + 0] <- #0
    => goto "L4";
  @"L4":
    call %"v35" : W = $"__printf_buffer_done"(P %"v0")
    => ret %"v35"
} }.

Definition hello_image_fn_glibc_obstack'23print_and_abort : func :=
  ir_fn{ "local" "glibc_obstack#print_and_abort"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_obstack#str.148";
    %"v1" : P = Copy $"__GI__libc_intl_domainname";
    %"v2" : P = Copy $"glibc_obstack#str.149";
    call %"v3" : P = $"__GI___dcgettext"(P %"v1", P %"v2", W #5);
    call %"v4" : W = $"__fxprintf"(P #0, P %"v0", P %"v3");
    %"v5" : P = Copy $"obstack_exit_failure";
    %"chk0" : A = (Check 0 4 Read 1) %"v5";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call void $"__GI_exit"(W %"v6")
    => ret void
} }.

Definition hello_image_fn_glibc_getopt'23process_long_option : func :=
  ir_fn{ "local" "glibc_getopt#process_long_option"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8", W %"v10", P %"v12", W %"v14", P %"v16") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v25" = %"v12" +p #32;
    %"chk0" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L27" };
  ir_blk{ @"L27" [%"pr.1" : P = phi("L29" => %"v41", "start" => %"v26")]:
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v32" : W = (RawLoad (LdNarrow Sb) 0) %"chk1"
    => br %"v32" ? "L33" : "L34" };
  ir_blk{ @"L33":
    %"v36" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v37" : W = (Cmp Ne W) %"v36", #61
    => goto "L34" };
  ir_blk{ @"L34" [%"v39" : W = phi("L27" => #0, "L33" => %"v37")]:
    => br %"v39" ? "L29" : "L30" };
  ir_blk{ @"L29":
    %"v41" = %"pr.1" +p #1
    => goto poll "L27" };
  ir_blk{ @"L30":
    %"v44" = %"v12" +p #32;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v46" : L = Ptoi %"pr.1";
    %"v47" : L = Ptoi %"v45";
    %"v48" : L = Sub %"v46", %"v47"
    => goto "L50" };
  ir_blk{ @"L50" [%"pr.9" : W = phi("L30" => #0, "L52" => %"v84"); %"pr.2" : P = phi("L30" => %"v6", "L52" => %"v82")]:
    %"chk4" : A = (Check 0 8 Read 8) %"pr.2";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v56" : L = Ptoi %"v55";
    %"v57" : W = (Cmp Ne L) %"v56", #0
    => br %"v57" ? "L51" : "L53" };
  ir_blk{ @"L51":
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v64" = %"v12" +p #32;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v67" : W = $"__GI_strncmp"(P %"v62", P %"v65", L %"v48");
    %"v68" : W = (Cmp Eq W) %"v67", #0
    => br %"v68" ? "L69" : "L70" };
  ir_blk{ @"L69":
    %"chk7" : A = (Renew 0 8 Read 8) %"chk4", %"pr.2";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call %"v74" : L = $"__GI_strlen"(P %"v73");
    %"v75" : W = (Cmp Eq L) %"v48", %"v74"
    => goto "L70" };
  ir_blk{ @"L70" [%"v77" : W = phi("L51" => #0, "L69" => %"v75")]:
    => br %"v77" ? "L53" : "L52" };
  ir_blk{ @"L52":
    %"v82" = %"pr.2" +p #32;
    %"v84" : W = Add %"pr.9", #1
    => goto poll "L50" };
  ir_blk{ @"L53" [%"pr.11" : W = phi("L50" => #0, "L70" => %"pr.9"); %"pr.6" : P = phi("L50" => #0, "L70" => %"pr.2")]:
    %"v89" : L = Ptoi %"pr.6";
    %"v90" : L = Ptoi #0;
    %"v91" : W = (Cmp Eq L) %"v89", %"v90"
    => br %"v91" ? "L98" : "L87" };
  ir_blk{ @"L98" [%"pr.42" : W = phi("L108" => %"pr.40", "L53" => #4294967295); %"pr.39" : W = phi("L108" => %"pr.31", "L53" => #0); %"pr.30" : W = phi("L108" => %"pr.22", "L53" => #0); %"pr.21" : P = phi("L108" => %"pr.14", "L53" => #0); %"pr.13" : W = phi("L108" => %"v227", "L53" => #0); %"pr.8" : P = phi("L108" => %"pr.4", "L53" => %"pr.6"); %"pr.3" : P = phi("L108" => %"v225", "L53" => %"v6")]:
    %"chk8" : A = (Check 0 8 Read 8) %"pr.3";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v104" : L = Ptoi %"v103";
    %"v105" : W = (Cmp Ne L) %"v104", #0
    => br %"v105" ? "L99" : "L101" };
  ir_blk{ @"L99":
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v112" = %"v12" +p #32;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk10";
    call %"v115" : W = $"__GI_strncmp"(P %"v110", P %"v113", L %"v48");
    %"v116" : W = (Cmp Eq W) %"v115", #0
    => br %"v116" ? "L106" : "L108" };
  ir_blk{ @"L106":
    %"v121" : L = Ptoi %"pr.8";
    %"v123" : W = (Cmp Eq L) %"v121", %"v90"
    => br %"v123" ? "L108" : "L118" };
  ir_blk{ @"L118":
    => br %"v10" ? "L131" : "L130" };
  ir_blk{ @"L130":
    %"v133" = %"pr.8" +p #8;
    %"chk11" : A = (Check 0 4 Read 1) %"v133";
    %"v134" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"v136" = %"pr.3" +p #8;
    %"chk12" : A = (HalfCheck Upper 0 4 Read 1) %"chk8", %"v136";
    %"v137" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v138" : W = (Cmp Ne W) %"v134", %"v137"
    => goto "L131" };
  ir_blk{ @"L131" [%"v140" : W = phi("L118" => #1, "L130" => %"v138")]:
    => br %"v140" ? "L142" : "L141" };
  ir_blk{ @"L141":
    %"v144" = %"pr.8" +p #16;
    %"chk13" : A = (Check 0 8 Read 8) %"v144";
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v147" = %"pr.3" +p #16;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk8", %"v147";
    %"v148" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v149" : L = Ptoi %"v145";
    %"v150" : L = Ptoi %"v148";
    %"v151" : W = (Cmp Ne L) %"v149", %"v150"
    => goto "L142" };
  ir_blk{ @"L142" [%"v153" : W = phi("L131" => #1, "L141" => %"v151")]:
    => br %"v153" ? "L155" : "L154" };
  ir_blk{ @"L154":
    %"v157" = %"pr.8" +p #24;
    %"chk15" : A = (Check 0 4 Read 1) %"v157";
    %"v158" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v160" = %"pr.3" +p #24;
    %"chk16" : A = (HalfCheck Upper 0 4 Read 1) %"chk8", %"v160";
    %"v161" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v162" : W = (Cmp Ne W) %"v158", %"v161"
    => goto "L155" };
  ir_blk{ @"L155" [%"v164" : W = phi("L142" => #1, "L154" => %"v162")]:
    => br %"v164" ? "L126" : "L108" };
  ir_blk{ @"L126":
    %"v169" : W = (Cmp Eq W) %"pr.39", #0
    => br %"v169" ? "L165" : "L108" };
  ir_blk{ @"L165":
    %"v174" : W = (Cmp Eq W) %"v14", #0
    => br %"v174" ? "L172" : "L171" };
  ir_blk{ @"L171":
    %"v179" : L = Ptoi %"pr.21";
    %"v181" : W = (Cmp Eq L) %"v179", #0
    => br %"v181" ? "L175" : "L172" };
  ir_blk{ @"L175":
    %"v186" : L = (Ext Sw) %"pr.9";
    call %"iw_1.v3" : W = $"__GI___libc_alloca_cutoff"(L %"v186");
    %"iw_1.v4" : L = (Ext Sw) %"iw_1.v3";
    %"iw_1.v5" : W = (Cmp Ne L) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "iw_1.L7" : "iw_1.L6" };
  ir_blk{ @"iw_1.L6":
    %"iw_1.v11" : W = (Cmp Ule L) %"v186", #4096
    => goto "iw_1.L7" };
  ir_blk{ @"iw_1.L7" [%"iw_1.v15" : W = phi("L175" => #1, "iw_1.L6" => %"iw_1.v11")]:
    => br %"iw_1.v15" ? "L182" : "L183" };
  ir_blk{ @"L182":
    %"v190" : P = (Alloc 16) %"v186"
    => goto "L184" };
  ir_blk{ @"L183":
    call %"v196" : P = $"malloc"(L %"v186");
    %"v197" : L = Ptoi %"v196";
    %"v199" : W = (Cmp Eq L) %"v197", %"v90"
    => br %"v199" ? "L184" : "L192" };
  ir_blk{ @"L192":
    => goto "L184" };
  ir_blk{ @"L184" [%"pr.37" : W = phi("L182" => %"pr.39", "L192" => %"pr.39", "L183" => #1); %"pr.28" : W = phi("L182" => %"pr.30", "L192" => #1, "L183" => %"pr.30"); %"pr.20" : P = phi("L182" => %"v190", "L192" => %"v196", "L183" => %"v196")]:
    %"v204" : L = Ptoi %"pr.20";
    %"v205" : W = (Cmp Ne L) %"v204", #0
    => br %"v205" ? "L200" : "L172" };
  ir_blk{ @"L200":
    call %"v209" : P = $"__GI_memset"(P %"pr.20", W #0, L %"v186");
    %"v212" : L = (Ext Sw) %"pr.42";
    %"v213" = %"pr.20" +p %"v212";
    %"chk17" : A = (Check 0 1 Write 1) %"v213";
    store Wb [%"chk17" + 0] <- #1
    => goto "L172" };
  ir_blk{ @"L172" [%"pr.35" : W = phi("L165" => #1, "L200" => %"pr.37", "L184" => %"pr.37", "L171" => %"pr.39"); %"pr.26" : W = phi("L165" => %"pr.30", "L200" => %"pr.28", "L184" => %"pr.28", "L171" => %"pr.30"); %"pr.18" : P = phi("L165" => %"pr.21", "L200" => %"pr.20", "L184" => %"pr.20", "L171" => %"pr.21")]:
    %"v218" : L = Ptoi %"pr.18";
    %"v219" : W = (Cmp Ne L) %"v218", #0
    => br %"v219" ? "L214" : "L108" };
  ir_blk{ @"L214":
    %"v222" : L = (Ext Sw) %"pr.13";
    %"v223" = %"pr.18" +p %"v222";
    %"chk18" : A = (Check 0 1 Write 1) %"v223";
    store Wb [%"chk18" + 0] <- #1
    => goto "L108" };
  ir_blk{ @"L108" [%"pr.40" : W = phi("L106" => %"pr.13", "L214" => %"pr.42", "L172" => %"pr.42", "L126" => %"pr.42", "L155" => %"pr.42", "L99" => %"pr.42"); %"pr.31" : W = phi("L106" => %"pr.39", "L214" => %"pr.35", "L172" => %"pr.35", "L126" => %"pr.39", "L155" => %"pr.39", "L99" => %"pr.39"); %"pr.22" : W = phi("L106" => %"pr.30", "L214" => %"pr.26", "L172" => %"pr.26", "L126" => %"pr.30", "L155" => %"pr.30", "L99" => %"pr.30"); %"pr.14" : P = phi("L106" => %"pr.21", "L214" => %"pr.18", "L172" => %"pr.18", "L126" => %"pr.21", "L155" => %"pr.21", "L99" => %"pr.21"); %"pr.4" : P = phi("L106" => %"pr.3", "L214" => %"pr.8", "L172" => %"pr.8", "L126" => %"pr.8", "L155" => %"pr.8", "L99" => %"pr.8")]:
    %"v225" = %"pr.3" +p #32;
    %"v227" : W = Add %"pr.13", #1
    => goto poll "L98" };
  ir_blk{ @"L101":
    %"v232" : L = Ptoi %"pr.21";
    %"v233" : W = (Cmp Ne L) %"v232", #0
    => br %"v233" ? "L235" : "L234" };
  ir_blk{ @"L234":
    %"v237" : W = (Cmp Ne W) %"pr.39", #0
    => goto "L235" };
  ir_blk{ @"L235" [%"v238" : W = phi("L101" => #1, "L234" => %"v237")]:
    => br %"v238" ? "L228" : "L87" };
  ir_blk{ @"L228":
    => br %"v14" ? "L239" : "L241" }] [ir_blk{ @"L239":
    => br %"pr.39" ? "L243" : "L244" };
  ir_blk{ @"L243":
    %"v247" : P = Copy $"stderr";
    %"chk19" : A = (Check 0 8 Read 8) %"v247";
    %"v248" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v249" : P = Copy $"__GI__libc_intl_domainname";
    %"v250" : P = Copy $"glibc_getopt#str.138";
    call %"v251" : P = $"__GI___dcgettext"(P %"v249", P %"v250", W #5);
    %"chk20" : A = (Check 0 8 Read 8) %"v2";
    %"v254" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v257" = %"v12" +p #32;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk0", %"v257";
    %"v258" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"v259" : W = $"__fxprintf_nocancel"(P %"v248", P %"v251", P %"v254", P %"v16", P %"v258")
    => goto "L241" };
  ir_blk{ @"L244":
    %"v260" : P = Copy $"stderr";
    %"chk22" : A = (Check 0 8 Read 8) %"v260";
    %"v261" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v262" : P = Copy $"__GI__libc_intl_domainname";
    %"v263" : P = Copy $"glibc_getopt#str.139";
    call %"v264" : P = $"__GI___dcgettext"(P %"v262", P %"v263", W #5);
    %"chk23" : A = (Check 0 8 Read 8) %"v2";
    %"v267" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v270" = %"v12" +p #32;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"v270";
    %"v271" : P = (RawLoadPointer 0 load_effects) %"chk24";
    call %"v272" : W = $"__fxprintf_nocancel"(P %"v261", P %"v264", P %"v267", P %"v16", P %"v271")
    => goto "L273" };
  ir_blk{ @"L273" [%"pr.10" : W = phi("L244" => #0, "L275" => %"v300")]:
    %"v279" : W = (Cmp Slt W) %"pr.10", %"pr.9"
    => br %"v279" ? "L274" : "L276" };
  ir_blk{ @"L274":
    %"v285" : L = (Ext Sw) %"pr.10";
    %"v286" = %"pr.21" +p %"v285";
    %"chk25" : A = (Check 0 1 Read 1) %"v286";
    %"v287" : W = (RawLoad (LdNarrow Ub) 0) %"chk25"
    => br %"v287" ? "L280" : "L275" };
  ir_blk{ @"L280":
    %"v288" : P = Copy $"stderr";
    %"chk26" : A = (Check 0 8 Read 8) %"v288";
    %"v289" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v290" : P = Copy $"glibc_getopt#str.140";
    %"v295" : L = Shl %"v285", #5;
    %"v296" = %"v6" +p %"v295";
    %"chk27" : A = (Check 0 8 Read 8) %"v296";
    %"v297" : P = (RawLoadPointer 0 load_effects) %"chk27";
    call %"v298" : W = $"__fxprintf_nocancel"(P %"v289", P %"v290", P %"v16", P %"v297")
    => goto "L275" };
  ir_blk{ @"L275":
    %"v300" : W = Add %"pr.10", #1
    => goto poll "L273" };
  ir_blk{ @"L276":
    %"v301" : P = Copy $"stderr";
    %"chk28" : A = (Check 0 8 Read 8) %"v301";
    %"v302" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v303" : P = Copy $"glibc_getopt#str.141";
    call %"v304" : W = $"__fxprintf_nocancel"(P %"v302", P %"v303")
    => goto "L241" };
  ir_blk{ @"L241":
    => br %"pr.30" ? "L305" : "L307" };
  ir_blk{ @"L305":
    call void $"free"(P %"pr.21")
    => goto "L307" };
  ir_blk{ @"L307":
    %"v311" = %"v12" +p #32;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v311";
    %"v312" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v315" : P = (RawLoadPointer 0 load_effects) %"chk29";
    call %"v316" : L = $"__GI_strlen"(P %"v315");
    %"v317" = %"v312" +p %"v316";
    %"chk31" : A = (Renew 0 8 Write 8) %"chk0", %"v311";
    store.ptr [%"chk31" + 0] <- %"v317";
    %"chk32" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v319" : W = (RawLoad (LdNarrow Sw) 0) %"chk32";
    %"v320" : W = Add %"v319", #1;
    %"chk33" : A = (Renew 0 4 Write 1) %"chk32", %"v12";
    store Ww [%"chk33" + 0] <- %"v320";
    %"v322" = %"v12" +p #8;
    %"chk34" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v322";
    store Ww [%"chk34" + 0] <- #0
    => ret #63 };
  ir_blk{ @"L87" [%"pr.12" : W = phi("L235" => %"pr.42", "L53" => %"pr.11"); %"pr.7" : P = phi("L235" => %"pr.8", "L53" => %"pr.6")]:
    %"v329" : L = Ptoi %"pr.7";
    %"v331" : W = (Cmp Eq L) %"v329", %"v90"
    => br %"v331" ? "L325" : "L327" };
  ir_blk{ @"L325":
    %"v336" : W = (Cmp Eq W) %"v10", #0
    => br %"v336" ? "L338" : "L337" };
  ir_blk{ @"L337":
    %"chk35" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v341" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v342" : L = (Ext Sw) %"v341";
    %"v343" : L = Shl %"v342", #3;
    %"v344" = %"v2" +p %"v343";
    %"chk36" : A = (Check 0 8 Read 8) %"v344";
    %"v345" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v346" = %"v345" +p #1;
    %"chk37" : A = (Check 0 1 Read 1) %"v346";
    %"v347" : W = (RawLoad (LdNarrow Sb) 0) %"chk37";
    %"v348" : W = (Cmp Eq W) %"v347", #45
    => goto "L338" };
  ir_blk{ @"L338" [%"v350" : W = phi("L325" => #1, "L337" => %"v348")]:
    => br %"v350" ? "L352" : "L351" };
  ir_blk{ @"L351":
    %"v355" = %"v12" +p #32;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk0", %"v355";
    %"v356" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 1 Read 1) %"v356";
    %"v357" : W = (RawLoad (LdNarrow Sb) 0) %"chk39";
    call %"v358" : P = $"__GI_strchr"(P %"v4", W %"v357");
    %"v359" : L = Ptoi %"v358";
    %"v361" : W = (Cmp Eq L) %"v359", %"v90"
    => goto "L352" };
  ir_blk{ @"L352" [%"v363" : W = phi("L338" => #1, "L351" => %"v361")]:
    => br %"v363" ? "L332" : "L334" };
  ir_blk{ @"L332":
    => br %"v14" ? "L364" : "L366" };
  ir_blk{ @"L364":
    %"v368" : P = Copy $"stderr";
    %"chk40" : A = (Check 0 8 Read 8) %"v368";
    %"v369" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v370" : P = Copy $"__GI__libc_intl_domainname";
    %"v371" : P = Copy $"glibc_getopt#str.142";
    call %"v372" : P = $"__GI___dcgettext"(P %"v370", P %"v371", W #5);
    %"chk41" : A = (Check 0 8 Read 8) %"v2";
    %"v375" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v378" = %"v12" +p #32;
    %"chk42" : A = (Renew 0 8 Read 8) %"chk0", %"v378";
    %"v379" : P = (RawLoadPointer 0 load_effects) %"chk42";
    call %"v380" : W = $"__fxprintf_nocancel"(P %"v369", P %"v372", P %"v375", P %"v16", P %"v379")
    => goto "L366" };
  ir_blk{ @"L366":
    %"v382" = %"v12" +p #32;
    %"chk43" : A = (Renew 0 8 Write 8) %"chk0", %"v382";
    store.ptr [%"chk43" + 0] <- #0;
    %"chk44" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v384" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"v385" : W = Add %"v384", #1;
    %"chk45" : A = (Renew 0 4 Write 1) %"chk44", %"v12";
    store Ww [%"chk45" + 0] <- %"v385";
    %"v387" = %"v12" +p #8;
    %"chk46" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v387";
    store Ww [%"chk46" + 0] <- #0
    => ret #63 };
  ir_blk{ @"L334":
    => ret #4294967295 };
  ir_blk{ @"L327":
    %"chk47" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v12";
    %"v392" : W = (RawLoad (LdNarrow Sw) 0) %"chk47";
    %"v393" : W = Add %"v392", #1;
    %"chk48" : A = (Renew 0 4 Write 1) %"chk47", %"v12";
    store Ww [%"chk48" + 0] <- %"v393";
    %"v395" = %"v12" +p #32;
    %"chk49" : A = (Renew 0 8 Write 8) %"chk0", %"v395";
    store.ptr [%"chk49" + 0] <- #0;
    %"chk50" : A = (Renew 0 1 Read 1) %"chk1", %"pr.1";
    %"v400" : W = (RawLoad (LdNarrow Sb) 0) %"chk50"
    => br %"v400" ? "L396" : "L397" };
  ir_blk{ @"L396":
    %"v405" = %"pr.7" +p #8;
    %"chk51" : A = (Check 0 4 Read 1) %"v405";
    %"v406" : W = (RawLoad (LdNarrow Sw) 0) %"chk51"
    => br %"v406" ? "L401" : "L402" };
  ir_blk{ @"L401":
    %"v408" = %"v12" +p #16;
    %"v410" = %"pr.1" +p #1;
    %"chk52" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v408";
    store.ptr [%"chk52" + 0] <- %"v410"
    => goto "L398" };
  ir_blk{ @"L402":
    => br %"v14" ? "L411" : "L413" };
  ir_blk{ @"L411":
    %"v415" : P = Copy $"stderr";
    %"chk53" : A = (Check 0 8 Read 8) %"v415";
    %"v416" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v417" : P = Copy $"__GI__libc_intl_domainname";
    %"v418" : P = Copy $"glibc_getopt#str.143";
    call %"v419" : P = $"__GI___dcgettext"(P %"v417", P %"v418", W #5);
    %"chk54" : A = (Check 0 8 Read 8) %"v2";
    %"v422" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"chk55" : A = (HalfCheck Lower 0 8 Read 8) %"chk51", %"pr.7";
    %"v425" : P = (RawLoadPointer 0 load_effects) %"chk55";
    call %"v426" : W = $"__fxprintf_nocancel"(P %"v416", P %"v419", P %"v422", P %"v16", P %"v425")
    => goto "L413" };
  ir_blk{ @"L413":
    %"v428" = %"v12" +p #8;
    %"v430" = %"pr.7" +p #24;
    %"chk56" : A = (HalfCheck Upper 0 4 Read 1) %"chk51", %"v430";
    %"v431" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"chk57" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v428";
    store Ww [%"chk57" + 0] <- %"v431"
    => ret #63 };
  ir_blk{ @"L397":
    %"v436" = %"pr.7" +p #8;
    %"chk58" : A = (Check 0 4 Read 1) %"v436";
    %"v437" : W = (RawLoad (LdNarrow Sw) 0) %"chk58";
    %"v438" : W = (Cmp Eq W) %"v437", #1
    => br %"v438" ? "L432" : "L398" };
  ir_blk{ @"L432":
    %"chk59" : A = (Renew 0 4 Read 1) %"chk47", %"v12";
    %"v443" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"v445" : W = (Cmp Slt W) %"v443", %"v0"
    => br %"v445" ? "L439" : "L440" };
  ir_blk{ @"L439":
    %"v447" = %"v12" +p #16;
    %"v450" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"v451" : W = Add %"v450", #1;
    %"chk61" : A = (Renew 0 4 Write 1) %"chk47", %"v12";
    store Ww [%"chk61" + 0] <- %"v451";
    %"v452" : L = (Ext Sw) %"v450";
    %"v453" : L = Shl %"v452", #3;
    %"v454" = %"v2" +p %"v453";
    %"chk62" : A = (Check 0 8 Read 8) %"v454";
    %"v455" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"chk63" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v447";
    store.ptr [%"chk63" + 0] <- %"v455"
    => goto "L398" };
  ir_blk{ @"L440":
    => br %"v14" ? "L456" : "L458" };
  ir_blk{ @"L456":
    %"v460" : P = Copy $"stderr";
    %"chk64" : A = (Check 0 8 Read 8) %"v460";
    %"v461" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v462" : P = Copy $"__GI__libc_intl_domainname";
    %"v463" : P = Copy $"glibc_getopt#str.144";
    call %"v464" : P = $"__GI___dcgettext"(P %"v462", P %"v463", W #5);
    %"chk65" : A = (Check 0 8 Read 8) %"v2";
    %"v467" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (HalfCheck Lower 0 8 Read 8) %"chk58", %"pr.7";
    %"v470" : P = (RawLoadPointer 0 load_effects) %"chk66";
    call %"v471" : W = $"__fxprintf_nocancel"(P %"v461", P %"v464", P %"v467", P %"v16", P %"v470")
    => goto "L458" };
  ir_blk{ @"L458":
    %"v473" = %"v12" +p #8;
    %"v475" = %"pr.7" +p #24;
    %"chk67" : A = (HalfCheck Upper 0 4 Read 1) %"chk58", %"v475";
    %"v476" : W = (RawLoad (LdNarrow Sw) 0) %"chk67";
    %"chk68" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v473";
    store Ww [%"chk68" + 0] <- %"v476";
    %"chk69" : A = (Check 0 1 Read 1) %"v4";
    %"v482" : W = (RawLoad (LdNarrow Sb) 0) %"chk69";
    %"v483" : W = (Cmp Eq W) %"v482", #58
    => br %"v483" ? "L479" : "L478" };
  ir_blk{ @"L478":
    => goto "L479" };
  ir_blk{ @"L479" [%"v484" : W = phi("L478" => #63, "L458" => #58)]:
    => ret %"v484" };
  ir_blk{ @"L398":
    %"v489" : L = Ptoi %"v8";
    %"v491" : W = (Cmp Ne L) %"v489", %"v90"
    => br %"v491" ? "L485" : "L487" };
  ir_blk{ @"L485":
    %"chk70" : A = (Check 0 4 Write 1) %"v8";
    store Ww [%"chk70" + 0] <- %"pr.12"
    => goto "L487" };
  ir_blk{ @"L487":
    %"v498" = %"pr.7" +p #16;
    %"chk71" : A = (Check 0 8 Read 8) %"v498";
    %"v499" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v500" : L = Ptoi %"v499";
    %"v501" : W = (Cmp Ne L) %"v500", #0
    => br %"v501" ? "L494" : "L496" };
  ir_blk{ @"L494":
    %"v503" = %"pr.7" +p #16;
    %"v504" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v506" = %"pr.7" +p #24;
    %"chk73" : A = (HalfCheck Upper 0 4 Read 1) %"chk71", %"v506";
    %"v507" : W = (RawLoad (LdNarrow Sw) 0) %"chk73";
    %"chk74" : A = (Check 0 4 Write 1) %"v504";
    store Ww [%"chk74" + 0] <- %"v507"
    => ret #0 };
  ir_blk{ @"L496":
    %"v510" = %"pr.7" +p #24;
    %"chk75" : A = (HalfCheck Upper 0 4 Read 1) %"chk71", %"v510";
    %"v511" : W = (RawLoad (LdNarrow Sw) 0) %"chk75"
    => ret %"v511" }])) }.

Definition hello_image_fn___printf : func :=
  ir_fn{ "export" "__printf"(P %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk0" + 0] <- %"va_args";
    %"v4" : P = Copy $"stdout";
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v7" : W = $"__vfprintf_internal"(P %"v5", P %"v0", P %"v2", W #0)
    => ret %"v7"
} }.

Definition hello_image_fn___printf_buffer_as_file_overflow : func :=
  ir_fn{ "export" "__printf_buffer_as_file_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"iw_1.v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v9" = %"v0" +p #224;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v9";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v11" = %"iw_1.v10" +p #8;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v13" : L = Ptoi %"iw_1.v7";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v16" : P = Copy $"glibc_printf_buffer_as_file#str.266";
    %"iw_1.v17" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v18" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v16", P %"iw_1.v17", W #30, P %"iw_1.v18")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v23" = %"v0" +p #40;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v23";
    %"iw_1.v24" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v26" = %"v0" +p #224;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v26";
    %"iw_1.v27" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v28" = %"iw_1.v27" +p #16;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v30" : L = Ptoi %"iw_1.v24";
    %"iw_1.v31" : L = Ptoi %"iw_1.v29";
    %"iw_1.v32" : W = (Cmp Ule L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L21" : "iw_1.L20";
  @"iw_1.L20":
    %"iw_1.v33" : P = Copy $"glibc_printf_buffer_as_file#str.269";
    %"iw_1.v34" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v35" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v33", P %"iw_1.v34", W #31, P %"iw_1.v35")
    => goto "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v40" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v43" = %"v0" +p #224;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v44";
    %"iw_1.v45" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v46" : L = Ptoi %"iw_1.v41";
    %"iw_1.v47" : L = Ptoi %"iw_1.v45";
    %"iw_1.v48" : W = (Cmp Eq L) %"iw_1.v46", %"iw_1.v47"
    => br %"iw_1.v48" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v49" : P = Copy $"glibc_printf_buffer_as_file#str.270";
    %"iw_1.v50" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v51" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v49", P %"iw_1.v50", W #32, P %"iw_1.v51")
    => goto "iw_1.L38";
  @"iw_1.L38":
    %"iw_1.v56" = %"v0" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v56";
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v59" = %"v0" +p #224;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v59";
    %"iw_1.v60" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v61" = %"iw_1.v60" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v61";
    %"iw_1.v62" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v63" : L = Ptoi %"iw_1.v57";
    %"iw_1.v64" : L = Ptoi %"iw_1.v62";
    %"iw_1.v65" : W = (Cmp Eq L) %"iw_1.v63", %"iw_1.v64"
    => br %"iw_1.v65" ? "iw_1.L54" : "iw_1.L53";
  @"iw_1.L53":
    %"iw_1.v66" : P = Copy $"glibc_printf_buffer_as_file#str.271";
    %"iw_1.v67" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v68" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v66", P %"iw_1.v67", W #33, P %"iw_1.v68")
    => goto "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v70" = %"v0" +p #224;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v70";
    %"iw_1.v71" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v72" = %"iw_1.v71" +p #8;
    %"iw_1.v74" = %"v0" +p #40;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Write 8) %"iw_1.v72";
    store.ptr [%"chk14" + 0] <- %"iw_1.v75";
    %"v12" : W = (Cmp Ne W) %"v2", #4294967295
    => br %"v12" ? "L7" : "L9";
  @"L7":
    %"v14" = %"v0" +p #224;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk1", %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v17" : W = (Ext Sb) %"v2";
    %"iw_2.v8" = %"v15" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"iw_2.v8";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v11" = %"v15" +p #16;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_2.v13" : L = Ptoi %"iw_2.v9";
    %"iw_2.v14" : L = Ptoi %"iw_2.v12";
    %"iw_2.v15" : W = (Cmp Ne L) %"iw_2.v13", %"iw_2.v14"
    => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
  @"iw_2.L4":
    %"iw_2.v17" = %"v15" +p #8;
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v19" = %"iw_2.v18" +p #1;
    %"chk19" : A = (Renew 0 8 Write 8) %"chk16", %"iw_2.v17";
    store.ptr [%"chk19" + 0] <- %"iw_2.v19";
    %"chk20" : A = (Check 0 1 Write 1) %"iw_2.v18";
    store Wb [%"chk20" + 0] <- %"v17"
    => goto "L9";
  @"iw_2.L5":
    call void $"__printf_buffer_putc_1"(P %"v15", W %"v17")
    => goto "L9";
  @"L9":
    %"v22" = %"v0" +p #224;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk1", %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_3.v3" = %"v23" +p #32;
    %"chk22" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v26" : W = (Cmp Ne W) %"iw_3.v4", #0
    => br %"v26" ? "L27" : "L28";
  @"L27":
    %"v30" = %"v0" +p #224;
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v32" = %"v31" +p #8;
    %"chk24" : A = (Check 0 8 Read 8) %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v37" = %"v36" +p #16;
    %"chk26" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v39" : L = Ptoi %"v33";
    %"v40" : L = Ptoi %"v38";
    %"v41" : W = (Cmp Eq L) %"v39", %"v40"
    => goto "L28";
  @"L28" [%"v43" : W = phi("L9" => #0, "L27" => %"v41")]:
    => br %"v43" ? "L18" : "iw_4.start";
  @"L18":
    %"v45" = %"v0" +p #224;
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"v47" : W = $"__printf_buffer_flush"(P %"v46")
    => goto "iw_4.start";
  @"iw_4.start":
    %"iw_4.v3" = %"v0" +p #32;
    %"iw_4.v5" = %"v0" +p #224;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v5";
    %"iw_4.v6" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"chk29" : A = (Check 0 8 Read 8) %"iw_4.v6";
    %"iw_4.v7" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (Renew 0 8 Write 8) %"chk6", %"iw_4.v3";
    store.ptr [%"chk30" + 0] <- %"iw_4.v7";
    %"iw_4.v9" = %"v0" +p #40;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v5";
    %"iw_4.v12" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_4.v13" = %"iw_4.v12" +p #8;
    %"chk32" : A = (Check 0 8 Read 8) %"iw_4.v13";
    %"iw_4.v14" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Renew 0 8 Write 8) %"chk0", %"iw_4.v9";
    store.ptr [%"chk33" + 0] <- %"iw_4.v14";
    %"iw_4.v16" = %"v0" +p #48;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v5";
    %"iw_4.v19" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_4.v20" = %"iw_4.v19" +p #16;
    %"chk35" : A = (Check 0 8 Read 8) %"iw_4.v20";
    %"iw_4.v21" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Write 8) %"chk9", %"iw_4.v16";
    store.ptr [%"chk36" + 0] <- %"iw_4.v21";
    %"v54" = %"v0" +p #224;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk1", %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_5.v3" = %"v55" +p #32;
    %"chk38" : A = (Check 0 4 Read 1) %"iw_5.v3";
    %"iw_5.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk38";
    %"v58" : W = (Cmp Ne W) %"iw_5.v4", #0
    => br %"v58" ? "L50" : "L51";
  @"L50":
    %"v60" : W = (Ext Ub) %"v2"
    => ret %"v60";
  @"L51":
    => ret #4294967295
} }.

Definition hello_image_fn___printf_buffer_as_file_xsputn : func :=
  ir_fn{ "export" "__printf_buffer_as_file_xsputn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"iw_1.v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v9" = %"v0" +p #224;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v9";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v11" = %"iw_1.v10" +p #8;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v13" : L = Ptoi %"iw_1.v7";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v16" : P = Copy $"glibc_printf_buffer_as_file#str.266";
    %"iw_1.v17" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v18" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v16", P %"iw_1.v17", W #30, P %"iw_1.v18")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v23" = %"v0" +p #40;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v23";
    %"iw_1.v24" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v26" = %"v0" +p #224;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v26";
    %"iw_1.v27" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v28" = %"iw_1.v27" +p #16;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v30" : L = Ptoi %"iw_1.v24";
    %"iw_1.v31" : L = Ptoi %"iw_1.v29";
    %"iw_1.v32" : W = (Cmp Ule L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L21" : "iw_1.L20";
  @"iw_1.L20":
    %"iw_1.v33" : P = Copy $"glibc_printf_buffer_as_file#str.269";
    %"iw_1.v34" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v35" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v33", P %"iw_1.v34", W #31, P %"iw_1.v35")
    => goto "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v40" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v43" = %"v0" +p #224;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v44";
    %"iw_1.v45" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v46" : L = Ptoi %"iw_1.v41";
    %"iw_1.v47" : L = Ptoi %"iw_1.v45";
    %"iw_1.v48" : W = (Cmp Eq L) %"iw_1.v46", %"iw_1.v47"
    => br %"iw_1.v48" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v49" : P = Copy $"glibc_printf_buffer_as_file#str.270";
    %"iw_1.v50" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v51" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v49", P %"iw_1.v50", W #32, P %"iw_1.v51")
    => goto "iw_1.L38";
  @"iw_1.L38":
    %"iw_1.v56" = %"v0" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v56";
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v59" = %"v0" +p #224;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v59";
    %"iw_1.v60" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v61" = %"iw_1.v60" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v61";
    %"iw_1.v62" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v63" : L = Ptoi %"iw_1.v57";
    %"iw_1.v64" : L = Ptoi %"iw_1.v62";
    %"iw_1.v65" : W = (Cmp Eq L) %"iw_1.v63", %"iw_1.v64"
    => br %"iw_1.v65" ? "iw_1.L54" : "iw_1.L53";
  @"iw_1.L53":
    %"iw_1.v66" : P = Copy $"glibc_printf_buffer_as_file#str.271";
    %"iw_1.v67" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v68" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v66", P %"iw_1.v67", W #33, P %"iw_1.v68")
    => goto "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v70" = %"v0" +p #224;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v70";
    %"iw_1.v71" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v72" = %"iw_1.v71" +p #8;
    %"iw_1.v74" = %"v0" +p #40;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Write 8) %"iw_1.v72";
    store.ptr [%"chk14" + 0] <- %"iw_1.v75";
    %"v10" = %"v0" +p #224;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk1", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call void $"__printf_buffer_write"(P %"v11", P %"v2", L %"v4");
    %"iw_2.v3" = %"v0" +p #32;
    %"iw_2.v5" = %"v0" +p #224;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v5";
    %"iw_2.v6" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 8 Read 8) %"iw_2.v6";
    %"iw_2.v7" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Renew 0 8 Write 8) %"chk6", %"iw_2.v3";
    store.ptr [%"chk18" + 0] <- %"iw_2.v7";
    %"iw_2.v9" = %"v0" +p #40;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v5";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"iw_2.v13" = %"iw_2.v12" +p #8;
    %"chk20" : A = (Check 0 8 Read 8) %"iw_2.v13";
    %"iw_2.v14" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk0", %"iw_2.v9";
    store.ptr [%"chk21" + 0] <- %"iw_2.v14";
    %"iw_2.v16" = %"v0" +p #48;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v5";
    %"iw_2.v19" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_2.v20" = %"iw_2.v19" +p #16;
    %"chk23" : A = (Check 0 8 Read 8) %"iw_2.v20";
    %"iw_2.v21" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Renew 0 8 Write 8) %"chk9", %"iw_2.v16";
    store.ptr [%"chk24" + 0] <- %"iw_2.v21";
    %"v19" = %"v0" +p #224;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk1", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_3.v3" = %"v20" +p #32;
    %"chk26" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v23" : W = (Cmp Ne W) %"iw_3.v4", #0
    => br %"v23" ? "L15" : "L16";
  @"L15":
    => ret %"v4";
  @"L16":
    => ret #0
} }.

Definition hello_image_fn___printf_buffer_as_file_init : func :=
  ir_fn{ "export" "__printf_buffer_as_file_init"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v5" = %"v0" +p #136;
    %"chk0" : A = (Check 0 8 Write 8) %"v5";
    store.ptr [%"chk0" + 0] <- #0;
    call void $"_IO_no_init"(P %"v0", W #32768, W #4294967295, P #0, P #0);
    %"v9" = %"v0" +p #216;
    %"v10" : P = Copy $"__io_vtables";
    %"v11" = %"v10" +p #2016;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v9";
    store.ptr [%"chk1" + 0] <- %"v11";
    %"v13" = %"v0" +p #224;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v13";
    store.ptr [%"chk2" + 0] <- %"v2";
    %"iw_1.v3" = %"v0" +p #32;
    %"iw_1.v5" = %"v0" +p #224;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v5";
    %"iw_1.v6" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Check 0 8 Read 8) %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"iw_1.v3";
    store.ptr [%"chk5" + 0] <- %"iw_1.v7";
    %"iw_1.v9" = %"v0" +p #40;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v5";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v13" = %"iw_1.v12" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"iw_1.v13";
    %"iw_1.v14" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"iw_1.v9";
    store.ptr [%"chk8" + 0] <- %"iw_1.v14";
    %"iw_1.v16" = %"v0" +p #48;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v5";
    %"iw_1.v19" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v20" = %"iw_1.v19" +p #16;
    %"chk10" : A = (Check 0 8 Read 8) %"iw_1.v20";
    %"iw_1.v21" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"iw_1.v16";
    store.ptr [%"chk11" + 0] <- %"iw_1.v21";
    %"v17" = %"v0" +p #24;
    %"v19" = %"v0" +p #32;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk5", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v17";
    store.ptr [%"chk13" + 0] <- %"v20";
    %"v22" = %"v0" +p #8;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk5", %"v19";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v22";
    store.ptr [%"chk15" + 0] <- %"v25";
    %"v27" = %"v0" +p #16;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk5", %"v19";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v27";
    store.ptr [%"chk17" + 0] <- %"v30"
    => ret void
} }.

Definition hello_image_fn___printf_buffer_as_file_terminate : func :=
  ir_fn{ "export" "__printf_buffer_as_file_terminate"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #32
    => br %"v7" ? "L2" : "iw_1.start";
  @"L2":
    => ret #0;
  @"iw_1.start":
    %"iw_1.v6" = %"v0" +p #40;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v9" = %"v0" +p #224;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v9";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v11" = %"iw_1.v10" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v13" : L = Ptoi %"iw_1.v7";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v16" : P = Copy $"glibc_printf_buffer_as_file#str.266";
    %"iw_1.v17" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v18" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v16", P %"iw_1.v17", W #30, P %"iw_1.v18")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v23" = %"v0" +p #40;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v23";
    %"iw_1.v24" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v26" = %"v0" +p #224;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v26";
    %"iw_1.v27" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v28" = %"iw_1.v27" +p #16;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v30" : L = Ptoi %"iw_1.v24";
    %"iw_1.v31" : L = Ptoi %"iw_1.v29";
    %"iw_1.v32" : W = (Cmp Ule L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L21" : "iw_1.L20";
  @"iw_1.L20":
    %"iw_1.v33" : P = Copy $"glibc_printf_buffer_as_file#str.269";
    %"iw_1.v34" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v35" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v33", P %"iw_1.v34", W #31, P %"iw_1.v35")
    => goto "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v40" = %"v0" +p #32;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v43" = %"v0" +p #224;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"iw_1.v44";
    %"iw_1.v45" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v46" : L = Ptoi %"iw_1.v41";
    %"iw_1.v47" : L = Ptoi %"iw_1.v45";
    %"iw_1.v48" : W = (Cmp Eq L) %"iw_1.v46", %"iw_1.v47"
    => br %"iw_1.v48" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v49" : P = Copy $"glibc_printf_buffer_as_file#str.270";
    %"iw_1.v50" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v51" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v49", P %"iw_1.v50", W #32, P %"iw_1.v51")
    => goto "iw_1.L38";
  @"iw_1.L38":
    %"iw_1.v56" = %"v0" +p #48;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v56";
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v59" = %"v0" +p #224;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v59";
    %"iw_1.v60" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v61" = %"iw_1.v60" +p #16;
    %"chk12" : A = (Check 0 8 Read 8) %"iw_1.v61";
    %"iw_1.v62" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v63" : L = Ptoi %"iw_1.v57";
    %"iw_1.v64" : L = Ptoi %"iw_1.v62";
    %"iw_1.v65" : W = (Cmp Eq L) %"iw_1.v63", %"iw_1.v64"
    => br %"iw_1.v65" ? "iw_1.L54" : "iw_1.L53";
  @"iw_1.L53":
    %"iw_1.v66" : P = Copy $"glibc_printf_buffer_as_file#str.271";
    %"iw_1.v67" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v68" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v66", P %"iw_1.v67", W #33, P %"iw_1.v68")
    => goto "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v70" = %"v0" +p #224;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v70";
    %"iw_1.v71" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v72" = %"iw_1.v71" +p #8;
    %"iw_1.v74" = %"v0" +p #40;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"iw_1.v72";
    store.ptr [%"chk15" + 0] <- %"iw_1.v75"
    => ret #1
} }.

Definition hello_image_fn___printf_buffer_done : func :=
  ir_fn{ "export" "__printf_buffer_done"(P %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v12" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v16" : L = Ptoi %"v13";
    %"v17" : L = Ptoi %"v15";
    %"v18" : L = Sub %"v16", %"v17";
    %"v24" = %"v0" +p #24;
    %"v25" : L = (RawLoad LdL (-8)) %"chk0";
    %"v27" : L = Add %"v25", %"v18";
    %"v28" : W = (Cmp Ult L) %"v27", %"v25";
    %"v29" : L = (Ext Uw) %"v28";
    %"v32" : L = (Ext Sw) %"v27";
    %"v33" : L = Sar %"v32", #63;
    %"v34" : W = (Cmp Ne L) %"v27", %"v32";
    %"v35" : W = (Cmp Ne L) %"v29", %"v33";
    %"v36" : W = Or %"v34", %"v35"
    => br %"v36" ? "L20" : "L21";
  @"L20":
    %"v37" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v37";
    store Ww [%"chk4" + 0] <- #75
    => ret #4294967295;
  @"L21":
    %"v40" : W = Copy %"v27"
    => ret %"v40"
} }.
