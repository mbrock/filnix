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

Definition hello_image_fn___GI___gconv_create_spec : func :=
  ir_fn{ "export" "__GI___gconv_create_spec"(P %"v0", P %"v2", P %"v4") -> (RClass P) blocks ((app [ir_blk{ @"start":
    %"v7" : P = (Alloc 8) #16;
    call %"v10" : P = $"__GI___strdup"(P %"v2");
    call %"v12" : P = $"__GI___strdup"(P %"v4");
    %"chk0" : A = (Check 0 8 Write 8) %"v7";
    store.ptr [%"chk0" + 0] <- %"v12";
    %"v17" : L = Ptoi %"v10";
    %"v18" : L = Ptoi #0;
    %"v19" : W = (Cmp Eq L) %"v17", %"v18"
    => br %"v19" ? "L21" : "L20" };
  ir_blk{ @"L20":
    %"chk1" : A = (Renew 0 8 Read 8) %"chk0", %"v7";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v23" : L = Ptoi %"v22";
    %"v25" : W = (Cmp Eq L) %"v23", %"v18"
    => goto "L21" };
  ir_blk{ @"L21" [%"v27" : W = phi("start" => #1, "L20" => %"v25")]:
    => br %"v27" ? "L28" : "iw_1.L9" };
  ir_blk{ @"iw_1.L9":
    call %"iw_1.v14" : L = $"__GI_strlen"(P %"v10")
    => goto "iw_1.L15" };
  ir_blk{ @"iw_1.L15" [%"iw_1.pr.1" : L = phi("iw_1.L16" => %"iw_1.v60", "iw_1.L9" => %"iw_1.v14")]:
    %"iw_1.v19" : W = (Cmp Ugt L) %"iw_1.pr.1", #0
    => br %"iw_1.v19" ? "iw_1.iw_1.start" : "iw_1.L21" };
  ir_blk{ @"iw_1.iw_1.start":
    %"iw_1.iw_1.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v0";
    %"iw_1.v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v27" : L = Sub %"iw_1.pr.1", #1;
    %"iw_1.v28" = %"v10" +p %"iw_1.v27";
    %"chk3" : A = (Check 0 1 Read 1) %"iw_1.v28";
    %"iw_1.v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"iw_1.v30" : L = (Ext Sw) %"iw_1.v29";
    %"iw_1.v31" : L = Shl %"iw_1.v30", #1;
    %"iw_1.v32" = %"iw_1.v23" +p %"iw_1.v31";
    %"chk4" : A = (Check 0 2 Read 1) %"iw_1.v32";
    %"iw_1.v33" : W = (RawLoad (LdNarrow Uh) 0) %"chk4";
    %"iw_1.v34" : W = And %"iw_1.v33", #8192
    => br %"iw_1.v34" ? "iw_1.L36" : "iw_1.L35" };
  ir_blk{ @"iw_1.L35":
    %"iw_1.v42" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"iw_1.v43" : W = (Cmp Eq W) %"iw_1.v42", #44
    => goto "iw_1.L36" };
  ir_blk{ @"iw_1.L36" [%"iw_1.v45" : W = phi("iw_1.iw_1.start" => #1, "iw_1.L35" => %"iw_1.v43")]:
    => br %"iw_1.v45" ? "iw_1.L21" : "iw_1.L46" };
  ir_blk{ @"iw_1.L46":
    %"iw_1.v53" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"iw_1.v54" : W = (Cmp Eq W) %"iw_1.v53", #47
    => goto "iw_1.L21" };
  ir_blk{ @"iw_1.L21" [%"iw_1.v58" : W = phi("iw_1.L15" => #0, "iw_1.L36" => #1, "iw_1.L46" => %"iw_1.v54")]:
    => br %"iw_1.v58" ? "iw_1.L16" : "iw_1.L17" };
  ir_blk{ @"iw_1.L16":
    %"iw_1.v60" : L = Sub %"iw_1.pr.1", #1
    => goto poll "iw_1.L15" };
  ir_blk{ @"iw_1.L17":
    %"iw_1.v64" = %"v10" +p %"iw_1.pr.1";
    %"chk7" : A = (Check 0 1 Write 1) %"iw_1.v64";
    store Wb [%"chk7" + 0] <- #0;
    %"iw_1.v69" : W = (Cmp Eq L) %"iw_1.pr.1", #0
    => br %"iw_1.v69" ? "iw_1.join" : "iw_1.iw_2.L5" };
  ir_blk{ @"iw_1.iw_2.L5" [%"iw_1.iw_2.pr.6" : W = phi("iw_1.iw_2.L21" => %"iw_1.iw_2.v35", "iw_1.L17" => #0); %"iw_1.iw_2.pr.5" : P = phi("iw_1.iw_2.L21" => %"iw_1.iw_2.pr.4", "iw_1.L17" => #0); %"iw_1.iw_2.pr.3" : W = phi("iw_1.iw_2.L21" => %"iw_1.iw_2.pr.1", "iw_1.L17" => #0)]:
    %"iw_1.iw_2.v11" : L = (Ext Sw) %"iw_1.iw_2.pr.6";
    %"iw_1.iw_2.v12" = %"v10" +p %"iw_1.iw_2.v11";
    %"chk8" : A = (Check 0 1 Read 1) %"iw_1.iw_2.v12";
    %"iw_1.iw_2.v13" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"iw_1.iw_2.v14" : W = (Cmp Ne W) %"iw_1.iw_2.v13", #0
    => br %"iw_1.iw_2.v14" ? "iw_1.iw_2.L6" : "iw_1.iw_2.L8" };
  ir_blk{ @"iw_1.iw_2.L6":
    %"iw_1.iw_2.v19" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"iw_1.iw_2.v30" : W = (Cmp Eq W) %"iw_1.iw_2.v19", #47
    => br %"iw_1.iw_2.v30" ? "iw_1.iw_2.L22" : "iw_1.iw_2.L31" };
  ir_blk{ @"iw_1.iw_2.L22":
    %"iw_1.iw_2.v24" : W = Add %"iw_1.iw_2.pr.3", #1
    => goto "iw_1.iw_2.L21" };
  ir_blk{ @"iw_1.iw_2.L31":
    %"iw_1.iw_2.v32" : W = (Cmp Eq W) %"iw_1.iw_2.v19", #44
    => br %"iw_1.iw_2.v32" ? "iw_1.iw_2.L21" : "iw_1.iw_2.L33" };
  ir_blk{ @"iw_1.iw_2.L33":
    => goto "iw_1.iw_2.L21" };
  ir_blk{ @"iw_1.iw_2.L21" [%"iw_1.iw_2.pr.4" : P = phi("iw_1.iw_2.L33" => %"iw_1.iw_2.pr.5", "iw_1.iw_2.L22" => %"iw_1.iw_2.v12", "iw_1.iw_2.L31" => %"iw_1.iw_2.v12"); %"iw_1.iw_2.pr.1" : W = phi("iw_1.iw_2.L33" => %"iw_1.iw_2.pr.3", "iw_1.iw_2.L22" => %"iw_1.iw_2.v24", "iw_1.iw_2.L31" => %"iw_1.iw_2.pr.3")]:
    %"iw_1.iw_2.v35" : W = Add %"iw_1.iw_2.pr.6", #1
    => goto poll "iw_1.iw_2.L5" };
  ir_blk{ @"iw_1.iw_2.L8":
    %"iw_1.iw_2.v40" : W = (Cmp Sge W) %"iw_1.iw_2.pr.3", #2
    => br %"iw_1.iw_2.v40" ? "iw_1.iw_2.join" : "iw_1.iw_2.L38" };
  ir_blk{ @"iw_1.iw_2.L38":
    => goto "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.join" [%"iw_1.v74" : P = phi("iw_1.iw_2.L38" => #0, "iw_1.iw_2.L8" => %"iw_1.iw_2.pr.5")]:
    %"iw_1.v79" : L = Ptoi %"iw_1.v74";
    %"iw_1.v81" : W = (Cmp Eq L) %"iw_1.v79", %"v18"
    => br %"iw_1.v81" ? "iw_1.join" : "iw_1.L76" };
  ir_blk{ @"iw_1.L76":
    %"iw_1.v87" : P = Copy $"glibc_gconv_charset#str.244";
    %"iw_1.v88" : P = Copy $"_nl_C_locobj";
    call %"iw_1.v89" : W = $"__GI___strcasecmp_l"(P %"iw_1.v74", P %"iw_1.v87", P %"iw_1.v88");
    %"iw_1.v90" : W = (Cmp Eq W) %"iw_1.v89", #0
    => br %"iw_1.v90" ? "iw_1.L92" : "iw_1.L91" };
  ir_blk{ @"iw_1.L91":
    %"iw_1.v94" : P = Copy $"glibc_gconv_charset#str.245";
    %"iw_1.v95" : P = Copy $"_nl_C_locobj";
    call %"iw_1.v96" : W = $"__GI___strcasecmp_l"(P %"iw_1.v74", P %"iw_1.v94", P %"iw_1.v95");
    %"iw_1.v97" : W = (Cmp Eq W) %"iw_1.v96", #0
    => goto "iw_1.L92" };
  ir_blk{ @"iw_1.L92" [%"iw_1.v99" : W = phi("iw_1.L76" => #1, "iw_1.L91" => %"iw_1.v97")]:
    => br %"iw_1.v99" ? "iw_1.L83" : "iw_1.L85" };
  ir_blk{ @"iw_1.L83":
    => goto "iw_1.L85" };
  ir_blk{ @"iw_1.L85":
    %"iw_1.v107" : P = Copy $"glibc_gconv_charset#str.246";
    %"iw_1.v108" : P = Copy $"_nl_C_locobj";
    call %"iw_1.v109" : W = $"__GI___strcasecmp_l"(P %"iw_1.v74", P %"iw_1.v107", P %"iw_1.v108");
    %"iw_1.v110" : W = (Cmp Eq W) %"iw_1.v109", #0
    => br %"iw_1.v110" ? "iw_1.L112" : "iw_1.L111" };
  ir_blk{ @"iw_1.L111":
    %"iw_1.v114" : P = Copy $"glibc_gconv_charset#str.247";
    %"iw_1.v115" : P = Copy $"_nl_C_locobj";
    call %"iw_1.v116" : W = $"__GI___strcasecmp_l"(P %"iw_1.v74", P %"iw_1.v114", P %"iw_1.v115");
    %"iw_1.v117" : W = (Cmp Eq W) %"iw_1.v116", #0
    => goto "iw_1.L112" };
  ir_blk{ @"iw_1.L112" [%"iw_1.v119" : W = phi("iw_1.L85" => #1, "iw_1.L111" => %"iw_1.v117")]:
    => br %"iw_1.v119" ? "iw_1.L103" : "iw_1.L105" };
  ir_blk{ @"iw_1.L103":
    => goto "iw_1.L105" };
  ir_blk{ @"iw_1.L105":
    %"chk10" : A = (Check 0 1 Write 1) %"iw_1.v74";
    store Wb [%"chk10" + 0] <- #0
    => goto poll "iw_1.L9" };
  ir_blk{ @"iw_1.join":
    call void $"glibc_gconv_charset#gconv_parse_code"(P %"v7");
    %"v31" = %"v0" +p #16;
    %"v32" = %"v7" +p #8;
    %"chk11" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v32";
    %"v33" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"chk12" : A = (Check 0 1 Write 1) %"v31";
    store Wb [%"chk12" + 0] <- %"v33";
    %"v35" = %"v0" +p #17;
    %"v36" = %"v7" +p #9;
    %"chk13" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v36";
    %"v37" : W = (RawLoad (LdNarrow Ub) 0) %"chk13";
    %"chk14" : A = (HalfCheck Upper 0 1 Write 1) %"chk12", %"v35";
    store Wb [%"chk14" + 0] <- %"v37";
    call %"v40" : L = $"__GI_strlen"(P %"v2");
    %"v41" : L = Add %"v40", #3;
    call %"v42" : P = $"malloc"(L %"v41");
    %"chk15" : A = (HalfCheck Lower 0 8 Write 8) %"chk12", %"v0";
    store.ptr [%"chk15" + 0] <- %"v42";
    %"chk16" : A = (Renew 0 8 Read 8) %"chk15", %"v0";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v48" : L = Ptoi %"v47";
    %"v50" : W = (Cmp Eq L) %"v48", %"v18"
    => br %"v50" ? "L28" : "L45" };
  ir_blk{ @"L45":
    %"v53" = %"v0" +p #8;
    call %"v55" : L = $"__GI_strlen"(P %"v4");
    %"v56" : L = Add %"v55", #3;
    call %"v57" : P = $"malloc"(L %"v56");
    %"chk17" : A = (HalfCheck Lower 0 8 Write 8) %"chk12", %"v53";
    store.ptr [%"chk17" + 0] <- %"v57";
    %"chk18" : A = (Renew 0 8 Read 8) %"chk17", %"v53";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v64" : L = Ptoi %"v63";
    %"v66" : W = (Cmp Eq L) %"v64", %"v18"
    => br %"v66" ? "L58" : "L60" };
  ir_blk{ @"L58":
    %"chk19" : A = (Renew 0 8 Read 8) %"chk15", %"v0";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk19";
    call void $"free"(P %"v68");
    %"chk20" : A = (Renew 0 8 Write 8) %"chk15", %"v0";
    store.ptr [%"chk20" + 0] <- #0
    => goto "L28" };
  ir_blk{ @"L60":
    %"chk21" : A = (Renew 0 8 Read 8) %"chk15", %"v0";
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk21"
    => goto "iw_2.L5" };
  ir_blk{ @"iw_2.L5" [%"iw_2.pr.9" : W = phi("iw_2.L13" => %"iw_2.pr.8", "L60" => #0); %"iw_2.pr.5" : P = phi("iw_2.L13" => %"iw_2.v125", "L60" => %"v10"); %"iw_2.pr.4" : P = phi("iw_2.L13" => %"iw_2.pr.3", "L60" => %"v72")]:
    %"chk22" : A = (Check 0 1 Read 1) %"iw_2.pr.5";
    %"iw_2.v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk22";
    %"iw_2.v10" : W = (Cmp Ne W) %"iw_2.v9", #0
    => br %"iw_2.v10" ? "iw_2.L6" : "iw_2.L126" };
  ir_blk{ @"iw_2.L6":
    %"iw_2.v14" : P = Copy $"_nl_C_locobj";
    %"iw_2.v15" = %"iw_2.v14" +p #104;
    %"chk23" : A = (Check 0 8 Read 8) %"iw_2.v15";
    %"iw_2.v16" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Renew 0 1 Read 1) %"chk22", %"iw_2.pr.5";
    %"iw_2.v18" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v19" : L = (Ext Sw) %"iw_2.v18";
    %"iw_2.v20" : L = Shl %"iw_2.v19", #1;
    %"iw_2.v21" = %"iw_2.v16" +p %"iw_2.v20";
    %"chk25" : A = (Check 0 2 Read 1) %"iw_2.v21";
    %"iw_2.v22" : W = (RawLoad (LdNarrow Uh) 0) %"chk25";
    %"iw_2.v23" : W = And %"iw_2.v22", #8
    => br %"iw_2.v23" ? "iw_2.L25" : "iw_2.L24" };
  ir_blk{ @"iw_2.L24":
    %"iw_2.v27" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v28" : W = (Cmp Eq W) %"iw_2.v27", #95
    => goto "iw_2.L25" }] [ir_blk{ @"iw_2.L25" [%"iw_2.v30" : W = phi("iw_2.L6" => #1, "iw_2.L24" => %"iw_2.v28")]:
    => br %"iw_2.v30" ? "iw_2.L32" : "iw_2.L31" };
  ir_blk{ @"iw_2.L31":
    %"iw_2.v34" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v35" : W = (Cmp Eq W) %"iw_2.v34", #45
    => goto "iw_2.L32" };
  ir_blk{ @"iw_2.L32" [%"iw_2.v37" : W = phi("iw_2.L25" => #1, "iw_2.L31" => %"iw_2.v35")]:
    => br %"iw_2.v37" ? "iw_2.L39" : "iw_2.L38" };
  ir_blk{ @"iw_2.L38":
    %"iw_2.v41" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v42" : W = (Cmp Eq W) %"iw_2.v41", #46
    => goto "iw_2.L39" };
  ir_blk{ @"iw_2.L39" [%"iw_2.v44" : W = phi("iw_2.L32" => #1, "iw_2.L38" => %"iw_2.v42")]:
    => br %"iw_2.v44" ? "iw_2.L46" : "iw_2.L45" };
  ir_blk{ @"iw_2.L45":
    %"iw_2.v48" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v49" : W = (Cmp Eq W) %"iw_2.v48", #44
    => goto "iw_2.L46" };
  ir_blk{ @"iw_2.L46" [%"iw_2.v51" : W = phi("iw_2.L39" => #1, "iw_2.L45" => %"iw_2.v49")]:
    => br %"iw_2.v51" ? "iw_2.L53" : "iw_2.L52" };
  ir_blk{ @"iw_2.L52":
    %"iw_2.v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v56" : W = (Cmp Eq W) %"iw_2.v55", #58
    => goto "iw_2.L53" };
  ir_blk{ @"iw_2.L53" [%"iw_2.v58" : W = phi("iw_2.L46" => #1, "iw_2.L52" => %"iw_2.v56")]:
    => br %"iw_2.v58" ? "iw_2.L11" : "iw_2.L12" };
  ir_blk{ @"iw_2.L11":
    %"iw_2.v60" = %"iw_2.pr.4" +p #1;
    %"iw_2.v98" : P = Copy $"_nl_C_locobj";
    %"iw_2.v99" = %"iw_2.v98" +p #120;
    %"chk31" : A = (Check 0 8 Read 8) %"iw_2.v99";
    %"iw_2.v100" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Renew 0 1 Read 1) %"chk22", %"iw_2.pr.5";
    %"iw_2.v102" : W = (RawLoad (LdNarrow Sb) 0) %"chk32";
    %"iw_2.v103" : L = (Ext Sw) %"iw_2.v102";
    %"iw_2.v104" : L = Shl %"iw_2.v103", #2;
    %"iw_2.v105" = %"iw_2.v100" +p %"iw_2.v104";
    %"chk33" : A = (Check 0 4 Read 1) %"iw_2.v105";
    %"iw_2.v106" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"iw_2.v108" : W = (Ext Sb) %"iw_2.v106";
    %"chk34" : A = (Check 0 1 Write 1) %"iw_2.pr.4";
    store Wb [%"chk34" + 0] <- %"iw_2.v108"
    => goto "iw_2.L13" };
  ir_blk{ @"iw_2.L12":
    %"iw_2.v113" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v114" : W = (Cmp Eq W) %"iw_2.v113", #47
    => br %"iw_2.v114" ? "iw_2.L109" : "iw_2.L13" };
  ir_blk{ @"iw_2.L109":
    %"iw_2.v119" : W = Add %"iw_2.pr.9", #1;
    %"iw_2.v120" : W = (Cmp Eq W) %"iw_2.v119", #3
    => br %"iw_2.v120" ? "iw_2.L126" : "iw_2.L117" };
  ir_blk{ @"iw_2.L117":
    %"iw_2.v123" = %"iw_2.pr.4" +p #1;
    %"chk36" : A = (Check 0 1 Write 1) %"iw_2.pr.4";
    store Wb [%"chk36" + 0] <- #47
    => goto "iw_2.L13" };
  ir_blk{ @"iw_2.L13" [%"iw_2.pr.8" : W = phi("iw_2.L11" => %"iw_2.pr.9", "iw_2.L117" => %"iw_2.v119", "iw_2.L12" => %"iw_2.pr.9"); %"iw_2.pr.3" : P = phi("iw_2.L11" => %"iw_2.v60", "iw_2.L117" => %"iw_2.v123", "iw_2.L12" => %"iw_2.pr.4")]:
    %"iw_2.v125" = %"iw_2.pr.5" +p #1
    => goto poll "iw_2.L5" };
  ir_blk{ @"iw_2.L126" [%"iw_2.pr.7" : W = phi("iw_2.L127" => %"iw_2.v130", "iw_2.L5" => %"iw_2.pr.9", "iw_2.L109" => %"iw_2.v119"); %"iw_2.pr.2" : P = phi("iw_2.L127" => %"iw_2.v133", "iw_2.L5" => %"iw_2.pr.4", "iw_2.L109" => %"iw_2.pr.4")]:
    %"iw_2.v130" : W = Add %"iw_2.pr.7", #1;
    %"iw_2.v131" : W = (Cmp Slt W) %"iw_2.pr.7", #2
    => br %"iw_2.v131" ? "iw_2.L127" : "iw_2.L128" };
  ir_blk{ @"iw_2.L127":
    %"iw_2.v133" = %"iw_2.pr.2" +p #1;
    %"chk37" : A = (Check 0 1 Write 1) %"iw_2.pr.2";
    store Wb [%"chk37" + 0] <- #47
    => goto poll "iw_2.L126" };
  ir_blk{ @"iw_2.L128":
    %"chk38" : A = (Check 0 1 Write 1) %"iw_2.pr.2";
    store Wb [%"chk38" + 0] <- #0;
    %"v75" = %"v0" +p #8;
    %"chk39" : A = (Renew 0 8 Read 8) %"chk17", %"v75";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"chk40" : A = (Renew 0 8 Read 8) %"chk0", %"v7";
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk40"
    => goto "iw_3.L5" };
  ir_blk{ @"iw_3.L5" [%"iw_3.pr.9" : W = phi("iw_3.L13" => %"iw_3.pr.8", "iw_2.L128" => #0); %"iw_3.pr.5" : P = phi("iw_3.L13" => %"iw_3.v125", "iw_2.L128" => %"v77"); %"iw_3.pr.4" : P = phi("iw_3.L13" => %"iw_3.pr.3", "iw_2.L128" => %"v76")]:
    %"chk41" : A = (Check 0 1 Read 1) %"iw_3.pr.5";
    %"iw_3.v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk41";
    %"iw_3.v10" : W = (Cmp Ne W) %"iw_3.v9", #0
    => br %"iw_3.v10" ? "iw_3.L6" : "iw_3.L126" };
  ir_blk{ @"iw_3.L6":
    %"iw_3.v14" : P = Copy $"_nl_C_locobj";
    %"iw_3.v15" = %"iw_3.v14" +p #104;
    %"chk42" : A = (Check 0 8 Read 8) %"iw_3.v15";
    %"iw_3.v16" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"chk43" : A = (Renew 0 1 Read 1) %"chk41", %"iw_3.pr.5";
    %"iw_3.v18" : W = (RawLoad (LdNarrow Sb) 0) %"chk43";
    %"iw_3.v19" : L = (Ext Sw) %"iw_3.v18";
    %"iw_3.v20" : L = Shl %"iw_3.v19", #1;
    %"iw_3.v21" = %"iw_3.v16" +p %"iw_3.v20";
    %"chk44" : A = (Check 0 2 Read 1) %"iw_3.v21";
    %"iw_3.v22" : W = (RawLoad (LdNarrow Uh) 0) %"chk44";
    %"iw_3.v23" : W = And %"iw_3.v22", #8
    => br %"iw_3.v23" ? "iw_3.L25" : "iw_3.L24" };
  ir_blk{ @"iw_3.L24":
    %"iw_3.v27" : W = (RawLoad (LdNarrow Sb) 0) %"chk43";
    %"iw_3.v28" : W = (Cmp Eq W) %"iw_3.v27", #95
    => goto "iw_3.L25" };
  ir_blk{ @"iw_3.L25" [%"iw_3.v30" : W = phi("iw_3.L6" => #1, "iw_3.L24" => %"iw_3.v28")]:
    => br %"iw_3.v30" ? "iw_3.L32" : "iw_3.L31" };
  ir_blk{ @"iw_3.L31":
    %"iw_3.v34" : W = (RawLoad (LdNarrow Sb) 0) %"chk43";
    %"iw_3.v35" : W = (Cmp Eq W) %"iw_3.v34", #45
    => goto "iw_3.L32" };
  ir_blk{ @"iw_3.L32" [%"iw_3.v37" : W = phi("iw_3.L25" => #1, "iw_3.L31" => %"iw_3.v35")]:
    => br %"iw_3.v37" ? "iw_3.L39" : "iw_3.L38" };
  ir_blk{ @"iw_3.L38":
    %"iw_3.v41" : W = (RawLoad (LdNarrow Sb) 0) %"chk43";
    %"iw_3.v42" : W = (Cmp Eq W) %"iw_3.v41", #46
    => goto "iw_3.L39" };
  ir_blk{ @"iw_3.L39" [%"iw_3.v44" : W = phi("iw_3.L32" => #1, "iw_3.L38" => %"iw_3.v42")]:
    => br %"iw_3.v44" ? "iw_3.L46" : "iw_3.L45" };
  ir_blk{ @"iw_3.L45":
    %"iw_3.v48" : W = (RawLoad (LdNarrow Sb) 0) %"chk43";
    %"iw_3.v49" : W = (Cmp Eq W) %"iw_3.v48", #44
    => goto "iw_3.L46" };
  ir_blk{ @"iw_3.L46" [%"iw_3.v51" : W = phi("iw_3.L39" => #1, "iw_3.L45" => %"iw_3.v49")]:
    => br %"iw_3.v51" ? "iw_3.L53" : "iw_3.L52" };
  ir_blk{ @"iw_3.L52":
    %"iw_3.v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk43";
    %"iw_3.v56" : W = (Cmp Eq W) %"iw_3.v55", #58
    => goto "iw_3.L53" };
  ir_blk{ @"iw_3.L53" [%"iw_3.v58" : W = phi("iw_3.L46" => #1, "iw_3.L52" => %"iw_3.v56")]:
    => br %"iw_3.v58" ? "iw_3.L11" : "iw_3.L12" };
  ir_blk{ @"iw_3.L11":
    %"iw_3.v60" = %"iw_3.pr.4" +p #1;
    %"iw_3.v98" : P = Copy $"_nl_C_locobj";
    %"iw_3.v99" = %"iw_3.v98" +p #120;
    %"chk50" : A = (Check 0 8 Read 8) %"iw_3.v99";
    %"iw_3.v100" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"chk51" : A = (Renew 0 1 Read 1) %"chk41", %"iw_3.pr.5";
    %"iw_3.v102" : W = (RawLoad (LdNarrow Sb) 0) %"chk51";
    %"iw_3.v103" : L = (Ext Sw) %"iw_3.v102";
    %"iw_3.v104" : L = Shl %"iw_3.v103", #2;
    %"iw_3.v105" = %"iw_3.v100" +p %"iw_3.v104";
    %"chk52" : A = (Check 0 4 Read 1) %"iw_3.v105";
    %"iw_3.v106" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    %"iw_3.v108" : W = (Ext Sb) %"iw_3.v106";
    %"chk53" : A = (Check 0 1 Write 1) %"iw_3.pr.4";
    store Wb [%"chk53" + 0] <- %"iw_3.v108"
    => goto "iw_3.L13" };
  ir_blk{ @"iw_3.L12":
    %"iw_3.v113" : W = (RawLoad (LdNarrow Sb) 0) %"chk43";
    %"iw_3.v114" : W = (Cmp Eq W) %"iw_3.v113", #47
    => br %"iw_3.v114" ? "iw_3.L109" : "iw_3.L13" };
  ir_blk{ @"iw_3.L109":
    %"iw_3.v119" : W = Add %"iw_3.pr.9", #1;
    %"iw_3.v120" : W = (Cmp Eq W) %"iw_3.v119", #3
    => br %"iw_3.v120" ? "iw_3.L126" : "iw_3.L117" };
  ir_blk{ @"iw_3.L117":
    %"iw_3.v123" = %"iw_3.pr.4" +p #1;
    %"chk55" : A = (Check 0 1 Write 1) %"iw_3.pr.4";
    store Wb [%"chk55" + 0] <- #47
    => goto "iw_3.L13" };
  ir_blk{ @"iw_3.L13" [%"iw_3.pr.8" : W = phi("iw_3.L11" => %"iw_3.pr.9", "iw_3.L117" => %"iw_3.v119", "iw_3.L12" => %"iw_3.pr.9"); %"iw_3.pr.3" : P = phi("iw_3.L11" => %"iw_3.v60", "iw_3.L117" => %"iw_3.v123", "iw_3.L12" => %"iw_3.pr.4")]:
    %"iw_3.v125" = %"iw_3.pr.5" +p #1
    => goto poll "iw_3.L5" };
  ir_blk{ @"iw_3.L126" [%"iw_3.pr.7" : W = phi("iw_3.L127" => %"iw_3.v130", "iw_3.L5" => %"iw_3.pr.9", "iw_3.L109" => %"iw_3.v119"); %"iw_3.pr.2" : P = phi("iw_3.L127" => %"iw_3.v133", "iw_3.L5" => %"iw_3.pr.4", "iw_3.L109" => %"iw_3.pr.4")]:
    %"iw_3.v130" : W = Add %"iw_3.pr.7", #1;
    %"iw_3.v131" : W = (Cmp Slt W) %"iw_3.pr.7", #2
    => br %"iw_3.v131" ? "iw_3.L127" : "iw_3.L128" };
  ir_blk{ @"iw_3.L127":
    %"iw_3.v133" = %"iw_3.pr.2" +p #1;
    %"chk56" : A = (Check 0 1 Write 1) %"iw_3.pr.2";
    store Wb [%"chk56" + 0] <- #47
    => goto poll "iw_3.L126" };
  ir_blk{ @"iw_3.L128":
    %"chk57" : A = (Check 0 1 Write 1) %"iw_3.pr.2";
    store Wb [%"chk57" + 0] <- #0
    => goto "L28" };
  ir_blk{ @"L28" [%"pr.1" : P = phi("L58" => #0, "L21" => #0, "iw_1.join" => #0, "iw_3.L128" => %"v0")]:
    call void $"free"(P %"v10");
    %"chk58" : A = (Renew 0 8 Read 8) %"chk0", %"v7";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk58";
    call void $"free"(P %"v80")
    => ret %"pr.1" }])) }.

Definition hello_image_fn___GI___gconv_destroy_spec : func :=
  ir_fn{ "export" "__GI___gconv_destroy_spec"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v3" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"free"(P %"v3");
    %"v5" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v5";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call void $"free"(P %"v6")
    => ret void
} }.

Definition hello_image_fn_glibc_gconv_conf'23__gconv_get_path : func :=
  ir_fn{ "local" "glibc_gconv_conf#__gconv_get_path"() -> RVoid {
  @"start":
    %"v13" : P = (Alloc 8) #8;
    %"v1" : P = Copy $"__gconv_path_elem";
    %"chk0" : A = (Check 0 8 Read 8) %"v1";
    %"v2" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v7" : L = Ptoi %"v2";
    %"v8" : L = Ptoi #0;
    %"v9" : W = (Cmp Eq L) %"v7", %"v8"
    => br %"v9" ? "L5" : "L4";
  @"L4":
    %"v10" : P = Copy $"glibc_gconv_conf#str.274";
    %"v11" : P = Copy $"glibc_gconv_conf#str.275";
    %"v12" : P = Copy $"glibc_gconv_conf#str.276";
    call void $"__libc_assert_fail"(P %"v10", P %"v11", W #362, P %"v12")
    => goto "L5";
  @"L5":
    %"v24" : P = Copy $"__gconv_path_envvar";
    %"chk1" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v26" : L = Ptoi %"v25";
    %"v28" : W = (Cmp Eq L) %"v26", %"v8"
    => br %"v28" ? "L21" : "L22";
  @"L21":
    %"v30" : P = Copy $"glibc_gconv_conf#default_gconv_path";
    call %"v33" : L = $"__GI_strlen"(P %"v30");
    %"v34" : L = Add %"v33", #1;
    %"v37" : P = (Alloc 16) %"v34";
    call %"v41" : P = $"__GI_memcpy"(P %"v37", P %"v30", L %"v34");
    %"chk2" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk2" + 0] <- %"v41"
    => goto "L23";
  @"L22":
    %"v43" : P = Copy $"__gconv_path_envvar";
    %"chk3" : A = (Check 0 8 Read 8) %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call %"v45" : L = $"__GI_strlen"(P %"v44");
    %"v47" : L = Add %"v45", #1;
    %"v48" : L = Add %"v47", #73;
    %"v50" : P = (Alloc 16) %"v48";
    %"chk4" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk4" + 0] <- %"v50";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk4", %"v13";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v52" : P = Copy $"__gconv_path_envvar";
    %"chk6" : A = (Check 0 8 Read 8) %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v55" : P = $"__GI_mempcpy"(P %"v51", P %"v53", L %"v45");
    %"v56" : P = Copy $"glibc_gconv_conf#str.277";
    call %"v57" : P = $"__GI_mempcpy"(P %"v55", P %"v56", L #1);
    %"v58" : P = Copy $"glibc_gconv_conf#default_gconv_path";
    call %"v59" : P = $"__GI_mempcpy"(P %"v57", P %"v58", L #73);
    call %"v60" : P = $"__GI___getcwd"(P #0, L #0);
    %"v65" : L = Ptoi %"v60";
    %"v67" : W = (Cmp Eq L) %"v65", %"v8"
    => br %"v67" ? "L23" : "L62";
  @"L62":
    call %"v71" : L = $"__GI_strlen"(P %"v60")
    => goto "L23";
  @"L23" [%"pr.8" : L = phi("L21" => #0, "L62" => %"v71", "L22" => #0); %"pr.7" : P = phi("L21" => #0, "L62" => %"v60", "L22" => %"v60"); %"pr.1" : L = phi("L21" => #73, "L62" => %"v48", "L22" => %"v48")]:
    %"v76" : P = Copy $"glibc_gconv_conf#default_gconv_path";
    %"chk7" : A = (Check 0 1 Read 1) %"v76";
    %"v78" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"v79" : W = (Cmp Eq W) %"v78", #47
    => br %"v79" ? "L75" : "L74";
  @"L74":
    %"v80" : P = Copy $"glibc_gconv_conf#str.278";
    %"v81" : P = Copy $"glibc_gconv_conf#str.275";
    %"v82" : P = Copy $"glibc_gconv_conf#str.276";
    call void $"__libc_assert_fail"(P %"v80", P %"v81", W #397, P %"v82")
    => goto "L75";
  @"L75":
    %"chk8" : A = (Check 0 8 Read 8) %"v13";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk8";
    call %"v84" : P = $"__GI_strchr"(P %"v83", W #58)
    => goto "L85";
  @"L85" [%"pr.5" : W = phi("L75" => #1, "L94" => %"pr.6"); %"pr.4" : P = phi("L75" => %"v84", "L94" => %"v106"); %"pr.3" : P = phi("L75" => #0, "L94" => %"pr.4")]:
    %"v89" : L = Ptoi %"pr.4";
    %"v91" : W = (Cmp Ne L) %"v89", %"v8"
    => br %"v91" ? "L86" : "L87";
  @"L86":
    %"v97" = %"pr.3" +p #1;
    %"v99" : L = Ptoi %"v97";
    %"v100" : W = (Cmp Ne L) %"v89", %"v99"
    => br %"v100" ? "L92" : "L94";
  @"L92":
    %"v102" : W = Add %"pr.5", #1
    => goto "L94";
  @"L94" [%"pr.6" : W = phi("L92" => %"v102", "L86" => %"pr.5")]:
    %"v105" = %"pr.4" +p #1;
    call %"v106" : P = $"__GI_strchr"(P %"v105", W #58)
    => goto poll "L85";
  @"L87":
    %"v108" : W = Add %"pr.5", #1;
    %"v109" : L = (Ext Sw) %"v108";
    %"v110" : L = Shl %"v109", #4;
    %"v112" : L = Add %"v110", %"pr.1";
    %"v114" : L = (Ext Sw) %"pr.5";
    %"v115" : L = Add %"v112", %"v114";
    %"v117" : W = Sub %"pr.5", #1;
    %"v119" : L = Add %"pr.8", #1;
    %"v120" : L = (Ext Sw) %"v117";
    %"v121" : L = Mul %"v120", %"v119";
    %"v122" : L = Add %"v115", %"v121";
    call %"v123" : P = $"malloc"(L %"v122");
    %"v128" : L = Ptoi %"v123";
    %"v130" : W = (Cmp Ne L) %"v128", %"v8"
    => br %"v130" ? "L124" : "L126";
  @"L124":
    %"v137" = %"v123" +p %"v110";
    %"v139" : P = Copy $"__gconv_max_path_elem_len";
    %"chk9" : A = (Check 0 8 Write 1) %"v139";
    store Wl [%"chk9" + 0] <- #0;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk8", %"v13";
    %"v140" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v141" : P = Copy $"glibc_gconv_conf#str.277";
    call %"v142" : P = $"__GI___strtok_r"(P %"v140", P %"v141", P %"v13");
    %"v147" : L = Ptoi %"v142";
    %"v149" : W = (Cmp Ne L) %"v147", %"v8"
    => br %"v149" ? "L153" : "L144";
  @"L144":
    %"v150" : P = Copy $"glibc_gconv_conf#str.279";
    %"v151" : P = Copy $"glibc_gconv_conf#str.275";
    %"v152" : P = Copy $"glibc_gconv_conf#str.276";
    call void $"__libc_assert_fail"(P %"v150", P %"v151", W #424, P %"v152")
    => goto "L153";
  @"L153" [%"pr.12" : W = phi("L217" => %"v239", "L144" => #0, "L124" => #0); %"pr.9" : P = phi("L217" => %"v237", "L144" => %"v137", "L124" => %"v137"); %"pr.2" : P = phi("L217" => %"v241", "L144" => %"v142", "L124" => %"v142")]:
    %"v158" : L = (Ext Sw) %"pr.12";
    %"v159" : L = Shl %"v158", #4;
    %"v160" = %"v123" +p %"v159";
    %"chk11" : A = (Check 0 8 Write 8) %"v160";
    store.ptr [%"chk11" + 0] <- %"pr.9";
    %"chk12" : A = (Check 0 1 Read 1) %"pr.2";
    %"v167" : W = (RawLoad (LdNarrow Sb) 0) %"chk12";
    %"v168" : W = (Cmp Ne W) %"v167", #47
    => br %"v168" ? "L162" : "L164";
  @"L162":
    %"v173" : L = Ptoi %"pr.7";
    %"v175" : W = (Cmp Ne L) %"v173", %"v8"
    => br %"v175" ? "L171" : "L170";
  @"L170":
    %"v176" : P = Copy $"glibc_gconv_conf#str.280";
    %"v177" : P = Copy $"glibc_gconv_conf#str.275";
    %"v178" : P = Copy $"glibc_gconv_conf#str.276";
    call void $"__libc_assert_fail"(P %"v176", P %"v177", W #430, P %"v178")
    => goto "L171";
  @"L171":
    call %"v182" : P = $"__GI_mempcpy"(P %"pr.9", P %"pr.7", L %"pr.8");
    %"v184" = %"v182" +p #1;
    %"chk13" : A = (Check 0 1 Write 1) %"v182";
    store Wb [%"chk13" + 0] <- #47
    => goto "L164";
  @"L164" [%"pr.10" : P = phi("L171" => %"v184", "L153" => %"pr.9")]:
    call %"v187" : P = $"__GI_stpcpy"(P %"pr.10", P %"pr.2");
    %"v194" = %"v187" +p #18446744073709551615;
    %"chk14" : A = (Check 0 1 Read 1) %"v194";
    %"v195" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v196" : W = (Cmp Ne W) %"v195", #47
    => br %"v196" ? "L188" : "L190";
  @"L188":
    %"v198" = %"v187" +p #1;
    %"chk15" : A = (HalfCheck Upper 0 1 Write 1) %"chk14", %"v187";
    store Wb [%"chk15" + 0] <- #47
    => goto "L190";
  @"L190" [%"pr.11" : P = phi("L188" => %"v198", "L164" => %"v187")]:
    %"v204" = %"v160" +p #8;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk11", %"v160";
    %"v211" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v212" : L = Ptoi %"pr.11";
    %"v213" : L = Ptoi %"v211";
    %"v214" : L = Sub %"v212", %"v213";
    %"chk17" : A = (HalfCheck Upper 0 8 Write 1) %"chk11", %"v204";
    store Wl [%"chk17" + 0] <- %"v214";
    %"v224" : L = (RawLoad LdL 0) %"chk17";
    %"v225" : P = Copy $"__gconv_max_path_elem_len";
    %"chk19" : A = (Check 0 8 Read 1) %"v225";
    %"v226" : L = (RawLoad LdL 0) %"chk19";
    %"v227" : W = (Cmp Ugt L) %"v224", %"v226"
    => br %"v227" ? "L215" : "L217";
  @"L215":
    %"v228" : P = Copy $"__gconv_max_path_elem_len";
    %"v234" = %"v160" +p #8;
    %"chk20" : A = (Renew 0 8 Read 1) %"chk17", %"v234";
    %"v235" : L = (RawLoad LdL 0) %"chk20";
    %"chk21" : A = (Check 0 8 Write 1) %"v228";
    store Wl [%"chk21" + 0] <- %"v235"
    => goto "L217";
  @"L217":
    %"v237" = %"pr.11" +p #1;
    %"chk22" : A = (Check 0 1 Write 1) %"pr.11";
    store Wb [%"chk22" + 0] <- #0;
    %"v239" : W = Add %"pr.12", #1;
    %"v240" : P = Copy $"glibc_gconv_conf#str.277";
    call %"v241" : P = $"__GI___strtok_r"(P #0, P %"v240", P %"v13");
    %"v242" : L = Ptoi %"v241";
    %"v244" : W = (Cmp Ne L) %"v242", %"v8"
    => br %"v244" ? poll "L153" : "L155";
  @"L155":
    %"v247" : L = (Ext Sw) %"v239";
    %"v248" : L = Shl %"v247", #4;
    %"v249" = %"v123" +p %"v248";
    %"chk23" : A = (Check 0 8 Write 8) %"v249";
    store.ptr [%"chk23" + 0] <- #0;
    %"v255" = %"v249" +p #8;
    %"chk24" : A = (HalfCheck Upper 0 8 Write 1) %"chk23", %"v255";
    store Wl [%"chk24" + 0] <- #0
    => goto "L126";
  @"L126":
    %"v256" : P = Copy $"__gconv_path_elem";
    %"v259" : W = (Cmp Ne L) %"v128", #0
    => br %"v259" ? "L262" : "L261";
  @"L261":
    %"v263" : P = Copy $"glibc_gconv_conf#empty_path_elem"
    => goto "L262";
  @"L262" [%"v264" : P = phi("L261" => %"v263", "L126" => %"v123")]:
    %"chk25" : A = (Check 0 8 Write 8) %"v256";
    store.ptr [%"chk25" + 0] <- %"v264";
    call void $"free"(P %"pr.7")
    => ret void
} }.

Definition hello_image_fn_glibc_gconv_conf'23__gconv_read_conf : func :=
  ir_fn{ "local" "glibc_gconv_conf#__gconv_read_conf"() -> RVoid {
  @"start":
    %"v49" : P = (Alloc 8) #16;
    %"v1" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Read 1) %"v1";
    %"v2" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"v7" : W = $"__gconv_load_cache"();
    %"v8" : W = (Cmp Eq W) %"v7", #0
    => br %"v8" ? "L4" : "L6";
  @"L4":
    %"v9" : P = Copy $"__libc_errno";
    %"chk1" : A = (Check 0 4 Write 1) %"v9";
    store Ww [%"chk1" + 0] <- %"v2"
    => ret void;
  @"L6":
    call void $"glibc_gconv_conf#__gconv_get_path"()
    => goto "L12";
  @"L12" [%"pr.1" : L = phi("L14" => %"v41", "L6" => #0)]:
    %"v16" : P = Copy $"__gconv_path_elem";
    %"chk2" : A = (Check 0 8 Read 8) %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v19" : L = Shl %"pr.1", #4;
    %"v20" = %"v17" +p %"v19";
    %"chk3" : A = (Check 0 8 Read 8) %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v22" : L = Ptoi %"v21";
    %"v23" : L = Ptoi #0;
    %"v24" : W = (Cmp Ne L) %"v22", %"v23"
    => br %"v24" ? "L13" : "L42";
  @"L13":
    %"v25" : P = Copy $"__gconv_path_elem";
    %"chk4" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v29" = %"v26" +p %"v19";
    %"chk5" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v31" : P = Copy $"__gconv_path_elem";
    %"chk6" : A = (Check 0 8 Read 8) %"v31";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v35" = %"v32" +p %"v19";
    %"v36" = %"v35" +p #8;
    %"chk7" : A = (Check 0 8 Read 1) %"v36";
    %"v37" : L = (RawLoad LdL 0) %"chk7";
    (Flight (a "iw_1.v0") Copy [(FAddress (Const 0))] (LowerOf (Const 0)));
    %"iw_1.v136" : P = (Alloc 8) #8;
    %"iw_1.v137" : P = (Alloc 8) #144;
    %"iw_1.v8" : L = Add %"v37", #14;
    %"iw_1.v9" : L = Add %"iw_1.v8", #2;
    %"iw_1.v16" : L = Ptoi %"iw_1.v0";
    %"iw_1.v18" : W = (Cmp Ne L) %"iw_1.v16", %"v23"
    => br %"iw_1.v18" ? "iw_1.L12" : "iw_1.L14";
  @"iw_1.L12":
    call %"iw_1.v20" : L = $"__GI_strlen"(P %"iw_1.v0")
    => goto "iw_1.L14";
  @"iw_1.L14" [%"iw_1.v21" : L = phi("iw_1.L12" => %"iw_1.v20", "L13" => #0)]:
    %"iw_1.v22" : L = Add %"iw_1.v9", %"iw_1.v21";
    call %"iw_1.v23" : P = $"malloc"(L %"iw_1.v22");
    %"iw_1.v32" : L = Ptoi %"iw_1.v23";
    %"iw_1.v34" : W = (Cmp Eq L) %"iw_1.v32", %"v23"
    => br %"iw_1.v34" ? "L14" : "iw_1.L30";
  @"iw_1.L30":
    => br %"iw_1.v18" ? "iw_1.L37" : "iw_1.L39";
  @"iw_1.L37":
    call %"iw_1.v46" : P = $"__GI_stpcpy"(P %"iw_1.v23", P %"iw_1.v0")
    => goto "iw_1.L39";
  @"iw_1.L39" [%"iw_1.pr.1" : P = phi("iw_1.L37" => %"iw_1.v46", "iw_1.L30" => %"iw_1.v23")]:
    call %"iw_1.v50" : P = $"__GI_mempcpy"(P %"iw_1.pr.1", P %"v30", L %"v37");
    %"iw_1.v51" : P = Copy $"glibc_gconv_conf#gconv_conf_filename";
    call %"iw_1.v52" : P = $"__GI_mempcpy"(P %"iw_1.v50", P %"iw_1.v51", L #14);
    call %"iw_1.v56" : W = $"glibc_gconv_conf#read_conf_file"(P %"iw_1.v23", P %"v30", L %"v37");
    (Flight (a "iw_1.v59") Sub [(FAddress (t "iw_1.v52")); (FValue (Const 1))] (LowerOf (t "iw_1.v52")));
    %"chk8" : A = (Check 0 1 Write 1) %"iw_1.v59";
    store Wb [%"chk8" + 0] <- #46;
    %"iw_1.v63" = %"iw_1.v59" +p #1;
    %"chk9" : A = (HalfCheck Upper 0 1 Write 1) %"chk8", %"iw_1.v63";
    store Wb [%"chk9" + 0] <- #100;
    %"iw_1.v65" = %"iw_1.v59" +p #2;
    %"chk10" : A = (HalfCheck Upper 0 1 Write 1) %"chk8", %"iw_1.v65";
    store Wb [%"chk10" + 0] <- #0;
    call %"iw_1.v68" : P = $"__opendir"(P %"iw_1.v23");
    %"iw_1.v73" : L = Ptoi %"iw_1.v68";
    %"iw_1.v75" : W = (Cmp Ne L) %"iw_1.v73", %"v23"
    => br %"iw_1.v75" ? "iw_1.L77" : "iw_1.L71";
  @"iw_1.L77":
    call %"iw_1.v81" : P = $"__GI___readdir64"(P %"iw_1.v68");
    %"iw_1.v82" : L = Ptoi %"iw_1.v81";
    %"iw_1.v84" : W = (Cmp Ne L) %"iw_1.v82", %"v23"
    => br %"iw_1.v84" ? "iw_1.L78" : "iw_1.L79";
  @"iw_1.L78":
    %"iw_1.v89" = %"iw_1.v81" +p #18;
    %"chk11" : A = (Check 0 1 Read 1) %"iw_1.v89";
    %"iw_1.v90" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"iw_1.v91" : W = (Cmp Ne W) %"iw_1.v90", #8
    => br %"iw_1.v91" ? "iw_1.L92" : "iw_1.L93";
  @"iw_1.L92":
    %"iw_1.v95" = %"iw_1.v81" +p #18;
    %"iw_1.v96" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"iw_1.v97" : W = (Cmp Ne W) %"iw_1.v96", #0
    => goto "iw_1.L93";
  @"iw_1.L93" [%"iw_1.v99" : W = phi("iw_1.L78" => #0, "iw_1.L92" => %"iw_1.v97")]:
    => br %"iw_1.v99" ? "iw_1.L100" : "iw_1.L101";
  @"iw_1.L100":
    %"iw_1.v103" = %"iw_1.v81" +p #18;
    %"iw_1.v104" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"iw_1.v105" : W = (Cmp Ne W) %"iw_1.v104", #10
    => goto "iw_1.L101";
  @"iw_1.L101" [%"iw_1.v107" : W = phi("iw_1.L93" => #0, "iw_1.L100" => %"iw_1.v105")]:
    => br %"iw_1.v107" ? poll "iw_1.L77" : "iw_1.L87";
  @"iw_1.L87":
    %"iw_1.v111" = %"iw_1.v81" +p #19;
    call %"iw_1.v112" : L = $"__GI_strlen"(P %"iw_1.v111");
    %"iw_1.v114" : P = Copy $"glibc_gconv_conf#str.281";
    call %"iw_1.v120" : L = $"__GI_strlen"(P %"iw_1.v114");
    %"iw_1.v121" : W = (Cmp Ugt L) %"iw_1.v112", %"iw_1.v120"
    => br %"iw_1.v121" ? "iw_1.L122" : "iw_1.L123";
  @"iw_1.L122":
    %"iw_1.v125" = %"iw_1.v81" +p #19;
    %"iw_1.v127" = %"iw_1.v125" +p %"iw_1.v112";
    call %"iw_1.v129" : L = $"__GI_strlen"(P %"iw_1.v114");
    (Flight (a "iw_1.v130") Sub [(FAddress (t "iw_1.v127")); (FValue (t "iw_1.v129"))] (LowerOf (t "iw_1.v127")));
    call %"iw_1.v132" : W = $"__GI_strcmp"(P %"iw_1.v130", P %"iw_1.v114");
    %"iw_1.v133" : W = (Cmp Eq W) %"iw_1.v132", #0
    => goto "iw_1.L123";
  @"iw_1.L123" [%"iw_1.v135" : W = phi("iw_1.L87" => #0, "iw_1.L122" => %"iw_1.v133")]:
    => br %"iw_1.v135" ? "iw_1.L115" : poll "iw_1.L77";
  @"iw_1.L115":
    %"iw_1.v141" : P = Copy $"glibc_gconv_conf#str.282";
    %"iw_1.v144" = %"iw_1.v81" +p #19;
    call %"iw_1.v145" : W = $"__GI___asprintf"(P %"iw_1.v136", P %"iw_1.v141", P %"iw_1.v23", P %"iw_1.v144");
    %"iw_1.v146" : W = (Cmp Slt W) %"iw_1.v145", #0
    => br %"iw_1.v146" ? poll "iw_1.L77" : "iw_1.L140";
  @"iw_1.L140":
    %"iw_1.v152" = %"iw_1.v81" +p #18;
    %"chk14" : A = (Renew 0 1 Read 1) %"chk11", %"iw_1.v152";
    %"iw_1.v153" : W = (RawLoad (LdNarrow Ub) 0) %"chk14";
    %"iw_1.v154" : W = (Cmp Ne W) %"iw_1.v153", #0
    => br %"iw_1.v154" ? "iw_1.L156" : "iw_1.L155";
  @"iw_1.L155":
    %"chk15" : A = (Check 0 8 Read 8) %"iw_1.v136";
    %"iw_1.v157" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call %"iw_1.v158" : W = $"__GI___stat64"(P %"iw_1.v157", P %"iw_1.v137");
    %"iw_1.v160" : W = (Cmp Ne W) %"iw_1.v158", #4294967295
    => br %"iw_1.v160" ? "iw_1.L161" : "iw_1.L156";
  @"iw_1.L161":
    %"iw_1.v163" = %"iw_1.v137" +p #24;
    %"chk16" : A = (Check 0 4 Read 1) %"iw_1.v163";
    %"iw_1.v164" : W = (RawLoad (LdNarrow Uw) 0) %"chk16";
    %"iw_1.v165" : W = And %"iw_1.v164", #61440;
    %"iw_1.v166" : W = (Cmp Eq W) %"iw_1.v165", #32768
    => goto "iw_1.L156";
  @"iw_1.L156" [%"iw_1.v170" : W = phi("iw_1.L140" => #1, "iw_1.L155" => #0, "iw_1.L161" => %"iw_1.v166")]:
    => br %"iw_1.v170" ? "iw_1.L148" : "iw_1.L150";
  @"iw_1.L148":
    %"chk17" : A = (Check 0 8 Read 8) %"iw_1.v136";
    %"iw_1.v172" : P = (RawLoadPointer 0 load_effects) %"chk17";
    call %"iw_1.v175" : W = $"glibc_gconv_conf#read_conf_file"(P %"iw_1.v172", P %"v30", L %"v37")
    => goto "iw_1.L150";
  @"iw_1.L150":
    %"chk18" : A = (Check 0 8 Read 8) %"iw_1.v136";
    %"iw_1.v179" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call void $"free"(P %"iw_1.v179")
    => goto poll "iw_1.L77";
  @"iw_1.L79":
    call %"iw_1.v181" : W = $"__closedir"(P %"iw_1.v68")
    => goto "iw_1.L71";
  @"iw_1.L71":
    call void $"free"(P %"iw_1.v23")
    => goto "L14";
  @"L14":
    %"v41" : L = Add %"pr.1", #1
    => goto poll "L12";
  @"L42" [%"pr.2" : L = phi("L44" => %"v70", "L12" => #0)]:
    %"v48" : W = (Cmp Ult L) %"pr.2", #12
    => br %"v48" ? "L43" : "L45";
  @"L43":
    %"v50" : P = Copy $"glibc_gconv_conf#builtin_modules";
    %"v52" : L = Mul %"pr.2", #56;
    %"v53" = %"v50" +p %"v52";
    %"chk19" : A = (Check 0 8 Read 8) %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk20" + 0] <- %"v54";
    %"v58" : P = Copy $"__gconv_alias_db";
    %"v59" : P = Copy $"__gconv_alias_compare";
    call %"v60" : P = $"__GI___tfind"(P %"v49", P %"v58", P %"v59");
    %"v61" : L = Ptoi %"v60";
    %"v63" : W = (Cmp Ne L) %"v61", %"v23"
    => br %"v63" ? "L44" : "L57";
  @"L57":
    %"v65" : P = Copy $"glibc_gconv_conf#builtin_modules";
    %"v68" = %"v65" +p %"v52";
    %"iw_2.v5" : P = Copy $"__gconv_modules_db"
    => goto "iw_2.L6";
  @"iw_2.L6" [%"iw_2.pr.4" : P = phi("L57" => %"iw_2.v5", "iw_2.L125" => %"iw_2.v131", "iw_2.L126" => %"iw_2.v133")]:
    %"chk21" : A = (Check 0 8 Read 8) %"iw_2.pr.4";
    %"iw_2.v10" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_2.v11" : L = Ptoi %"iw_2.v10";
    %"iw_2.v13" : W = (Cmp Ne L) %"iw_2.v11", %"v23"
    => br %"iw_2.v13" ? "iw_2.L7" : "iw_2.L8";
  @"iw_2.L7":
    %"iw_2.v16" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk23" : A = (Check 0 8 Read 8) %"v68";
    %"iw_2.v19" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Check 0 8 Read 8) %"iw_2.v16";
    %"iw_2.v21" : P = (RawLoadPointer 0 load_effects) %"chk24";
    call %"iw_2.v22" : W = $"__GI_strcmp"(P %"iw_2.v19", P %"iw_2.v21");
    %"iw_2.v27" : W = (Cmp Eq W) %"iw_2.v22", #0
    => br %"iw_2.v27" ? "iw_2.L28" : "iw_2.L24";
  @"iw_2.L28" [%"iw_2.pr.6" : P = phi("iw_2.L7" => %"iw_2.v16", "iw_2.L29" => %"iw_2.v52"); %"iw_2.pr.2" : P = phi("iw_2.L7" => %"iw_2.pr.4", "iw_2.L29" => %"iw_2.v50")]:
    %"chk25" : A = (Renew 0 8 Read 8) %"chk23", %"v68";
    %"iw_2.v32" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : A = (Check 0 8 Read 8) %"iw_2.pr.6";
    %"iw_2.v34" : P = (RawLoadPointer 0 load_effects) %"chk26";
    call %"iw_2.v35" : W = $"__GI_strcmp"(P %"iw_2.v32", P %"iw_2.v34");
    %"iw_2.v36" : W = (Cmp Ne W) %"iw_2.v35", #0
    => br %"iw_2.v36" ? "iw_2.L38" : "iw_2.L37";
  @"iw_2.L37":
    %"iw_2.v40" = %"v68" +p #8;
    %"chk27" : A = (HalfCheck Upper 0 8 Read 8) %"chk23", %"iw_2.v40";
    %"iw_2.v41" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"iw_2.v43" = %"iw_2.pr.6" +p #8;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk26", %"iw_2.v43";
    %"iw_2.v44" : P = (RawLoadPointer 0 load_effects) %"chk28";
    call %"iw_2.v45" : W = $"__GI_strcmp"(P %"iw_2.v41", P %"iw_2.v44");
    %"iw_2.v46" : W = (Cmp Ne W) %"iw_2.v45", #0
    => goto "iw_2.L38";
  @"iw_2.L38" [%"iw_2.v48" : W = phi("iw_2.L28" => #1, "iw_2.L37" => %"iw_2.v46")]:
    => br %"iw_2.v48" ? "iw_2.L29" : "iw_2.L30";
  @"iw_2.L29":
    %"iw_2.v50" = %"iw_2.pr.6" +p #40;
    %"chk29" : A = (HalfCheck Upper 0 8 Read 8) %"chk26", %"iw_2.v50";
    %"iw_2.v52" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_2.v57" : L = Ptoi %"iw_2.v52";
    %"iw_2.v59" : W = (Cmp Eq L) %"iw_2.v57", %"v23"
    => br %"iw_2.v59" ? "iw_2.L30" : poll "iw_2.L28";
  @"iw_2.L30" [%"iw_2.pr.7" : P = phi("iw_2.L38" => %"iw_2.pr.6", "iw_2.L29" => %"iw_2.v52"); %"iw_2.pr.3" : P = phi("iw_2.L38" => %"iw_2.pr.2", "iw_2.L29" => %"iw_2.v50")]:
    %"iw_2.v65" : L = Ptoi %"iw_2.pr.7";
    %"iw_2.v67" : W = (Cmp Ne L) %"iw_2.v65", %"v23"
    => br %"iw_2.v67" ? "iw_2.L61" : "iw_2.L8";
  @"iw_2.L61":
    %"iw_2.v72" = %"v68" +p #16;
    %"chk30" : A = (HalfCheck Upper 0 4 Read 1) %"chk23", %"iw_2.v72";
    %"iw_2.v73" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"iw_2.v75" = %"iw_2.pr.7" +p #16;
    %"chk31" : A = (Check 0 4 Read 1) %"iw_2.v75";
    %"iw_2.v76" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"iw_2.v77" : W = (Cmp Slt W) %"iw_2.v73", %"iw_2.v76"
    => br %"iw_2.v77" ? "iw_2.L79" : "iw_2.L78";
  @"iw_2.L78":
    %"iw_2.v81" = %"v68" +p #16;
    %"iw_2.v82" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"iw_2.v84" = %"iw_2.pr.7" +p #16;
    %"iw_2.v85" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"iw_2.v86" : W = (Cmp Eq W) %"iw_2.v82", %"iw_2.v85"
    => br %"iw_2.v86" ? "iw_2.L87" : "iw_2.L79";
  @"iw_2.L87":
    %"iw_2.v90" = %"v68" +p #20;
    %"chk34" : A = (HalfCheck Upper 0 4 Read 1) %"chk23", %"iw_2.v90";
    %"iw_2.v91" : W = (RawLoad (LdNarrow Sw) 0) %"chk34";
    %"iw_2.v93" = %"iw_2.pr.7" +p #20;
    %"chk35" : A = (HalfCheck Upper 0 4 Read 1) %"chk31", %"iw_2.v93";
    %"iw_2.v94" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"iw_2.v95" : W = (Cmp Slt W) %"iw_2.v91", %"iw_2.v94"
    => goto "iw_2.L79";
  @"iw_2.L79" [%"iw_2.v99" : W = phi("iw_2.L61" => #1, "iw_2.L78" => #0, "iw_2.L87" => %"iw_2.v95")]:
    => br %"iw_2.v99" ? "iw_2.L68" : "L44";
  @"iw_2.L68":
    %"iw_2.v101" = %"v68" +p #32;
    %"iw_2.v103" = %"iw_2.pr.7" +p #32;
    %"chk36" : A = (HalfCheck Upper 0 8 Read 8) %"chk31", %"iw_2.v103";
    %"iw_2.v104" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"chk37" : A = (HalfCheck Upper 0 8 Write 8) %"chk23", %"iw_2.v101";
    store.ptr [%"chk37" + 0] <- %"iw_2.v104";
    %"iw_2.v106" = %"v68" +p #48;
    %"iw_2.v108" = %"iw_2.pr.7" +p #48;
    %"chk38" : A = (HalfCheck Upper 0 8 Read 8) %"chk31", %"iw_2.v108";
    %"iw_2.v109" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (HalfCheck Upper 0 8 Write 8) %"chk23", %"iw_2.v106";
    store.ptr [%"chk39" + 0] <- %"iw_2.v109";
    %"iw_2.v111" = %"v68" +p #40;
    %"iw_2.v113" = %"iw_2.pr.7" +p #40;
    %"chk40" : A = (HalfCheck Upper 0 8 Read 8) %"chk31", %"iw_2.v113";
    %"iw_2.v114" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : A = (HalfCheck Upper 0 8 Write 8) %"chk23", %"iw_2.v111";
    store.ptr [%"chk41" + 0] <- %"iw_2.v114";
    %"chk42" : A = (Check 0 8 Write 8) %"iw_2.pr.3";
    store.ptr [%"chk42" + 0] <- %"v68";
    call void $"free"(P %"iw_2.pr.7")
    => goto "L44";
  @"iw_2.L24":
    %"iw_2.v129" : W = (Cmp Slt W) %"iw_2.v22", #0
    => br %"iw_2.v129" ? "iw_2.L125" : "iw_2.L126";
  @"iw_2.L125":
    %"iw_2.v131" = %"iw_2.v16" +p #32
    => goto poll "iw_2.L6";
  @"iw_2.L126":
    %"iw_2.v133" = %"iw_2.v16" +p #48
    => goto poll "iw_2.L6";
  @"iw_2.L8" [%"iw_2.pr.5" : P = phi("iw_2.L6" => %"iw_2.pr.4", "iw_2.L30" => %"iw_2.pr.3")]:
    %"chk43" : A = (Check 0 8 Write 8) %"iw_2.pr.5";
    store.ptr [%"chk43" + 0] <- %"v68"
    => goto "L44";
  @"L44":
    %"v70" : L = Add %"pr.2", #1
    => goto poll "L42";
  @"L45":
    %"v72" : P = Copy $"glibc_gconv_conf#builtin_aliases"
    => goto "L73";
  @"L73" [%"pr.3" : P = phi("L45" => %"v72", "L73" => %"v84")]:
    call %"v80" : P = $"__GI_strchr"(P %"pr.3", W #0);
    %"v81" = %"v80" +p #1;
    call %"v83" : P = $"__GI_strchr"(P %"v81", W #0);
    %"v84" = %"v83" +p #1;
    call void $"glibc_gconv_conf#add_alias2"(P %"pr.3", P %"v81", P %"v84");
    %"chk44" : A = (Check 0 1 Read 1) %"v84";
    %"v89" : W = (RawLoad (LdNarrow Sb) 0) %"chk44";
    %"v90" : W = (Cmp Ne W) %"v89", #0
    => br %"v90" ? poll "L73" : "L75";
  @"L75":
    %"v91" : P = Copy $"__libc_errno";
    %"chk45" : A = (Check 0 4 Write 1) %"v91";
    store Ww [%"chk45" + 0] <- %"v2"
    => ret void
} }.

Definition hello_image_fn___gconv_load_conf : func :=
  ir_fn{ "export" "__gconv_load_conf"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_gconv_conf#once";
    %"v1" : P = Copy $"glibc_gconv_conf#__gconv_read_conf";
    call %"v2" : W = $"__GI___pthread_once"(P %"v0", P %"v1")
    => ret void
} }.

Definition hello_image_fn___gconv_alias_compare : func :=
  ir_fn{ "export" "__gconv_alias_compare"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v12" : W = $"__GI_strcmp"(P %"v9", P %"v11")
    => ret %"v12"
} }.

Definition hello_image_fn___gconv_release_step : func :=
  ir_fn{ "export" "__gconv_release_step"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v7" : L = Ptoi %"v6";
    %"v8" : L = Ptoi #0;
    %"v9" : W = (Cmp Ne L) %"v7", %"v8"
    => br %"v9" ? "L10" : "L11";
  @"L10":
    %"v13" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v13";
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v15" : W = Sub %"v14", #1;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk1", %"v13";
    store Ww [%"chk2" + 0] <- %"v15";
    %"v16" : W = (Cmp Eq W) %"v15", #0
    => goto "L11";
  @"L11" [%"v18" : W = phi("start" => #0, "L10" => %"v16")]:
    => br %"v18" ? "L2" : "L3";
  @"L2":
    %"v21" = %"v0" +p #64;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v28" : L = Ptoi %"v22";
    %"v30" : W = (Cmp Ne L) %"v28", %"v8"
    => br %"v30" ? "iw_1.join" : "L26";
  @"iw_1.join":
    %"chk4" : F = CheckFunction %"v22";
    rawcall void %"chk4"(P %"v0")
    => goto "L26";
  @"L26":
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call void $"__gconv_release_shlib"(P %"v35");
    %"chk6" : A = (Renew 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk6" + 0] <- #0
    => goto "L4";
  @"L3":
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v42" : L = Ptoi %"v41";
    %"v44" : W = (Cmp Eq L) %"v42", %"v8"
    => br %"v44" ? "L37" : "L4";
  @"L37":
    %"v49" = %"v0" +p #64;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v51" : L = Ptoi %"v50";
    %"v53" : W = (Cmp Eq L) %"v51", %"v8"
    => br %"v53" ? "L4" : "L46";
  @"L46":
    %"v54" : P = Copy $"glibc_gconv_db#str.275";
    %"v55" : P = Copy $"glibc_gconv_db#str.276";
    %"v56" : P = Copy $"glibc_gconv_db#str.277";
    call void $"__libc_assert_fail"(P %"v54", P %"v55", W #221, P %"v56")
    => goto "L4";
  @"L4":
    => ret void
} }.

Definition hello_image_fn___gconv_compare_alias : func :=
  ir_fn{ "export" "__gconv_compare_alias"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 4) #4;
    call void $"__gconv_load_conf"();
    call %"v10" : W = $"__gconv_compare_alias_cache"(P %"v0", P %"v2", P %"v4");
    %"v11" : W = (Cmp Ne W) %"v10", #0
    => br %"v11" ? "iw_1.start" : "L7";
  @"iw_1.start":
    %"iw_1.v2" : P = (Alloc 8) #16;
    %"chk0" : A = (Check 0 8 Write 8) %"iw_1.v2";
    store.ptr [%"chk0" + 0] <- %"v0";
    %"iw_1.v5" : P = Copy $"__gconv_alias_db";
    %"iw_1.v6" : P = Copy $"__gconv_alias_compare";
    call %"iw_1.v7" : P = $"__GI___tfind"(P %"iw_1.v2", P %"iw_1.v5", P %"iw_1.v6");
    %"iw_1.v12" : L = Ptoi %"iw_1.v7";
    %"iw_1.v13" : L = Ptoi #0;
    %"iw_1.v14" : W = (Cmp Ne L) %"iw_1.v12", %"iw_1.v13"
    => br %"iw_1.v14" ? "iw_1.L8" : "iw_1.L10";
  @"iw_1.L8":
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v7";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v17" = %"iw_1.v16" +p #8;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v17";
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk2"
    => goto "iw_1.L10";
  @"iw_1.L10" [%"iw_1.v19" : P = phi("iw_1.L8" => %"iw_1.v18", "iw_1.start" => #0)]:
    %"v14" : L = Ptoi %"iw_1.v19";
    %"v15" : W = (Cmp Ne L) %"v14", #0
    => br %"v15" ? "L18" : "L17";
  @"L17":
    => goto "L18";
  @"L18" [%"v20" : P = phi("L17" => %"v0", "iw_1.L10" => %"iw_1.v19")]:
    %"iw_2.v2" : P = (Alloc 8) #16;
    %"chk3" : A = (Check 0 8 Write 8) %"iw_2.v2";
    store.ptr [%"chk3" + 0] <- %"v2";
    %"iw_2.v5" : P = Copy $"__gconv_alias_db";
    %"iw_2.v6" : P = Copy $"__gconv_alias_compare";
    call %"iw_2.v7" : P = $"__GI___tfind"(P %"iw_2.v2", P %"iw_2.v5", P %"iw_2.v6");
    %"iw_2.v12" : L = Ptoi %"iw_2.v7";
    %"iw_2.v14" : W = (Cmp Ne L) %"iw_2.v12", %"iw_1.v13"
    => br %"iw_2.v14" ? "iw_2.L8" : "iw_2.L10";
  @"iw_2.L8":
    %"chk4" : A = (Check 0 8 Read 8) %"iw_2.v7";
    %"iw_2.v16" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_2.v17" = %"iw_2.v16" +p #8;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_2.v17";
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk5"
    => goto "iw_2.L10";
  @"iw_2.L10" [%"iw_2.v19" : P = phi("iw_2.L8" => %"iw_2.v18", "L18" => #0)]:
    %"v23" : L = Ptoi %"iw_2.v19";
    %"v24" : W = (Cmp Ne L) %"v23", #0
    => br %"v24" ? "L27" : "L26";
  @"L26":
    => goto "L27";
  @"L27" [%"v29" : P = phi("L26" => %"v2", "iw_2.L10" => %"iw_2.v19")]:
    call %"v30" : W = $"__GI_strcmp"(P %"v20", P %"v29");
    %"chk6" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk6" + 0] <- %"v30"
    => goto "L7";
  @"L7":
    %"chk7" : A = (Check 0 4 Read 1) %"v4";
    %"v31" : W = (RawLoad (LdNarrow Sw) 0) %"chk7"
    => ret %"v31"
} }.

Definition hello_image_fn___gconv_find_transform : func :=
  ir_fn{ "export" "__gconv_find_transform"(P %"v0", P %"v2", P %"v4", P %"v6", W %"v8") -> (RClass W) {
  @"start":
    call void $"__gconv_load_conf"();
    %"v14" : P = Copy $"__gconv_lock";
    %"chk0" : A = (Check 0 4 Write 4) %"v14";
    %"v21" : W = (RawCas (CasNarrow Sw) 0) %"chk0", #0, #1;
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => br %"v22" ? "L24" : "L23";
  @"L23":
    => goto "L24";
  @"L24":
    %"v25" : W = (Cmp Ne W) %"v21", #0
    => br %"v25" ? "L28" : "L17";
  @"L28":
    call void $"__GI___lll_lock_wait_private"(P %"v14")
    => goto "L17";
  @"L17":
    call %"v43" : W = $"__gconv_lookup_cache"(P %"v0", P %"v2", P %"v4", P %"v6", W %"v8");
    %"v48" : W = (Cmp Ne W) %"v43", #2
    => br %"v48" ? "L44" : "L46";
  @"L44":
    %"v50" : P = Copy $"__gconv_lock";
    %"chk1" : A = (Check 0 4 Read 1) %"v50";
    %"v54" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => goto "L55";
  @"L55" [%"v57" : W = phi("L44" => %"v54", "L55" => %"v58")]:
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v50";
    %"v58" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"v57", #0;
    %"v59" : W = (Cmp Eq W) %"v58", %"v57"
    => br %"v59" ? "L56" : poll "L55";
  @"L56":
    %"v64" : W = (Cmp Sgt W) %"v57", #1
    => br %"v64" ? "L67" : "L62";
  @"L67":
    call void $"__GI___lll_lock_wake_private"(P %"v50")
    => goto "L62";
  @"L62":
    => ret %"v43";
  @"L46":
    %"v83" : P = Copy $"__gconv_modules_db";
    %"chk3" : A = (Check 0 8 Read 8) %"v83";
    %"v84" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v85" : L = Ptoi %"v84";
    %"v86" : L = Ptoi #0;
    %"v87" : W = (Cmp Eq L) %"v85", %"v86"
    => br %"v87" ? "L80" : "iw_1.start";
  @"L80":
    %"v89" : P = Copy $"__gconv_lock";
    %"chk4" : A = (Check 0 4 Read 1) %"v89";
    %"v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk4"
    => goto "L94";
  @"L94" [%"v96" : W = phi("L80" => %"v93", "L94" => %"v97")]:
    %"chk5" : A = (HalfCheck Lower 0 4 Write 4) %"chk4", %"v89";
    %"v97" : W = (RawCas (CasNarrow Sw) 0) %"chk5", %"v96", #0;
    %"v98" : W = (Cmp Eq W) %"v97", %"v96"
    => br %"v98" ? "L95" : poll "L94";
  @"L95":
    %"v103" : W = (Cmp Sgt W) %"v96", #1
    => br %"v103" ? "L106" : "L101";
  @"L106":
    call void $"__GI___lll_lock_wake_private"(P %"v89")
    => goto "L101";
  @"L101":
    => ret #1;
  @"iw_1.start":
    %"iw_1.v2" : P = (Alloc 8) #16;
    %"chk6" : A = (Check 0 8 Write 8) %"iw_1.v2";
    store.ptr [%"chk6" + 0] <- %"v2";
    %"iw_1.v5" : P = Copy $"__gconv_alias_db";
    %"iw_1.v6" : P = Copy $"__gconv_alias_compare";
    call %"iw_1.v7" : P = $"__GI___tfind"(P %"iw_1.v2", P %"iw_1.v5", P %"iw_1.v6");
    %"iw_1.v12" : L = Ptoi %"iw_1.v7";
    %"iw_1.v14" : W = (Cmp Ne L) %"iw_1.v12", %"v86"
    => br %"iw_1.v14" ? "iw_1.L8" : "iw_1.L10";
  @"iw_1.L8":
    %"chk7" : A = (Check 0 8 Read 8) %"iw_1.v7";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v17" = %"iw_1.v16" +p #8;
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v17";
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk8"
    => goto "iw_1.L10";
  @"iw_1.L10" [%"iw_1.v19" : P = phi("iw_1.L8" => %"iw_1.v18", "iw_1.start" => #0)]:
    %"iw_2.v2" : P = (Alloc 8) #16;
    %"chk9" : A = (Check 0 8 Write 8) %"iw_2.v2";
    store.ptr [%"chk9" + 0] <- %"v0";
    %"iw_2.v5" : P = Copy $"__gconv_alias_db";
    %"iw_2.v6" : P = Copy $"__gconv_alias_compare";
    call %"iw_2.v7" : P = $"__GI___tfind"(P %"iw_2.v2", P %"iw_2.v5", P %"iw_2.v6");
    %"iw_2.v12" : L = Ptoi %"iw_2.v7";
    %"iw_2.v14" : W = (Cmp Ne L) %"iw_2.v12", %"v86"
    => br %"iw_2.v14" ? "iw_2.L8" : "iw_2.L10";
  @"iw_2.L8":
    %"chk10" : A = (Check 0 8 Read 8) %"iw_2.v7";
    %"iw_2.v16" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_2.v17" = %"iw_2.v16" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_2.v17";
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto "iw_2.L10";
  @"iw_2.L10" [%"iw_2.v19" : P = phi("iw_2.L8" => %"iw_2.v18", "iw_1.L10" => #0)]:
    %"v126" : W = And %"v8", #1
    => br %"v126" ? "L129" : "L130";
  @"L129":
    call %"v133" : W = $"__GI_strcmp"(P %"v0", P %"v2");
    %"v134" : W = (Cmp Eq W) %"v133", #0
    => br %"v134" ? "L136" : "L135";
  @"L135":
    %"v138" : L = Ptoi %"iw_2.v19";
    %"v140" : W = (Cmp Ne L) %"v138", %"v86"
    => br %"v140" ? "L141" : "L136";
  @"L141":
    call %"v145" : W = $"__GI_strcmp"(P %"iw_2.v19", P %"v2");
    %"v146" : W = (Cmp Eq W) %"v145", #0
    => goto "L136";
  @"L136" [%"v150" : W = phi("L129" => #1, "L135" => #0, "L141" => %"v146")]:
    => br %"v150" ? "L130" : "L151";
  @"L151":
    %"v154" : L = Ptoi %"iw_1.v19";
    %"v156" : W = (Cmp Ne L) %"v154", %"v86"
    => br %"v156" ? "L157" : "L130";
  @"L157":
    call %"v161" : W = $"__GI_strcmp"(P %"v0", P %"iw_1.v19");
    %"v162" : W = (Cmp Eq W) %"v161", #0
    => br %"v162" ? "L130" : "L163";
  @"L163":
    %"v166" : L = Ptoi %"iw_2.v19";
    %"v168" : W = (Cmp Ne L) %"v166", %"v86"
    => br %"v168" ? "L169" : "L130";
  @"L169":
    call %"v173" : W = $"__GI_strcmp"(P %"iw_2.v19", P %"iw_1.v19");
    %"v174" : W = (Cmp Eq W) %"v173", #0
    => goto "L130";
  @"L130" [%"v184" : W = phi("iw_2.L10" => #0, "L136" => #1, "L151" => #0, "L157" => #1, "L163" => #0, "L169" => %"v174")]:
    => br %"v184" ? "L122" : "L124";
  @"L122":
    %"v186" : P = Copy $"__gconv_lock";
    %"chk12" : A = (Check 0 4 Read 1) %"v186";
    %"v190" : W = (RawLoad (LdNarrow Sw) 0) %"chk12"
    => goto "L191";
  @"L191" [%"v193" : W = phi("L122" => %"v190", "L191" => %"v194")]:
    %"chk13" : A = (HalfCheck Lower 0 4 Write 4) %"chk12", %"v186";
    %"v194" : W = (RawCas (CasNarrow Sw) 0) %"chk13", %"v193", #0;
    %"v195" : W = (Cmp Eq W) %"v194", %"v193"
    => br %"v195" ? "L192" : poll "L191";
  @"L192":
    %"v200" : W = (Cmp Sgt W) %"v193", #1
    => br %"v200" ? "L203" : "L198";
  @"L203":
    call void $"__GI___lll_lock_wake_private"(P %"v186")
    => goto "L198";
  @"L198":
    => ret #(-1);
  @"L124":
    call %"v221" : W = $"glibc_gconv_db#find_derivation"(P %"v0", P %"iw_2.v19", P %"v2", P %"iw_1.v19", P %"v4", P %"v6");
    %"v223" : P = Copy $"__gconv_lock";
    %"chk14" : A = (Check 0 4 Read 1) %"v223";
    %"v227" : W = (RawLoad (LdNarrow Sw) 0) %"chk14"
    => goto "L228";
  @"L228" [%"v230" : W = phi("L124" => %"v227", "L228" => %"v231")]:
    %"chk15" : A = (HalfCheck Lower 0 4 Write 4) %"chk14", %"v223";
    %"v231" : W = (RawCas (CasNarrow Sw) 0) %"chk15", %"v230", #0;
    %"v232" : W = (Cmp Eq W) %"v231", %"v230"
    => br %"v232" ? "L229" : poll "L228";
  @"L229":
    %"v237" : W = (Cmp Sgt W) %"v230", #1
    => br %"v237" ? "L240" : "L235";
  @"L240":
    call void $"__GI___lll_lock_wake_private"(P %"v223")
    => goto "L235";
  @"L235":
    %"v255" : W = (Cmp Eq W) %"v221", #0
    => br %"v255" ? "L251" : "L253";
  @"L251":
    %"chk16" : A = (Check 0 8 Read 8) %"v4";
    %"v260" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v261" : L = Ptoi %"v260";
    %"v263" : W = (Cmp Eq L) %"v261", %"v86"
    => br %"v263" ? "L253" : "L257";
  @"L257":
    => goto "L253";
  @"L253" [%"v266" : W = phi("L257" => #0, "L251" => #1, "L235" => %"v221")]:
    => ret %"v266"
} }.

Definition hello_image_fn___gconv_close_transform : func :=
  ir_fn{ "export" "__gconv_close_transform"(P %"v0", L %"v2") -> (RClass W) {
  @"start":
    %"v7" : P = Copy $"__gconv_lock";
    %"chk0" : A = (Check 0 4 Write 4) %"v7";
    %"v14" : W = (RawCas (CasNarrow Sw) 0) %"chk0", #0, #1;
    %"v15" : W = (Cmp Eq W) %"v14", #0
    => br %"v15" ? "L17" : "L16";
  @"L16":
    => goto "L17";
  @"L17":
    %"v18" : W = (Cmp Ne W) %"v14", #0
    => br %"v18" ? "L21" : "L32";
  @"L21":
    call void $"__GI___lll_lock_wait_private"(P %"v7")
    => goto "L32";
  @"L32" [%"pr.1" : L = phi("L33" => %"v36", "L21" => %"v2", "L17" => %"v2")]:
    %"v36" : L = Sub %"pr.1", #1;
    %"v37" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v37" ? "L33" : "L34";
  @"L33":
    %"v40" : L = Mul %"v36", #104;
    %"v41" = %"v0" +p %"v40";
    call void $"__gconv_release_step"(P %"v41")
    => goto poll "L32";
  @"L34":
    call void $"__gconv_release_cache"(P %"v0", L %"v2");
    %"v45" : P = Copy $"__gconv_lock";
    %"chk1" : A = (Check 0 4 Read 1) %"v45";
    %"v49" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => goto "L50";
  @"L50" [%"v52" : W = phi("L34" => %"v49", "L50" => %"v53")]:
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk1", %"v45";
    %"v53" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"v52", #0;
    %"v54" : W = (Cmp Eq W) %"v53", %"v52"
    => br %"v54" ? "L51" : poll "L50";
  @"L51":
    %"v59" : W = (Cmp Sgt W) %"v52", #1
    => br %"v59" ? "L62" : "L57";
  @"L62":
    call void $"__GI___lll_lock_wake_private"(P %"v45")
    => goto "L57";
  @"L57":
    => ret #0
} }.
