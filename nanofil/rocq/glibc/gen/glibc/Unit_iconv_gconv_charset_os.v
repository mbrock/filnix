(** This file defines checked IR from glibc’s `iconv/gconv_charset.os` object.
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

Definition fn___GI___gconv_create_spec : func :=
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

Definition fn___GI___gconv_destroy_spec : func :=
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

Definition fn_glibc_gconv_charset'23gconv_parse_code : func :=
  ir_fn{ "local" "glibc_gconv_charset#gconv_parse_code"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #8;
    %"chk0" : A = (Check 0 1 Write 1) %"v3";
    store Wb [%"chk0" + 0] <- #0;
    %"v6" = %"v0" +p #9;
    %"chk1" : A = (HalfCheck Upper 0 1 Write 1) %"chk0", %"v6";
    store Wb [%"chk1" + 0] <- #0
    => goto "L9";
  @"L9":
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call %"v14" : L = $"__GI_strlen"(P %"v13")
    => goto "L15";
  @"L15" [%"pr.1" : L = phi("L16" => %"v60", "L9" => %"v14")]:
    %"v19" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v19" ? "iw_1.start" : "L21";
  @"iw_1.start":
    %"iw_1.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v0";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v0";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v27" : L = Sub %"pr.1", #1;
    %"v28" = %"v25" +p %"v27";
    %"chk5" : A = (Check 0 1 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v30" : L = (Ext Sw) %"v29";
    %"v31" : L = Shl %"v30", #1;
    %"v32" = %"v23" +p %"v31";
    %"chk6" : A = (Check 0 2 Read 1) %"v32";
    %"v33" : W = (RawLoad (LdNarrow Uh) 0) %"chk6";
    %"v34" : W = And %"v33", #8192
    => br %"v34" ? "L36" : "L35";
  @"L35":
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v41" = %"v38" +p %"v27";
    %"chk8" : A = (Check 0 1 Read 1) %"v41";
    %"v42" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v43" : W = (Cmp Eq W) %"v42", #44
    => goto "L36";
  @"L36" [%"v45" : W = phi("iw_1.start" => #1, "L35" => %"v43")]:
    => br %"v45" ? "L21" : "L46";
  @"L46":
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v52" = %"v49" +p %"v27";
    %"chk10" : A = (Check 0 1 Read 1) %"v52";
    %"v53" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"v54" : W = (Cmp Eq W) %"v53", #47
    => goto "L21";
  @"L21" [%"v58" : W = phi("L15" => #0, "L36" => #1, "L46" => %"v54")]:
    => br %"v58" ? "L16" : "L17";
  @"L16":
    %"v60" : L = Sub %"pr.1", #1
    => goto poll "L15";
  @"L17":
    %"chk11" : A = (Renew 0 8 Read 8) %"chk2", %"v0";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v64" = %"v62" +p %"pr.1";
    %"chk12" : A = (Check 0 1 Write 1) %"v64";
    store Wb [%"chk12" + 0] <- #0;
    %"v69" : W = (Cmp Eq L) %"pr.1", #0
    => br %"v69" ? "L65" : "L67";
  @"L65":
    => ret void;
  @"L67":
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto "iw_2.L5";
  @"iw_2.L5" [%"iw_2.pr.6" : W = phi("iw_2.L21" => %"iw_2.v35", "L67" => #0); %"iw_2.pr.5" : P = phi("iw_2.L21" => %"iw_2.pr.4", "L67" => #0); %"iw_2.pr.3" : W = phi("iw_2.L21" => %"iw_2.pr.1", "L67" => #0)]:
    %"iw_2.v11" : L = (Ext Sw) %"iw_2.pr.6";
    %"iw_2.v12" = %"v73" +p %"iw_2.v11";
    %"chk14" : A = (Check 0 1 Read 1) %"iw_2.v12";
    %"iw_2.v13" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_2.v14" : W = (Cmp Ne W) %"iw_2.v13", #0
    => br %"iw_2.v14" ? "iw_2.L6" : "iw_2.L8";
  @"iw_2.L6":
    %"iw_2.v19" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"iw_2.v30" : W = (Cmp Eq W) %"iw_2.v19", #47
    => br %"iw_2.v30" ? "iw_2.L22" : "iw_2.L31";
  @"iw_2.L22":
    %"iw_2.v24" : W = Add %"iw_2.pr.3", #1
    => goto "iw_2.L21";
  @"iw_2.L31":
    %"iw_2.v32" : W = (Cmp Eq W) %"iw_2.v19", #44
    => br %"iw_2.v32" ? "iw_2.L21" : "iw_2.L33";
  @"iw_2.L33":
    => goto "iw_2.L21";
  @"iw_2.L21" [%"iw_2.pr.4" : P = phi("iw_2.L33" => %"iw_2.pr.5", "iw_2.L22" => %"iw_2.v12", "iw_2.L31" => %"iw_2.v12"); %"iw_2.pr.1" : W = phi("iw_2.L33" => %"iw_2.pr.3", "iw_2.L22" => %"iw_2.v24", "iw_2.L31" => %"iw_2.pr.3")]:
    %"iw_2.v35" : W = Add %"iw_2.pr.6", #1
    => goto poll "iw_2.L5";
  @"iw_2.L8":
    %"iw_2.v40" : W = (Cmp Sge W) %"iw_2.pr.3", #2
    => br %"iw_2.v40" ? "iw_2.join" : "iw_2.L38";
  @"iw_2.L38":
    => goto "iw_2.join";
  @"iw_2.join" [%"v74" : P = phi("iw_2.L38" => #0, "iw_2.L8" => %"iw_2.pr.5")]:
    %"v79" : L = Ptoi %"v74";
    %"v80" : L = Ptoi #0;
    %"v81" : W = (Cmp Eq L) %"v79", %"v80"
    => br %"v81" ? "L75" : "L76";
  @"L75":
    => ret void;
  @"L76":
    %"v87" : P = Copy $"glibc_gconv_charset#str.244";
    %"v88" : P = Copy $"_nl_C_locobj";
    call %"v89" : W = $"__GI___strcasecmp_l"(P %"v74", P %"v87", P %"v88");
    %"v90" : W = (Cmp Eq W) %"v89", #0
    => br %"v90" ? "L92" : "L91";
  @"L91":
    %"v94" : P = Copy $"glibc_gconv_charset#str.245";
    %"v95" : P = Copy $"_nl_C_locobj";
    call %"v96" : W = $"__GI___strcasecmp_l"(P %"v74", P %"v94", P %"v95");
    %"v97" : W = (Cmp Eq W) %"v96", #0
    => goto "L92";
  @"L92" [%"v99" : W = phi("L76" => #1, "L91" => %"v97")]:
    => br %"v99" ? "L83" : "L85";
  @"L83":
    %"v101" = %"v0" +p #8;
    %"chk16" : A = (Renew 0 1 Write 1) %"chk0", %"v101";
    store Wb [%"chk16" + 0] <- #1
    => goto "L85";
  @"L85":
    %"v107" : P = Copy $"glibc_gconv_charset#str.246";
    %"v108" : P = Copy $"_nl_C_locobj";
    call %"v109" : W = $"__GI___strcasecmp_l"(P %"v74", P %"v107", P %"v108");
    %"v110" : W = (Cmp Eq W) %"v109", #0
    => br %"v110" ? "L112" : "L111";
  @"L111":
    %"v114" : P = Copy $"glibc_gconv_charset#str.247";
    %"v115" : P = Copy $"_nl_C_locobj";
    call %"v116" : W = $"__GI___strcasecmp_l"(P %"v74", P %"v114", P %"v115");
    %"v117" : W = (Cmp Eq W) %"v116", #0
    => goto "L112";
  @"L112" [%"v119" : W = phi("L85" => #1, "L111" => %"v117")]:
    => br %"v119" ? "L103" : "L105";
  @"L103":
    %"v121" = %"v0" +p #9;
    %"chk17" : A = (Renew 0 1 Write 1) %"chk1", %"v121";
    store Wb [%"chk17" + 0] <- #1
    => goto "L105";
  @"L105":
    %"chk18" : A = (Check 0 1 Write 1) %"v74";
    store Wb [%"chk18" + 0] <- #0
    => goto poll "L9"
} }.

Definition item_glibc_gconv_charset'23str'2e244 : item :=
  (IData (a "glibc_gconv_charset#str.244") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 84); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 83); (Item Wb 76); (Item Wb 73); (Item Wb 84); (Item Wb 0)]).

Definition item_glibc_gconv_charset'23str'2e245 : item :=
  (IData (a "glibc_gconv_charset#str.245") (LRo (a "local")) 1 [(Item Wb 44); (Item Wb 84); (Item Wb 82); (Item Wb 65); (Item Wb 78); (Item Wb 83); (Item Wb 76); (Item Wb 73); (Item Wb 84); (Item Wb 0)]).

Definition item_glibc_gconv_charset'23str'2e246 : item :=
  (IData (a "glibc_gconv_charset#str.246") (LRo (a "local")) 1 [(Item Wb 47); (Item Wb 73); (Item Wb 71); (Item Wb 78); (Item Wb 79); (Item Wb 82); (Item Wb 69); (Item Wb 0)]).

Definition item_glibc_gconv_charset'23str'2e247 : item :=
  (IData (a "glibc_gconv_charset#str.247") (LRo (a "local")) 1 [(Item Wb 44); (Item Wb 73); (Item Wb 71); (Item Wb 78); (Item Wb 79); (Item Wb 82); (Item Wb 69); (Item Wb 0)]).
