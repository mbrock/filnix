(** This file defines checked IR from glibc’s `stdio-common/printf_fphex.os` object.
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

Definition fn___printf_buffer_flush_fphex_to_wide : func :=
  ir_fn{ "export" "__printf_buffer_flush_fphex_to_wide"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #56
    => goto "L5";
  @"L5" [%"pr.1" : P = phi("L7" => %"v32", "start" => %"v4")]:
    %"v11" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" : L = Ptoi %"pr.1";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ult L) %"v13", %"v14"
    => br %"v15" ? "L6" : "L8";
  @"L6":
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v18" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v23" : W = (Cmp Eq W) %"v18", #46
    => br %"v23" ? "L19" : "L21";
  @"L19":
    %"v25" = %"v0" +p #40;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v25";
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk2"
    => goto "L21";
  @"L21" [%"pr.2" : W = phi("L19" => %"v26", "L6" => %"v18")]:
    %"v28" = %"v0" +p #48;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v8" = %"v29" +p #8;
    %"chk4" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v11" = %"v29" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk4", %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v13" : L = Ptoi %"iw_1.v9";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Ne L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L5";
  @"iw_1.L4":
    %"iw_1.v17" = %"v29" +p #8;
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v19" = %"iw_1.v18" +p #4;
    %"chk7" : A = (Renew 0 8 Write 8) %"chk4", %"iw_1.v17";
    store.ptr [%"chk7" + 0] <- %"iw_1.v19";
    %"chk8" : A = (Check 0 4 Write 1) %"iw_1.v18";
    store Ww [%"chk8" + 0] <- %"pr.2"
    => goto "L7";
  @"iw_1.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v29", W %"pr.2")
    => goto "L7";
  @"L7":
    %"v32" = %"pr.1" +p #1
    => goto poll "L5";
  @"L8":
    %"v37" = %"v0" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_2.v3" = %"v38" +p #32;
    %"chk10" : A = (Check 0 4 Read 1) %"iw_2.v3";
    %"iw_2.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"v41" : W = (Cmp Ne W) %"iw_2.v4", #0
    => br %"v41" ? "L33" : "iw_3.start";
  @"L33":
    %"v43" = %"v0" +p #8;
    %"v45" = %"v0" +p #56;
    %"chk11" : A = (Renew 0 8 Write 8) %"chk0", %"v43";
    store.ptr [%"chk11" + 0] <- %"v45"
    => goto "L35";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk12" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_3.v3";
    store Ww [%"chk12" + 0] <- #0
    => goto "L35";
  @"L35":
    => ret void
} }.

Definition fn___printf_fphex_l_buffer : func :=
  ir_fn{ "export" "__printf_fphex_l_buffer"(P %"v0", P %"v2", P %"v4", P %"v6") -> RVoid {
  @"start":
    %"iw_1.v10" = %"v2" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v12" = %"iw_1.v11" +p #56;
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v12";
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call void $"glibc_printf_fphex#__printf_fphex_buffer"(P %"v0", P %"iw_1.v18", P %"v4", P %"v6")
    => ret void
} }.

Definition fn___wprintf_fphex_l_buffer : func :=
  ir_fn{ "export" "__wprintf_fphex_l_buffer"(P %"v0", P %"v2", P %"v4", P %"v6") -> RVoid {
  @"start":
    %"v8" : P = (Alloc 8) #120;
    %"v9" = %"v8" +p #56;
    %"iw_1.v12" = %"v9" +p #64;
    %"chk0" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk0" + 0] <- %"v9";
    %"iw_1.iw_1.v11" = %"v8" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v9";
    %"iw_1.iw_1.v14" = %"v8" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v12";
    %"iw_1.iw_1.v17" = %"v8" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.iw_1.v17";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.iw_1.v19" = %"v8" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.iw_1.v19";
    store Ww [%"chk4" + 0] <- #10;
    %"v10" = %"v8" +p #40;
    %"iw_2.v10" = %"v2" +p #8;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_2.v10";
    %"iw_2.v11" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_2.v12" = %"iw_2.v11" +p #56;
    %"iw_2.v17" = %"iw_2.v12" +p #24;
    %"chk6" : A = (Check 0 4 Read 1) %"iw_2.v17";
    %"iw_2.v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"chk7" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v10";
    store Ww [%"chk7" + 0] <- %"iw_2.v18";
    %"v13" = %"v8" +p #48;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v13";
    store.ptr [%"chk8" + 0] <- %"v0";
    %"v15" : P = Copy $"glibc_printf_fphex#str.295";
    call void $"glibc_printf_fphex#__printf_fphex_buffer"(P %"v8", P %"v15", P %"v4", P %"v6");
    %"iw_3.v3" = %"v8" +p #32;
    %"chk9" : A = (Renew 0 4 Read 1) %"chk4", %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L18" : "L20";
  @"L18":
    %"v23" = %"v8" +p #48;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk8", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_4.v3" = %"v24" +p #32;
    %"chk11" : A = (Check 0 4 Write 1) %"iw_4.v3";
    store Ww [%"chk11" + 0] <- #0
    => ret void;
  @"L20":
    call void $"__printf_buffer_flush_fphex_to_wide"(P %"v8")
    => ret void
} }.

Definition fn_glibc_printf_fphex'23__printf_fphex_buffer : func :=
  ir_fn{ "local" "glibc_printf_fphex#__printf_fphex_buffer"(P %"v0", P %"v2", P %"v4", P %"v6") -> RVoid blocks ((app (app [ir_blk{ @"start":
    %"v8" : P = (Alloc 16) #16;
    %"v22" : P = (Alloc 4) #32;
    %"v26" : P = (Alloc 4) #5;
    alloca "v81" 16;
    alloca "v131" 16;
    alloca "v367" 16;
    %"v13" = %"v4" +p #12;
    %"chk0" : A = (Check 0 4 Read 1) %"v13";
    %"v14" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v15" : W = Shl %"v14", #23;
    %"v16" : W = Shr %"v15", #31;
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => br %"v17" ? "L11" : "L10" };
  ir_blk{ @"L10":
    %"v18" : P = Copy $"glibc_printf_fphex#str.287";
    %"v19" : P = Copy $"glibc_printf_fphex#str.288";
    %"v20" : P = Copy $"glibc_printf_fphex#str.289";
    call void $"__libc_assert_fail"(P %"v18", P %"v19", W #65, P %"v20")
    => goto "L11" };
  ir_blk{ @"L11":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v4";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v37" = %"v4" +p #4;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v37";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v43" = %"v4" +p #12;
    %"chk3" : A = (Renew 0 4 Read 1) %"chk0", %"v43";
    %"v44" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v45" : W = Shl %"v44", #31;
    %"v46" : W = Shr %"v45", #31
    => br %"v46" ? "L47" : "L48" };
  ir_blk{ @"L47":
    => goto "L48" };
  ir_blk{ @"L48" [%"v51" : W = phi("L11" => #0, "L47" => #1)]:
    => br %"v51" ? "L39" : "L40" };
  ir_blk{ @"L39":
    %"chk4" : A = (Check 0 8 Read 8) %"v6";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 10 Read 8) %"v54";
    %"v55" : Extended = (RawLoad LdX 0) %"chk5";
    %"chk6" : A = (Check 0 10 Write 8) %"v8";
    store Wx [%"chk6" + 0] <- %"v55";
    %"v59" : Extended = (RawLoad LdX 0) %"chk6";
    %"v60" : Double = Truncx %"v59";
    %"v61" : W = (Cmp Unord Double) %"v60", %"v60"
    => br %"v61" ? "iw_1.start" : "L57" };
  ir_blk{ @"iw_1.start":
    %"iw_1.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v0";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v68" = %"v4" +p #8;
    %"chk9" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v68";
    %"v69" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v70" : L = (Ext Sw) %"v69";
    %"v71" : L = Shl %"v70", #1;
    %"v72" = %"v66" +p %"v71";
    %"chk10" : A = (Check 0 2 Read 1) %"v72";
    %"v73" : W = (RawLoad (LdNarrow Uh) 0) %"chk10";
    %"v74" : W = And %"v73", #256
    => br %"v74" ? "L62" : "L63" };
  ir_blk{ @"L62":
    %"v75" : P = Copy $"glibc_printf_fphex#str.290"
    => goto "L58" };
  ir_blk{ @"L63":
    %"v76" : P = Copy $"glibc_printf_fphex#str.291"
    => goto "L58" };
  ir_blk{ @"L57":
    %"v80" : Extended = (RawLoad LdX 0) %"chk6";
    %"chk12" : A = (CheckLocal (a "v81") 0 10 Write 8);
    store Wx [%"chk12" + 0] <- %"v80";
    %"chk13" : A = (CheckLocal (a "v81") 0 8 Read 1);
    %"v82" : L = (RawLoad LdL 0) %"chk13";
    %"chk14" : A = (CheckLocal (a "v81") 8 2 Read 1);
    %"v84" : W = (RawLoad (LdNarrow Uh) 0) %"chk14";
    %"v85" : W = Shr %"v84", #15;
    %"v86" : W = And %"v84", #32767;
    %"v89" : W = (Cmp Eq W) %"v86", #32767;
    %"v91" : W = (Cmp Slt L) %"v82", #0;
    %"v94" : L = Shl %"v82", #1;
    %"v95" : W = (Cmp Ne L) %"v94", #0;
    %"v99" : W = And %"v89", %"v91";
    %"v100" : W = Xor %"v95", #1;
    %"v101" : W = And %"v99", %"v100";
    %"v112" : W = And %"v101", %"v85";
    %"v113" : W = Add %"v112", %"v112";
    %"v114" : W = Sub %"v101", %"v113"
    => br %"v114" ? "iw_2.start" : "L58" };
  ir_blk{ @"iw_2.start":
    %"iw_2.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk15" : A = (Check 0 8 Read 8) %"iw_2.v0";
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v121" = %"v4" +p #8;
    %"chk16" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v121";
    %"v122" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v123" : L = (Ext Sw) %"v122";
    %"v124" : L = Shl %"v123", #1;
    %"v125" = %"v119" +p %"v124";
    %"chk17" : A = (Check 0 2 Read 1) %"v125";
    %"v126" : W = (RawLoad (LdNarrow Uh) 0) %"chk17";
    %"v127" : W = And %"v126", #256
    => br %"v127" ? "L115" : "L116" };
  ir_blk{ @"L115":
    %"v128" : P = Copy $"glibc_printf_fphex#str.292"
    => goto "L58" };
  ir_blk{ @"L116":
    %"v129" : P = Copy $"glibc_printf_fphex#str.293"
    => goto "L58" };
  ir_blk{ @"L58" [%"pr.7" : P = phi("L62" => %"v75", "L63" => %"v76", "L115" => %"v128", "L116" => %"v129", "L57" => #0)]:
    %"chk18" : A = (Renew 0 10 Read 8) %"chk6", %"v8";
    %"v130" : Extended = (RawLoad LdX 0) %"chk18";
    %"chk19" : A = (CheckLocal (a "v131") 0 10 Write 8);
    store Wx [%"chk19" + 0] <- %"v130";
    %"chk20" : A = (CheckLocal (a "v131") 8 2 Read 1);
    %"v133" : W = (RawLoad (LdNarrow Uh) 0) %"chk20";
    %"v134" : W = Shr %"v133", #15
    => goto "L41" };
  ir_blk{ @"L40":
    %"chk21" : A = (Check 0 8 Read 8) %"v6";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (Check 0 8 Read 1) %"v137";
    %"v138" : Double = (RawLoad LdD 0) %"chk22";
    %"chk23" : A = (Check 0 8 Write 1) %"v8";
    store Wd [%"chk23" + 0] <- %"v138";
    %"v142" : Double = (RawLoad LdD 0) %"chk23";
    %"v143" : W = (Cmp Unord Double) %"v142", %"v142"
    => br %"v143" ? "iw_3.start" : "L140" };
  ir_blk{ @"iw_3.start":
    %"iw_3.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk25" : A = (Check 0 8 Read 8) %"iw_3.v0";
    %"v148" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v150" = %"v4" +p #8;
    %"chk26" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v150";
    %"v151" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v152" : L = (Ext Sw) %"v151";
    %"v153" : L = Shl %"v152", #1;
    %"v154" = %"v148" +p %"v153";
    %"chk27" : A = (Check 0 2 Read 1) %"v154";
    %"v155" : W = (RawLoad (LdNarrow Uh) 0) %"chk27";
    %"v156" : W = And %"v155", #256
    => br %"v156" ? "L144" : "L145" };
  ir_blk{ @"L144":
    %"v157" : P = Copy $"glibc_printf_fphex#str.290"
    => goto "L141" };
  ir_blk{ @"L145":
    %"v158" : P = Copy $"glibc_printf_fphex#str.291"
    => goto "L141" };
  ir_blk{ @"L140":
    %"v162" : Double = (RawLoad LdD 0) %"chk23";
    %"v163" : L = Cast %"v162";
    %"v164" : L = And %"v163", #9223372036854775807;
    %"v165" : W = (Cmp Eq L) %"v164", #9218868437227405312;
    %"v166" : W = (Cmp Slt L) %"v163", #0;
    %"v167" : W = And %"v165", %"v166";
    %"v168" : W = Add %"v167", %"v167";
    %"v169" : W = Sub %"v165", %"v168"
    => br %"v169" ? "iw_4.start" : "L141" };
  ir_blk{ @"iw_4.start":
    %"iw_4.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk29" : A = (Check 0 8 Read 8) %"iw_4.v0";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v176" = %"v4" +p #8;
    %"chk30" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v176";
    %"v177" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v178" : L = (Ext Sw) %"v177";
    %"v179" : L = Shl %"v178", #1;
    %"v180" = %"v174" +p %"v179";
    %"chk31" : A = (Check 0 2 Read 1) %"v180";
    %"v181" : W = (RawLoad (LdNarrow Uh) 0) %"chk31";
    %"v182" : W = And %"v181", #256
    => br %"v182" ? "L170" : "L171" };
  ir_blk{ @"L170":
    %"v183" : P = Copy $"glibc_printf_fphex#str.292"
    => goto "L141" };
  ir_blk{ @"L171":
    %"v184" : P = Copy $"glibc_printf_fphex#str.293"
    => goto "L141" };
  ir_blk{ @"L141" [%"pr.2" : P = phi("L144" => %"v157", "L145" => %"v158", "L170" => %"v183", "L171" => %"v184", "L140" => #0)]:
    %"chk32" : A = (Renew 0 8 Read 1) %"chk23", %"v8";
    %"v185" : Double = (RawLoad LdD 0) %"chk32";
    %"v186" : L = Cast %"v185";
    %"v188" : W = (Cmp Slt L) %"v186", #0
    => goto "L41" };
  ir_blk{ @"L41" [%"pr.17" : W = phi("L141" => %"v188", "L58" => %"v134"); %"pr.6" : P = phi("L141" => %"pr.2", "L58" => %"pr.7")]:
    %"v193" : L = Ptoi %"pr.6";
    %"v194" : W = (Cmp Ne L) %"v193", #0
    => br %"v194" ? "L189" : "L191" };
  ir_blk{ @"L189":
    %"v197" = %"v4" +p #4;
    %"chk33" : A = (Renew 0 4 Read 1) %"chk2", %"v197";
    %"v198" : W = (RawLoad (LdNarrow Sw) 0) %"chk33"
    => br %"pr.17" ? "L204" : "L203" };
  ir_blk{ @"L203":
    %"v206" = %"v4" +p #12;
    %"chk34" : A = (Renew 0 4 Read 1) %"chk0", %"v206";
    %"v207" : W = (RawLoad (LdNarrow Uw) 0) %"chk34";
    %"v208" : W = Shl %"v207", #25;
    %"v209" : W = Shr %"v208", #31;
    %"v210" : W = (Cmp Ne W) %"v209", #0
    => goto "L204" };
  ir_blk{ @"L204" [%"v211" : W = phi("L189" => #1, "L203" => %"v210")]:
    => br %"v211" ? "L213" : "L212" };
  ir_blk{ @"L212":
    %"v215" = %"v4" +p #12;
    %"chk35" : A = (Renew 0 4 Read 1) %"chk0", %"v215";
    %"v216" : W = (RawLoad (LdNarrow Uw) 0) %"chk35";
    %"v217" : W = Shl %"v216", #27;
    %"v218" : W = Shr %"v217", #31;
    %"v219" : W = (Cmp Ne W) %"v218", #0
    => goto "L213" };
  ir_blk{ @"L213" [%"v220" : W = phi("L204" => #1, "L212" => %"v219")]:
    => br %"v220" ? "L199" : "L201" };
  ir_blk{ @"L199":
    %"v222" : W = Sub %"v198", #1
    => goto "L201" };
  ir_blk{ @"L201" [%"pr.60" : W = phi("L199" => %"v222", "L213" => %"v198")]:
    %"v224" : W = Sub %"pr.60", #3;
    %"v229" = %"v4" +p #12;
    %"chk36" : A = (Renew 0 4 Read 1) %"chk0", %"v229";
    %"v230" : W = (RawLoad (LdNarrow Uw) 0) %"chk36";
    %"v231" : W = Shl %"v230", #26;
    %"v232" : W = Shr %"v231", #31;
    %"v233" : W = (Cmp Eq W) %"v232", #0
    => br %"v233" ? "L225" : "L227" };
  ir_blk{ @"L225":
    %"v236" : L = (Ext Sw) %"v224";
    %"iw_5.v10" : W = (Cmp Sgt L) %"v236", #0
    => br %"iw_5.v10" ? "iw_5.L6" : "L227" };
  ir_blk{ @"iw_5.L6":
    call void $"__printf_buffer_pad_1"(P %"v0", W #32, L %"v236")
    => goto "L227" };
  ir_blk{ @"L227":
    => br %"pr.17" ? "iw_6.start" : "L238" };
  ir_blk{ @"iw_6.start":
    %"iw_6.v8" = %"v0" +p #8;
    %"chk37" : A = (Check 0 8 Read 8) %"iw_6.v8";
    %"iw_6.v9" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_6.v11" = %"v0" +p #16;
    %"chk38" : A = (HalfCheck Upper 0 8 Read 8) %"chk37", %"iw_6.v11";
    %"iw_6.v12" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"iw_6.v13" : L = Ptoi %"iw_6.v9";
    %"iw_6.v14" : L = Ptoi %"iw_6.v12";
    %"iw_6.v15" : W = (Cmp Ne L) %"iw_6.v13", %"iw_6.v14"
    => br %"iw_6.v15" ? "iw_6.L4" : "iw_6.L5" };
  ir_blk{ @"iw_6.L4":
    %"iw_6.v17" = %"v0" +p #8;
    %"iw_6.v18" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_6.v19" = %"iw_6.v18" +p #1;
    %"chk40" : A = (Renew 0 8 Write 8) %"chk37", %"iw_6.v17";
    store.ptr [%"chk40" + 0] <- %"iw_6.v19";
    %"chk41" : A = (Check 0 1 Write 1) %"iw_6.v18";
    store Wb [%"chk41" + 0] <- #45
    => goto "iw_9.start" };
  ir_blk{ @"iw_6.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #45)
    => goto "iw_9.start" };
  ir_blk{ @"L238":
    %"v246" = %"v4" +p #12;
    %"chk42" : A = (Renew 0 4 Read 1) %"chk0", %"v246";
    %"v247" : W = (RawLoad (LdNarrow Uw) 0) %"chk42";
    %"v248" : W = Shl %"v247", #25;
    %"v249" : W = Shr %"v248", #31
    => br %"v249" ? "iw_7.start" : "L243" };
  ir_blk{ @"iw_7.start":
    %"iw_7.v8" = %"v0" +p #8;
    %"chk43" : A = (Check 0 8 Read 8) %"iw_7.v8";
    %"iw_7.v9" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"iw_7.v11" = %"v0" +p #16;
    %"chk44" : A = (HalfCheck Upper 0 8 Read 8) %"chk43", %"iw_7.v11";
    %"iw_7.v12" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"iw_7.v13" : L = Ptoi %"iw_7.v9";
    %"iw_7.v14" : L = Ptoi %"iw_7.v12";
    %"iw_7.v15" : W = (Cmp Ne L) %"iw_7.v13", %"iw_7.v14"
    => br %"iw_7.v15" ? "iw_7.L4" : "iw_7.L5" };
  ir_blk{ @"iw_7.L4":
    %"iw_7.v17" = %"v0" +p #8;
    %"iw_7.v18" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"iw_7.v19" = %"iw_7.v18" +p #1;
    %"chk46" : A = (Renew 0 8 Write 8) %"chk43", %"iw_7.v17";
    store.ptr [%"chk46" + 0] <- %"iw_7.v19";
    %"chk47" : A = (Check 0 1 Write 1) %"iw_7.v18";
    store Wb [%"chk47" + 0] <- #43
    => goto "iw_9.start" };
  ir_blk{ @"iw_7.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #43)
    => goto "iw_9.start" };
  ir_blk{ @"L243":
    %"v255" = %"v4" +p #12;
    %"v256" : W = (RawLoad (LdNarrow Uw) 0) %"chk42";
    %"v257" : W = Shl %"v256", #27;
    %"v258" : W = Shr %"v257", #31
    => br %"v258" ? "iw_8.start" : "iw_9.start" };
  ir_blk{ @"iw_8.start":
    %"iw_8.v8" = %"v0" +p #8;
    %"chk49" : A = (Check 0 8 Read 8) %"iw_8.v8";
    %"iw_8.v9" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_8.v11" = %"v0" +p #16;
    %"chk50" : A = (HalfCheck Upper 0 8 Read 8) %"chk49", %"iw_8.v11";
    %"iw_8.v12" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"iw_8.v13" : L = Ptoi %"iw_8.v9";
    %"iw_8.v14" : L = Ptoi %"iw_8.v12";
    %"iw_8.v15" : W = (Cmp Ne L) %"iw_8.v13", %"iw_8.v14"
    => br %"iw_8.v15" ? "iw_8.L4" : "iw_8.L5" };
  ir_blk{ @"iw_8.L4":
    %"iw_8.v17" = %"v0" +p #8;
    %"iw_8.v18" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_8.v19" = %"iw_8.v18" +p #1;
    %"chk52" : A = (Renew 0 8 Write 8) %"chk49", %"iw_8.v17";
    store.ptr [%"chk52" + 0] <- %"iw_8.v19";
    %"chk53" : A = (Check 0 1 Write 1) %"iw_8.v18";
    store Wb [%"chk53" + 0] <- #32
    => goto "iw_9.start" };
  ir_blk{ @"iw_8.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #32)
    => goto "iw_9.start" };
  ir_blk{ @"iw_9.start":
    call void $"__printf_buffer_puts_1"(P %"v0", P %"pr.6");
    %"v266" = %"v4" +p #12;
    %"chk54" : A = (Renew 0 4 Read 1) %"chk0", %"v266";
    %"v267" : W = (RawLoad (LdNarrow Uw) 0) %"chk54";
    %"v268" : W = Shl %"v267", #26;
    %"v269" : W = Shr %"v268", #31
    => br %"v269" ? "L262" : "L264" };
  ir_blk{ @"L262":
    %"v272" : L = (Ext Sw) %"v224";
    %"iw_10.v10" : W = (Cmp Sgt L) %"v272", #0
    => br %"iw_10.v10" ? "iw_10.L6" : "L264" };
  ir_blk{ @"iw_10.L6":
    call void $"__printf_buffer_pad_1"(P %"v0", W #32, L %"v272")
    => goto "L264" };
  ir_blk{ @"L264":
    => ret void };
  ir_blk{ @"L191":
    %"v278" = %"v4" +p #12;
    %"chk55" : A = (Renew 0 4 Read 1) %"chk0", %"v278";
    %"v279" : W = (RawLoad (LdNarrow Uw) 0) %"chk55";
    %"v280" : W = Shl %"v279", #31;
    %"v281" : W = Shr %"v280", #31;
    %"v282" : W = (Cmp Eq W) %"v281", #0
    => br %"v282" ? "L284" : "L283" };
  ir_blk{ @"L283":
    => goto "L284" }] [ir_blk{ @"L284" [%"v287" : W = phi("L191" => #1, "L283" => #0)]:
    => br %"v287" ? "L274" : "L363" };
  ir_blk{ @"L274":
    %"v289" = %"v8" +p #4;
    %"chk56" : A = (Check 0 4 Read 1) %"v289";
    %"v290" : W = (RawLoad (LdNarrow Uw) 0) %"chk56";
    %"v291" : W = Shl %"v290", #12;
    %"v292" : W = Shr %"v291", #12;
    %"v293" : L = (Ext Sw) %"v292";
    %"v294" : L = Shl %"v293", #32;
    %"chk57" : A = (HalfCheck Lower 0 4 Read 1) %"chk56", %"v8";
    %"v295" : W = (RawLoad (LdNarrow Uw) 0) %"chk57";
    %"v296" : L = (Ext Uw) %"v295";
    %"v297" : L = Or %"v294", %"v296";
    %"v299" : W = (Cmp Eq L) %"v297", #0;
    %"v305" = %"v22" +p #32;
    %"v307" = %"v4" +p #8;
    %"chk58" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v307";
    %"v308" : W = (RawLoad (LdNarrow Sw) 0) %"chk58";
    %"v309" : W = (Cmp Eq W) %"v308", #65;
    call %"v310" : P = $"_itoa_word"(L %"v297", P %"v305", W #16, W %"v309")
    => goto "L318" };
  ir_blk{ @"L318" [%"pr.12" : P = phi("L319" => %"v328", "L274" => %"v310")]:
    %"v323" = %"v22" +p #19;
    %"v324" : L = Ptoi %"pr.12";
    %"v325" : L = Ptoi %"v323";
    %"v326" : W = (Cmp Ugt L) %"v324", %"v325"
    => br %"v326" ? "L319" : "L320" };
  ir_blk{ @"L319":
    (Flight (a "v328") Sub [(FAddress (t "pr.12")); (FValue (Const 1))] (LowerOf (t "pr.12")));
    %"chk59" : A = (Check 0 1 Write 1) %"v328";
    store Wb [%"chk59" + 0] <- #48
    => goto poll "L318" };
  ir_blk{ @"L320":
    %"v332" = %"v8" +p #4;
    %"chk60" : A = (Renew 0 4 Read 1) %"chk56", %"v332";
    %"v333" : W = (RawLoad (LdNarrow Uw) 0) %"chk60";
    %"v334" : W = Shl %"v333", #1;
    %"v335" : W = Shr %"v334", #21;
    %"v336" : W = (Cmp Eq W) %"v335", #0
    => br %"v336" ? "L331" : "L330" };
  ir_blk{ @"L330":
    => goto "L331" };
  ir_blk{ @"L331" [%"v337" : W = phi("L330" => #49, "L320" => #48)]:
    %"v338" : W = (Ext Sb) %"v337";
    %"v339" = %"v8" +p #4;
    %"v340" : W = (RawLoad (LdNarrow Uw) 0) %"chk60";
    %"v341" : W = Shl %"v340", #1;
    %"v342" : W = Shr %"v341", #21;
    %"v347" : W = (Cmp Eq W) %"v342", #0
    => br %"v347" ? "L343" : "L344" };
  ir_blk{ @"L343":
    => br %"v299" ? "L276" : "L349" };
  ir_blk{ @"L349":
    => goto "L276" };
  ir_blk{ @"L344":
    %"v357" : W = (Cmp Sge W) %"v342", #1023
    => br %"v357" ? "L353" : "L354" };
  ir_blk{ @"L353":
    %"v359" : W = Sub %"v342", #1023
    => goto "L276" };
  ir_blk{ @"L354":
    %"v361" : W = Sub %"v342", #1023;
    %"v362" : W = Neg %"v361"
    => goto "L276" };
  ir_blk{ @"L363":
    %"chk62" : A = (Check 0 10 Read 8) %"v8";
    %"v368" : Extended = (RawLoad LdX 0) %"chk62";
    %"chk63" : A = (CheckLocal (a "v367") 0 10 Write 8);
    store Wx [%"chk63" + 0] <- %"v368";
    %"chk64" : A = (CheckLocal (a "v367") 4 4 Read 1);
    %"v370" : W = (RawLoad (LdNarrow Uw) 0) %"chk64";
    %"v371" : L = (Ext Uw) %"v370";
    %"v372" : L = Shl %"v371", #32;
    %"chk65" : A = (CheckLocal (a "v367") 0 4 Read 1);
    %"v373" : W = (RawLoad (LdNarrow Uw) 0) %"chk65";
    %"v374" : L = (Ext Uw) %"v373";
    %"v375" : L = Or %"v372", %"v374";
    %"v377" : W = (Cmp Eq L) %"v375", #0;
    %"v383" = %"v22" +p #32;
    %"v385" = %"v4" +p #8;
    %"chk66" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v385";
    %"v386" : W = (RawLoad (LdNarrow Sw) 0) %"chk66";
    %"v387" : W = (Cmp Eq W) %"v386", #65;
    call %"v388" : P = $"_itoa_word"(L %"v375", P %"v383", W #16, W %"v387")
    => goto "L396" };
  ir_blk{ @"L396" [%"pr.14" : P = phi("L397" => %"v408", "L363" => %"v388")]:
    %"v403" = %"v22" +p #16;
    %"v404" : L = Ptoi %"pr.14";
    %"v405" : L = Ptoi %"v403";
    %"v406" : W = (Cmp Ugt L) %"v404", %"v405"
    => br %"v406" ? "L397" : "L398" };
  ir_blk{ @"L397":
    (Flight (a "v408") Sub [(FAddress (t "pr.14")); (FValue (Const 1))] (LowerOf (t "pr.14")));
    %"chk67" : A = (Check 0 1 Write 1) %"v408";
    store Wb [%"chk67" + 0] <- #48
    => goto poll "L396" };
  ir_blk{ @"L398":
    %"v410" = %"pr.14" +p #1;
    %"chk68" : A = (Check 0 1 Read 1) %"pr.14";
    %"v411" : W = (RawLoad (LdNarrow Sb) 0) %"chk68";
    %"chk69" : A = (CheckLocal (a "v367") 8 4 Read 1);
    %"v413" : W = (RawLoad (LdNarrow Uw) 0) %"chk69";
    %"v414" : W = Shl %"v413", #17;
    %"v415" : W = Shr %"v414", #17;
    %"v420" : W = (Cmp Eq W) %"v415", #0
    => br %"v420" ? "L416" : "L417" };
  ir_blk{ @"L416":
    => br %"v377" ? "L418" : "L422" };
  ir_blk{ @"L422":
    => goto "L418" };
  ir_blk{ @"L417":
    %"v432" : W = (Cmp Sge W) %"v415", #16386
    => br %"v432" ? "L427" : "L428" };
  ir_blk{ @"L427":
    %"v435" : W = Sub %"v415", #16386
    => goto "L418" };
  ir_blk{ @"L428":
    %"v438" : W = Sub %"v415", #16386;
    %"v439" : W = Neg %"v438"
    => goto "L418" };
  ir_blk{ @"L418" [%"pr.37" : W = phi("L422" => #16385, "L416" => %"v415", "L427" => %"v435", "L428" => %"v439"); %"pr.22" : W = phi("L422" => #1, "L416" => #0, "L427" => #0, "L428" => #1)]:
    => goto "L276" };
  ir_blk{ @"L276" [%"pr.49" : W = phi("L349" => %"v338", "L343" => %"v338", "L353" => %"v338", "L354" => %"v338", "L418" => %"v411"); %"pr.48" : W = phi("L349" => %"v299", "L343" => %"v299", "L353" => %"v299", "L354" => %"v299", "L418" => %"v377"); %"pr.33" : W = phi("L349" => #1022, "L343" => %"v342", "L353" => %"v359", "L354" => %"v362", "L418" => %"pr.37"); %"pr.18" : W = phi("L349" => #1, "L343" => #0, "L353" => #0, "L354" => #1, "L418" => %"pr.22"); %"pr.10" : P = phi("L349" => %"pr.12", "L343" => %"pr.12", "L353" => %"pr.12", "L354" => %"pr.12", "L418" => %"v410")]:
    => br %"pr.48" ? "L441" : "L440" };
  ir_blk{ @"L440":
    %"v448" = %"v22" +p #32
    => goto "L449" };
  ir_blk{ @"L449" [%"pr.16" : P = phi("L440" => %"v448", "L450" => %"v459")]:
    %"v455" = %"pr.16" +p #18446744073709551615;
    %"chk70" : A = (Check 0 1 Read 1) %"v455";
    %"v456" : W = (RawLoad (LdNarrow Sb) 0) %"chk70";
    %"v457" : W = (Cmp Eq W) %"v456", #48
    => br %"v457" ? "L450" : "L451" };
  ir_blk{ @"L450":
    (Flight (a "v459") Sub [(FAddress (t "pr.16")); (FValue (Const 1))] (LowerOf (t "pr.16")))
    => goto poll "L449" };
  ir_blk{ @"L451":
    %"v467" : W = (Cmp Ne W) %"v34", #4294967295
    => br %"v467" ? "L468" : "L469" };
  ir_blk{ @"L468":
    %"v473" : L = Ptoi %"pr.16";
    %"v474" : L = Ptoi %"pr.10";
    %"v475" : L = Sub %"v473", %"v474";
    %"v476" : L = (Ext Sw) %"v34";
    %"v477" : W = (Cmp Slt L) %"v476", %"v475"
    => goto "L469" };
  ir_blk{ @"L469" [%"v479" : W = phi("L451" => #0, "L468" => %"v477")]:
    => br %"v479" ? "L462" : "L464" };
  ir_blk{ @"L462":
    %"v485" : W = (Cmp Sgt W) %"v34", #0
    => br %"v485" ? "L481" : "L482" };
  ir_blk{ @"L481":
    %"v488" : W = Sub %"v34", #1;
    %"v489" : L = (Ext Sw) %"v488";
    %"v490" = %"pr.10" +p %"v489";
    %"chk71" : A = (Check 0 1 Read 1) %"v490";
    %"v491" : W = (RawLoad (LdNarrow Sb) 0) %"chk71"
    => goto "L483" };
  ir_blk{ @"L482":
    %"v492" : W = (Ext Sb) %"pr.49"
    => goto "L483" };
  ir_blk{ @"L483" [%"v493" : W = phi("L481" => %"v491", "L482" => %"v492")]:
    %"v494" : W = (Ext Sb) %"v493";
    %"v498" : L = (Ext Sw) %"v34";
    %"v499" = %"pr.10" +p %"v498";
    %"chk72" : A = (Check 0 1 Read 1) %"v499";
    %"v500" : W = (RawLoad (LdNarrow Sb) 0) %"chk72";
    %"v506" : W = (Cmp Sge W) %"v494", #65
    => br %"v506" ? "L507" : "L508" };
  ir_blk{ @"L507":
    %"v510" : W = (Cmp Sle W) %"v494", #70
    => goto "L508" };
  ir_blk{ @"L508" [%"v512" : W = phi("L483" => #0, "L507" => %"v510")]:
    => br %"v512" ? "L502" : "L503" };
  ir_blk{ @"L502":
    %"v514" : W = Sub %"v494", #65;
    %"v515" : W = Add %"v514", #10
    => goto "L504" };
  ir_blk{ @"L503":
    %"v520" : W = (Cmp Sge W) %"v494", #97
    => br %"v520" ? "L521" : "L522" };
  ir_blk{ @"L521":
    %"v524" : W = (Cmp Sle W) %"v494", #102
    => goto "L522" };
  ir_blk{ @"L522" [%"v526" : W = phi("L503" => #0, "L521" => %"v524")]:
    => br %"v526" ? "L516" : "L517" };
  ir_blk{ @"L516":
    %"v528" : W = Sub %"v494", #97;
    %"v529" : W = Add %"v528", #10
    => goto "L504" };
  ir_blk{ @"L517":
    %"v531" : W = Sub %"v494", #48
    => goto "L504" };
  ir_blk{ @"L504" [%"v533" : W = phi("L502" => %"v515", "L516" => %"v529", "L517" => %"v531")]:
    %"v539" : W = (Cmp Sge W) %"v500", #65
    => br %"v539" ? "L540" : "L541" };
  ir_blk{ @"L540":
    %"v543" : W = (Cmp Sle W) %"v500", #70
    => goto "L541" };
  ir_blk{ @"L541" [%"v545" : W = phi("L504" => #0, "L540" => %"v543")]:
    => br %"v545" ? "L535" : "L536" };
  ir_blk{ @"L535":
    %"v547" : W = Sub %"v500", #65;
    %"v548" : W = Add %"v547", #10
    => goto "L537" };
  ir_blk{ @"L536":
    %"v553" : W = (Cmp Sge W) %"v500", #97
    => br %"v553" ? "L554" : "L555" };
  ir_blk{ @"L554":
    %"v557" : W = (Cmp Sle W) %"v500", #102
    => goto "L555" };
  ir_blk{ @"L555" [%"v559" : W = phi("L536" => #0, "L554" => %"v557")]:
    => br %"v559" ? "L549" : "L550" };
  ir_blk{ @"L549":
    %"v561" : W = Sub %"v500", #97;
    %"v562" : W = Add %"v561", #10
    => goto "L537" };
  ir_blk{ @"L550":
    %"v564" : W = Sub %"v500", #48
    => goto "L537" };
  ir_blk{ @"L537" [%"v566" : W = phi("L535" => %"v548", "L549" => %"v562", "L550" => %"v564")]:
    %"v569" : W = And %"v566", #7;
    %"v570" : W = (Cmp Ne W) %"v569", #0
    => br %"v570" ? "L572" : "L571" }]) (app [ir_blk{ @"L571":
    %"v574" : W = Add %"v34", #1;
    %"v577" : L = Ptoi %"pr.16";
    %"v578" : L = Ptoi %"pr.10";
    %"v579" : L = Sub %"v577", %"v578";
    %"v580" : L = (Ext Sw) %"v574";
    %"v581" : W = (Cmp Slt L) %"v580", %"v579"
    => goto "L572" };
  ir_blk{ @"L572" [%"v583" : W = phi("L537" => #1, "L571" => %"v581")]:
    call %"iw_11.v7" : W = $"zmath_getcw"();
    %"iw_11.v8" : W = (Ext Uh) %"iw_11.v7";
    %"iw_11.v11" : W = And %"iw_11.v8", #3072;
    %"iw_11.v19" : W = (Cmp Eq W) %"iw_11.v11", #1024
    => br %"iw_11.v19" ? "iw_11.join" : "iw_11.L20" };
  ir_blk{ @"iw_11.L18":
    call void $"__GI_abort"()
    => goto "iw_11.join" };
  ir_blk{ @"iw_11.L20":
    %"iw_11.v21" : W = (Cmp Eq W) %"iw_11.v11", #0
    => br %"iw_11.v21" ? "iw_11.join" : "iw_11.L22" };
  ir_blk{ @"iw_11.L22":
    %"iw_11.v23" : W = (Cmp Eq W) %"iw_11.v11", #3072
    => br %"iw_11.v23" ? "iw_11.join" : "iw_11.L24" };
  ir_blk{ @"iw_11.L24":
    %"iw_11.v25" : W = (Cmp Eq W) %"iw_11.v11", #2048
    => br %"iw_11.v25" ? "iw_11.join" : poll "iw_11.L18" };
  ir_blk{ @"iw_11.join" [%"v586" : W = phi("iw_11.L18" => #0, "L572" => #1024, "iw_11.L20" => #0, "iw_11.L22" => #3072, "iw_11.L24" => #2048)]:
    %"v588" : W = (Cmp Ne W) %"pr.17", #0;
    %"v590" : W = And %"v533", #1;
    %"v593" : W = (Cmp Sge W) %"v566", #8;
    %"iw_12.v56" : W = (Cmp Eq W) %"v586", #1024
    => br %"iw_12.v56" ? "iw_12.L13" : "iw_12.L57" };
  ir_blk{ @"iw_12.L13":
    => br %"v588" ? "iw_12.L15" : "L464" };
  ir_blk{ @"iw_12.L15":
    => br %"v593" ? "L464" : "iw_12.L18" };
  ir_blk{ @"iw_12.L18":
    => goto "L464" };
  ir_blk{ @"iw_12.L26":
    => br %"v593" ? "iw_12.L28" : "L464" };
  ir_blk{ @"iw_12.L28":
    => br %"v590" ? "L464" : "iw_12.L31" };
  ir_blk{ @"iw_12.L31":
    => goto "L464" };
  ir_blk{ @"iw_12.L41":
    %"iw_12.v43" : W = (Cmp Eq W) %"pr.17", #0
    => br %"iw_12.v43" ? "iw_12.L44" : "L464" };
  ir_blk{ @"iw_12.L44":
    => br %"v593" ? "L464" : "iw_12.L47" };
  ir_blk{ @"iw_12.L47":
    => goto "L464" };
  ir_blk{ @"iw_12.L55":
    call void $"__GI_abort"()
    => goto "L464" };
  ir_blk{ @"iw_12.L57":
    %"iw_12.v58" : W = (Cmp Eq W) %"v586", #0
    => br %"iw_12.v58" ? poll "iw_12.L26" : "iw_12.L59" };
  ir_blk{ @"iw_12.L59":
    %"iw_12.v60" : W = (Cmp Eq W) %"v586", #3072
    => br %"iw_12.v60" ? "L464" : "iw_12.L61" };
  ir_blk{ @"iw_12.L61":
    %"iw_12.v62" : W = (Cmp Eq W) %"v586", #2048
    => br %"iw_12.v62" ? poll "iw_12.L41" : poll "iw_12.L55" };
  ir_blk{ @"L464" [%"pr.61" : W = phi("iw_12.L55" => #0, "iw_12.L13" => #0, "iw_12.L15" => #1, "iw_12.L18" => %"v583", "iw_12.L26" => #0, "iw_12.L28" => #1, "iw_12.L31" => %"v583", "iw_12.L59" => #0, "iw_12.L41" => #0, "iw_12.L44" => #1, "iw_12.L47" => %"v583", "L469" => #0)]:
    %"v604" : W = (Cmp Eq W) %"v34", #4294967295
    => br %"v604" ? "L599" : "L600" };
  ir_blk{ @"L599":
    %"v607" : L = Ptoi %"pr.16";
    %"v608" : L = Ptoi %"pr.10";
    %"v609" : L = Sub %"v607", %"v608"
    => goto "L442" };
  ir_blk{ @"L600":
    => br %"pr.61" ? "L616" : "L442" };
  ir_blk{ @"L616" [%"pr.62" : W = phi("L600" => %"v34", "L643" => %"v620")]:
    %"v620" : W = Sub %"pr.62", #1;
    %"v621" : W = (Cmp Sge W) %"v620", #0
    => br %"v621" ? "L617" : "L618" };
  ir_blk{ @"L617":
    %"v625" : L = (Ext Sw) %"v620";
    %"v626" = %"pr.10" +p %"v625";
    %"chk73" : A = (Check 0 1 Read 1) %"v626";
    %"v627" : W = (RawLoad (LdNarrow Sb) 0) %"chk73";
    %"v632" : W = (Cmp Eq W) %"v627", #57
    => br %"v632" ? "L628" : "iw_14.start" };
  ir_blk{ @"L628":
    %"v638" = %"v4" +p #8;
    %"chk74" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v638";
    %"v639" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"v640" : W = (Ext Sb) %"v639";
    %"chk75" : A = (Renew 0 1 Write 1) %"chk73", %"v626";
    store Wb [%"chk75" + 0] <- %"v640"
    => goto "L618" };
  ir_blk{ @"iw_14.start":
    %"iw_14.v0" : P = Copy $"__libc_tsd_CTYPE_TOLOWER";
    %"chk76" : A = (Check 0 8 Read 8) %"iw_14.v0";
    %"v679" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v681" : L = (Ext Sw) %"v627";
    %"v682" : L = Shl %"v681", #2;
    %"v683" = %"v679" +p %"v682";
    %"chk77" : A = (Check 0 4 Read 1) %"v683";
    %"v684" : W = (RawLoad (LdNarrow Sw) 0) %"chk77";
    %"v686" : W = (Cmp Slt W) %"v684", #102
    => br %"v686" ? "L642" : "L643" };
  ir_blk{ @"L642":
    %"chk78" : A = (Renew 0 1 Read 1) %"chk73", %"v626";
    %"v691" : W = (RawLoad (LdNarrow Sb) 0) %"chk78";
    %"v692" : W = Add %"v691", #1;
    %"v693" : W = (Ext Sb) %"v692";
    %"chk79" : A = (Renew 0 1 Write 1) %"chk73", %"v626";
    store Wb [%"chk79" + 0] <- %"v693"
    => goto "L618" };
  ir_blk{ @"L643":
    %"chk80" : A = (Renew 0 1 Write 1) %"chk73", %"v626";
    store Wb [%"chk80" + 0] <- #48
    => goto poll "L616" };
  ir_blk{ @"L618":
    %"v703" : W = (Cmp Slt W) %"v620", #0
    => br %"v703" ? "L699" : "L442" };
  ir_blk{ @"L699":
    %"v707" : W = (Ext Sb) %"pr.49";
    %"v708" : W = (Cmp Eq W) %"v707", #57
    => br %"v708" ? "L704" : "iw_16.start" };
  ir_blk{ @"L704":
    %"v710" = %"v4" +p #8;
    %"chk81" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v710";
    %"v711" : W = (RawLoad (LdNarrow Sw) 0) %"chk81";
    %"v712" : W = (Ext Sb) %"v711"
    => goto "L442" };
  ir_blk{ @"iw_16.start":
    %"iw_16.v0" : P = Copy $"__libc_tsd_CTYPE_TOLOWER";
    %"chk82" : A = (Check 0 8 Read 8) %"iw_16.v0";
    %"v750" : P = (RawLoadPointer 0 load_effects) %"chk82";
    %"v752" : L = (Ext Sw) %"v707";
    %"v753" : L = Shl %"v752", #2;
    %"v754" = %"v750" +p %"v753";
    %"chk83" : A = (Check 0 4 Read 1) %"v754";
    %"v755" : W = (RawLoad (LdNarrow Sw) 0) %"chk83";
    %"v757" : W = (Cmp Slt W) %"v755", #102
    => br %"v757" ? "L713" : "L714" };
  ir_blk{ @"L713":
    %"v759" : W = Add %"v707", #1;
    %"v760" : W = (Ext Sb) %"v759"
    => goto "L442" };
  ir_blk{ @"L714":
    => br %"pr.18" ? "L761" : "L762" };
  ir_blk{ @"L761":
    %"v766" : W = Sub %"pr.33", #4;
    %"v771" : W = (Cmp Sle W) %"v766", #0
    => br %"v771" ? "L767" : "L442" };
  ir_blk{ @"L767":
    %"v773" : W = Neg %"v766"
    => goto "L442" };
  ir_blk{ @"L762":
    %"v775" : W = Add %"pr.33", #4
    => goto "L442" };
  ir_blk{ @"L441":
    %"v781" : W = (Cmp Eq W) %"v34", #4294967295
    => br %"v781" ? "L442" : "L777" };
  ir_blk{ @"L777":
    => goto "L442" };
  ir_blk{ @"L442" [%"pr.56" : W = phi("L599" => %"v609", "L704" => %"v34", "L713" => %"v34", "L762" => %"v34", "L767" => %"v34", "L761" => %"v34", "L618" => %"v34", "L600" => %"v34", "L777" => %"v34", "L441" => #0); %"pr.50" : W = phi("L599" => %"pr.49", "L704" => %"v712", "L713" => %"v760", "L762" => #49, "L767" => #49, "L761" => #49, "L618" => %"pr.49", "L600" => %"pr.49", "L777" => %"pr.49", "L441" => %"pr.49"); %"pr.40" : W = phi("L599" => %"pr.33", "L704" => %"pr.33", "L713" => %"pr.33", "L762" => %"v775", "L767" => %"v773", "L761" => %"v766", "L618" => %"pr.33", "L600" => %"pr.33", "L777" => %"pr.33", "L441" => %"pr.33"); %"pr.25" : W = phi("L599" => %"pr.18", "L704" => %"pr.18", "L713" => %"pr.18", "L762" => %"pr.18", "L767" => #0, "L761" => %"pr.18", "L618" => %"pr.18", "L600" => %"pr.18", "L777" => %"pr.18", "L441" => %"pr.18"); %"pr.15" : P = phi("L599" => %"pr.16", "L704" => %"pr.16", "L713" => %"pr.16", "L762" => %"pr.16", "L767" => %"pr.16", "L761" => %"pr.16", "L618" => %"pr.16", "L600" => %"pr.16", "L777" => %"pr.10", "L441" => %"pr.10")]:
    %"v784" : L = (Ext Sw) %"pr.40";
    %"v785" = %"v26" +p #5;
    call %"v786" : P = $"_itoa_word"(L %"v784", P %"v785", W #10, W #0)
    => br %"pr.17" ? "L790" : "L789" };
  ir_blk{ @"L789":
    %"v792" = %"v4" +p #12;
    %"chk84" : A = (Renew 0 4 Read 1) %"chk0", %"v792";
    %"v793" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
    %"v794" : W = Shl %"v793", #25;
    %"v795" : W = Shr %"v794", #31;
    %"v796" : W = (Cmp Ne W) %"v795", #0
    => goto "L790" };
  ir_blk{ @"L790" [%"v797" : W = phi("L442" => #1, "L789" => %"v796")]:
    => br %"v797" ? "L799" : "L798" };
  ir_blk{ @"L798":
    %"v801" = %"v4" +p #12;
    %"chk85" : A = (Renew 0 4 Read 1) %"chk0", %"v801";
    %"v802" : W = (RawLoad (LdNarrow Uw) 0) %"chk85";
    %"v803" : W = Shl %"v802", #27;
    %"v804" : W = Shr %"v803", #31;
    %"v805" : W = (Cmp Ne W) %"v804", #0
    => goto "L799" };
  ir_blk{ @"L799" [%"v806" : W = phi("L790" => #1, "L798" => %"v805")]:
    %"v807" : W = Add %"v806", #2;
    %"v808" : W = Add %"v807", #1;
    %"v811" : W = Add %"v808", %"pr.56";
    %"v812" : W = Add %"v811", #1;
    %"v813" : W = Add %"v812", #1;
    %"v814" = %"v26" +p #5;
    %"v816" : L = Ptoi %"v814";
    %"v817" : L = Ptoi %"v786";
    %"v818" : L = Sub %"v816", %"v817";
    %"v819" : L = (Ext Sw) %"v813";
    %"v820" : L = Add %"v819", %"v818";
    %"v821" : L = (Ext Sw) %"v38";
    %"v822" : L = Sub %"v821", %"v820";
    %"v827" : W = (Cmp Sgt W) %"pr.56", #0
    => br %"v827" ? "L829" : "L828" };
  ir_blk{ @"L828":
    %"v831" = %"v4" +p #12;
    %"chk86" : A = (Renew 0 4 Read 1) %"chk0", %"v831";
    %"v832" : W = (RawLoad (LdNarrow Uw) 0) %"chk86";
    %"v833" : W = Shl %"v832", #28;
    %"v834" : W = Shr %"v833", #31;
    %"v835" : W = (Cmp Ne W) %"v834", #0
    => goto "L829" };
  ir_blk{ @"L829" [%"v836" : W = phi("L799" => #1, "L828" => %"v835")]:
    => br %"v836" ? "L823" : "L825" };
  ir_blk{ @"L823":
    %"v837" : W = Copy %"v822";
    %"v838" : W = Sub %"v837", #1
    => goto "L825" };
  ir_blk{ @"L825" [%"pr.59" : W = phi("L823" => %"v838", "L829" => %"v822")]:
    %"v843" = %"v4" +p #12;
    %"chk87" : A = (Renew 0 4 Read 1) %"chk0", %"v843";
    %"v844" : W = (RawLoad (LdNarrow Uw) 0) %"chk87";
    %"v845" : W = Shl %"v844", #26;
    %"v846" : W = Shr %"v845", #31;
    %"v847" : W = (Cmp Eq W) %"v846", #0
    => br %"v847" ? "L848" : "L849" };
  ir_blk{ @"L848":
    %"v851" = %"v4" +p #16;
    %"chk88" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v851";
    %"v852" : W = (RawLoad (LdNarrow Sw) 0) %"chk88";
    %"v853" : W = (Cmp Ne W) %"v852", #48
    => goto "L849" };
  ir_blk{ @"L849" [%"v855" : W = phi("L825" => #0, "L848" => %"v853")]:
    => br %"v855" ? "L839" : "L841" }] [ir_blk{ @"L839":
    %"v858" : L = (Ext Sw) %"pr.59";
    %"iw_17.v10" : W = (Cmp Sgt L) %"v858", #0
    => br %"iw_17.v10" ? "iw_17.L6" : "L841" };
  ir_blk{ @"iw_17.L6":
    call void $"__printf_buffer_pad_1"(P %"v0", W #32, L %"v858")
    => goto "L841" };
  ir_blk{ @"L841":
    => br %"pr.17" ? "iw_18.start" : "L860" };
  ir_blk{ @"iw_18.start":
    %"iw_18.v8" = %"v0" +p #8;
    %"chk89" : A = (Check 0 8 Read 8) %"iw_18.v8";
    %"iw_18.v9" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"iw_18.v11" = %"v0" +p #16;
    %"chk90" : A = (HalfCheck Upper 0 8 Read 8) %"chk89", %"iw_18.v11";
    %"iw_18.v12" : P = (RawLoadPointer 0 load_effects) %"chk90";
    %"iw_18.v13" : L = Ptoi %"iw_18.v9";
    %"iw_18.v14" : L = Ptoi %"iw_18.v12";
    %"iw_18.v15" : W = (Cmp Ne L) %"iw_18.v13", %"iw_18.v14"
    => br %"iw_18.v15" ? "iw_18.L4" : "iw_18.L5" };
  ir_blk{ @"iw_18.L4":
    %"iw_18.v17" = %"v0" +p #8;
    %"iw_18.v18" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"iw_18.v19" = %"iw_18.v18" +p #1;
    %"chk92" : A = (Renew 0 8 Write 8) %"chk89", %"iw_18.v17";
    store.ptr [%"chk92" + 0] <- %"iw_18.v19";
    %"chk93" : A = (Check 0 1 Write 1) %"iw_18.v18";
    store Wb [%"chk93" + 0] <- #45
    => goto "iw_21.start" };
  ir_blk{ @"iw_18.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #45)
    => goto "iw_21.start" };
  ir_blk{ @"L860":
    %"v868" = %"v4" +p #12;
    %"chk94" : A = (Renew 0 4 Read 1) %"chk0", %"v868";
    %"v869" : W = (RawLoad (LdNarrow Uw) 0) %"chk94";
    %"v870" : W = Shl %"v869", #25;
    %"v871" : W = Shr %"v870", #31
    => br %"v871" ? "iw_19.start" : "L865" };
  ir_blk{ @"iw_19.start":
    %"iw_19.v8" = %"v0" +p #8;
    %"chk95" : A = (Check 0 8 Read 8) %"iw_19.v8";
    %"iw_19.v9" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"iw_19.v11" = %"v0" +p #16;
    %"chk96" : A = (HalfCheck Upper 0 8 Read 8) %"chk95", %"iw_19.v11";
    %"iw_19.v12" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"iw_19.v13" : L = Ptoi %"iw_19.v9";
    %"iw_19.v14" : L = Ptoi %"iw_19.v12";
    %"iw_19.v15" : W = (Cmp Ne L) %"iw_19.v13", %"iw_19.v14"
    => br %"iw_19.v15" ? "iw_19.L4" : "iw_19.L5" };
  ir_blk{ @"iw_19.L4":
    %"iw_19.v17" = %"v0" +p #8;
    %"iw_19.v18" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"iw_19.v19" = %"iw_19.v18" +p #1;
    %"chk98" : A = (Renew 0 8 Write 8) %"chk95", %"iw_19.v17";
    store.ptr [%"chk98" + 0] <- %"iw_19.v19";
    %"chk99" : A = (Check 0 1 Write 1) %"iw_19.v18";
    store Wb [%"chk99" + 0] <- #43
    => goto "iw_21.start" };
  ir_blk{ @"iw_19.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #43)
    => goto "iw_21.start" };
  ir_blk{ @"L865":
    %"v877" = %"v4" +p #12;
    %"v878" : W = (RawLoad (LdNarrow Uw) 0) %"chk94";
    %"v879" : W = Shl %"v878", #27;
    %"v880" : W = Shr %"v879", #31
    => br %"v880" ? "iw_20.start" : "iw_21.start" };
  ir_blk{ @"iw_20.start":
    %"iw_20.v8" = %"v0" +p #8;
    %"chk101" : A = (Check 0 8 Read 8) %"iw_20.v8";
    %"iw_20.v9" : P = (RawLoadPointer 0 load_effects) %"chk101";
    %"iw_20.v11" = %"v0" +p #16;
    %"chk102" : A = (HalfCheck Upper 0 8 Read 8) %"chk101", %"iw_20.v11";
    %"iw_20.v12" : P = (RawLoadPointer 0 load_effects) %"chk102";
    %"iw_20.v13" : L = Ptoi %"iw_20.v9";
    %"iw_20.v14" : L = Ptoi %"iw_20.v12";
    %"iw_20.v15" : W = (Cmp Ne L) %"iw_20.v13", %"iw_20.v14"
    => br %"iw_20.v15" ? "iw_20.L4" : "iw_20.L5" };
  ir_blk{ @"iw_20.L4":
    %"iw_20.v17" = %"v0" +p #8;
    %"iw_20.v18" : P = (RawLoadPointer 0 load_effects) %"chk101";
    %"iw_20.v19" = %"iw_20.v18" +p #1;
    %"chk104" : A = (Renew 0 8 Write 8) %"chk101", %"iw_20.v17";
    store.ptr [%"chk104" + 0] <- %"iw_20.v19";
    %"chk105" : A = (Check 0 1 Write 1) %"iw_20.v18";
    store Wb [%"chk105" + 0] <- #32
    => goto "iw_21.start" };
  ir_blk{ @"iw_20.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #32)
    => goto "iw_21.start" };
  ir_blk{ @"iw_21.start":
    %"iw_21.v8" = %"v0" +p #8;
    %"chk106" : A = (Check 0 8 Read 8) %"iw_21.v8";
    %"iw_21.v9" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"iw_21.v11" = %"v0" +p #16;
    %"chk107" : A = (HalfCheck Upper 0 8 Read 8) %"chk106", %"iw_21.v11";
    %"iw_21.v12" : P = (RawLoadPointer 0 load_effects) %"chk107";
    %"iw_21.v13" : L = Ptoi %"iw_21.v9";
    %"iw_21.v14" : L = Ptoi %"iw_21.v12";
    %"iw_21.v15" : W = (Cmp Ne L) %"iw_21.v13", %"iw_21.v14"
    => br %"iw_21.v15" ? "iw_21.L4" : "iw_21.L5" };
  ir_blk{ @"iw_21.L4":
    %"iw_21.v17" = %"v0" +p #8;
    %"iw_21.v18" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"iw_21.v19" = %"iw_21.v18" +p #1;
    %"chk109" : A = (Renew 0 8 Write 8) %"chk106", %"iw_21.v17";
    store.ptr [%"chk109" + 0] <- %"iw_21.v19";
    %"chk110" : A = (Check 0 1 Write 1) %"iw_21.v18";
    store Wb [%"chk110" + 0] <- #48
    => goto "L883" };
  ir_blk{ @"iw_21.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W #48)
    => goto "L883" };
  ir_blk{ @"L883":
    %"v891" = %"v4" +p #8;
    %"chk111" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v891";
    %"v892" : W = (RawLoad (LdNarrow Sw) 0) %"chk111";
    %"v894" : W = Add %"v892", #23;
    %"v895" : W = (Ext Sb) %"v894";
    %"iw_22.v8" = %"v0" +p #8;
    %"chk112" : A = (Renew 0 8 Read 8) %"chk106", %"iw_22.v8";
    %"iw_22.v9" : P = (RawLoadPointer 0 load_effects) %"chk112";
    %"iw_22.v11" = %"v0" +p #16;
    %"chk113" : A = (Renew 0 8 Read 8) %"chk107", %"iw_22.v11";
    %"iw_22.v12" : P = (RawLoadPointer 0 load_effects) %"chk113";
    %"iw_22.v13" : L = Ptoi %"iw_22.v9";
    %"iw_22.v14" : L = Ptoi %"iw_22.v12";
    %"iw_22.v15" : W = (Cmp Ne L) %"iw_22.v13", %"iw_22.v14"
    => br %"iw_22.v15" ? "iw_22.L4" : "iw_22.L5" };
  ir_blk{ @"iw_22.L4":
    %"iw_22.v17" = %"v0" +p #8;
    %"iw_22.v18" : P = (RawLoadPointer 0 load_effects) %"chk112";
    %"iw_22.v19" = %"iw_22.v18" +p #1;
    %"chk115" : A = (Renew 0 8 Write 8) %"chk106", %"iw_22.v17";
    store.ptr [%"chk115" + 0] <- %"iw_22.v19";
    %"chk116" : A = (Check 0 1 Write 1) %"iw_22.v18";
    store Wb [%"chk116" + 0] <- %"v895"
    => goto "L885" };
  ir_blk{ @"iw_22.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W %"v895")
    => goto "L885" };
  ir_blk{ @"L885":
    %"v910" = %"v4" +p #12;
    %"chk117" : A = (Renew 0 4 Read 1) %"chk0", %"v910";
    %"v911" : W = (RawLoad (LdNarrow Uw) 0) %"chk117";
    %"v912" : W = Shl %"v911", #26;
    %"v913" : W = Shr %"v912", #31;
    %"v914" : W = (Cmp Eq W) %"v913", #0
    => br %"v914" ? "L915" : "L916" };
  ir_blk{ @"L915":
    %"v918" = %"v4" +p #16;
    %"chk118" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v918";
    %"v919" : W = (RawLoad (LdNarrow Sw) 0) %"chk118";
    %"v920" : W = (Cmp Eq W) %"v919", #48
    => goto "L916" };
  ir_blk{ @"L916" [%"v922" : W = phi("L885" => #0, "L915" => %"v920")]:
    => br %"v922" ? "L906" : "L908" };
  ir_blk{ @"L906":
    %"v925" : L = (Ext Sw) %"pr.59";
    %"iw_24.v10" : W = (Cmp Sgt L) %"v925", #0
    => br %"iw_24.v10" ? "iw_24.L6" : "L908" };
  ir_blk{ @"iw_24.L6":
    call void $"__printf_buffer_pad_1"(P %"v0", W #48, L %"v925")
    => goto "L908" };
  ir_blk{ @"L908":
    %"v927" : W = (Ext Sb) %"pr.50";
    %"iw_25.v8" = %"v0" +p #8;
    %"chk119" : A = (Renew 0 8 Read 8) %"chk106", %"iw_25.v8";
    %"iw_25.v9" : P = (RawLoadPointer 0 load_effects) %"chk119";
    %"iw_25.v11" = %"v0" +p #16;
    %"chk120" : A = (Renew 0 8 Read 8) %"chk107", %"iw_25.v11";
    %"iw_25.v12" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_25.v13" : L = Ptoi %"iw_25.v9";
    %"iw_25.v14" : L = Ptoi %"iw_25.v12";
    %"iw_25.v15" : W = (Cmp Ne L) %"iw_25.v13", %"iw_25.v14"
    => br %"iw_25.v15" ? "iw_25.L4" : "iw_25.L5" };
  ir_blk{ @"iw_25.L4":
    %"iw_25.v17" = %"v0" +p #8;
    %"iw_25.v18" : P = (RawLoadPointer 0 load_effects) %"chk119";
    %"iw_25.v19" = %"iw_25.v18" +p #1;
    %"chk122" : A = (Renew 0 8 Write 8) %"chk106", %"iw_25.v17";
    store.ptr [%"chk122" + 0] <- %"iw_25.v19";
    %"chk123" : A = (Check 0 1 Write 1) %"iw_25.v18";
    store Wb [%"chk123" + 0] <- %"v927"
    => goto "iw_25.join" };
  ir_blk{ @"iw_25.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W %"v927")
    => goto "iw_25.join" };
  ir_blk{ @"iw_25.join":
    => br %"v827" ? "L934" : "L933" };
  ir_blk{ @"L933":
    %"v936" = %"v4" +p #12;
    %"chk124" : A = (Renew 0 4 Read 1) %"chk0", %"v936";
    %"v937" : W = (RawLoad (LdNarrow Uw) 0) %"chk124";
    %"v938" : W = Shl %"v937", #28;
    %"v939" : W = Shr %"v938", #31;
    %"v940" : W = (Cmp Ne W) %"v939", #0
    => goto "L934" };
  ir_blk{ @"L934" [%"v941" : W = phi("iw_25.join" => #1, "L933" => %"v940")]:
    => br %"v941" ? "iw_26.start" : "L930" };
  ir_blk{ @"iw_26.start":
    call void $"__printf_buffer_puts_1"(P %"v0", P %"v2")
    => goto "L930" };
  ir_blk{ @"L930":
    => br %"v827" ? "L944" : "L981" };
  ir_blk{ @"L944":
    %"v953" : L = Ptoi %"pr.15";
    %"v954" : L = Ptoi %"pr.10";
    %"v955" : L = Sub %"v953", %"v954";
    %"v956" : L = (Ext Sw) %"pr.56";
    %"v957" : L = Sub %"v956", %"v955";
    %"v970" : W = (Cmp Slt L) %"v955", %"v956"
    => br %"v970" ? "L962" : "L961" };
  ir_blk{ @"L961":
    => goto "L962" };
  ir_blk{ @"L962" [%"v978" : L = phi("L961" => %"v956", "L944" => %"v955")]:
    call void $"__printf_buffer_write"(P %"v0", P %"pr.10", L %"v978");
    %"iw_27.v10" : W = (Cmp Sgt L) %"v957", #0
    => br %"iw_27.v10" ? "iw_27.L6" : "L981" };
  ir_blk{ @"iw_27.L6":
    call void $"__printf_buffer_pad_1"(P %"v0", W #48, L %"v957")
    => goto "L981" };
  ir_blk{ @"L981":
    %"v989" = %"v4" +p #8;
    %"chk125" : A = (Renew 0 4 Read 1) %"chk111", %"v989";
    %"v990" : W = (RawLoad (LdNarrow Sw) 0) %"chk125";
    %"v992" : W = Add %"v990", #15;
    %"v993" : W = (Ext Sb) %"v992";
    %"iw_28.v8" = %"v0" +p #8;
    %"chk126" : A = (Renew 0 8 Read 8) %"chk106", %"iw_28.v8";
    %"iw_28.v9" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"iw_28.v11" = %"v0" +p #16;
    %"chk127" : A = (Renew 0 8 Read 8) %"chk107", %"iw_28.v11";
    %"iw_28.v12" : P = (RawLoadPointer 0 load_effects) %"chk127";
    %"iw_28.v13" : L = Ptoi %"iw_28.v9";
    %"iw_28.v14" : L = Ptoi %"iw_28.v12";
    %"iw_28.v15" : W = (Cmp Ne L) %"iw_28.v13", %"iw_28.v14"
    => br %"iw_28.v15" ? "iw_28.L4" : "iw_28.L5" };
  ir_blk{ @"iw_28.L4":
    %"iw_28.v17" = %"v0" +p #8;
    %"iw_28.v18" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"iw_28.v19" = %"iw_28.v18" +p #1;
    %"chk129" : A = (Renew 0 8 Write 8) %"chk106", %"iw_28.v17";
    store.ptr [%"chk129" + 0] <- %"iw_28.v19";
    %"chk130" : A = (Check 0 1 Write 1) %"iw_28.v18";
    store Wb [%"chk130" + 0] <- %"v993"
    => goto "L983" };
  ir_blk{ @"iw_28.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W %"v993")
    => goto "L983" };
  ir_blk{ @"L983":
    => br %"pr.25" ? "L1007" : "L1006" };
  ir_blk{ @"L1006":
    => goto "L1007" };
  ir_blk{ @"L1007" [%"v1009" : W = phi("L1006" => #43, "L983" => #45)]:
    %"v1010" : W = (Ext Sb) %"v1009";
    %"iw_30.v8" = %"v0" +p #8;
    %"chk131" : A = (Renew 0 8 Read 8) %"chk106", %"iw_30.v8";
    %"iw_30.v9" : P = (RawLoadPointer 0 load_effects) %"chk131";
    %"iw_30.v11" = %"v0" +p #16;
    %"chk132" : A = (Renew 0 8 Read 8) %"chk107", %"iw_30.v11";
    %"iw_30.v12" : P = (RawLoadPointer 0 load_effects) %"chk132";
    %"iw_30.v13" : L = Ptoi %"iw_30.v9";
    %"iw_30.v14" : L = Ptoi %"iw_30.v12";
    %"iw_30.v15" : W = (Cmp Ne L) %"iw_30.v13", %"iw_30.v14"
    => br %"iw_30.v15" ? "iw_30.L4" : "iw_30.L5" };
  ir_blk{ @"iw_30.L4":
    %"iw_30.v17" = %"v0" +p #8;
    %"iw_30.v18" : P = (RawLoadPointer 0 load_effects) %"chk131";
    %"iw_30.v19" = %"iw_30.v18" +p #1;
    %"chk134" : A = (Renew 0 8 Write 8) %"chk106", %"iw_30.v17";
    store.ptr [%"chk134" + 0] <- %"iw_30.v19";
    %"chk135" : A = (Check 0 1 Write 1) %"iw_30.v18";
    store Wb [%"chk135" + 0] <- %"v1010"
    => goto "iw_30.join" };
  ir_blk{ @"iw_30.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W %"v1010")
    => goto "iw_30.join" };
  ir_blk{ @"iw_30.join":
    %"v1013" = %"v26" +p #5;
    %"v1015" : L = Ptoi %"v1013";
    %"v1017" : L = Sub %"v1015", %"v817";
    call void $"__printf_buffer_write"(P %"v0", P %"v786", L %"v1017");
    %"v1022" = %"v4" +p #12;
    %"chk136" : A = (Renew 0 4 Read 1) %"chk0", %"v1022";
    %"v1023" : W = (RawLoad (LdNarrow Uw) 0) %"chk136";
    %"v1024" : W = Shl %"v1023", #26;
    %"v1025" : W = Shr %"v1024", #31
    => br %"v1025" ? "L1026" : "L1027" };
  ir_blk{ @"L1026":
    %"v1029" = %"v4" +p #16;
    %"chk137" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1029";
    %"v1030" : W = (RawLoad (LdNarrow Sw) 0) %"chk137";
    %"v1031" : W = (Cmp Ne W) %"v1030", #48
    => goto "L1027" };
  ir_blk{ @"L1027" [%"v1033" : W = phi("iw_30.join" => #0, "L1026" => %"v1031")]:
    => br %"v1033" ? "L1018" : "L1020" };
  ir_blk{ @"L1018":
    %"v1036" = %"v4" +p #16;
    %"chk138" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v1036";
    %"v1037" : W = (RawLoad (LdNarrow Sw) 0) %"chk138";
    %"v1038" : W = (Ext Sb) %"v1037";
    %"v1040" : L = (Ext Sw) %"pr.59";
    %"iw_31.v10" : W = (Cmp Sgt L) %"v1040", #0
    => br %"iw_31.v10" ? "iw_31.L6" : "L1020" };
  ir_blk{ @"iw_31.L6":
    call void $"__printf_buffer_pad_1"(P %"v0", W %"v1038", L %"v1040")
    => goto "L1020" };
  ir_blk{ @"L1020":
    => ret void }]))) }.

Definition item_glibc_printf_fphex'23str'2e287 : item :=
  (IData (a "glibc_printf_fphex#str.287") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 111); (Item Wb 45); (Item Wb 62); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 114); (Item Wb 97); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_printf_fphex'23str'2e288 : item :=
  (IData (a "glibc_printf_fphex#str.288") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 116); (Item Wb 100); (Item Wb 105); (Item Wb 111); (Item Wb 45); (Item Wb 99); (Item Wb 111); (Item Wb 109); (Item Wb 109); (Item Wb 111); (Item Wb 110); (Item Wb 47); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 104); (Item Wb 101); (Item Wb 120); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_fphex'23str'2e289 : item :=
  (IData (a "glibc_printf_fphex#str.289") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 104); (Item Wb 101); (Item Wb 120); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_printf_fphex'23str'2e290 : item :=
  (IData (a "glibc_printf_fphex#str.290") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 65); (Item Wb 78); (Item Wb 0)]).

Definition item_glibc_printf_fphex'23str'2e291 : item :=
  (IData (a "glibc_printf_fphex#str.291") (LRo (a "local")) 1 [(Item Wb 110); (Item Wb 97); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_printf_fphex'23str'2e292 : item :=
  (IData (a "glibc_printf_fphex#str.292") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 78); (Item Wb 70); (Item Wb 0)]).

Definition item_glibc_printf_fphex'23str'2e293 : item :=
  (IData (a "glibc_printf_fphex#str.293") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 0)]).

Definition item_glibc_printf_fphex'23str'2e295 : item :=
  (IData (a "glibc_printf_fphex#str.295") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 0)]).
