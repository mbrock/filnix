(** This file defines checked IR from glibc’s `stdlib/ldbl2mpn.os` object.
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

Definition fn___mpn_extract_long_double : func :=
  ir_fn{ "export" "__mpn_extract_long_double"(P %"v0", L %"v2", P %"v4", P %"v6", L %"v8", L %"v9") -> (RClass L) {
  @"start":
    %"v10" : P = (Alloc 16) #16;
    alloca "v12" 16;
    %"chk0" : A = (Check 0 8 Write 1) %"v10";
    store Wl [%"chk0" + 0] <- %"v8";
    %"v11" = %"v10" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v11";
    store Wl [%"chk1" + 0] <- %"v9";
    %"va_args" : P = VaArgs #48;
    %"chk2" : A = (HalfCheck Upper 0 10 Read 8) %"chk0", %"v10";
    %"v13" : Extended = (RawLoad LdX 0) %"chk2";
    %"chk3" : A = (CheckLocal (a "v12") 0 10 Write 8);
    store Wx [%"chk3" + 0] <- %"v13";
    %"chk4" : A = (CheckLocal (a "v12") 8 4 Read 1);
    %"v16" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v17" : W = Shl %"v16", #16;
    %"v18" : W = Shr %"v17", #31;
    %"chk5" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk5" + 0] <- %"v18";
    %"chk6" : A = (CheckLocal (a "v12") 8 4 Read 1);
    %"v21" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v22" : W = Shl %"v21", #17;
    %"v23" : W = Shr %"v22", #17;
    %"v24" : W = Sub %"v23", #16383;
    %"chk7" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk7" + 0] <- %"v24";
    %"chk8" : A = (CheckLocal (a "v12") 4 4 Read 1);
    %"v28" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v29" : L = (Ext Uw) %"v28";
    %"v30" : L = Shl %"v29", #32;
    %"chk9" : A = (CheckLocal (a "v12") 0 4 Read 1);
    %"v31" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"v32" : L = (Ext Uw) %"v31";
    %"v33" : L = Or %"v30", %"v32";
    %"chk10" : A = (Check 0 8 Write 1) %"v0";
    store Wl [%"chk10" + 0] <- %"v33";
    %"chk11" : A = (CheckLocal (a "v12") 8 4 Read 1);
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v39" : W = Shl %"v38", #17;
    %"v40" : W = Shr %"v39", #17;
    %"v41" : W = (Cmp Eq W) %"v40", #0
    => br %"v41" ? "L34" : "L35";
  @"L34":
    %"v47" : L = (RawLoad LdL 0) %"chk10";
    %"v48" : W = (Cmp Eq L) %"v47", #0
    => br %"v48" ? "L49" : "L50";
  @"L49":
    %"v56" : L = (RawLoad LdL 0) %"chk10";
    %"v57" : W = (Cmp Eq L) %"v56", #0
    => goto "L50";
  @"L50" [%"v59" : W = phi("L34" => #0, "L49" => %"v57")]:
    => br %"v59" ? "L42" : "L43";
  @"L42":
    store Ww [%"chk7" + 0] <- #0
    => goto "L36";
  @"L43":
    %"v67" : L = (RawLoad LdL 0) %"chk10";
    %"v72" : L = And %"v67", #9223372036854775807;
    store Wl [%"chk10" + 0] <- %"v72";
    %"v81" : L = (RawLoad LdL 0) %"chk10";
    %"v82" : W = (Cmp Ne L) %"v81", #0
    => br %"v82" ? "L73" : "L74";
  @"L73":
    %"v88" : L = (RawLoad LdL 0) %"chk10";
    %"iw_1.v6" : W = (Cmp Eq L) %"v88", #0
    => br %"iw_1.v6" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v8" : L = Shr %"v88", #1;
    %"iw_1.v9" : L = Or %"v88", %"iw_1.v8";
    %"iw_1.v10" : L = Shr %"iw_1.v9", #2;
    %"iw_1.v11" : L = Or %"iw_1.v9", %"iw_1.v10";
    %"iw_1.v12" : L = Shr %"iw_1.v11", #4;
    %"iw_1.v13" : L = Or %"iw_1.v11", %"iw_1.v12";
    %"iw_1.v14" : L = Shr %"iw_1.v13", #8;
    %"iw_1.v15" : L = Or %"iw_1.v13", %"iw_1.v14";
    %"iw_1.v16" : L = Shr %"iw_1.v15", #16;
    %"iw_1.v17" : L = Or %"iw_1.v15", %"iw_1.v16";
    %"iw_1.v18" : L = Shr %"iw_1.v17", #32;
    %"iw_1.v19" : L = Or %"iw_1.v17", %"iw_1.v18";
    %"iw_1.v20" : L = Shr %"iw_1.v19", #1;
    %"iw_1.v21" : L = And %"iw_1.v20", #6148914691236517205;
    %"iw_1.v22" : L = Sub %"iw_1.v19", %"iw_1.v21";
    %"iw_1.v23" : L = And %"iw_1.v22", #3689348814741910323;
    %"iw_1.v24" : L = Shr %"iw_1.v22", #2;
    %"iw_1.v25" : L = And %"iw_1.v24", #3689348814741910323;
    %"iw_1.v26" : L = Add %"iw_1.v23", %"iw_1.v25";
    %"iw_1.v27" : L = Shr %"iw_1.v26", #4;
    %"iw_1.v28" : L = Add %"iw_1.v26", %"iw_1.v27";
    %"iw_1.v29" : L = And %"iw_1.v28", #1085102592571150095;
    %"iw_1.v30" : L = Mul %"iw_1.v29", #72340172838076673;
    %"iw_1.v31" : L = Shr %"iw_1.v30", #56;
    %"iw_1.v32" : L = Sub %"iw_1.v31", #64;
    %"iw_1.v33" : L = Neg %"iw_1.v32"
    => goto "iw_1.L4";
  @"iw_1.L4" [%"iw_1.v34" : W = phi("iw_1.L3" => %"iw_1.v33", "L73" => #64)]:
    %"v97" : W = (Cmp Ne W) %"iw_1.v34", #0
    => br %"v97" ? "L93" : "L95";
  @"L93":
    %"v103" : L = (RawLoad LdL 0) %"chk10";
    %"v105" : L = Shl %"v103", %"iw_1.v34";
    store Wl [%"chk10" + 0] <- %"v105"
    => goto "L95";
  @"L95":
    %"v110" : W = Sub #4294950914, %"iw_1.v34";
    store Ww [%"chk7" + 0] <- %"v110"
    => goto "L36";
  @"L74":
    %"v116" : L = (RawLoad LdL 0) %"chk10";
    %"v117" : W = (Cmp Ne L) %"v116", #0
    => br %"v117" ? "L111" : "L112";
  @"L111":
    %"v120" : L = (RawLoad LdL 0) %"chk10";
    %"iw_2.v6" : W = (Cmp Eq L) %"v120", #0
    => br %"iw_2.v6" ? "iw_2.L4" : "iw_2.L3";
  @"iw_2.L3":
    %"iw_2.v8" : L = Shr %"v120", #1;
    %"iw_2.v9" : L = Or %"v120", %"iw_2.v8";
    %"iw_2.v10" : L = Shr %"iw_2.v9", #2;
    %"iw_2.v11" : L = Or %"iw_2.v9", %"iw_2.v10";
    %"iw_2.v12" : L = Shr %"iw_2.v11", #4;
    %"iw_2.v13" : L = Or %"iw_2.v11", %"iw_2.v12";
    %"iw_2.v14" : L = Shr %"iw_2.v13", #8;
    %"iw_2.v15" : L = Or %"iw_2.v13", %"iw_2.v14";
    %"iw_2.v16" : L = Shr %"iw_2.v15", #16;
    %"iw_2.v17" : L = Or %"iw_2.v15", %"iw_2.v16";
    %"iw_2.v18" : L = Shr %"iw_2.v17", #32;
    %"iw_2.v19" : L = Or %"iw_2.v17", %"iw_2.v18";
    %"iw_2.v20" : L = Shr %"iw_2.v19", #1;
    %"iw_2.v21" : L = And %"iw_2.v20", #6148914691236517205;
    %"iw_2.v22" : L = Sub %"iw_2.v19", %"iw_2.v21";
    %"iw_2.v23" : L = And %"iw_2.v22", #3689348814741910323;
    %"iw_2.v24" : L = Shr %"iw_2.v22", #2;
    %"iw_2.v25" : L = And %"iw_2.v24", #3689348814741910323;
    %"iw_2.v26" : L = Add %"iw_2.v23", %"iw_2.v25";
    %"iw_2.v27" : L = Shr %"iw_2.v26", #4;
    %"iw_2.v28" : L = Add %"iw_2.v26", %"iw_2.v27";
    %"iw_2.v29" : L = And %"iw_2.v28", #1085102592571150095;
    %"iw_2.v30" : L = Mul %"iw_2.v29", #72340172838076673;
    %"iw_2.v31" : L = Shr %"iw_2.v30", #56;
    %"iw_2.v32" : L = Sub %"iw_2.v31", #64;
    %"iw_2.v33" : L = Neg %"iw_2.v32"
    => goto "iw_2.L4";
  @"iw_2.L4" [%"iw_2.v34" : W = phi("iw_2.L3" => %"iw_2.v33", "L111" => #64)]:
    %"v132" : L = (RawLoad LdL 0) %"chk10";
    %"v134" : L = Shl %"v132", %"iw_2.v34";
    store Wl [%"chk10" + 0] <- %"v134";
    store Wl [%"chk10" + 0] <- #0;
    %"v142" : W = Sub #4294950850, %"iw_2.v34";
    store Ww [%"chk7" + 0] <- %"v142"
    => goto "L36";
  @"L112":
    store Wl [%"chk10" + 0] <- #9223372036854775808;
    store Ww [%"chk7" + 0] <- #4294950914
    => goto "L36";
  @"L35":
    %"chk30" : A = (CheckLocal (a "v12") 8 4 Read 1);
    %"v152" : W = (RawLoad (LdNarrow Uw) 0) %"chk30";
    %"v153" : W = Shl %"v152", #17;
    %"v154" : W = Shr %"v153", #17;
    %"v155" : W = (Cmp Slt W) %"v154", #32767
    => br %"v155" ? "L156" : "L157";
  @"L156":
    %"v163" : L = (RawLoad LdL 0) %"chk10";
    %"v164" : W = (Cmp Eq L) %"v163", #0
    => goto "L157";
  @"L157" [%"v166" : W = phi("L35" => #0, "L156" => %"v164")]:
    => br %"v166" ? "L148" : "L36";
  @"L148":
    store Ww [%"chk7" + 0] <- #0
    => goto "L36";
  @"L36":
    => ret #1
} }.
