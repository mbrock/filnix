(** This file defines checked IR from glibc’s `stdlib/dbl2mpn.os` object.
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

Definition fn___mpn_extract_double : func :=
  ir_fn{ "export" "__mpn_extract_double"(P %"v0", L %"v2", P %"v4", P %"v6", Double %"v8") -> (RClass L) {
  @"start":
    alloca "v10" 8;
    %"chk0" : A = (CheckLocal (a "v10") 0 8 Write 1);
    store Wd [%"chk0" + 0] <- %"v8";
    %"chk1" : A = (CheckLocal (a "v10") 4 4 Read 1);
    %"v14" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v15" : W = Shr %"v14", #31;
    %"chk2" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk2" + 0] <- %"v15";
    %"chk3" : A = (CheckLocal (a "v10") 4 4 Read 1);
    %"v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v19" : W = Shl %"v18", #1;
    %"v20" : W = Shr %"v19", #21;
    %"v21" : W = Sub %"v20", #1023;
    %"chk4" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk4" + 0] <- %"v21";
    %"chk5" : A = (CheckLocal (a "v10") 4 4 Read 1);
    %"v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v26" : W = Shl %"v25", #12;
    %"v27" : W = Shr %"v26", #12;
    %"v28" : L = (Ext Sw) %"v27";
    %"v29" : L = Shl %"v28", #32;
    %"chk6" : A = (CheckLocal (a "v10") 0 4 Read 1);
    %"v30" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v31" : L = (Ext Uw) %"v30";
    %"v32" : L = Or %"v29", %"v31";
    %"chk7" : A = (Check 0 8 Write 1) %"v0";
    store Wl [%"chk7" + 0] <- %"v32";
    %"chk8" : A = (CheckLocal (a "v10") 4 4 Read 1);
    %"v37" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v38" : W = Shl %"v37", #1;
    %"v39" : W = Shr %"v38", #21;
    %"v40" : W = (Cmp Eq W) %"v39", #0
    => br %"v40" ? "L33" : "L34";
  @"L33":
    %"v46" : L = (RawLoad LdL 0) %"chk7";
    %"v47" : W = (Cmp Eq L) %"v46", #0
    => br %"v47" ? "L48" : "L49";
  @"L48":
    %"v55" : L = (RawLoad LdL 0) %"chk7";
    %"v56" : W = (Cmp Eq L) %"v55", #0
    => goto "L49";
  @"L49" [%"v58" : W = phi("L33" => #0, "L48" => %"v56")]:
    => br %"v58" ? "L41" : "L42";
  @"L41":
    store Ww [%"chk4" + 0] <- #0
    => goto "L35";
  @"L42":
    %"v69" : L = (RawLoad LdL 0) %"chk7";
    %"v70" : W = (Cmp Ne L) %"v69", #0
    => br %"v70" ? "L61" : "L62";
  @"L61":
    %"v76" : L = (RawLoad LdL 0) %"chk7";
    %"iw_1.v6" : W = (Cmp Eq L) %"v76", #0
    => br %"iw_1.v6" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v8" : L = Shr %"v76", #1;
    %"iw_1.v9" : L = Or %"v76", %"iw_1.v8";
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
  @"iw_1.L4" [%"iw_1.v34" : W = phi("iw_1.L3" => %"iw_1.v33", "L61" => #64)]:
    %"v86" : W = Sub %"iw_1.v34", #11;
    %"v92" : L = (RawLoad LdL 0) %"chk7";
    %"v94" : L = Shl %"v92", %"v86";
    store Wl [%"chk7" + 0] <- %"v94";
    %"v99" : W = Sub #4294966274, %"v86";
    store Ww [%"chk4" + 0] <- %"v99"
    => goto "L35";
  @"L62":
    %"v102" : L = (RawLoad LdL 0) %"chk7";
    %"iw_2.v6" : W = (Cmp Eq L) %"v102", #0
    => br %"iw_2.v6" ? "iw_2.L4" : "iw_2.L3";
  @"iw_2.L3":
    %"iw_2.v8" : L = Shr %"v102", #1;
    %"iw_2.v9" : L = Or %"v102", %"iw_2.v8";
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
  @"iw_2.L4" [%"iw_2.v34" : W = phi("iw_2.L3" => %"iw_2.v33", "L62" => #64)]:
    %"v115" : W = (Cmp Sge W) %"iw_2.v34", #11
    => br %"v115" ? "L107" : "L108";
  @"L107":
    %"v123" : L = (RawLoad LdL 0) %"chk7";
    %"v129" : W = Sub %"iw_2.v34", #11;
    %"v130" : L = Shl %"v123", %"v129";
    store Wl [%"chk7" + 0] <- %"v130";
    store Wl [%"chk7" + 0] <- #0
    => goto "L109";
  @"L108":
    %"v140" : L = (RawLoad LdL 0) %"chk7";
    %"v146" : W = Sub #11, %"iw_2.v34";
    %"v147" : L = Shr %"v140", %"v146";
    store Wl [%"chk7" + 0] <- %"v147";
    %"v150" : L = (RawLoad LdL 0) %"chk7";
    %"v157" : W = Sub #64, %"v146";
    %"v158" : L = Shl %"v150", %"v157";
    store Wl [%"chk7" + 0] <- %"v158"
    => goto "L109";
  @"L109":
    %"v169" : W = Sub #4294966221, %"iw_2.v34";
    store Ww [%"chk4" + 0] <- %"v169"
    => goto "L35";
  @"L34":
    %"v175" : L = (RawLoad LdL 0) %"chk7";
    %"v181" : L = Or %"v175", #4503599627370496;
    store Wl [%"chk7" + 0] <- %"v181"
    => goto "L35";
  @"L35":
    => ret #1
} }.
